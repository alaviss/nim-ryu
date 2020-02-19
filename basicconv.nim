#
#           Basic float-to-string converter
#
#  Copyright (c) 2020 Leorize <leorize+oss@disroot.org>
#

## This converter is based upon the "Basic Conversion Routine" depicted in
## `"Ryū: fast float-to-string conversion" <https://doi.org/10.1145/3296979.3192369>`_
##
## This converter aims for correctness over performance, and is used as a
## reference to evaluate other algorithms, such as ryū. It should not be used
## in production due to slow arithmetic regarding larger float sizes.

import bitops, typetraits, strutils

type
  Exponent* = distinct int16
    ## A type that can store the biggest IEEE exponent of supported float types
  Fraction* = distinct int64
    ## A type that can store the biggest IEEE fraction of supported float types

  FloatClass* = enum
    fcNormal = "Normal"
    fcSubnormal = "Subnormal"
    fcZero = "0E0"
    fcInf = "Infinity"
    fcNaN = "NaN"

proc `==`(a, b: Exponent): bool {.borrow.}
proc `==`(a, b: Fraction): bool {.borrow.}

template notSupp(T: typedesc[SomeFloat]) =
  {.error: "Unsupported float type: " & $T.}

template toImpl(f: SomeFloat): untyped =
  when f is float32:
    cast[uint32](f)
  elif f is float64:
    cast[uint64](f)
  else:
    notSupp typeof f

template fractionBitSize*(f: float32): int = 23
  ## The number of bits in the fraction part of IEEE binary32 format
template fractionBitSize*(f: float64): int = 52
  ## The number of bits in the fraction part of IEEE binary64 format
template expBitSize*(f: float32): int = 8
  ## The number of bits in the exponent part of IEEE binary32 format
template expBitSize*(f: float64): int = 11
  ## The number of bits in the exponent part of IEEE binary64 format

template fractionMask*(f: SomeFloat): untyped = 1 shl f.fractionBitSize - 1
  ## Mask to extract the fraction part from a float
template expMax*(f: SomeFloat): untyped = 1 shl f.expBitSize - 1
  ## The maximal value of the exponent part in a float
template expBias*(f: SomeFloat): untyped = 1 shl (f.expBitSize - 1) - 1
  ## The exponent bias of a float

func sign*(f: SomeFloat): bool {.inline.} =
  ## Check if the sign bit in the float is set.
  let impl = f.toImpl
  testBit(impl, sizeof(impl) * 8 - 1)

func exponent*(f: SomeFloat): Exponent {.inline.} =
  ## Extract the exponent part of the float.
  Exponent bitand(f.toImpl, f.expMax shl f.fractionBitSize) shr f.fractionBitSize

func fraction*(f: SomeFloat): Fraction {.inline.} =
  ## Extract the fraction part of the float.
  Fraction bitand(f.toImpl, f.fractionMask)

func classify*(f: SomeFloat): FloatClass {.inline.} =
  ## Classify the float into different classes.
  case f.exponent
  of 0.Exponent:
    if f.fraction == 0.Fraction:
      fcZero
    else:
      fcSubnormal
  of f.expMax.Exponent:
    if f.fraction == 0.Fraction:
      fcInf
    else:
      fcNaN
  else:
    fcNormal

template toBase[T](d: T): untyped =
  T.distinctBase()(d)

func addF(s: var string, f: SomeFloat) =
  let class = f.classify
  if class notin {fcSubnormal, fcNormal}:
    if class != fcNaN and f.sign:
      s.add '-'
    s.add $class
    return

  # An IEEE float is encoded as:
  #   sign (bool) | exponent (uint) | fraction (uint)
  #
  # Ignoring special cases, the number it represents is calculated using this
  # formula:
  #   (-1) ^ sign.ord * 2 ^ (exp - expBias) * frac * 2 ^ (-fractionBitSize)
  #   where
  #     frac =
  #       if exponent != 0:
  #         fraction + 2 ^ (fractionBitSize) -- normal case
  #       else:
  #         fraction -- subnormal case
  #     exp =
  #       if exponent != 0:
  #         exponent -- normal
  #       else:
  #         1 -- subnormal
  #
  # In here we flatten the formula into:
  #   sign * 2 ^ exp * frac
  #   where -- see below
  let
    sign = if f.sign: -1 else: 1
    frac =
      if class == fcNormal:
        f.fraction.toBase + 1 shl f.fractionBitSize
      else:
        f.fraction.toBase
    exp =
      if class == fcNormal:
        f.exponent.toBase - f.expBias - f.fractionBitSize
      else:
        1 - f.expBias - f.fractionBitSize

  # To generate a string representation, we want to change this:
  #   sign * 2 ^ exp * frac
  #
  # Into this:
  #   sign * 10 ^ exp10 * frac10
  #
  # Which will allow us to print the fraction using a simple
  # int-to-string function, then place the decimal point according to the
  # exponent.
  #
  # But it's not that easy. Here's how 10.1 is represented in IEEE single
  # precision binary floating point:
  #
  #   sign|exponent|       fraction
  #      0|10000010|01000011001100110011010
  #
  # Which translates exactly to:
  #   10.1000003814697265625
  #
  # which is the closest possible representation of 10.1 in IEEE binary32 float.
  #
  # But we want to print 10.1, so we have to find a way to omit unneeded digits
  #   10.1000003814697265625
  #       ^~~~~~~~~~~~~~~~~~
  #       we want to get rid of this
  #
  # According to the "Ryū" paper, the interval in which we would find the
  # desired output would be the halfway point between the next smaller and
  # larger floating point values of the same type, which could be represented
  # like this with our flattened representation:
  #
  #   (frac * 2 ^ exp + (frac - 1) * 2 ^ exp) / 2 .. (frac * 2 ^ exp + (frac + 1) * 2 ^ exp) / 2
  #    ^~~~~~~~~~~~~~   ^~~~~~~~~~~~~~~~~~~~                           ^~~~~~~~~~~~~~~~~~~~
  #    our current float  the next smaller float                       the next larger float
  #
  # However, notice the phrase "floating point values of the same type".
  # This forces us to take the type of the current float into account, meaning:
  # [(frac - 1) * 2 ^ exp] and [(frac + 1) * 2 ^ exp] each must be representable
  # by the current floating point type. We don't evaluate the sign here since
  # it doesn't affect the precision of the floating point type. We also assume
  # that infinity doesn't exist, since if we represent infinity just like any
  # other normal number, it will be the next larger float of the largest
  # representable float, so ignoring it will simplify calculations.
  #
  # Refering to the floating point type described above, `fraction` is stored
  # as an uint, which means that the overflow/underflow behavior of it must be
  # taken into account.
  #
  # If `fraction` is at maximum (2 ^ fractionBitSize - 1), then the next larger
  # floating point value will be:
  #   2 ^ (exp' - expBias) * frac' * 2 ^ (-fractionBitSize)
  #   where
  #     frac' = 2 ^ fractionBitSize
  #     exp' =
  #       if exponent != 0:
  #         exponent + 1 -- normal
  #       else:
  #         1 -- subnormal
  #
  # Which, in our flattened representation, will be:
  #   2 ^ exp' * frac'
  #   where
  #     exp' =
  #       if exponent != 0:
  #         exponent + 1 - expBias - fractionBitSize -- normal
  #       else:
  #         1 - expBias - fractionBitSize -- subnormal
  #
  # Let's see if our "next larger float" is the same as this float:
  #     2 ^ exp' * frac' = 2 ^ exp * (frac + 1)
  # if exponent == 0:
  #     exp' = exp
  #     frac = 2 ^ fractionBitSize - 1
  # <=> 2 ^ exp * frac' = 2 ^ exp * (frac + 1)
  # <=> 2 ^ exp * 2 ^ fractionBitSize = 2 ^ exp * (frac + 1)
  # <=> 2 ^ exp * (2 ^ fractionBitSize - 1 + 1) = 2 ^ exp * (frac + 1)
  # <=> 2 ^ exp * (fraction + 1) = 2 ^ exp * (frac + 1)
  # <=> 2 ^ exp * (frac + 1) = 2 ^ exp * (frac + 1)
  # else:
  #     exp' = exp + 1
  #     frac = 2 ^ (fractionBitSize + 1) - 1
  # <=> 2 ^ (exp + 1) * frac' = 2 ^ exp * (frac + 1)
  # <=> 2 ^ (exp + 1) * 2 ^ fractionBitSize = 2 ^ exp * (frac + 1)
  # <=> 2 ^ exp * 2 ^ (fractionBitSize + 1) = 2 ^ exp * (frac + 1)
  # <=> 2 ^ exp * (2 ^ (fractionBitSize + 1) - 1 + 1) = 2 ^ exp * (frac + 1)
  # <=> 2 ^ exp * (frac + 1) = 2 ^ exp * (frac + 1)
  #
  # So yes, our "next larger float" should be the same as this one.

when isMainModule:
  import unittest

  check classify(0.0f32) == fcZero
  check classify(0.0f64) == fcZero
  check classify(-0.0f32) == fcZero
  check classify(-0.0f64) == fcZero
  check classify(Inf.float32) == fcInf
  check classify(Inf.float64) == fcInf
  check classify(NegInf.float32) == fcInf
  check classify(NegInf.float64) == fcInf
  check classify(NaN.float32) == fcNaN
  check classify(NaN.float64) == fcNaN
  check classify(1.0f32) == fcNormal
  check classify(1.0f64) == fcNormal
  check classify(-1.0f32) == fcNormal
  check classify(-1.0f64) == fcNormal
  check classify(7.175E-43f32) == fcSubnormal
  check classify(1.8459939872957E-310f64) == fcSubnormal

  check not sign(0.0f32)
  check not sign(0.0f64)
  check sign(-0.0f32)
  check sign(-0.0f64)
  check not sign(Inf.float32)
  check not sign(Inf.float64)
  check sign(NegInf.float32)
  check sign(NegInf.float64)

  var s: string
  s.addF NaN
  echo s
  s.addF 10.1
  s.addF 10.1f32
  s.addF 7.175E-43f32
