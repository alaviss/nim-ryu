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

import bitops, strutils, typetraits
import math except classify
import stint

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

template toImpl(f: float32): untyped = cast[uint32](f)
template toImpl(f: float64): untyped = cast[uint64](f)

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
  ## The maximal value of the exponent part in a float. Note that it is not
  ## the maximal valid value in an IEEE float.
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
  let sign = if f.sign: -1 else: 1

  var
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
  # floating point value of the same type will be:
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
  #
  # If `fraction` is at minimum (0), then the next smaller floating point value
  # of the same type will be:
  #   2 ^ (exp' - expBias) * frac' * 2 ^ (-fractionBitSize)
  #   where
  #     exp' =
  #       if exponent > 1:
  #         exponent - 1
  #       else:
  #         1
  #     frac' =
  #       if exponent > 1:
  #         2 ^ (fractionBitSize + 1) - 1
  #       else:
  #         2 ^ fractionBitSize - 1
  #
  # Which, in our flattened representation, will be:
  #   2 ^ exp' * frac'
  #   where
  #     exp' =
  #       if exponent > 1:
  #         exponent - 1 - expBias - fractionBitSize
  #       else:
  #         1 - expBias - fractionBitSize
  #
  # Let's see if our "next smaller float" is the same as this float:
  #   2 ^ exp' * frac' = 2 ^ exp * (frac - 1)
  # if exponent == 1:
  #     exp' = exp
  #     frac' = 2 ^ fractionBitSize - 1
  #     frac = 2 ^ fractionBitSize
  #     2 ^ exp * frac' = 2 ^ exp * (frac - 1)
  # <=> 2 ^ exp * (2 ^ fractionBitSize - 1) = 2 ^ exp * (frac - 1)
  # <=> 2 ^ exp * (frac - 1) = 2 ^ exp * (frac - 1)
  # elif exponent > 1:
  #     exp' = exp - 1
  #     frac' = 2 ^ (fractionBitSize + 1) - 1
  #     frac = 2 ^ fractionBitSize
  #     2 ^ (exp - 1) * frac' = 2 ^ exp * (frac - 1)
  # <=> 2 ^ (exp - 1) * (2 ^ (fractionBitSize + 1) - 1) = 2 ^ exp * (frac - 1)
  # <=> 2 ^ exp * (2 ^ fractionBitSize - 1/2) = 2 ^ exp * (frac - 1)
  # <=> 2 ^ exp * (frac - 1/2) = 2 ^ exp * (frac - 1) -- not true
  #
  # It appears that our representation only works when the exponent is equal
  # to 1 and fraction equals to 0. For when exponent is larger than 1 and
  # fraction equal to 0, it can be represented as shown above:
  #   2 ^ exp * (frac - 1/2)
  # = 2 ^ (exp - 1) * (2 * frac - 1) -- keeping frac as an uint
  #
  # Note that we do not consider when the exponent is 0 for this case, since
  # exponent = 0 and fraction = 0 is a special case (zero) and is already
  # handled above.
  #
  # In summary, to represent the next larger float and the next smaller float:
  # |-  2 ^ exp * (frac + 1) -- next larger
  # |
  # |-  2 ^ exp * frac -- current float
  # |
  # |   -- next smaller
  # |- |- exponent > 1 and fraction == 0: 2 ^ (exp - 1) * (2 * frac - 1)
  #    |- else: 2 ^ exp * (frac - 1)
  #
  # To keep things simple, let's use an unified exponent:
  #   exp' = exp - 1
  #   current float: 2 ^ exp' * 2 * frac
  #   next larger: 2 ^ exp' * (2 * frac + 2)
  #   next smaller:
  #     if exponent > 1 and fraction == 0:
  #       2 ^ exp' * (2 * frac - 1)
  #     else:
  #       2 ^ exp' * (2 * frac - 2)
  #
  # Now these will be our halfway points:
  #   exp' = exp - 1
  #   current float: 2 ^ exp' * 2 * frac
  #   half to next larger:
  #       (2 ^ exp' * (2 * frac + 2) + 2 ^ exp' * 2 * frac) / 2
  #     = 2 ^ exp' * (4 * frac + 2) / 2
  #     = 2 ^ (exp' - 1) * (4 * frac + 2)
  #   half to next smaller:
  #     if exponent > 1 and fraction == 0:
  #         (2 ^ exp' * (2 * frac - 1) + 2 ^ exp' * 2 * frac) / 2
  #       = 2 ^ exp' * (4 * frac - 1) / 2
  #       = 2 ^ (exp' - 1) * (4 * frac - 1)
  #     else:
  #         (2 ^ exp' * (2 * frac - 2) + 2 ^ exp' * 2 * frac) / 2
  #       = 2 ^ exp' * (4 * frac - 2) / 2
  #       = 2 ^ (exp' - 1) * (4 * frac - 2)
  #
  # Which we will again unify under the same exponent of:
  exp = exp - 2
  frac = 4 * frac
  let
    upperFrac = frac + 2
    lowerFrac =
      if f.exponent.toBase > 1 and f.fraction.toBase == 0:
        frac - 1
      else:
        frac - 2

  # Convert to decimal power base:
  # We want to find an exp10 so that:
  #   2 ^ exp * frac = 10 ^ exp10 * frac10
  # There are many options, but we will use the one as found in the paper as
  # it's related to the Ryū algorithm, which is based on this simple algorithm.
  let exp10 =
    if exp >= 0:
      0
    else:
      exp
  # Now we have a problem, if the exponent >= 0, then frac10 will be:
  #   frac * 2 ^ exp
  # where exp could be as big as 969 for float64. That's 1073 bits required!
  # Now if exponent < 0, then frac10 will be:
  #   frac * 5 ^ (-exp)
  # where exp might be -1076 for float64. That's 2551 bits required!
  # We clearly need a way to avoid usage of arbitrary precision integers.
  # Well that's the point of Ryū. So we are bringing in some outside help for
  # this.
  # Here we estimate the amount of bits needed to store the resuting frac10:
  #
  #   Our worst case scenario would be:
  #     frac = 2 ^ fractionBitSize - 1 -- maximal fraction
  #     exp = 1 - expBias - fractionBitSize - 2 -- minimal exponent
  #   which results in the equation:
  #     frac * 5 ^ (-exp)
  #   We can estimate the required bits by summing the amount of bits required
  #   for each of the components, which is:
  #     fracBits = fractionBitSize
  #     5 ^ (-exp) = 3 * -(1 - expBias + fractionBitSize - 2)
  #   or:
  #     frac10Bits = fractionBitSize + 3 * (expBias - 1 - fractionBitSize + 2)
  #   Then we find the nearest power of two of frac10Bits to use with stint.
  const Bits = nextPowerofTwo f.fractionBitSize + 3 * (f.expBias - 1 - f.fractionBitSize + 2)
  type Fraction10 = ref StUint[Bits]
  # this have to be stored on the heap due to it's huge size (might be over
  # a half of the typical stack size).
  let
    frac10 = new Fraction10
    upperFrac10 = new Fraction10
    lowerFrac10 = new Fraction10
  template toFrac10(frac: untyped): untyped =
    if exp >= 0:
      frac.stuint(Bits) shl exp.int
    else:
      # will be an integer since exp < 0
      frac.stuint(Bits) * 5.stuint(Bits).pow(-exp)
  frac10[] = frac.toFrac10
  upperFrac10[] = frac.toFrac10
  lowerFrac10[] = frac.toFrac10

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
