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

import bitops

type
  Exponent* = distinct uint16
    ## A type that can store the biggest IEEE exponent of supported float types
  Fraction* = distinct uint64
    ## A type that can store the biggest IEEE fraction of supported float types

  FloatClass* = enum
    fcNormal = "Normal"
    fcSubnormal = "Subnormal"
    fcZero = "0E0"
    fcNegZero = "-0E0"
    fcInf = "Infinity"
    fcNegInf = "-Infinity"
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

func isNegative*(f: SomeFloat): bool {.inline.} =
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
      if f.isNegative:
        fcNegZero
      else:
        fcZero
    else:
      fcSubnormal
  of f.expMax.Exponent:
    if f.fraction == 0.Fraction:
      if f.isNegative:
        fcNegInf
      else:
        fcInf
    else:
      fcNaN
  else:
    fcNormal

type
  UnifiedFloat = object
    negative: bool
    frac: Fraction
    exponent: Exponent

func addF(s: var string, f: SomeFloat) =
  let class = f.classify
  if class notin {fcSubnormal, fcNormal}:
    s.add $class
    return

  # An IEEE float is encoded as:
  #   sign (bool) | exponent (uint) | fraction (uint)
  #
  # Ignoring special cases, the number it represents is calculated using this
  # formula:
  #   (-1) ^ sign.ord * 2 ^ (exp - exponent_bias) * frac * 2 ^ (-fractionBitSize)
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
  let
    sign = if f.isNegative: -1 else: 1
    frac =
      if class == fcNormal:
        f.fraction.uint64 + 2 shl (f.fractionBitSize - 1)
      else:
        f.fraction.uint64
    exp =
      if class == fcNormal:
        f.exponent.int - f.expBias.int - f.fractionBitSize
      else:
        1 - f.expBias.int - f.fractionBitSize

when isMainModule:
  import unittest

  check classify(0.0f32) == fcZero
  check classify(0.0f64) == fcZero
  check classify(-0.0f32) == fcNegZero
  check classify(-0.0f64) == fcNegZero
  check classify(Inf.float32) == fcInf
  check classify(Inf.float64) == fcInf
  check classify(NegInf.float32) == fcNegInf
  check classify(NegInf.float64) == fcNegInf
  check classify(NaN.float32) == fcNaN
  check classify(NaN.float64) == fcNaN
  check classify(1.0f32) == fcNormal
  check classify(1.0f64) == fcNormal
  check classify(-1.0f32) == fcNormal
  check classify(-1.0f64) == fcNormal
  check classify(7.175E-43f32) == fcSubnormal
  check classify(1.8459939872957E-310f64) == fcSubnormal

  var s: string
  s.addF NaN
  echo s
  s.addF 10.1
  s.addF 7.175E-43f32
