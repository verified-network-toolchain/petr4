open Decimal
open Hexadecimal

type uint =
| UIntDecimal of Decimal.uint
| UIntHexadecimal of Hexadecimal.uint

type int =
| IntDecimal of Decimal.int
| IntHexadecimal of Hexadecimal.int
