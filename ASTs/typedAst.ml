open CommonAST
open ParserAST

type ty =
  | TUnit | TBit | TBitArray of static_exp | TProd of ty list
  | TVar of link ref
and link =
  | TIndex of int
  | TLink of ty
let invalid_type = TUnit
