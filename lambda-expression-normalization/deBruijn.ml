type expr =
    | Application of expr * expr
    | Abstraction of expr
    | Value of int
    | Free_Value of string;;
