type expr =
    | Application of expr * expr
    | Abstraction of expr * expr
    | Value of string;;