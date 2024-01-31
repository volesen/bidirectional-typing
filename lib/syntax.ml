type ty = TInt | TBool | TVar of int | TArr of ty * ty

type binop = Add | Sub

type expr =
  | EInt of int
  | EBool of bool
  | EVar of string
  | ELet of string * expr * expr
  | EBinop of binop * expr * expr
  | EIf of expr * expr * expr
  | EFun of string * expr
  | EApp of expr * expr
