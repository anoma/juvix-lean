
import Batteries.Data.AssocList

namespace Juvix.Core.Main

open Batteries

abbrev Name : Type := String

inductive Constant : Type where
  | int : Int → Constant
  | string : String → Constant
  deriving Inhabited, BEq, DecidableEq

inductive BinaryOp : Type where
  | add_int : BinaryOp
  | sub_int : BinaryOp
  | mul_int : BinaryOp
  | div_int : BinaryOp
  deriving Inhabited, BEq, DecidableEq

inductive Expr : Type where
  | var : Nat → Expr
  | ident : Name → Expr
  | constr : Name → Expr
  | const : Constant → Expr
  | app : Expr → Expr → Expr
  | constr_app : Expr → Expr → Expr
  | binop : (oper : BinaryOp) → (arg₁ arg₂ : Expr) → Expr
  | lambda : (body : Expr) → Expr
  | save : (value : Expr) → (body : Expr) → Expr
  | branch : (constr : Name) → (body : Expr) → (next : Expr) → Expr
  | default : (body : Expr) → Expr
  | unit : Expr
  deriving Inhabited, BEq, DecidableEq

structure Program where
  defs : AssocList Name Expr
  main : Expr

def Expr.mk_app (f : Expr) : List Expr → Expr
  | [] => f
  | x :: xs => Expr.mk_app (Expr.app f x) xs

end Juvix.Core.Main
