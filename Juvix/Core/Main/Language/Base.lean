
import Batteries.Data.AssocList
import Mathlib.Data.Set.Basic

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

infixr:80 "@@" => Expr.app

def Expr.mk_app (f : Expr) : List Expr → Expr
  | [] => f
  | x :: xs => Expr.mk_app (Expr.app f x) xs

-- The domain of a program is the set of names of its definitions.
def Program.dom (p : Program) : Set Name :=
  {x | x ∈ p.defs.toList.map Prod.fst}

-- The domain of an expression is the set of identifiers referenced in the
-- expression.
@[simp]
def Expr.dom (e : Expr) : Set Name :=
  match e with
  | Expr.var _ => ∅
  | Expr.ident n => {n}
  | Expr.constr _ => ∅
  | Expr.const _ => ∅
  | Expr.app f x => f.dom ∪ x.dom
  | Expr.constr_app c x => c.dom ∪ x.dom
  | Expr.binop _ x y => x.dom ∪ y.dom
  | Expr.lambda b => b.dom
  | Expr.save v b => v.dom ∪ b.dom
  | Expr.branch _ b n => b.dom ∪ n.dom
  | Expr.default b => b.dom
  | Expr.unit => ∅

def Program.dom_ok (p : Program) : Prop :=
  p.main.dom ⊆ p.dom ∧
  ∀ (n : Name) (e : Expr), p.defs.find? n = some e → e.dom ⊆ p.dom

end Juvix.Core.Main
