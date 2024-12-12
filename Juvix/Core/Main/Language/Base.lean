
namespace Juvix.Core.Main

abbrev Name : Type := String

inductive Constant : Type where
  | int : Int → Constant
  | string : String → Constant
  deriving Inhabited, DecidableEq

inductive BuiltinOp : Type where
  | add_int : BuiltinOp
  | sub_int : BuiltinOp
  | mul_int : BuiltinOp
  | div_int : BuiltinOp
  deriving Inhabited, DecidableEq

mutual
  inductive Expr : Type where
    | var : Nat → Expr
    | ident : Name → Expr
    | const : Constant → Expr
    | app : Expr → Expr → Expr
    | builtin_app : (oper : BuiltinOp) → (args : List Expr) → Expr
    | constr_app : (constr : Name) → (args : List Expr) → Expr
    | lambda : (body : Expr) → Expr
    | let : (value : Expr) → (body : Expr) → Expr
    | case : (value : Expr) → (branches : List CaseBranch) → Expr
    | unit : Expr
    deriving Inhabited

  structure CaseBranch where
    constr : Name
    body : Expr
end

structure Program where
  defs : List Expr

end Juvix.Core.Main
