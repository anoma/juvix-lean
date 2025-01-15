
import Juvix.Core.Main.Language.Base

namespace Juvix.Core.Main


inductive Context : Type where
  | hole : Context
  | app_left : Context → Expr → Context
  | app_right : Expr → Context → Context
  | constr_app_left : Context → Expr → Context
  | constr_app_right : Expr → Context → Context
  | binop_left : (oper : BinaryOp) → (arg₁ : Context) → (arg₂ : Expr) → Context
  | binop_right : (oper : BinaryOp) → (arg₁ : Expr) → (arg₂ : Context) → Context
  | lambda : (body : Context) → Context
  | save_left : (value : Context) → (body : Expr) → Context
  | save_right : (value : Expr) → (body : Context) → Context
  | branch_left : (constr : Name) → (body : Context) → (next : Expr) → Context
  | branch_right : (constr : Name) → (body : Expr) → (next : Context) → Context
  | default : (body : Context) → Context
  deriving Inhabited, BEq, DecidableEq

def Context.subst (C : Context) (e : Expr) : Expr :=
  match C with
  | Context.hole => e
  | Context.app_left C' e' => Expr.app (C'.subst e) e'
  | Context.app_right e' C' => Expr.app e' (C'.subst e)
  | Context.constr_app_left C' e' => Expr.constr_app (C'.subst e) e'
  | Context.constr_app_right e' C' => Expr.constr_app e' (C'.subst e)
  | Context.binop_left oper C₁ e₂ => Expr.binop oper (C₁.subst e) e₂
  | Context.binop_right oper e₁ C₂ => Expr.binop oper e₁ (C₂.subst e)
  | Context.lambda C' => Expr.lambda (C'.subst e)
  | Context.save_left C' e' => Expr.save (C'.subst e) e'
  | Context.save_right e' C' => Expr.save e' (C'.subst e)
  | Context.branch_left constr C' next => Expr.branch constr (C'.subst e) next
  | Context.branch_right constr body C' => Expr.branch constr body (C'.subst e)
  | Context.default C' => Expr.default (C'.subst e)

end Juvix.Core.Main
