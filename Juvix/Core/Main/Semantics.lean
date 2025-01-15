
import Juvix.Core.Main.Language
import Mathlib.Tactic.CC

namespace Juvix.Core.Main

def eval_binop_int (op : BinaryOp) (i₁ i₂ : Int) : Int :=
  match op with
  | BinaryOp.add_int => i₁ + i₂
  | BinaryOp.sub_int => i₁ - i₂
  | BinaryOp.mul_int => i₁ * i₂
  | BinaryOp.div_int => i₁ / i₂

inductive Eval (P : Program) : Context → Expr → Value → Prop where
  | eval_var {ctx idx val} :
    ctx.get? idx = some val →
    Eval P ctx (Expr.var idx) val
  | eval_ident {ctx name expr val} :
    P.defs.find? name = some expr →
    Eval P [] expr val →
    Eval P ctx (Expr.ident name) val
  | eval_const {ctx c} :
    Eval P ctx (Expr.const c) (Value.const c)
  | eval_app {ctx ctx' f body arg val val'} :
    Eval P ctx f (Value.closure ctx' body) →
    Eval P ctx arg val →
    Eval P (val :: ctx') body val' →
    Eval P ctx (Expr.app f arg) val'
  | eval_constr_app {ctx ctr ctr_name ctr_args_rev arg val} :
    Eval P ctx ctr (Value.constr_app ctr_name ctr_args_rev) →
    Eval P ctx arg val →
    Eval P ctx (Expr.constr_app ctr arg) (Value.constr_app ctr_name (val :: ctr_args_rev))
  | eval_binop {ctx op arg₁ arg₂ val₁ val₂} :
    Eval P ctx arg₁ (Value.const (Constant.int val₁)) →
    Eval P ctx arg₂ (Value.const (Constant.int val₂)) →
    Eval P ctx (Expr.binop op arg₁ arg₂) (Value.const (Constant.int (eval_binop_int op val₁ val₂)))
  | eval_lambda {ctx body} :
    Eval P ctx (Expr.lambda body) (Value.closure ctx body)
  | eval_save {ctx value body val val'} :
    Eval P ctx value val →
    Eval P (val :: ctx) body val' →
    Eval P ctx (Expr.save value body) val'
  | eval_branch_matches {ctx name args_rev body val} :
    Eval P (args_rev ++ ctx) body val →
    Eval P (Value.constr_app name args_rev :: ctx) (Expr.branch name body _) val
  | eval_branch_fails {ctx name name' next val} :
    name ≠ name' →
    Eval P ctx next val →
    Eval P (Value.constr_app name _ :: ctx) (Expr.branch name' _ next) val
  | eval_default {ctx body val} :
    Eval P ctx body val →
    Eval P (_ :: ctx) (Expr.default body) val
  | eval_unit {ctx} :
    Eval P ctx Expr.unit Value.unit

notation "[" P "] " ctx " ⊢ " e " ↦ " v:40 => Eval P ctx e v

-- The evaluation relation is deterministic.
theorem Eval.deterministic {P ctx e v₁ v₂} (h₁ : [P] ctx ⊢ e ↦ v₁) (h₂ : [P] ctx ⊢ e ↦ v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | eval_var =>
    cases h₂ <;> cc
  | eval_ident _ _ ih =>
    specialize (@ih v₂)
    cases h₂ <;> cc
  | eval_const =>
    cases h₂ <;> cc
  | eval_app _ _ _ ih ih' aih =>
    cases h₂ with
    | eval_app hval harg =>
      apply aih
      specialize (ih hval)
      specialize (ih' harg)
      simp_all
  | eval_constr_app _ _ ih ih' =>
    cases h₂ with
    | eval_constr_app hctr harg =>
      specialize (ih hctr)
      specialize (ih' harg)
      simp_all
  | eval_binop _ _ ih₁ ih₂ =>
    cases h₂ with
    | eval_binop h₁ h₂ =>
      specialize (ih₁ h₁)
      specialize (ih₂ h₂)
      simp_all
  | eval_lambda =>
    cases h₂ <;> cc
  | eval_save _ _ ih ih' =>
    cases h₂ with
    | eval_save hval hbody =>
      specialize (ih hval)
      rw [<- ih] at hbody
      specialize (ih' hbody)
      simp_all
  | eval_branch_matches _ ih =>
    specialize (@ih v₂)
    cases h₂ <;> cc
  | eval_branch_fails _ _ ih =>
    specialize (@ih v₂)
    cases h₂ <;> cc
  | eval_default _ ih =>
    specialize (@ih v₂)
    cases h₂ <;> cc
  | eval_unit =>
    cases h₂ <;> cc

-- The termination predicate for values. It is too strong for higher-order
-- functions -- requires termination for all function arguments, even
-- non-terminating ones.
inductive Value.Terminating (P : Program) : Value → Prop where
  | const {c} : Value.Terminating P (Value.const c)
  | constr_app {ctr_name args_rev} :
    Value.Terminating P (Value.constr_app ctr_name args_rev)
  | closure {ctx body} :
    (∀ v v',
      [P] v :: ctx ⊢ body ↦ v' →
      Value.Terminating P v') →
    Value.Terminating P (Value.closure ctx body)
  | unit : Value.Terminating P Value.unit

def Expr.Terminating (P : Program) (ctx : Context) (e : Expr) : Prop :=
  (∃ v, [P] ctx ⊢ e ↦ v ∧ Value.Terminating P v)

def Program.Terminating (P : Program) : Prop :=
  Expr.Terminating P [] P.main

lemma Eval.Expr.Terminating {P ctx e v} :
  Expr.Terminating P ctx e → [P] ctx ⊢ e ↦ v → Value.Terminating P v := by
  intro h₁ h₂
  rcases h₁ with ⟨v', hval, hterm⟩
  rewrite [Eval.deterministic h₂ hval]
  assumption

end Juvix.Core.Main
