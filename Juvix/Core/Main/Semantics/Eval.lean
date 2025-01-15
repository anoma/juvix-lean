
import Juvix.Core.Main.Language
import Mathlib.Tactic.CC

namespace Juvix.Core.Main

def eval_binop_int (op : BinaryOp) (i₁ i₂ : Int) : Int :=
  match op with
  | BinaryOp.add_int => i₁ + i₂
  | BinaryOp.sub_int => i₁ - i₂
  | BinaryOp.mul_int => i₁ * i₂
  | BinaryOp.div_int => i₁ / i₂

inductive Eval (P : Program) : Env → Expr → Value → Prop where
  | eval_var {env idx val} :
    env.get? idx = some val →
    Eval P env (Expr.var idx) val
  | eval_ident {env name expr val} :
    P.defs.find? name = some expr →
    Eval P [] expr val →
    Eval P env (Expr.ident name) val
  | eval_const {env c} :
    Eval P env (Expr.const c) (Value.const c)
  | eval_app {env env' f body arg val val'} :
    Eval P env f (Value.closure env' body) →
    Eval P env arg val →
    Eval P (val :: env') body val' →
    Eval P env (Expr.app f arg) val'
  | eval_constr_app {env ctr ctr_name ctr_args_rev arg val} :
    Eval P env ctr (Value.constr_app ctr_name ctr_args_rev) →
    Eval P env arg val →
    Eval P env (Expr.constr_app ctr arg) (Value.constr_app ctr_name (val :: ctr_args_rev))
  | eval_binop {env op arg₁ arg₂ val₁ val₂} :
    Eval P env arg₁ (Value.const (Constant.int val₁)) →
    Eval P env arg₂ (Value.const (Constant.int val₂)) →
    Eval P env (Expr.binop op arg₁ arg₂) (Value.const (Constant.int (eval_binop_int op val₁ val₂)))
  | eval_lambda {env body} :
    Eval P env (Expr.lambda body) (Value.closure env body)
  | eval_save {env value body val val'} :
    Eval P env value val →
    Eval P (val :: env) body val' →
    Eval P env (Expr.save value body) val'
  | eval_branch_matches {env name args_rev body val} :
    Eval P (args_rev ++ env) body val →
    Eval P (Value.constr_app name args_rev :: env) (Expr.branch name body _) val
  | eval_branch_fails {env name name' next val} :
    name ≠ name' →
    Eval P env next val →
    Eval P (Value.constr_app name _ :: env) (Expr.branch name' _ next) val
  | eval_default {env body val} :
    Eval P env body val →
    Eval P (_ :: env) (Expr.default body) val
  | eval_unit {env} :
    Eval P env Expr.unit Value.unit

notation "⟨" P "⟩ " env " ⊢ " e " ↦ " v:40 => Eval P env e v

def Eval.Defined (P : Program) (env : Env) (e : Expr) : Prop :=
  ∃ v, ⟨P⟩ env ⊢ e ↦ v

notation "⟨" P "⟩ " env " ⊢ " e:40 " ↓" => Eval.Defined P env e

-- The evaluation relation is deterministic.
theorem Eval.deterministic {P env e v₁ v₂} (h₁ : ⟨P⟩ env ⊢ e ↦ v₁) (h₂ : ⟨P⟩ env ⊢ e ↦ v₂) : v₁ = v₂ := by
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

end Juvix.Core.Main
