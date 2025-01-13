
import Juvix.Core.Main.Language
import Mathlib.Tactic.CC
import Juvix.Utils
import Aesop

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

notation "⟨" P "⟩ " ctx " ⊢ " e " ↦ " v:40 => Eval P ctx e v

-- The evaluation relation is deterministic.
theorem Eval.deterministic {P ctx e v₁ v₂} (h₁ : ⟨P⟩ ctx ⊢ e ↦ v₁) (h₂ : ⟨P⟩ ctx ⊢ e ↦ v₂) : v₁ = v₂ := by
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

mutual
  @[aesop unsafe [constructors, cases]]
  inductive Value.Approx.Indexed (P : Program) : Nat → Value → Value → Prop where
    | refl {n v} : Value.Approx.Indexed P n v v
    | constr_app {n ctr_name args_rev args_rev'} :
      (∀ p ∈ List.zip args_rev args_rev', Value.Approx.Indexed P n (Prod.fst p) (Prod.snd p)) →
      Value.Approx.Indexed P (Nat.succ n) (Value.constr_app ctr_name args_rev) (Value.constr_app ctr_name args_rev')
    | closure {n ctx₁ body₁ ctx₂ body₂} :
      (∀ v v₁, ⟨P⟩ v :: ctx₁ ⊢ body₁ ↦ v₁ → Expr.ApproxEvals.Indexed P n (v :: ctx₂) body₂ v₁) →
      Value.Approx.Indexed P (Nat.succ n) (Value.closure ctx₁ body₁) (Value.closure ctx₂ body₂)

  -- We need `Expr.ApproxEvals.Indexed` in order to avoid existential quantification in
  -- the definition of `Value.Approx.Indexed`.
  @[aesop unsafe [constructors, cases]]
  inductive Expr.ApproxEvals.Indexed (P : Program) : Nat → Context → Expr → Value → Prop where
    | equiv {n ctx e v₁ v₂} :
      ⟨P⟩ ctx ⊢ e ↦ v₂ →
      Value.Approx.Indexed P n v₂ v₁ →
      Expr.ApproxEvals.Indexed P n ctx e v₁
end

lemma Value.Approx.Indexed.monotone {P n n' v v'} (h : Value.Approx.Indexed P n v v') (h' : n ≤ n') : Value.Approx.Indexed P n' v v' := by
  induction n' generalizing n v v' with
  | zero =>
    cases h'
    exact h
  | succ n' ih =>
    cases h'
    case succ.refl =>
      exact h
    case succ.step h' =>
      have ih' : Indexed P n' v v' := by
        apply ih
        case h =>
          exact h
        case h' =>
          exact h'
      cases ih'
      case refl =>
        exact Value.Approx.Indexed.refl
      case constr_app n' ctr_name args_rev args_rev' ch =>
        aesop
      case closure n' ctx₁ body₁ ctx₂ body₂ ch =>
        have : ∀ (v v' : Value), ⟨P⟩ v :: ctx₁ ⊢ body₁ ↦ v' → Expr.ApproxEvals.Indexed P n'.succ (v :: ctx₂) body₂ v' := by
          intro v v' h''
          have eh : Expr.ApproxEvals.Indexed P n' (v :: ctx₂) body₂ v' := by
            apply ch
            exact h''
          rcases eh with ⟨h1, h2⟩
          constructor
          exact h1
          aesop
        aesop

def Value.Approx (P : Program) (v v' : Value) : Prop :=
  ∃ n, Value.Approx.Indexed P n v v'

def Expr.ApproxEvals (P : Program) (ctx : Context) (e : Expr) (v : Value) : Prop :=
  ∃ n, Expr.ApproxEvals.Indexed P n ctx e v

notation "⟨" P "⟩ " e " ≲ " e':40 => Value.Approx P e e'

notation "⟨" P "⟩ " ctx " ⊢ " e " ↦≳ " v:40 => Expr.ApproxEvals P ctx e v

lemma Value.Approx.refl {P v} : ⟨P⟩ v ≲ v := by
  exists 0
  exact Value.Approx.Indexed.refl

lemma Value.Approx.zip_refl {P p} {l : List Value} (h : p ∈ l.zip l) : ⟨P⟩ p.fst ≲ p.snd := by
  have h : p.fst = p.snd := Utils.zip_refl_eq l p h
  rewrite [h]
  exact Value.Approx.refl

lemma Value.Approx.constr_app_inv {P ctr_name args_rev args_rev'} :
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ Value.constr_app ctr_name args_rev' →
  ∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ Prod.snd p := by
  intros h p hp
  rcases h with ⟨n, h⟩
  cases h
  case constr_app =>
    constructor
    aesop
  case refl =>
    exact Value.Approx.zip_refl hp

lemma Value.Approx.constr_app {P ctr_name args_rev args_rev'} :
  (∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ Prod.snd p) →
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ Value.constr_app ctr_name args_rev' := by
  intro h
  have h' : ∀ p ∈ List.zip args_rev args_rev', ∃ n, Value.Approx.Indexed P n (Prod.fst p) (Prod.snd p) := by
    aesop
  have nh : ∃ n, ∀ p ∈ List.zip args_rev args_rev', Value.Approx.Indexed P n (Prod.fst p) (Prod.snd p) := by
    apply Juvix.Utils.monotone_ex_all
    aesop (add unsafe apply Value.Approx.Indexed.monotone)
    assumption
  obtain ⟨n, h''⟩ := nh
  exists (Nat.succ n)
  constructor
  assumption

def Expr.Approx (P₁ : Program) (ctx₁ : Context) (e₁ : Expr) (P₂ : Program) (ctx₂ : Context) (e₂ : Expr) : Prop :=
  (∀ v, ⟨P₁⟩ ctx₁ ⊢ e₁ ↦ v → ⟨P₂⟩ ctx₂ ⊢ e₂ ↦≳ v)

def Expr.Equiv (P₁ : Program) (ctx₁ : Context) (e₁ : Expr) (P₂ : Program) (ctx₂ : Context) (e₂ : Expr) : Prop :=
  Expr.Approx P₁ ctx₁ e₁ P₂ ctx₂ e₂ ∧ Expr.Approx P₂ ctx₂ e₂ P₁ ctx₁ e₁

notation "⟨" P₁ "⟩ " ctx₁ " ⊢ " e₁ " ≋ " "⟨" P₂ "⟩ " ctx₂ " ⊢ " e₂:40 => Expr.Equiv P₁ ctx₁ e₁ P₂ ctx₂ e₂

def Program.Equiv (P₁ P₂ : Program) : Prop :=
  ⟨P₁⟩ [] ⊢ P₁.main ≋ ⟨P₂⟩ [] ⊢ P₂.main

notation "⟨" P₁ "⟩ " " ≋ " "⟨" P₂ "⟩" => Program.Equiv P₁ P₂

end Juvix.Core.Main
