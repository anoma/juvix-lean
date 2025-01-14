
import Juvix.Core.Main.Semantics.Eval
import Juvix.Utils
import Mathlib.Tactic.Linarith
import Aesop

namespace Juvix.Core.Main

mutual
  @[aesop unsafe [constructors, cases]]
  inductive Value.Approx.Indexed (P : Program) : Nat → Value → Value → Prop where
    | unit {n} : Value.Approx.Indexed P n Value.unit Value.unit
    | const {n c} : Value.Approx.Indexed P n (Value.const c) (Value.const c)
    | constr_app {n ctr_name args_rev args_rev'} :
      args_rev.length = args_rev'.length →
      (∀ k < n, ∀ p ∈ List.zip args_rev args_rev', Value.Approx.Indexed P k (Prod.fst p) (Prod.snd p)) →
      Value.Approx.Indexed P n (Value.constr_app ctr_name args_rev) (Value.constr_app ctr_name args_rev')
    | closure {n ctx₁ body₁ ctx₂ body₂} :
      (∀ k < n, ∀ v v₁, ⟨P⟩ v :: ctx₁ ⊢ body₁ ↦ v₁ → Expr.ApproxEvals.Indexed P k (v :: ctx₂) body₂ v₁) →
      Value.Approx.Indexed P n (Value.closure ctx₁ body₁) (Value.closure ctx₂ body₂)

  -- We need `Expr.ApproxEvals.Indexed` in order to avoid existential quantification in
  -- the definition of `Value.Approx.Indexed`.
  @[aesop unsafe [constructors, cases]]
  inductive Expr.ApproxEvals.Indexed (P : Program) : Nat → Context → Expr → Value → Prop where
    | equiv {n ctx e v₁} v₂ :
      ⟨P⟩ ctx ⊢ e ↦ v₂ →
      Value.Approx.Indexed P n v₂ v₁ →
      Expr.ApproxEvals.Indexed P n ctx e v₁
end

def Value.Approx (P : Program) (v v' : Value) : Prop :=
  ∀ n, Value.Approx.Indexed P n v v'

def Expr.ApproxEvals (P : Program) (ctx : Context) (e : Expr) (v : Value) : Prop :=
  ∀ n, Expr.ApproxEvals.Indexed P n ctx e v

notation "⟨" P "⟩ " e " ≲ " e':40 => Value.Approx P e e'

notation "⟨" P "⟩ " ctx " ⊢ " e " ↦≳ " v:40 => Expr.ApproxEvals P ctx e v

def Expr.Approx (P₁ : Program) (ctx₁ : Context) (e₁ : Expr) (P₂ : Program) (ctx₂ : Context) (e₂ : Expr) : Prop :=
  (∀ v, ⟨P₁⟩ ctx₁ ⊢ e₁ ↦ v → ⟨P₂⟩ ctx₂ ⊢ e₂ ↦≳ v)

def Expr.Equiv (P₁ : Program) (ctx₁ : Context) (e₁ : Expr) (P₂ : Program) (ctx₂ : Context) (e₂ : Expr) : Prop :=
  Expr.Approx P₁ ctx₁ e₁ P₂ ctx₂ e₂ ∧ Expr.Approx P₂ ctx₂ e₂ P₁ ctx₁ e₁

notation "⟨" P₁ "⟩ " ctx₁ " ⊢ " e₁ " ≋ " "⟨" P₂ "⟩ " ctx₂ " ⊢ " e₂:40 => Expr.Equiv P₁ ctx₁ e₁ P₂ ctx₂ e₂

def Program.Equiv (P₁ P₂ : Program) : Prop :=
  ⟨P₁⟩ [] ⊢ P₁.main ≋ ⟨P₂⟩ [] ⊢ P₂.main

notation "⟨" P₁ "⟩ " " ≋ " "⟨" P₂ "⟩" => Program.Equiv P₁ P₂

lemma Value.Approx.Indexed.refl {P n v} : Value.Approx.Indexed P n v v := by
  revert n
  suffices ∀ n, ∀ k ≤ n, Value.Approx.Indexed P k v v by
    intro k
    exact this k k k.le_refl
  intro n
  induction n generalizing v with
  | zero =>
    intros k hk
    cases v
    case unit =>
      exact Value.Approx.Indexed.unit
    case const c =>
      exact Value.Approx.Indexed.const
    case constr_app ctr_name args_rev =>
      constructor
      · rfl
      · intros
        have : k = 0 := by linarith
        subst k
        contradiction
    case closure ctx body =>
      constructor
      · intros
        have : k = 0 := by linarith
        subst k
        contradiction
  | succ n ih =>
    intros k hk
    cases v
    case unit =>
      exact Value.Approx.Indexed.unit
    case const c =>
      exact Value.Approx.Indexed.const
    case constr_app ctr_name args_rev =>
      constructor
      · rfl
      · intros k' hk' p hp
        have h : p.fst = p.snd := Utils.zip_refl_eq args_rev p hp
        rw [h]
        have : k' ≤ n := by linarith
        aesop
    case closure ctx body =>
      constructor
      · intros k' hk' v v'
        have : k' ≤ n := by linarith
        aesop

lemma Value.Approx.Indexed.trans {P n v₁ v₂ v₃} : Value.Approx.Indexed P n v₁ v₂ → Value.Approx.Indexed P n v₂ v₃ → Value.Approx.Indexed P n v₁ v₃ := by
  revert n
  suffices ∀ n, ∀ k ≤ n, Indexed P k v₁ v₂ → Indexed P k v₂ v₃ → Value.Approx.Indexed P k v₁ v₃ by
    intro k
    exact this k k k.le_refl
  intros n
  induction n generalizing v₁ v₂ v₃ with
  | zero =>
    intros k hk h₁ h₂
    cases h₁
    case unit =>
      cases h₂
      case unit =>
        exact Value.Approx.Indexed.unit
    case const =>
      cases h₂
      case const =>
        exact Value.Approx.Indexed.const
    case constr_app ctr_name args_rev₁ args_rev₁' hlen₁ ch₁ =>
      cases h₂
      case constr_app args_rev₂ hlen₂ ch₂ =>
        constructor <;> aesop
    case closure ctx₁ body₁ ctx₁' body₁' ch₁ =>
      cases h₂
      case closure ctx₂ body₂ ch₂ =>
        constructor
        · intro k' hk' v v₁ h
          have : k = 0 := by linarith
          subst k
          contradiction
  | succ n ih =>
    intros k hk h₁ h₂
    cases h₁
    case unit =>
      cases h₂
      case unit =>
        exact Value.Approx.Indexed.unit
    case const =>
      cases h₂
      case const =>
        exact Value.Approx.Indexed.const
    case constr_app ctr_name args_rev args_rev' hlen₁ ch₁ =>
      cases h₂
      case constr_app args_rev'' hlen₂ ch₂ =>
        constructor
        · aesop
        · intro k' hk' p hp
          obtain ⟨p₁, hp₁, p₂, hp₂, h₁, h₂, h₃⟩ := Utils.zip_ex_mid3 args_rev args_rev' args_rev'' p hlen₁ hlen₂ hp
          have : k' ≤ n := by linarith
          aesop
    case closure ctx₁ body₁ ctx₂ body₂ ch₁ =>
      cases h₂
      case closure ctx₃ body₃ ch₂ =>
        constructor
        · intro k' hk' v v₁ h
          have ah₁ : Expr.ApproxEvals.Indexed P k' (v :: ctx₂) body₂ v₁ := by
            apply ch₁ <;> assumption
          obtain ⟨v₂, _, h₂⟩ := ah₁
          have ah₂ : Expr.ApproxEvals.Indexed P k' (v :: ctx₃) body₃ v₂ := by
            apply ch₂ <;> assumption
          obtain ⟨v₃, _, h₃⟩ := ah₂
          have : k' ≤ n := by linarith
          aesop

lemma Value.Approx.refl {P v} : ⟨P⟩ v ≲ v := by
  intro n
  exact Value.Approx.Indexed.refl

lemma Value.Approx.trans {P v₁ v₂ v₃} : ⟨P⟩ v₁ ≲ v₂ → ⟨P⟩ v₂ ≲ v₃ → ⟨P⟩ v₁ ≲ v₃ := by
  intros h₁ h₂
  intro n
  aesop (add unsafe apply Value.Approx.Indexed.trans)

lemma Value.Approx.zip_refl {P p} {l : List Value} (h : p ∈ l.zip l) : ⟨P⟩ p.fst ≲ p.snd := by
  have h : p.fst = p.snd := Utils.zip_refl_eq l p h
  rewrite [h]
  exact Value.Approx.refl

lemma Value.Approx.constr_app_inv {P ctr_name args_rev args_rev'} :
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ Value.constr_app ctr_name args_rev' →
  (∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ Prod.snd p) ∧
  args_rev.length = args_rev'.length := by
  intro h
  constructor
  case left =>
    intros p hp n
    cases (h (n + 1))
    case constr_app =>
      aesop
  case right =>
    cases (h 0)
    case constr_app =>
      aesop

lemma Value.Approx.constr_app {P ctr_name args_rev args_rev'} :
  args_rev.length = args_rev'.length →
  (∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ Prod.snd p) →
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ Value.constr_app ctr_name args_rev' := by
  intro hlen h n
  aesop

lemma Value.Approx.closure_inv {P ctx₁ body₁ ctx₂ body₂} :
  ⟨P⟩ Value.closure ctx₁ body₁ ≲ Value.closure ctx₂ body₂ →
  ∀ v v₁, ⟨P⟩ v :: ctx₁ ⊢ body₁ ↦ v₁ → ⟨P⟩ v :: ctx₂ ⊢ body₂ ↦≳ v₁ := by
  intro h v v₁ h' n
  cases (h n.succ)
  case closure h =>
    aesop

lemma Value.Approx.closure {P ctx₁ body₁ ctx₂ body₂} :
  (∀ v v₁, ⟨P⟩ v :: ctx₁ ⊢ body₁ ↦ v₁ → ⟨P⟩ v :: ctx₂ ⊢ body₂ ↦≳ v₁) →
  ⟨P⟩ Value.closure ctx₁ body₁ ≲ Value.closure ctx₂ body₂ := by
  intro h n
  aesop

end Juvix.Core.Main
