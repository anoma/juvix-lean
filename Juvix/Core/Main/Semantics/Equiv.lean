
import Juvix.Core.Main.Semantics.Eval
import Juvix.Utils
import Aesop

namespace Juvix.Core.Main

mutual
  @[aesop unsafe [constructors, cases]]
  inductive Value.Approx.Indexed (P : Program) : Nat → Value → Value → Prop where
    | refl {n v} : Value.Approx.Indexed P n v v
    | constr_app {n ctr_name args_rev args_rev'} :
      args_rev.length = args_rev'.length →
      (∀ p ∈ List.zip args_rev args_rev', Value.Approx.Indexed P n (Prod.fst p) (Prod.snd p)) →
      Value.Approx.Indexed P (Nat.succ n) (Value.constr_app ctr_name args_rev) (Value.constr_app ctr_name args_rev')
    | closure {n ctx₁ body₁ ctx₂ body₂} :
      (∀ v v₁, ⟨P⟩ v :: ctx₁ ⊢ body₁ ↦ v₁ → Expr.ApproxEvals.Indexed P n (v :: ctx₂) body₂ v₁) →
      Value.Approx.Indexed P (Nat.succ n) (Value.closure ctx₁ body₁) (Value.closure ctx₂ body₂)

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
  ∃ n, Value.Approx.Indexed P n v v'

def Expr.ApproxEvals (P : Program) (ctx : Context) (e : Expr) (v : Value) : Prop :=
  ∃ n, Expr.ApproxEvals.Indexed P n ctx e v

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
          rcases eh with ⟨_, h1, _⟩
          constructor
          exact h1
          aesop
        aesop

lemma Value.Approx.Indexed.trans {P n v₁ v₂ v₃} (h₁ : Value.Approx.Indexed P n v₁ v₂) (h₂ : Value.Approx.Indexed P n v₂ v₃) : Value.Approx.Indexed P n v₁ v₃ := by
  induction n generalizing v₁ v₂ v₃ with
  | zero =>
    cases h₁
    cases h₂
    exact Value.Approx.Indexed.refl
  | succ n ih =>
    cases h₁
    case refl =>
      exact h₂
    case constr_app ctr_name args_rev args_rev' hlen₁ ch₁ =>
      cases h₂
      case refl =>
        exact Value.Approx.Indexed.constr_app hlen₁ ch₁
      case constr_app args_rev'' hlen₂ ch₂ =>
        constructor
        · aesop
        · intro p hp
          obtain ⟨p₁, hp₁, p₂, hp₂, h₁, h₂, h₃⟩ := Utils.zip_ex_mid3 args_rev args_rev' args_rev'' p hlen₁ hlen₂ hp
          aesop
    case closure ctx₁ body₁ ctx₂ body₂ ch₁ =>
      cases h₂
      case refl =>
        exact Value.Approx.Indexed.closure ch₁
      case closure ctx₃ body₃ ch₂ =>
        constructor
        · intro v v₁ h
          have eh : Expr.ApproxEvals.Indexed P n (v :: ctx₂) body₂ v₁ := by
            apply ch₁
            exact h
          rcases eh with ⟨v₂, h₁, h₂⟩
          have eh : Expr.ApproxEvals.Indexed P n (v :: ctx₃) body₃ v₂ := by
            apply ch₂
            exact h₁
          rcases eh with ⟨v₃, h₃, h₄⟩
          constructor
          · exact h₃
          · aesop

lemma Value.Approx.refl {P v} : ⟨P⟩ v ≲ v := by
  exists 0
  exact Value.Approx.Indexed.refl

lemma Value.Approx.trans {P v₁ v₂ v₃} : ⟨P⟩ v₁ ≲ v₂ → ⟨P⟩ v₂ ≲ v₃ → ⟨P⟩ v₁ ≲ v₃ := by
  intros h₁ h₂
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  exists (n₁ + n₂)
  have h₁ : Indexed P (n₁ + n₂) v₁ v₂ := by
    apply Value.Approx.Indexed.monotone
    · exact h₁
    · aesop
  have h₂ : Indexed P (n₁ + n₂) v₂ v₃ := by
    apply Value.Approx.Indexed.monotone
    · exact h₂
    · aesop
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
  rcases h with ⟨n, h⟩
  constructor
  case left =>
    intros p hp
    cases h
    case constr_app =>
      constructor
      aesop
    case refl =>
      exact Value.Approx.zip_refl hp
  case right =>
    aesop

lemma Value.Approx.constr_app {P ctr_name args_rev args_rev'} :
  args_rev.length = args_rev'.length →
  (∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ Prod.snd p) →
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ Value.constr_app ctr_name args_rev' := by
  intro hlen h
  have h' : ∀ p ∈ List.zip args_rev args_rev', ∃ n, Value.Approx.Indexed P n (Prod.fst p) (Prod.snd p) := by
    aesop
  have nh : ∃ n, ∀ p ∈ List.zip args_rev args_rev', Value.Approx.Indexed P n (Prod.fst p) (Prod.snd p) := by
    apply Juvix.Utils.monotone_ex_all
    aesop (add unsafe apply Value.Approx.Indexed.monotone)
    assumption
  obtain ⟨n, h''⟩ := nh
  exists (Nat.succ n)
  constructor <;> assumption

lemma Value.Approx.closure_inv {P ctx₁ body₁ ctx₂ body₂} :
  ⟨P⟩ Value.closure ctx₁ body₁ ≲ Value.closure ctx₂ body₂ →
  ∀ v v₁, ⟨P⟩ v :: ctx₁ ⊢ body₁ ↦ v₁ → ⟨P⟩ v :: ctx₂ ⊢ body₂ ↦≳ v₁ := by
  intro h
  rcases h with ⟨n, h⟩
  cases h
  case refl =>
    intro v v₁ h
    exists 0
    constructor
    exact h
    exact Value.Approx.Indexed.refl
  case closure n h =>
    intro v v₁ h'
    have h' : Expr.ApproxEvals.Indexed P n (v :: ctx₂) body₂ v₁ := by
      apply h
      exact h'
    rcases h' with ⟨v₂, h₁, h₂⟩
    constructor
    aesop

lemma Value.Approx.closure {P ctx₁ body₁ ctx₂ body₂} :
  (∀ v v₁, ⟨P⟩ v :: ctx₁ ⊢ body₁ ↦ v₁ → ⟨P⟩ v :: ctx₂ ⊢ body₂ ↦≳ v₁) →
  ⟨P⟩ Value.closure ctx₁ body₁ ≲ Value.closure ctx₂ body₂ := by
  intro h
  have h' : ∀ v v₁, ⟨P⟩ v :: ctx₁ ⊢ body₁ ↦ v₁ → ∃ n, Expr.ApproxEvals.Indexed P n (v :: ctx₂) body₂ v₁ := by
    intros v v₁ h'
    have h' : ⟨P⟩ v :: ctx₂ ⊢ body₂ ↦≳ v₁ := by
      apply h
      exact h'
    rcases h' with ⟨n, v₂, h₂⟩
    constructor
    constructor
    exact h₂
    assumption
  sorry

end Juvix.Core.Main
