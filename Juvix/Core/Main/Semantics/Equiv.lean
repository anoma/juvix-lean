
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
    | closure {n env₁ body₁ env₂ body₂} :
      (∀ k < n, ∀ v v₁, ⟨P⟩ v :: env₁ ⊢ body₁ ↦ v₁ → Expr.ApproxEvals.Indexed P k (v :: env₂) body₂ v₁) →
      Value.Approx.Indexed P n (Value.closure env₁ body₁) (Value.closure env₂ body₂)

  -- We need `Expr.ApproxEvals.Indexed` in order to avoid existential quantification in
  -- the definition of `Value.Approx.Indexed`.
  @[aesop unsafe [constructors, cases]]
  inductive Expr.ApproxEvals.Indexed (P : Program) : Nat → Env → Expr → Value → Prop where
    | equiv {n env e v₁} v₂ :
      ⟨P⟩ env ⊢ e ↦ v₂ →
      Value.Approx.Indexed P n v₂ v₁ →
      Expr.ApproxEvals.Indexed P n env e v₁
end

def Value.Approx (P : Program) (v v' : Value) : Prop :=
  ∀ n, Value.Approx.Indexed P n v v'

def Expr.ApproxEvals (P : Program) (env : Env) (e : Expr) (v : Value) : Prop :=
  ∀ n, Expr.ApproxEvals.Indexed P n env e v

notation "⟨" P "⟩ " v " ≲ " v':40 => Value.Approx P v v'

notation "⟨" P "⟩ " env " ⊢ " e " ↦≳ " v:40 => Expr.ApproxEvals P env e v

def Expr.Approx (P₁ : Program) (env₁ : Env) (e₁ : Expr) (P₂ : Program) (env₂ : Env) (e₂ : Expr) : Prop :=
  (∀ v, ⟨P₁⟩ env₁ ⊢ e₁ ↦ v → ⟨P₂⟩ env₂ ⊢ e₂ ↦≳ v)

notation "⟨" P "⟩ " env " ⊢ " e " ≲ " "⟨" P' "⟩ " env' " ⊢ " e':40 => Expr.Approx P env e P' env' e'

def Expr.Equiv (P₁ : Program) (env₁ : Env) (e₁ : Expr) (P₂ : Program) (env₂ : Env) (e₂ : Expr) : Prop :=
  ⟨P₁⟩ env₁ ⊢ e₁ ≲ ⟨P₂⟩ env₂ ⊢ e₂ ∧ ⟨P₂⟩ env₂ ⊢ e₂ ≲ ⟨P₁⟩ env₁ ⊢ e₁

notation "⟨" P₁ "⟩ " env₁ " ⊢ " e₁ " ≋ " "⟨" P₂ "⟩ " env₂ " ⊢ " e₂:40 => Expr.Equiv P₁ env₁ e₁ P₂ env₂ e₂

def Program.Equiv (P₁ P₂ : Program) : Prop :=
  ⟨P₁⟩ [] ⊢ P₁.main ≋ ⟨P₂⟩ [] ⊢ P₂.main

notation "⟨" P₁ "⟩ " " ≋ " "⟨" P₂ "⟩" => Program.Equiv P₁ P₂

@[refl]
lemma Value.Approx.Indexed.refl {P n} v : Value.Approx.Indexed P n v v := by
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
    case closure env body =>
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
    case closure env body =>
      constructor
      · intros k' hk' v v'
        have : k' ≤ n := by linarith
        aesop

@[trans]
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
    case closure env₁ body₁ env₁' body₁' ch₁ =>
      cases h₂
      case closure env₂ body₂ ch₂ =>
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
    case closure env₁ body₁ env₂ body₂ ch₁ =>
      cases h₂
      case closure env₃ body₃ ch₂ =>
        constructor
        · intro k' hk' v v₁ h
          have ah₁ : Expr.ApproxEvals.Indexed P k' (v :: env₂) body₂ v₁ := by
            apply ch₁ <;> assumption
          obtain ⟨v₂, _, h₂⟩ := ah₁
          have ah₂ : Expr.ApproxEvals.Indexed P k' (v :: env₃) body₃ v₂ := by
            apply ch₂ <;> assumption
          obtain ⟨v₃, _, h₃⟩ := ah₂
          have : k' ≤ n := by linarith
          aesop

@[refl]
lemma Value.Approx.refl {P} v : ⟨P⟩ v ≲ v := by
  intro n
  rfl

@[trans]
lemma Value.Approx.trans {P v₁ v₂ v₃} : ⟨P⟩ v₁ ≲ v₂ → ⟨P⟩ v₂ ≲ v₃ → ⟨P⟩ v₁ ≲ v₃ := by
  intros h₁ h₂
  intro n
  aesop (add unsafe apply Value.Approx.Indexed.trans)

@[simp]
lemma Value.Approx.unit_left {P v} : ⟨P⟩ v ≲ Value.unit ↔ v = Value.unit := by
  constructor
  case mp =>
    intro h
    cases h 0
    rfl
  case mpr =>
    intro h
    subst h
    rfl

@[simp]
lemma Value.Approx.unit_right {P v} : ⟨P⟩ Value.unit ≲ v ↔ v = Value.unit := by
  constructor
  case mp =>
    intro h
    cases h 0
    rfl
  case mpr =>
    intro h
    subst h
    rfl

@[simp]
lemma Value.Approx.const_left {P v c} : ⟨P⟩ v ≲ Value.const c ↔ v = Value.const c := by
  constructor
  case mp =>
    intro h
    cases h 0
    rfl
  case mpr =>
    intro h
    subst h
    rfl

@[simp]
lemma Value.Approx.const_right {P v c} : ⟨P⟩ Value.const c ≲ v ↔ v = Value.const c := by
  constructor
  case mp =>
    intro h
    cases h 0
    rfl
  case mpr =>
    intro h
    subst h
    rfl

@[aesop unsafe apply]
lemma Value.Approx.constr_app {P ctr_name args_rev args_rev'} :
  args_rev.length = args_rev'.length →
  (∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ Prod.snd p) →
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ Value.constr_app ctr_name args_rev' := by
  intro hlen h n
  aesop

@[aesop unsafe apply]
lemma Value.Approx.closure {P env₁ body₁ env₂ body₂} :
  (∀ v, ⟨P⟩ v :: env₁ ⊢ body₁ ≲ ⟨P⟩ v :: env₂ ⊢ body₂) →
  ⟨P⟩ Value.closure env₁ body₁ ≲ Value.closure env₂ body₂ := by
  intro h n
  aesop

@[aesop safe destruct]
lemma Value.Approx.constr_app_inv {P ctr_name args_rev args_rev'} :
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ Value.constr_app ctr_name args_rev' →
  (∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ Prod.snd p) ∧
  args_rev.length = args_rev'.length := by
  intro h
  constructor
  case left =>
    intros p hp n
    cases (h (n + 1))
    aesop
  case right =>
    cases (h 0)
    aesop

lemma Value.Approx.constr_app_inv_length {P ctr_name args_rev args_rev'} :
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ Value.constr_app ctr_name args_rev' →
  args_rev.length = args_rev'.length := by
  intro h
  exact (Value.Approx.constr_app_inv h).right

lemma Value.Approx.constr_app_inv_args {P ctr_name args_rev args_rev'} :
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ Value.constr_app ctr_name args_rev' →
  ∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ Prod.snd p := by
  intro h
  exact (Value.Approx.constr_app_inv h).left

@[aesop unsafe 90% destruct]
lemma Value.Approx.constr_app_inv_left {P ctr_name args_rev' v} :
  ⟨P⟩ v ≲ Value.constr_app ctr_name args_rev' →
  ∃ args_rev,
    v = Value.constr_app ctr_name args_rev ∧
    args_rev.length = args_rev'.length ∧
    ∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ Prod.snd p := by
  intro h
  cases (h 0)
  aesop

@[aesop unsafe 90% destruct]
lemma Value.Approx.constr_app_inv_right {P ctr_name args_rev v} :
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ v →
  ∃ args_rev',
    v = Value.constr_app ctr_name args_rev' ∧
    args_rev.length = args_rev'.length ∧
    ∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ Prod.snd p := by
  intro h
  cases (h 0)
  aesop

@[aesop safe destruct (immediate := [h])]
lemma Value.Approx.closure_inv {P env₁ body₁ env₂ body₂}
  (h : ⟨P⟩ Value.closure env₁ body₁ ≲ Value.closure env₂ body₂) :
  ∀ v, ⟨P⟩ v :: env₁ ⊢ body₁ ≲ ⟨P⟩ v :: env₂ ⊢ body₂ := by
  intro v v₁ h' n
  cases (h n.succ)
  aesop

@[aesop unsafe 90% destruct]
lemma Value.Approx.closure_inv_left {P env₂ body₂ v} :
  ⟨P⟩ v ≲ Value.closure env₂ body₂ →
  ∃ env₁ body₁,
    v = Value.closure env₁ body₁ ∧
    (∀ v', ⟨P⟩ v' :: env₁ ⊢ body₁ ≲ ⟨P⟩ v' :: env₂ ⊢ body₂) := by
  intro h
  cases (h 0)
  aesop

@[aesop unsafe 90% destruct]
lemma Value.Approx.closure_inv_right {P env₁ body₁ v} :
  ⟨P⟩ Value.closure env₁ body₁ ≲ v →
  ∃ env₂ body₂,
    v = Value.closure env₂ body₂ ∧
    (∀ v', ⟨P⟩ v' :: env₁ ⊢ body₁ ≲ ⟨P⟩ v' :: env₂ ⊢ body₂) := by
  intro h
  cases (h 0)
  aesop

@[aesop safe cases]
inductive Value.Approx.Inversion (P : Program) : Value -> Value -> Prop where
  | unit : Value.Approx.Inversion P Value.unit Value.unit
  | const {c} : Value.Approx.Inversion P (Value.const c) (Value.const c)
  | constr_app {ctr_name args_rev args_rev'} :
    args_rev.length = args_rev'.length →
    (∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ p.1 ≲ p.2) →
    Value.Approx.Inversion P (Value.constr_app ctr_name args_rev) (Value.constr_app ctr_name args_rev')
  | closure {env₁ body₁ env₂ body₂} :
    (∀ v, ⟨P⟩ v :: env₁ ⊢ body₁ ≲ ⟨P⟩ v :: env₂ ⊢ body₂) →
    Value.Approx.Inversion P (Value.closure env₁ body₁) (Value.closure env₂ body₂)

-- Use `cases (Value.Approx.invert h)` to invert `h : ⟨P⟩ v ≲ v'`.
@[aesop unsafe destruct]
lemma Value.Approx.invert {P v v'} :
  ⟨P⟩ v ≲ v' →
  Value.Approx.Inversion P v v' := by
  intro h
  cases (h 0) <;> constructor <;> aesop

@[aesop unsafe apply]
lemma Expr.ApproxEvals.equiv {P env e v v'} :
  ⟨P⟩ env ⊢ e ↦ v' → ⟨P⟩ v' ≲ v → ⟨P⟩ env ⊢ e ↦≳ v := by
  intro h₁ h₂ n
  aesop

lemma Expr.ApproxEvals.equiv_inv {P env e v} :
  ⟨P⟩ env ⊢ e ↦≳ v → ∃ v', ⟨P⟩ env ⊢ e ↦ v' ∧ ⟨P⟩ v' ≲ v := by
  intro h
  suffices ∀ n, ∃ v', ⟨P⟩ env ⊢ e ↦ v' ∧ Value.Approx.Indexed P n v' v by
    obtain ⟨v', h', _⟩ := h 0
    exists v'
    constructor
    · exact h'
    · intro n
      obtain ⟨v'', h₁, h₂⟩ := this n
      have : v' = v'' := by
        apply Eval.deterministic <;> assumption
      subst v''
      simp_all
  intro n
  cases (h n)
  aesop

@[aesop safe cases]
inductive Expr.ApproxEvals.Inversion (P : Program) (env : Env) (e : Expr) (v : Value) : Prop where
  | equiv {v'} :
    ⟨P⟩ env ⊢ e ↦ v' →
    ⟨P⟩ v' ≲ v →
    Expr.ApproxEvals.Inversion P env e v

-- Use `cases (Expr.ApproxEvals.invert h)` to invert `h : ⟨P⟩ env ⊢ e ↦≳ v`.
@[aesop unsafe destruct]
lemma Expr.ApproxEvals.invert {P env e v} :
  ⟨P⟩ env ⊢ e ↦≳ v → Expr.ApproxEvals.Inversion P env e v := by
  intro h
  cases (Expr.ApproxEvals.equiv_inv h)
  constructor
  · aesop (add safe cases And)
  · aesop

@[aesop unsafe 99% apply]
lemma Expr.Approx.refl {P env} e : ⟨P⟩ env ⊢ e ≲ ⟨P⟩ env ⊢ e := by
  intro v
  aesop

lemma Expr.Approx.rfl {P env e} : ⟨P⟩ env ⊢ e ≲ ⟨P⟩ env ⊢ e :=
  Expr.Approx.refl e

/-
lemma Expr.Approx.trans {P₁ env₁ e₁ P₂ env₂ e₂ P₃ env₃ e₃} :
  ⟨P₁⟩ env₁ ⊢ e₁ ≲ ⟨P₂⟩ env₂ ⊢ e₂ → ⟨P₂⟩ env₂ ⊢ e₂ ≲ ⟨P₃⟩ env₃ ⊢ e₃ → ⟨P₁⟩ env₁ ⊢ e₁ ≲ ⟨P₃⟩ env₃ ⊢ e₃ := by
  intros h₁ h₂ v hv
  have h₁' := h₁ v hv
  cases (Expr.ApproxEvals.invert h₁')
  case equiv v' hv' ha =>
    have h₂' := h₂ v' hv'
    cases (Expr.ApproxEvals.invert h₂')
    case equiv v'' hv'' ha' =>
      sorry
-/

end Juvix.Core.Main
