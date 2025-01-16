
import Juvix.Core.Main.Semantics.Eval
import Juvix.Utils
import Mathlib.Tactic.Linarith
import Aesop

namespace Juvix.Core.Main

mutual
  @[aesop unsafe [constructors, cases]]
  inductive Value.Approx.Indexed : Nat → Program → Program → Value → Value → Prop where
    | unit {n P₁ P₂} : Value.Approx.Indexed n P₁ P₂ Value.unit Value.unit
    | const {n P₁ P₂ c} : Value.Approx.Indexed n P₁ P₂ (Value.const c) (Value.const c)
    | constr_app {n P₁ P₂ ctr_name args_rev args_rev'} :
      args_rev.length = args_rev'.length →
      (∀ k < n, ∀ p ∈ List.zip args_rev args_rev',
        Value.Approx.Indexed k P₁ P₂ (Prod.fst p) (Prod.snd p)) →
      Value.Approx.Indexed n P₁ P₂ (Value.constr_app ctr_name args_rev) (Value.constr_app ctr_name args_rev')
    | closure {n P₁ P₂ env₁ body₁ env₂ body₂} :
      (∀ k < n, ∀ v v₁,
        v.dom ⊆ P₁.dom ∩ P₂.dom →
        ⟨P₁⟩ v :: env₁ ⊢ body₁ ↦ v₁ →
        Expr.ApproxEvals.Indexed k P₂ P₁ (v :: env₂) body₂ v₁) →
      Value.Approx.Indexed n P₁ P₂ (Value.closure env₁ body₁) (Value.closure env₂ body₂)

  -- We need `Expr.ApproxEvals.Indexed` in order to avoid existential quantification in
  -- the definition of `Value.Approx.Indexed`.
  @[aesop unsafe [constructors, cases]]
  inductive Expr.ApproxEvals.Indexed : Nat → Program → Program → Env → Expr → Value → Prop where
    | equiv {n P₁ P₂ env₂ e₂ v₁} v₂ :
      ⟨P₂⟩ env₂ ⊢ e₂ ↦ v₂ →
      Value.Approx.Indexed n P₂ P₁ v₂ v₁ →
      Expr.ApproxEvals.Indexed n P₂ P₁ env₂ e₂ v₁
end

def Value.Approx (P₁ P₂ : Program) (v v' : Value) : Prop :=
  ∀ n, Value.Approx.Indexed n P₁ P₂ v v'

def Expr.ApproxEvals (P₁ P₂ : Program) (env : Env) (e : Expr) (v : Value) : Prop :=
  ∀ n, Expr.ApproxEvals.Indexed n P₁ P₂ env e v

notation "⟨" P₁ "⟩ " v " ≲ " "⟨" P₂ "⟩ " v':40 => Value.Approx P₁ P₂ v v'

notation "⟨" P₁ "⟩ " env " ⊢ " e " ↦≳ " "⟨" P₂ "⟩ " v:40 => Expr.ApproxEvals P₁ P₂ env e v

def Expr.Approx (P₁ P₂ : Program) (env₁ env₂ : Env) (e₁ e₂ : Expr) : Prop :=
  (∀ v, ⟨P₁⟩ env₁ ⊢ e₁ ↦ v → ⟨P₂⟩ env₂ ⊢ e₂ ↦≳ ⟨P₁⟩ v)

notation "⟨" P "⟩ " env " ⊢ " e " ≲ " "⟨" P' "⟩ " env' " ⊢ " e':40 => Expr.Approx P P' env env' e e'

def Expr.Equiv (P₁ P₂ : Program) (env₁ env₂ : Env) (e₁ e₂ : Expr) : Prop :=
  ⟨P₁⟩ env₁ ⊢ e₁ ≲ ⟨P₂⟩ env₂ ⊢ e₂ ∧ ⟨P₂⟩ env₂ ⊢ e₂ ≲ ⟨P₁⟩ env₁ ⊢ e₁

notation "⟨" P₁ "⟩ " env₁ " ⊢ " e₁ " ≋ " "⟨" P₂ "⟩ " env₂ " ⊢ " e₂:40 => Expr.Equiv P₁ P₂ env₁ env₂ e₁ e₂

def Program.Equiv (P₁ P₂ : Program) : Prop :=
  ⟨P₁⟩ [] ⊢ P₁.main ≋ ⟨P₂⟩ [] ⊢ P₂.main

notation P₁ " ≋ " P₂:40 => Program.Equiv P₁ P₂

@[refl]
lemma Value.Approx.Indexed.refl {n P} v : Value.Approx.Indexed n P P v v := by
  revert n
  suffices ∀ n, ∀ k ≤ n, Value.Approx.Indexed k P P v v by
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
      · intros k' hk' v v' hdom heval
        have : k' ≤ n := by linarith
        aesop

@[trans]
lemma Value.Approx.Indexed.trans {n P₁ P₂ P₃ v₁ v₂ v₃} : Value.Approx.Indexed n P₁ P₂ v₁ v₂ → Value.Approx.Indexed n P₂ P₃ v₂ v₃ → Value.Approx.Indexed n P₁ P₃ v₁ v₃ := by
  revert n P₁ P₂ P₃
  suffices ∀ n, ∀ k ≤ n, ∀ P₁ P₂ P₃, Indexed k P₁ P₂ v₁ v₂ → Indexed k P₂ P₃ v₂ v₃ → Value.Approx.Indexed k P₁ P₃ v₁ v₃ by
    intro k P₁ P₂ P₃
    exact this k k k.le_refl P₁ P₂ P₃
  intros n
  induction n generalizing v₁ v₂ v₃ with
  | zero =>
    intros k hk P₁ P₂ P₃ h₁ h₂
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
    intros k hk P₁ P₂ P₃ h₁ h₂
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
        · intro k' hk' v v₁ hdom heval
          have : v.dom ⊆ P₁.dom ∩ P₂.dom := by sorry
          have : v.dom ⊆ P₂.dom ∩ P₃.dom := by sorry
          have ah₁ : Expr.ApproxEvals.Indexed k' P₂ P₁ (v :: env₂) body₂ v₁ := by
            apply ch₁ <;> assumption
          obtain ⟨v₂, _, h₂⟩ := ah₁
          have ah₂ : Expr.ApproxEvals.Indexed k' P₃ P₂ (v :: env₃) body₃ v₂ := by
            apply ch₂ <;> assumption
          obtain ⟨v₃, _, h₃⟩ := ah₂
          have : k' ≤ n := by linarith
          aesop

@[refl]
lemma Value.Approx.refl {P} v : ⟨P⟩ v ≲ ⟨P⟩ v := by
  intro n
  rfl

@[refl]
lemma Value.Approx.unit_refl {P P'} : ⟨P⟩ Value.unit ≲ ⟨P'⟩ Value.unit := by
  intro
  constructor

@[refl]
lemma Value.Approx.const_refl {P P' c} : ⟨P⟩ Value.const c ≲ ⟨P'⟩ Value.const c := by
  intro
  constructor

@[trans]
lemma Value.Approx.trans {P₁ P₂ P₃ v₁ v₂ v₃} : ⟨P₁⟩ v₁ ≲ ⟨P₂⟩ v₂ → ⟨P₂⟩ v₂ ≲ ⟨P₃⟩ v₃ → ⟨P₁⟩ v₁ ≲ ⟨P₃⟩ v₃ := by
  intros h₁ h₂
  intro n
  aesop (add unsafe apply Value.Approx.Indexed.trans)


@[simp]
lemma Value.Approx.unit_left {P P' v} : ⟨P⟩ v ≲ ⟨P'⟩ Value.unit ↔ v = Value.unit := by
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
lemma Value.Approx.unit_right {P P' v} : ⟨P⟩ Value.unit ≲ ⟨P'⟩ v ↔ v = Value.unit := by
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
lemma Value.Approx.const_left {P P' v c} : ⟨P⟩ v ≲ ⟨P'⟩ Value.const c ↔ v = Value.const c := by
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
lemma Value.Approx.const_right {P P' v c} : ⟨P⟩ Value.const c ≲ ⟨P'⟩ v ↔ v = Value.const c := by
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
lemma Value.Approx.constr_app {P P' ctr_name args_rev args_rev'} :
  args_rev.length = args_rev'.length →
  (∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ ⟨P'⟩ Prod.snd p) →
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ ⟨P'⟩ Value.constr_app ctr_name args_rev' := by
  intro hlen h n
  aesop

@[aesop unsafe apply]
lemma Value.Approx.closure {P₁ P₂ env₁ body₁ env₂ body₂} :
  (∀ v,
    v.dom ⊆ P₁.dom ∩ P₂.dom →
    ⟨P₁⟩ v :: env₁ ⊢ body₁ ≲ ⟨P₂⟩ v :: env₂ ⊢ body₂) →
  ⟨P₁⟩ Value.closure env₁ body₁ ≲ ⟨P₂⟩ Value.closure env₂ body₂ := by
  intro h n
  aesop

@[aesop safe destruct]
lemma Value.Approx.constr_app_inv {P P' ctr_name args_rev args_rev'} :
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ ⟨P'⟩ Value.constr_app ctr_name args_rev' →
  (∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ ⟨P'⟩ Prod.snd p) ∧
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

lemma Value.Approx.constr_app_inv_length {P P' ctr_name args_rev args_rev'} :
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ ⟨P'⟩ Value.constr_app ctr_name args_rev' →
  args_rev.length = args_rev'.length := by
  intro h
  exact (Value.Approx.constr_app_inv h).right

lemma Value.Approx.constr_app_inv_args {P P' ctr_name args_rev args_rev'} :
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ ⟨P'⟩ Value.constr_app ctr_name args_rev' →
  ∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ ⟨P'⟩ Prod.snd p := by
  intro h
  exact (Value.Approx.constr_app_inv h).left

@[aesop unsafe 90% destruct]
lemma Value.Approx.constr_app_inv_left {P P' ctr_name args_rev' v} :
  ⟨P⟩ v ≲ ⟨P'⟩ Value.constr_app ctr_name args_rev' →
  ∃ args_rev,
    v = Value.constr_app ctr_name args_rev ∧
    args_rev.length = args_rev'.length ∧
    ∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ ⟨P'⟩ Prod.snd p := by
  intro h
  cases (h 0)
  aesop

@[aesop unsafe 90% destruct]
lemma Value.Approx.constr_app_inv_right {P P' ctr_name args_rev v} :
  ⟨P⟩ Value.constr_app ctr_name args_rev ≲ ⟨P'⟩ v →
  ∃ args_rev',
    v = Value.constr_app ctr_name args_rev' ∧
    args_rev.length = args_rev'.length ∧
    ∀ p ∈ List.zip args_rev args_rev', ⟨P⟩ Prod.fst p ≲ ⟨P'⟩ Prod.snd p := by
  intro h
  cases (h 0)
  aesop

@[aesop safe destruct (immediate := [h])]
lemma Value.Approx.closure_inv {P₁ P₂ env₁ body₁ env₂ body₂}
  (h : ⟨P₁⟩ Value.closure env₁ body₁ ≲ ⟨P₂⟩ Value.closure env₂ body₂) :
  ∀ v, v.dom ⊆ P₁.dom ∩ P₂.dom → ⟨P₁⟩ v :: env₁ ⊢ body₁ ≲ ⟨P₂⟩ v :: env₂ ⊢ body₂ := by
  intro v hdom v₁ h' n
  cases (h n.succ)
  aesop

@[aesop unsafe 90% destruct]
lemma Value.Approx.closure_inv_left {P₁ P₂ env₂ body₂ v} :
  ⟨P₁⟩ v ≲ ⟨P₂⟩ Value.closure env₂ body₂ →
  ∃ env₁ body₁,
    v = Value.closure env₁ body₁ ∧
    (∀ v', v'.dom ⊆ P₁.dom ∩ P₂.dom → ⟨P₁⟩ v' :: env₁ ⊢ body₁ ≲ ⟨P₂⟩ v' :: env₂ ⊢ body₂) := by
  intro h
  cases (h 0)
  aesop

@[aesop unsafe 90% destruct]
lemma Value.Approx.closure_inv_right {P₁ P₂ env₁ body₁ v} :
  ⟨P₁⟩ Value.closure env₁ body₁ ≲ ⟨P₂⟩ v →
  ∃ env₂ body₂,
    v = Value.closure env₂ body₂ ∧
    (∀ v', v'.dom ⊆ P₁.dom ∩ P₂.dom → ⟨P₁⟩ v' :: env₁ ⊢ body₁ ≲ ⟨P₂⟩ v' :: env₂ ⊢ body₂) := by
  intro h
  cases (h 0)
  aesop

@[aesop safe cases]
inductive Value.Approx.Inversion (P₁ P₂ : Program) : Value -> Value -> Prop where
  | unit : Value.Approx.Inversion P₁ P₂ Value.unit Value.unit
  | const {c} : Value.Approx.Inversion P₁ P₂ (Value.const c) (Value.const c)
  | constr_app {ctr_name args_rev args_rev'} :
    args_rev.length = args_rev'.length →
    (∀ p ∈ List.zip args_rev args_rev', ⟨P₁⟩ p.1 ≲ ⟨P₂⟩ p.2) →
    Value.Approx.Inversion P₁ P₂ (Value.constr_app ctr_name args_rev) (Value.constr_app ctr_name args_rev')
  | closure {env₁ body₁ env₂ body₂} :
    (∀ v, v.dom ⊆ P₁.dom ∩ P₂.dom → ⟨P₁⟩ v :: env₁ ⊢ body₁ ≲ ⟨P₂⟩ v :: env₂ ⊢ body₂) →
    Value.Approx.Inversion P₁ P₂ (Value.closure env₁ body₁) (Value.closure env₂ body₂)

-- Use `cases (Value.Approx.invert h)` to invert `h : ⟨P⟩ v ≲ ⟨P'⟩ v'`.
@[aesop unsafe destruct]
lemma Value.Approx.invert {P P' v v'} :
  ⟨P⟩ v ≲ ⟨P'⟩ v' →
  Value.Approx.Inversion P P' v v' := by
  intro h
  cases (h 0) <;> constructor <;> aesop

@[aesop unsafe apply]
lemma Expr.ApproxEvals.equiv {P P' env e v v'} :
  ⟨P⟩ env ⊢ e ↦ v → ⟨P⟩ v ≲ ⟨P'⟩ v' → ⟨P⟩ env ⊢ e ↦≳ ⟨P'⟩ v' := by
  intro h₁ h₂ n
  aesop

lemma Expr.ApproxEvals.equiv_inv {P P' env e v'} :
  ⟨P⟩ env ⊢ e ↦≳ ⟨P'⟩ v' → ∃ v, ⟨P⟩ env ⊢ e ↦ v ∧ ⟨P⟩ v ≲ ⟨P'⟩ v' := by
  intro h
  suffices ∀ n, ∃ v, ⟨P⟩ env ⊢ e ↦ v ∧ Value.Approx.Indexed n P P' v v' by
    obtain ⟨v, h', _⟩ := h 0
    exists v
    constructor
    · exact h'
    · intro n
      obtain ⟨vv, h₁, h₂⟩ := this n
      have : v = vv := by
        apply Eval.deterministic <;> assumption
      subst vv
      simp_all
  intro n
  cases (h n)
  aesop

@[aesop safe cases]
inductive Expr.ApproxEvals.Inversion (P P' : Program) (env : Env) (e : Expr) (v' : Value) : Prop where
  | equiv {v} :
    ⟨P⟩ env ⊢ e ↦ v →
    ⟨P⟩ v ≲ ⟨P'⟩ v' →
    Expr.ApproxEvals.Inversion P P' env e v'

-- Use `cases (Expr.ApproxEvals.invert h)` to invert `h : ⟨P⟩ env ⊢ e ↦≳ ⟨P'⟩ v'`.
@[aesop unsafe destruct]
lemma Expr.ApproxEvals.invert {P P' env e v'} :
  ⟨P⟩ env ⊢ e ↦≳ ⟨P'⟩ v' → Expr.ApproxEvals.Inversion P P' env e v' := by
  intro h
  cases (Expr.ApproxEvals.equiv_inv h)
  constructor
  · aesop (add safe cases And)
  · aesop

@[refl]
lemma Expr.Approx.refl {P env} e : ⟨P⟩ env ⊢ e ≲ ⟨P⟩ env ⊢ e := by
  intro v
  aesop

lemma Expr.Approx.trans {P₁ env₁ e₁ P₂ env₂ e₂ P₃ env₃ e₃} :
  ⟨P₁⟩ env₁ ⊢ e₁ ≲ ⟨P₂⟩ env₂ ⊢ e₂ → ⟨P₂⟩ env₂ ⊢ e₂ ≲ ⟨P₃⟩ env₃ ⊢ e₃ → ⟨P₁⟩ env₁ ⊢ e₁ ≲ ⟨P₃⟩ env₃ ⊢ e₃ := by
  intros h₁ h₂ v hv
  have h₁' := h₁ v hv
  cases (Expr.ApproxEvals.invert h₁')
  case equiv v' hv' ha =>
    have h₂' := h₂ v' hv'
    cases (Expr.ApproxEvals.invert h₂')
    case equiv v'' hv'' ha' =>
      intro n
      constructor
      · assumption
      · apply Value.Approx.Indexed.trans (P₂ := P₂) (v₂ := v')
        · aesop
        · aesop

end Juvix.Core.Main
