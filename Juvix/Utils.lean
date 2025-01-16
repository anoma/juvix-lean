
import Aesop

namespace Juvix.Utils

theorem monotone_ex_all {α} {P : Nat → α → Prop}
  (mh: ∀ n n' x, P n x → n ≤ n' → P n' x)
  (l : List α)
  (h : ∀ x ∈ l, ∃ n, P n x) : ∃ n, ∀ x ∈ l, P n x := by
  induction l with
  | nil =>
    exists 0
    aesop
  | cons x xs ih =>
    obtain ⟨n, hn⟩ := h x (by simp)
    obtain ⟨m, hm⟩ := ih (λ x hx => h x (by simp [hx]))
    exists (Max.max n m)
    intros x' hx'
    cases hx'
    case intro.head =>
      apply mh
      exact hn
      exact Nat.le_max_left n m
    case intro.tail ht =>
      apply (mh m (Max.max n m) x')
      aesop
      exact Nat.le_max_right n m

theorem zip_refl_eq {α} (l : List α) (p : α × α) (h : p ∈ List.zip l l) : p.fst = p.snd := by
  induction l with
  | nil =>
    cases h
  | cons x xs ih =>
    cases h
    case cons.head =>
      simp
    case cons.tail ht =>
      exact ih ht

theorem zip_ex_mid3 {α} (l₁ l₂ l₃ : List α) (p : α × α)
  (hl₁ : l₁.length = l₂.length)
  (hl₂ : l₂.length = l₃.length)
  (hp : p ∈ List.zip l₁ l₃) :
  ∃ p₁ ∈ List.zip l₁ l₂,
  ∃ p₂ ∈ List.zip l₂ l₃,
  p.fst = p₁.fst ∧ p.snd = p₂.snd ∧ p₁.snd = p₂.fst := by
  induction l₁ generalizing l₂ l₃ with
  | nil =>
    cases hp
  | cons x xs ih =>
    cases l₂ with
    | nil =>
      cases l₃
      case nil =>
        cases hp
      case cons y ys =>
        contradiction
    | cons y ys =>
      cases l₃ with
      | nil =>
        cases hp
      | cons z zs =>
        cases hp
        case cons.head =>
          simp
        case cons.tail ht =>
          simp at hl₁ hl₂
          obtain ⟨p₁, hp₁, p₂, hp₂, h₁, h₂⟩ := ih ys zs hl₁ hl₂ ht
          exact ⟨p₁, List.mem_cons_of_mem _ hp₁, p₂, List.mem_cons_of_mem _ hp₂, h₁, h₂⟩

end Juvix.Utils
