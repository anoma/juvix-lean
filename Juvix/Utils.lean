
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

end Juvix.Utils
