
import Juvix.Core.Main.Language.Base

namespace Juvix.Core.Main

inductive Value : Type where
  | unit : Value
  | const : Constant → Value
  | constr_app : (constr : Name) → (args_rev : List Value) → Value
  | closure : (env : List Value) → (value : Expr) → Value
  deriving Inhabited

abbrev Env : Type := List Value

mutual
  @[simp]
  def Value.dom : (v : Value) → Set Name
    | Value.unit => ∅
    | Value.const _ => ∅
    | Value.constr_app _ args_rev => Value.List.dom args_rev
    | Value.closure env body => Value.List.dom env ∪ body.dom

  @[simp]
  def Value.List.dom : (vs : List Value) → Set Name
    | [] => ∅
    | v :: vs => v.dom ∪ Value.List.dom vs
end

@[simp]
def Env.dom : (env : Env) → Set Name :=
  Value.List.dom

lemma Value.dom_env (v : Value) (env : Env) : v ∈ env → v.dom ⊆ env.dom := by
  intro h
  induction env generalizing v
  case nil =>
    contradiction
  case cons hd tl ih =>
    cases h
    case head =>
      simp [Value.dom, Value.List.dom]
    case tail hm =>
      simp [Value.dom, Value.List.dom]
      exact Set.subset_union_of_subset_right (ih v hm) hd.dom

lemma Value.List.dom_append (vs₁ vs₂ : List Value) :
  Value.List.dom (vs₁ ++ vs₂) = Value.List.dom vs₁ ∪ Value.List.dom vs₂ := by
  induction vs₁ generalizing vs₂
  case nil =>
    simp [Value.List.dom]
  case cons hd tl ih =>
    simp [Value.List.dom]
    rw [ih]
    rw [Set.union_assoc]

end Juvix.Core.Main
