import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic

/-!
binary relation on a type, α 
- reflexive
- symmetric
- transitive
- equivalence (Core.lean)
- asymmetric
- antisymmetric
- closures
- inverse

- empty relation
- complete relation
- subrelation

binary relation from α → β, etc 
- compose
- join

inverse image
-/

inductive Person : Type
| lu
| mary 
| jane

open Person

def Likes : Person → Person → Prop :=
  λ p1 p2 => 
    (p1 = lu ∧ p2 = mary) ∨ 
    (p1 = mary ∧ p2 = lu)

#reduce Likes lu mary

#reduce Likes lu jane


example : Likes lu mary := Or.inl ⟨ rfl, rfl⟩

#reduce Likes lu jane

example : ¬ Likes lu jane := 
λ h : Likes lu jane => by
  unfold Likes at h
  cases h with 
  | inl l => nomatch l.2
  | inr r => nomatch r.1

  /-
    cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
  -/

/-
order relations
- partial order: reflexive, antisymmetric, transitive
- poset: a set α along with a partial order on α
- total order: partial order ∧ ∀ a b, a ≤ b ∨ b ≤ a
-/

/-
functions
- a single-valued relation is a function

- domain of definition
- codomain
- domain
- range
- partial
- total 

- identity function -- See Mathlib.Logic.Function.Basic

- one-to-one (vs many-to-one, injective)
- onto (surjective)
- bijective

- composition
- inverse
- etc
-/

