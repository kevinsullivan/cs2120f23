--import Mathlib.Init.Set

/-!
# Homework #11
-/

/-!
## #1. Quantifiers

Define to_prv as the proposition asserting that, for
any type, α, and for any predicate, *P : α → Prop* on
values of α, if there is no (a : α) that satisfies *P*,
then every (a : α) satisfies *¬P*.
-/

#check _    -- fill in the blank

/-!
Now use example to state and give a proof of it.
-/

#check ∀ (α : Type), ∀ (P : α → Prop), (¬∃ (a : α), P a) → (∀ (a : α), ¬ P a)

example : ∀ (α : Type), ∀ (P : α → Prop), (¬∃ (a : α), P a) → (∀ (a : α), ¬ P a)
| α, P, h =>
  λ a =>
    λ g =>
      let p := Exists.intro a g
      h p
      -- "h (Exists.intro a g)" would work too of course

/-!
#2 Set Theory

Use display notation to define foo in Lean as the set,
{ 1, 3, 4, 5 }. Use set comprehension notation to define
bar to be the set of odd numbers. Next define s to be
foo ∩ bar, and define t to be foo ∪ bar. Now prove that
4 ∉ s. Finally prove that 7 ∈ t.
-/

def foo : Set Nat := { 1, 3, 4, 5 }
def bar := { n : Nat | n % 2 ≠ 0 }

def s := foo ∩ bar
def t := foo ∪ bar

example : 4 ∉ s
| ⟨ _, h_bar ⟩ => nomatch h_bar

example : 7 ∈ foo ∪ bar := Or.inr (λ h => nomatch h)
