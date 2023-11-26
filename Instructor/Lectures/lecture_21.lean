import Mathlib.Init.Set

/-!
Predicates
-/
def ev := λ n : Nat => n % 2 = 0
def small := λ n : Nat => n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4

/-!
Sets, defined by (and equivalent to membership) predicates
-/
def ev_set := { n | ev n}
def small_set := {n | small n}

/-!
Membership propositions
-/

#reduce small 3
#reduce small_set 3
#reduce 3 ∈ small_set

/-!
Membership proofs
-/
example : small 3 := Or.inr (Or.inr ( Or.inr (Or.inl rfl)))
example : small_set 3 := Or.inr (Or.inr ( Or.inr (Or.inl rfl)))
example : 3 ∈ small_set := Or.inr (Or.inr ( Or.inr (Or.inl rfl)))

example : 7 ∉ small_set := λ h => nomatch h

/-!
Intersection

If S and T are sets of natural numbers with membership
predicates s : Nat → Prop and t : Nat → Prop, then S ∩ T
is the set of values that satisfy both s and t, and is
said to be the intersection of the two sets: the set of
elements that are in both sets.
-/

def even_and_small := λ (n : Nat) => ev n ∧ small n
def even_and_small_set := { n : Nat | n ∈ ev_set ∧ n ∈ small_set}
#reduce even_and_small 3
#reduce 3 ∈ even_and_small_set

example : 3 ∉ even_and_small_set :=
  λ h => nomatch h

example : 4 ∈ even_and_small_set :=
  ⟨ rfl, Or.inr (Or.inr ( Or.inr (Or.inr rfl))) ⟩

example : 4 ∈ ev_set ∩ small_set :=
  ⟨ rfl, Or.inr (Or.inr ( Or.inr (Or.inr rfl))) ⟩

/-!
Union

If S and T are sets of natural numbers with membership
predicates s : Nat → Prop and t : Nat → Prop, then S ∪ T
is the set of values that satisfy either s or t, and is
said to be the union of the two sets: the set of values
that are in one or the other or both of the two sets.
-/

def even_or_small := λ (n : Nat) => ev n ∨ small n
def even_or_small_set := { n : Nat | n ∈ ev_set ∨ n ∈ small_set}
#reduce even_or_small 3
#reduce 3 ∈ even_or_small_set

example : 3 ∈ even_or_small_set := Or.inr _

example : 4 ∈ even_or_small_set := _

example : 4 ∈ ev_set ∪ small_set := _


/-!
Empty set

The empty set of values (of a given type) is denoted ∅.
It's the set containing no values of a give type.
-/

example : 3 ∉ (∅ : Set Nat) := λ h => nomatch h

/-!
Exercise: What predicate defines ∅?
-/

/-!
Universal set

The universal set of a values of a given type is denoted
*univ* in Lean. This definition is in the Set namespace so
use "Open Set" to access it (or Set.univ).
-/

open Set

#reduce 2 ∈ {n : Nat | True}
#reduce 2 ∈ univ
example : 2 ∈ univ := True.intro

/-!
Complement.

The complement of a set S of elements of type T is the set of
elements of type T that are *not* in S.
-/
