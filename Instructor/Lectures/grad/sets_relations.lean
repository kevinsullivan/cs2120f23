import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic
import Mathlib.LinearAlgebra.AffineSpace.Basic

/-!
In Lean we will often represent a set, S, of elements
of type α, as a membership predicate, mem : α → Prop.
There are of course other ways to represent sets. 
-/

def a_set : Set Nat := { 1, 2, 3 }
def b_set : Set Nat := { 3, 4, 5 }

def a_set' : Set Nat := { n : Nat | n = 1 ∨ n = 2 ∨ n = 3 }

example : 1 ∈ a_set := by
  show a_set 1
  unfold a_set
  show 1=1 ∨ 1=2 ∨ 1=3
  exact Or.inl rfl

example : 3 ∈ a_set ∩ b_set := by
  show 3 ∈ a_set ∧ 3 ∈ b_set
  exact ⟨ Or.inr (Or.inr rfl), Or.inl rfl⟩ 

example : 2 ∈ a_set ∪ b_set := by
exact Or.inl (Or.inr (Or.inl rfl))

example : 2 ∈ a_set \ b_set := _
example : 3 ∉ a_set \ b_set := _

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
-/

/-!
Properties of Relations
-/
#check (@Reflexive)     -- Core.lean
#check (@Symmetric)
#check (@Transitive)
#check (@Equivalence)   -- Logic.lean


/-!
Theorem: The equality relation on natural numbers is 
an equivalence relation. 
-/
#reduce Reflexive (@Eq Nat)

-- ∀ (x : ℕ), x = x
lemma eq_nat_is_refl : Reflexive (@Eq Nat) := by
  unfold Reflexive
  intro x
  exact rfl

lemma eq_nat_is_symm: Symmetric (@Eq Nat) := by
  unfold Symmetric
  intro x y
  intro hxy
  rw [hxy]
  

#reduce eq_nat_is_symm

lemma eq_nat_is_trans : Transitive (@Eq Nat) := by
unfold Transitive
intros x y z
intros hxy hyz
rw [hxy]
rw [hyz]

theorem eq_nat_is_equiv : Equivalence (@Eq Nat) := 
  Equivalence.mk @eq_nat_is_refl @eq_nat_is_symm @eq_nat_is_trans


/-!
Theorem congruence mod n is an equivalence relation
-/

def cong_mod_n : Nat → Nat → Nat → Prop := λ n a b => a%n = b%n

theorem cong_mod_n_equiv': ∀ n, Equivalence (cong_mod_n n) := 
  by
    intro n
    exact Equivalence.mk _ _ _

example : cong_mod_n 3 2 5 := rfl

lemma cong_mod_n_rfl : ∀ (n : Nat), Reflexive (cong_mod_n n) := by
  intro n
  unfold cong_mod_n
  unfold Reflexive
  intro a
  exact rfl

lemma cong_mod_n_symm : ∀ (n : Nat), Symmetric (cong_mod_n n) := by
  intro n 
  unfold Symmetric
  intros x y
  intro hxy 
  unfold cong_mod_n
  unfold cong_mod_n at hxy
  rw [hxy]

lemma cong_mod_trans : ∀ (n : Nat), Transitive (cong_mod_n n) := by
  intro n a b c hab hbc
  unfold cong_mod_n
  unfold cong_mod_n at hab hbc
  rw [hab, hbc]

theorem cong_mod_n_equiv: ∀ (n : Nat), Equivalence (cong_mod_n n) := 
  by
    intro n
    unfold cong_mod_n
    exact Equivalence.mk 
      (by intro x; rfl)
      (by intros x y h; rw [h]) 
      (by intros x y z hxy hyz; rw [hxy, hyz])


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

example : ¬(Likes lu jane) := 
λ h : Likes lu jane => by
  unfold Likes at h
  cases h with 
  | inl l => nomatch l.2
  | inr r => nomatch r.1


/-
functions
- a single-valued relation is a function

- domain of definition
- codomain
- domain
- range
- partial
- total 

- injective: one-to-one, not many-to-one
- surjective: also called onto
- bijective: both injective and surjective

- composition
- inverse
- etc
-/

open Function
#check Injective

-- successor is injective
theorem succ_inj : Injective (λ n : Nat => n + 1) := by
  unfold Injective
  intros a1 a2 h
  simp [Nat.add] at h
  assumption

-- successor is not surjective
theorem not_succ_surj : ¬ Surjective (λ n : Nat => n + 1) := by
  unfold Surjective
  intro h
  let contra := h 0
  simp [Nat.add] at contra

-- Boolean Not is Bijective

lemma inj_not : Injective Bool.not := by
  unfold Injective
  intros a1 a2 h
  cases a1 with
    | true =>
        cases a2 with
        | true => rfl
        | false => nomatch h
    | false =>
          cases a2 with
          | true => nomatch h
          | false => rfl

lemma surj_not : Surjective Bool.not := by
  unfold Surjective
  intro b
  cases b with 
  | true => exact ⟨ false, rfl ⟩ 
  | false => exact ⟨ true, rfl ⟩ 

theorem not_bij : Bijective Bool.not := by
  unfold Bijective
  exact ⟨ inj_not, surj_not ⟩ 
  