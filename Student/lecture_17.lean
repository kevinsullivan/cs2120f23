#check Empty

-- inductive Empty : Type

inductive Chaos : Type

def from_empty (e : Empty) : Chaos := nomatch e

#check False

-- inductive False : Prop

def from_false {P : Prop} (p : False) : P := False.elim p

def from_false_true_is_false (p : False) : True = False := False.elim p

/-!
Unit ==> True
-/

#check Unit
-- inductive PUnit : Sort u where
--    | unit : PUnit

#check True
-- inductive True : Prop where
--    | intro : True

#check True.intro

-- no elimination rule

def proof_of_true : True := True.intro

def false_implies_true : False → True := λ f => False.elim f

/-!
Prod => And
-/

#check Prod

#check And

inductive Birds_chirping : Prop
| yep
| boo

inductive Sky_Blue : Prop
| yep

#check (And Birds_chirping Sky_Blue)

theorem both_and : And Birds_chirping Sky_Blue := And.intro Birds_chirping.boo Sky_Blue.yep

/-!
Proof Irrelevance
-/

namespace cs2120f23

inductive Bool : Type
| true
| false

theorem proof_equal : Birds_chirping.boo = Birds_chirping.yep := by trivial

-- In Prop all proofs are equivalent
-- Choice of values in Prop can't be influence computations

#check Sum
#check Or

theorem one_or_other : Or Birds_chirping Sky_Blue := Or.inl Birds_chirping.yep
theorem one_or_other' : Or Birds_chirping Sky_Blue := Or.inr Sky_Blue.yep

example : Or Birds_chirping (0=1) := Or.inl Birds_chirping.yep
example : (0=1) ∨ (1=2) := _

theorem or_comm {P Q : Prop} : P ∨ Q → Q ∨ P :=
λ d =>
  match d with
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q

/-!
Not (no)
-/

def no (α : Type) := α → Empty

#check Not

example : no Chaos := λ c => nomatch c

inductive Raining : Prop

example : ¬ Raining := λ (r : Raining) => nomatch r
