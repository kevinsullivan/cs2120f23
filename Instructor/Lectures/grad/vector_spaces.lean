import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.AddTorsor
import Mathlib.Data.Complex.Basic

/-!
## States

A circle can be rotated by any number of degrees.
One cannot compute with real numbers, but rationals
being.
-/

def K := Complex
#check [Field K]

-- 
inductive State
| heading (h : K) (unit := 1)

example : _ := _

/-!
## Rotations

There are three actions that can be applied to a triangle
state, taking it to a new state through a rotation by the
one of the give angles (in degrees). 
-/
inductive Rotation
| r0
| r120
| r240

open State Rotation

/-!
## Additive Monoid of Rotations

Now our task is to "make the set of rotations into a monoid.
This requires an associative addition operator and a zero that
acts as a left and a right identity.
-/

/-!
### Zero

We will specify *r0* is the identity rotation. The Zero typeclass
defines *0* as a notation for Zero.zero.
-/

instance zero_rot : Zero Rotation := ⟨ r0 ⟩
#check (0 : Rotation)     -- 0 is now notation for r0!
example : r0 = 0 := rfl   -- r0 and 0 mean the same thing (are equal)

/-!
### AddMonoid

We'll define a rotation addition function and then use it as 
the generic addition function for Rotation values.
-/

-- An implementation of add for rotations
def add_Rotations : Rotation → Rotation → Rotation
| r0, r => r        -- r matches any argument value
| r, r0 => r        -- r matches any argument value
| r120, r120 => r240
| r120, r240 => r0
| r240, r120 => r0
| r240, r240 => r120

-- Next we overload the add/+ operation
instance : Add Rotation := { add := add_Rotations }   -- using {} notation

-- Now we get a nice overloaded + operator for rotations
#reduce r0 + r120
#reduce r120 + r0
#reduce r120 + r120
#reduce r120 + r240
#reduce r120 + 0      -- Both + and 0 are overloaded for rotations now!


/-
## AddSemigroup

We need to instantiate AddSemigroup for the Rotation type.
For that we need a proof that rotation addition is associative. 
-/

example : ∀ a b c : Rotation, a + b + c = a + (b + c) :=
λ a b c => 
match a with
| r0 => match b with
  | r0 => match c with
    | r0 => rfl
    | r120 => rfl
    | r240 => rfl
  | r120 => match c with
    | r0 => rfl
    | r120 => rfl
    | r240 => rfl 
  | r240 => match c with
    | r0 => rfl
    | r120 => rfl
    | r240 => rfl 
| r120 => match b with
  | r0 => match c with
    | r0 => rfl
    | r120 => rfl
    | r240 => rfl
  | r120 => match c with
    | r0 => rfl
    | r120 => rfl
    | r240 => rfl 
  | r240 => match c with
    | r0 => rfl
    | r120 => rfl
    | r240 => rfl 
| r240 => match b with
  | r0 => match c with
    | r0 => rfl
    | r120 => rfl
    | r240 => rfl
  | r120 => match c with
    | r0 => rfl
    | r120 => rfl
    | r240 => rfl 
  | r240 => match c with
    | r0 => rfl
    | r120 => rfl
    | r240 => rfl 


theorem rot_add_assoc : ∀ a b c : Rotation, a + b + c = a + (b + c) :=
by 
  intros a b c
  cases a 
  repeat {
    cases b
    repeat {
     cases c
     repeat { rfl }
    }
  }

instance : AddSemigroup Rotation := { add_assoc := rot_add_assoc }

/-!
## AddMonoid
-/

example : ∀ (a : Rotation), 0 + a = a 
| r0 => rfl
| r120 => rfl
| r240 => rfl

theorem rot_zero_add : ∀ (a : Rotation), 0 + a = a :=
by 
  intro a
  cases a
  repeat { rfl }

theorem rot_add_zero : ∀ (a : Rotation), a + 0 = a :=
by 
  intro a
  cases a
  repeat { rfl }

instance : AddMonoid Rotation := {
  zero_add := rot_zero_add
  add_zero := rot_add_zero
}


/-!
## Action of Rotation on State
-/

#check AddAction

/-!
An additive action should be thought of in a general
sense as the addition of a vector-like object (such 
as a rotation) to a point-like object (such as a state)
yielding a new state. For example, in a Euclidean space
if we have a vector, v = (3,1) and a point p = (2,3) 
then the action of v on p "moves" the point from (2,3)
to (3+2,1+3) = (5,4). In our simpler space, rotations
are actions and states are points, and the action is
"addition" of a rotation (vector) to a state to yield
a new state. Here's the definition of this action.
-/

def vadd_rot_state : Rotation → State → State
| r0, s => s
| r120, s0 => s120
| r120, s120 => s240
| r120, s240 => s0
| r240, s0 => s240
| r240, s120 => s0
| r240, s240 => s120

/-!
We need now use this function as the definition
of Vadd.add, denoted +ᵥ in Lean.
-/

instance : VAdd Rotation State := ⟨ vadd_rot_state ⟩

-- Here's a little nit to keep in mind
#reduce 0 +ᵥ s0                 -- Lean sees 0 first, infers type (0 : Nat), then it's a type error
#reduce (0 : Rotation) +ᵥ s0    -- Need to type cast 0 to Rotation, then right overload is selected


/-!
## AddAction 
-/

theorem rot_zero_vadd : ∀ (p : State), (0 : Rotation) +ᵥ p = p :=
by
  intro p
  cases p
  repeat { rfl }

theorem rot_add_vadd : ∀ (g₁ g₂ : Rotation) (p : State), g₁ + g₂ +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p) :=
by
  intros g₁ g₂ p
  cases g₁
  repeat {
    cases g₂
    repeat {
      cases p
      repeat rfl
    }
  }

/-!
With those proofs we can overload the AddAction typeclass.
-/
instance : AddAction Rotation State := {
    zero_vadd := rot_zero_vadd,
    add_vadd := rot_add_vadd
  }

-- An example of an expression we can now write
#reduce ((2 • r120) + (3 • r240) + (0 • r120)) +ᵥ r120

/-!
## From a Monoid of Actions to a Group

A group differs from a monoid by the addition of an inverse
operator. In an *additive* group, this is negation. So a set
with a monoid structure plus an additive inverse (negation)
operation that behaves itself (∀ a, -a + a = 0), is a group.
Having an additive inverse immediately gives us subtraction,
defined as a - b = a + -b.

Can we define a sensible additive inverse operator for 
rotations?Sure, the inverse of any rotation is just another rotation so that
when you add the two of them together you get back to the identity
(as already defined by the monoid structure).

Here's the natural definition of subtraction of rotations that
we will use to overload the additive group typeclass in Lean.
Doing that will give us additive inverse, subtraction, and also
scalar multiplication by *negative* numbers, so not Nat but now
Int!
-/

-- Rotation-specific implementation of negation
def neg_Rotation : Rotation → Rotation
| r0 => r0
| r120 => r240
| r240 => r120

#check AddGroup.mk
/-!
AddGroup.mk.{u}
  {A : Type u}
  [toSubNegMonoid : SubNegMonoid A]
  (add_left_neg : ∀ (a : A), -a + a = 0) :
AddGroup A
-/

-- Hint:
#check SubNegMonoid.mk
/-!
SubNegMonoid.mk.{u}
  {G : Type u}
  [toAddMonoid : AddMonoid G]
  [toNeg : Neg G]
  [toSub : Sub G]
  (sub_eq_add_neg : ∀ (a b : G), a - b = a + -b := by intros; rfl) 
  (zsmul : ℤ → G → G)
  (zsmul_zero' : ∀ (a : G), zsmul 0 a = 0 := by intros; rfl)
  (zsmul_succ' : ∀ (n : ℕ) (a : G), zsmul (Int.ofNat (Nat.succ n)) a = a + zsmul (Int.ofNat n) a := by intros; rfl)
  (zsmul_neg' : ∀ (n : ℕ) (a : G), zsmul (Int.negSucc n) a = -zsmul (↑(Nat.succ n)) a := by intros; rfl) :
SubNegMonoid G
-/

/-!
We need to overload the standard negation operation.
-/

instance : Neg Rotation := { neg := neg_Rotation }

/-!
Now we have negation notation and computation for rotations.
-/

#reduce -r0
#reduce -r120
#reduce -r240

/-!
With negation, we can define a function for subtraction
of rotations (λ r2 r1 => r2 + -r1) and use it to overload
the subtraction operation needed to create a group.
-/

instance : Sub Rotation := { sub := λ r2 r1 => r2 + -r1 }

-- Look, ma! I can subtract rotations!
#reduce r240 - 0
#reduce r240 - r120
#reduce r240 - r240
#reduce r120 - 0
#reduce r120 - r120
#reduce r120 - r240
#reduce r0 - 0
#reduce r0 - r120
#reduce r0 - r240

/-!
Having analzed the AddGroup typeclass in Lean, we
know that to instantiate it, we need to have an instance
of SubNegMonoid, an AddMonoid with unary - and binary - 
operations with sub_eq_add_neg : ∀ a b, a - b = a + -b.
-/
instance : SubNegMonoid Rotation := {}

/-!
And with all that, we can define a *group structure* on
symmetry rotations of a triangle. All we have to add is
a proof that inverses work behave as we expect them to: 
∀ (a : Rotation), -a + a = 0.
-/

theorem rot_add_neg_left : ∀ (a : Rotation), -a + a = 0 :=
by
  intro a
  cases a
  repeat { rfl }

instance : AddGroup Rotation := ⟨ rot_add_neg_left ⟩ 

 #reduce -4 • r120 + 3 • r240 - 6 • r240

/-!
## Torsors (of Point-like objects)
-/

#check AddTorsor
/-!
class AddTorsor (G : outParam (Type*)) (P : Type*) [outParam <| AddGroup G] extends AddAction G P, VSub G P where
  [nonempty : Nonempty P]
  -- Torsor subtraction and addition with the same element cancels out.
  vsub_vadd' : ∀ p1 p2 : P, (p1 -ᵥ p2 : G) +ᵥ p2 = p1
  -- Torsor addition and subtraction with the same element cancels out.
  vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g
-/

#check AddTorsor.mk

instance : Nonempty State := ⟨ s0 ⟩ 

/-
Definition of subtraction of positional States.
On a clock, for example, you can subtract 3PM from
5PM (i.e., 5PM - 3PM) to get two hours. This is the
vector-like duration that, when added to the point
in time, 3PM, gets you 5PM.
-/

def sub_State : State → State → Rotation
-- p2-p1 ...
| s0, s0 => r0
| s0, s120 => r240
| s0, s240 => r120
| s120, s0 => r120
| s120, s120 => r0
| s120, s240 => r240
| s240, s0 => r240
| s240, s120 => r120
| s240, s240 => r0

/-!
 Type class for the `-ᵥ` notation. 
class VSub (G : outParam (Type*)) (P : Type*) where
  vsub : P → P → G
-/

instance : VSub Rotation State := { vsub := sub_State }

theorem rot_state_vsub_vadd' : ∀ (p1 p2 : State), p1 -ᵥ p2 +ᵥ p2 = p1 :=
by
  intro p1 p2
  cases p1
  repeat { 
    cases p2 
    repeat rfl
  } 
  
theorem rot_state_vadd_vsub' : ∀ (g : Rotation) (p : State), g +ᵥ p -ᵥ p = g :=
by
  intros g p
  cases g
  repeat {
    cases p
    repeat { rfl }
  }

#reduce s0 -ᵥ s0 +ᵥ s0 = s0

def rot_st_vsub_vadd' : ∀ (p1 p2 : State), p1 -ᵥ p2 +ᵥ p2 = p1 :=
by
    intro p1 p2
    cases p1
    repeat {
      cases p2
      rfl
      rfl
      rfl
    }

instance : AddTorsor Rotation State := 
{ 
  vsub_vadd' := rot_st_vsub_vadd'
  vadd_vsub' := rot_state_vadd_vsub'
}

/-!
Here's an example where we add a rotation (vector-like)
to another rotation calculated by subtraction of state
(point-like) s120 from s240. So it's r120 + r120 = r240.
And finally we have that vector act on s240 yielding a
final state of s120.
-/
#reduce (r120 + (s240 -ᵥ s120)) +ᵥ s240

/-!
So yay! We've now defined what a mathematician would 
call a torsor of points (states in the form of three
symmetry-preserving rotational angles of a triangle) 
over a group of actions (rotations by multiples of the
"unit" rotation, r120). 
-/

example : r0 = 0 • r120 := rfl
example : r120 = 1 • r120 := rfl
example : r240 = 2 • r120 := rfl
example : ∀ (r : Rotation), 3 • r = 0   -- interesting
| r0 => rfl
| r120 => rfl
| r240 => rfl

/-!
Can you see something in the preceding examples 
that would lead you to doubt that we can turn our
torsor into a vector space? We have something close
to a vector space, with r120 as a unit vector, and
scalar multiplication supported. Moreover these
vector-like things act in the "right" ways on our
states. But still, we don't have a vector space.
Yet.  
-/