import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.AddTorsor

/-!
We now turn to formalization of mathematical structures
using the rich collection of abstractions already defined
in Lean's math library, *mathlib*. You can search mathlib
for definitions of interest (here)[https://leanprover-community.github.io/mathlib4_docs/search.html?sitesearch=https%3A%2F%2Fleanprover-community.github.io%2Fmathlib4_docs&q=]
-/

/-!
# Monoids, Torsors, and Groups in Lean
-/

/-!
## Additive Monoids

Imagine a vacuuming robot that can spin on the floor to
point itself in a new direction. Now suppose the robot is
mean to turn by 120 degree and then to turn by another 240
degrees. It could perform each rotation separately, but
that result would be the same as if the robot had done
no rotations at all.

So instead of doing the two actions separately, it'd be
great if, in general, we could could combine any two
into one equivalent rotation, which we can think of as
the *sum* of two given rotations.

In this example the *sum* of the two rotations is equivalent
to a rotation by 360 degrees, which in turn is equivalent to
no rotation at all. So if the robot can add rotations then it
can decide to take no action, expending no power at all.

But what does it mean to add rotations? We can see that if we
have a sensible notion of addition, then no rotation will serve
as the identity rotation. So we'll end up with a mathematics in
which we have (1) a set of rotations, (2) an addition operation
on pairs of rotations, (3) an identity rotation. In other words,
the set of rotations equipped with the additional structure will
form a *monoid*.

Making rotations into a monoid will in turn enable us to derive
an n-ary version of addition by simply applying *foldr* to the
binary addition operator. Then our robot will be able to reduce
a list of *any number* of rotations into a single result that it
can then perform in lieu of carrying our each rotation in turn.
-/

/-! ### Tribot: A Triangular Robot

To see how all of this might work, let's simplify by assuming
we have a robot in the shape of an equilateral triangle, and
that this robot can carry out only three rotations: rotation
by zero degrees, by 120 degrees, and by 240 degrees. We will
call our robot a Tribot.

These three rotations are only rotations of the triangle
that result in the rotated triangle lying right on top of
the triangle in its initial state. We call such actions
"the rotational symmetries of an equilateral triangle."

Clearly the only rotations that are symmetries are rotations
by 0, 120, and 240 degrees. Our main task for the rest of this
chapter is to *equip this set of rotational symmetries with the
additional structure of an additive monoid*: with an operation
of rotation addition and with the zero rotation as the identity.
-/

/-!

### Triangle Rotation States and Rotation

So far we have two key concepts in this story. First, a triangle
can be in one of three rotational states: not rotated, rotated by
120, and rotated by 240 degrees. There are also three *actions*:
rotate by 0, by 120, and by 240 degrees. Rotations *act* on states
by rotating them to produce new states.

Given that there are only three states and three rotationally
symmetric rotation actions, we can represent each of these sets
(states and rotations) as a simple enumerated type. We'll call
the types State and Rotation. We'll call *states,* s0, s120, and
s240. We'll call the *rotations* r0, r120, and r240.
-/

inductive State
| s0
| s120
| s240

inductive Rotation
| r0
| r120
| r240

open State Rotation

/-!
### A plan for instantiating AddMonoid Rotation

Now our task is to "make the set of rotations into a monoid."
We will do this by defining an instance of Lean's AddMonoid
typeclass for the Rotation type. In a nutshell, we'll have
to provide a binary operation, *add*, for Rotations, and an
additive identity element, *zero*, for addition of Rotations.
The add operation will add given rotations in the obvious way
(e.g., r120 + r120 = r240); and we will use r0 as the identity
rotation.

The path to defining an *AddMonoid Rotation* instance in
Lean, by contrast, is somewhat complicated. Such structures
in mathlib tend to be specified as compositions of smaller
pieces. So in general, you have to figure out (recursively)
all the pieces you need, build them, and finally put them
together into the structure you want.

Here's the definition of AddMonoid. We see that the parts
we'll need include instances of AddSemigroup and AddZeroClass.
AddSemigroup in turn extends Add

class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  protected nsmul : ℕ → M → M := nsmulRec
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  protected nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

AddSemigroup extends Add.

Add simply defines an *add* field to hold an addition function for the
underlying type (here Rotations). Lean also defines + as a notation for
Add.add. Here's the Add class.

class Add (α : Type u) where
  add : α → α → α

The AddSemigroup extends Add by adding a proof-valued field to
enforce the constraint that the (inherited) *add* function is
associative.

class AddSemigroup (G : Type u) extends Add G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

The AddZeroClass class inherits from both the Zero and Add classes. We've
already seen Add.

The Zero class has a single field, zero, to hold what is usually meant
to serve as an additive identity element for some function. Lean defines
*0* as a notation for Zero.zero.

class Zero.{u} (α : Type u) where
  zero : α

The AddZeroClass typeclass, having inherited both an *add* function
and a *zero* element,  adds rules to enforce the constraint that the
identity element is a left and right identity for the given function.

class AddZeroClass (M : Type u) extends Zero M, Add M where
  protected zero_add : ∀ a : M, 0 + a = a
  protected add_zero : ∀ a : M, a + 0 = a

Finally, the AddMonoid class, having inherited all of these elements,
adds a convenience function, nsmul, for scalar (s) multiplication of
rotations by natural numbers (n), by iterated application of Add.add.

Finally, let's check the type of the AddMonoid constructor, to see
what we'll need to have in hand to use it to construct our desired
AddMonoid instance for Rotations.
-/

#check AddMonoid.mk

/-!
AddMonoid.mk.{u}
  {M : Type u}
  [toAddSemigroup : AddSemigroup M]
  [toZero : Zero M]
  (zero_add : ∀ (a : M), 0 + a = a)
  (add_zero : ∀ (a : M), a + 0 = a)
  (nsmul : ℕ → M → M)
  (nsmul_zero : ∀ (x : M), nsmul 0 x = 0 := by intros; rfl)
  (nsmul_succ : ∀ (n : ℕ) (x : M), nsmul (n + 1) x = x + nsmul n x := by intros; rfl) :
AddMonoid M

This constructor expects instances of AddSemigroup and Zero to be
passed as implicit arguments, which means that instances must already
be registered. We'll need to provide proofs of the identity axioms
explicitly. Finally we can rely on the default implementations of
nsmul and its axioms, which simply describe multiplication (of a
rotation in our case) by a natural number as repeated addition. So
let's define AddSemigroup Rotation and toZero Rotation.
-/


/-!
#### Zero
We will specify *r0* is the identity rotation. The Zero typeclass
defines *0* as a notation for Zero.zero.
-/

instance zero_rot : Zero Rotation := ⟨ r0 ⟩
#check (0 : Rotation)     -- 0 is now notation for r0!
example : r0 = 0 := rfl   -- r0 and 0 mean the same thing (are equal)

/-!
#### AddMonoid

To we create an instance of the AddMonoid class for Rotations
we'll need an instance of the Add typeclass for rotations. As
we said, that requires that we provide an implementation (i.e.,
a function) for adding Rotation values. Lean provides + as a
notation for Add.add (for addition). Here's our rotation adding
function, our instance definition, and a few examples using *+*
notation.
-/

def add_Rotations : Rotation → Rotation → Rotation
| r0, r => r        -- r matches any argument value
| r, r0 => r        -- r matches any argument value
| r120, r120 => r240
| r120, r240 => r0
| r240, r120 => r0
| r240, r240 => r120

instance : Add Rotation := { add := add_Rotations }   -- using {} notation

#reduce r0 + r120
#reduce r120 + r0
#reduce r120 + r120
#reduce r120 + r240
#reduce r120 + 0      -- Both + and 0 are overloaded for rotations now!


/-
#### AddSemigroup

We need to instantiate AddSemigroup for the Rotation type.
Let's check the constructor and see exactly how to do this.
-/

#check AddSemigroup.mk

/-!
AddSemigroup.mk.{u}
  {G : Type u}
  [toAdd : Add G]
  (add_assoc : ∀ (a b c : G), a + b + c = a + (b + c)) :
AddSemigroup G

Constructing an AddSemigroup instance using this constructor
takes the carrier type, *G*, and an already defined instance
of *Add G* as implicit arguments.  The only field we need to
provide explicitly is the proof of the associativity of the
inherited *Add.add* operation. For now, until we learn more
about constructing proofs, we'll just "stub out" this value.
-/

instance : AddSemigroup Rotation := { add_assoc := sorry }

/-!
#### AddMonoid

Now we can instantiate AddMonoid. We'll check its constructor
(again) and proceed accordingly.
-/

#check AddMonoid.mk

/-!
AddMonoid.mk.{u}
  {M : Type u}
  [toAddSemigroup : AddSemigroup M]
  [toZero : Zero M]
  (zero_add : ∀ (a : M), 0 + a = a)
  (add_zero : ∀ (a : M), a + 0 = a)
  (nsmul : ℕ → M → M)
  (nsmul_zero : ∀ (x : M), nsmul 0 x = 0 := by intros; rfl)
  (nsmul_succ : ∀ (n : ℕ) (x : M), nsmul (n + 1) x = x + nsmul n x := by intros; rfl) :
  AddMonoid M
  -/

/-!
We need provide explicily only proofs of the identity axioms!
AddSemigroup and Zero instances will be obtained implicitly.
The nsmul function, with notation •, implements multiplication
of an action by a natural number scalar (thus *nsmul*). This
function works by n-iterated addition of an action to itself,
with *0* (the identity action, *r0*, in our case) as identity
and the answer when *n = 0*. The proofs also have defaults to
verify that *nsmul* implements n-iterated addition. At this
point, it's thus super-easy to instantiate the AddMonoid class
for the Rotation type.
-/

instance : AddMonoid Rotation := {
  zero_add := sorry
  add_zero := sorry
}

#reduce 0 • r120              -- 0 means r0; • means *nsmul*
#reduce 1 • r120
#reduce 2 • r120
#reduce 3 • r120
#reduce 2 • (r120 + r120)     -- precedences are also set right
#reduce (2 • r120) + (3 • r240) + (0 • r120)



/-!
Taking stock of where we are, we have (1) a set of triangle
states, and (2) a monoid of symmetry-preserving rotations,
in which we can compute with addition (*+*) and natural number
scalar multiplication (*•*), with *0* as the identity rotation.
We can thus express and compute rotations in terms of given
rotations with arbitrarily complex expressions in this algebra.
Furthermore, this algebra lets us reduce complex compositions
of rotations to single values that can be carried out with at
most one actual physical movement.
-/

/-!
## The Action of a Rotation on a Triangle State (Point)

The next concept that we want to formalize is that of the
*action* of a rotation on a *state*. Consider *r120* as an
action and *s120* as a state. Intuitively we expect that the
rotation by 120 degrees acts on a triangle already rotated
by 120 degrees, leaving in in a state of being rotated by
240 degrees: the state we've already named s240.

Additive actions occur in many settings. In a two-dimensional
vector space, for example, vectors act on points in the plane.
If you have a point *p = (1,1)* and a vector *v = (2,3)*, then
*v* acts on *p* to yield the point *p +ᵥ v = (3,4)*. Here and
in Lean more generally we denote the operation of an additive
action *v* on an object *p* as *p +ᵥ v.*

We can now think of *actions* as vector-like things (that we
can add and scale), while rotational *states* are point-like
things that can be transformed (e.g., rotated, moved, etc) by
actions.

You may even want to visualize rotations as curved "vectorish"
arrows. The action of a rotation on a state is visualized by
placing the tail of the curved arrow at the point to be acted
upon, with the result being a point at the head of the arrow.
This is exactly how addition of a vector to a point works in
a vector (or more accurately an affine) space.

In Lean, we represent the action an element from a monoid of
"vector-like" actions, *G*, on a "point-like" object of a type,
*P,*  by defining an instance of the *AddAction* typeclass. That
class in turn extends the *VAdd* class, which carries a function,
*VAdd.vadd : G → P → P*, that defines the action of *G* on *P.*
Lean provides the notation, +ᵥ, for the action, by addition, of
a vector-like action *(g : G)* on a point-like object, *(p : P)*.
-/

#check AddAction


/-!*
So let's look at the AddAction* typeclass and its inherited Add class.

class AddAction
(G : Type u_10)
(P : Type u_11)
[AddMonoid G]
extends VAdd : Type (max u_10 u_11)
  vadd : G → P → P
  zero_vadd : ∀ (p : P), 0 +ᵥ p = p
  add_vadd : ∀ (g₁ g₂ : G) (p : P), g₁ + g₂ +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)


class VAdd (G : Type u) (P : Type v) : Type (max u v)
    vadd : G → P → P

-/

/-! EXERCISE. Explain in English the meanings of the axioms
for additive actions. Then implement AddAction for the Rotation type.
-/

def vadd_rot_state : Rotation → State → State
| r0, s => s
| r120, s0 => s120
| r120, s120 => s240
| r120, s240 => s0
| r240, s0 => s240
| r240, s120 => s0
| r240, s240 => s120

instance : VAdd Rotation State := ⟨ vadd_rot_state ⟩

#check AddAction

instance : AddAction Rotation State := {
    zero_vadd := sorry,
    add_vadd := sorry
  }

#check VAdd.vadd ((2 • r120) + (3 • r240) + (0 • r120)) s0



#check AddGroup.mk

/-!
## Torsors (of Point-like objects)

We've now established a firm separation between
point-like and vector-like things, and that we
can have structures in which vector-like things
that have an associated monoid structure can be
defined as acting on corresponding point-like
things, subject to certain axioms. Central is
the idea that, while points aren't vectors, and
can't be added like vectors, differences between
points can be defined as giving rise to vectors,
each of which is precisely the difference vector
that needs to be added to the second point to get
back to the first. p2 - p1 = v s.t. v + p1 = p2.

We get that vector-like transformations on points
have a natural monoidal structure. But what kind
of things are the sets of points themselves? They
don't contain vectors, so they aren't anything
like vector spaces. There is no operation to add
add points, and the very concept doesn't really
make sense. What is 3PM + 5PM?

The answer is, informally speaking, that a set
of points with differences that constitute a
monoid, or group, or module, or vector space
(M) is called an M-torsor. Differences of points
are actions (in the monoid, group, module, etc.)
that act on points in ways that follow ordinary
rules of arithmetic.
-/

/-!
Homework #1: Endow Rotation with the additional structure of an additive group.
-/
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
  (sub_eq_add_neg : ∀ (a b : G), a - b = a + -b := by intros; rfl) (zsmul : ℤ → G → G)
  (zsmul_zero' : ∀ (a : G), zsmul 0 a = 0 := by intros; rfl)
  (zsmul_succ' : ∀ (n : ℕ) (a : G), zsmul (Int.ofNat (Nat.succ n)) a = a + zsmul (Int.ofNat n) a := by intros; rfl)
  (zsmul_neg' : ∀ (n : ℕ) (a : G), zsmul (Int.negSucc n) a = -zsmul (↑(Nat.succ n)) a := by intros; rfl) :
SubNegMonoid G
-/

-- Rotation-specific implementation of negation
def neg_Rotation : Rotation → Rotation
| r0 => r0
| r120 => r240
| r240 => r120

/-!
We now endow rotations with Rotation-specific subtraction.
Doing that gives us unary negation, subtraction as addition
of the negative, and multiplication or a rotation by any
*integer* value, including negative values.
-/

instance : Neg Rotation := { neg := neg_Rotation }

/-!
Now we have negation notation and
computation.
-/

#reduce -r0
#reduce -r120
#reduce -r240

instance : Sub Rotation := { sub := λ r2 r1 => r2 + -r1 }

-- Look, ma: I can subtract!
#reduce r240 - 0
#reduce r240 - r120
#reduce r240 - r240
#reduce r120 - 0
#reduce r120 - r120
#reduce r120 - r240
#reduce r0 - 0
#reduce r0 - r120
#reduce r0 - r240

-- You finish!

#check AddTorsor
/-!
class AddTorsor (G : outParam (Type*)) (P : Type*) [outParam <| AddGroup G] extends AddAction G P,
  VSub G P where
  [nonempty : Nonempty P]
  /-- Torsor subtraction and addition with the same element cancels out. -/
  vsub_vadd' : ∀ p1 p2 : P, (p1 -ᵥ p2 : G) +ᵥ p2 = p1
  /-- Torsor addition and subtraction with the same element cancels out. -/
  vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g
#align add_torsor AddTorsor
-/

instance : SubNegMonoid Rotation := ⟨ _, _, _, _, _⟩ 

instance : AddGroup Rotation := ⟨ _ ⟩ 
/-
    show Add.add (-a) a = 0
    simp [Neg.neg]
    cases a
    repeat {
      simp [add_Rotations, neg_Rotation, Add.add]
      rfl
    }
 ⟩
-/


/-!
Homework #2: Endow State and Rotation with the 
additional structure of an additive torsor over 
that (additive) group.
-/

-- Hint: follow the same approach

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
