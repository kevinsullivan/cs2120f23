import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

/-!
## From Sets to Relations in the Abstract

We have just learned basic set theory. Now we turn to relations.

Whereas a set of values (of some type α) can be understood as
a collection of single values, a binary relation is understood
as a collection of *pairs* of objects.

Now whereas we represent sets as predicates with one argument,
we represent a relation as a predicate with two arguments. The
predicate specifies the property that a pair will have to have
to be in the relation (or not in it, otherwise).

The theory of relations extends sets theory with added
objects (relations), operations (e.g., inverse), and notations.
We'll focus on the special case of binary relations where both
elements of any given pair in a given relation have the type of
the relation's type argument.

Now finally recall that we chose to represent the type, Set α,
as α → Prop in the logic of Lean. That is as a proposition with
a parameter, that is, a predicate. What makes this predicate
define a set is that it expresses precisely the property that
indicates whether a given object is in a given set. If that
object satisfies the predicate, it's in, otherwise it's out.
-/

/-!
It's easy to see
how this representation strategy generalizes to relations. The
predicate will just take two, rather than one, arguments (both
of the same type now), and will reduce to a propositions to the
effect that the given *pair* of elements is in the mathematical
relation to be modeled.
-/

def evs_pred (n : Nat) : Prop := n % 2 = 0
def evs_set : Set Nat := { n : Nat | evs_pred n }
example : evs_pred = evs_set := rfl         -- literally equal

/-!
A set is the
special case of a relation of arity 1. We will focus entirely
on *binary* relations, which can be understood as sets of pairs
of values. We will further focus on the case where the types of
the first and second elements of these pairs is the same. We
will thus focus on what we'll call *binary relations on single
types of values.
-/


/-!
We've represented sets by their membership predicates. These
predicates take one argument, *a*; and *a* in the specified
set if and only if it satisfies the predicate.
-/
