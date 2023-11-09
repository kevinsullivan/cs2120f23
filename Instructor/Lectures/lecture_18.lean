import Mathlib.Init.Set

/-!
## Predicates

You've seen that in predicate logic, a proposition is a
declarative statement that asserts that some state of affairs
holds in some domain of discourse. For example, *the natural
number, four, is an even* is a proposition. We've seen one
way to formalize such a proposition using the mod operator.
-/

#check 4 % 2 = 0

/-!
### Families of Propositions

Indeed, there is an infinite family of propositions, all just
like this one except for the particular number we plug in instead
of four. As another example, *the natural number, five, is even*
is also a proposition. And there's one such proposition for each
and every natural number.

We can write this family of propositions by *abstracting* the value,
four, to a variable: e.g., *the natural number, n, is even*, where
*n* can be any natural number. Now we have a predicate. Applying it
to a specific number then returns a proposition about that number.

We could say that applying the predicate, *the natural number, n,
is even*, to the specific number, four, returns the *proposition*,
*the natural number, four, is even.*

In Lean and related logics, we represent a predicate as a
*function:* from one or more parameter values to propositions.
Here's our simple example reformulated.
-/

def is_even : Nat → Prop := λ n => n % 2 = 0

/-!
You can see that is_even is a predicate by checking its type.
Indeed, it's a function from a natural number to a proposition
*about* that number: namely that the given number mod two is
zero. The type of our predicate is thus *Nat → Prop*.
-/
#check (is_even)      -- Nat → Prop

/-!
### Applying a Predicate to Arguments Yields a Proposition

Given a predicate we derive a proposition by *applying* it to one
or more arguments of the specified types. The *is_even* predicate
is appliable to a natural number as an argument. Here are two examples
applying the is_even predicate.
-/

#check is_even 4
#check is_even 5
/-!
Note that Lean reduced n%2 in each case to 0 or 1, leaving us
with simpler propositions involving just 0 and 1.
-/

/-!
### To Satisfy a Predicate
We will say that specific parameter values *satisfy* a predicate
if they yield a proposition that is true. In a sense, a proposition
thus specifies a *property* (such as that of being even) that a value
might or might not have. For example, four has the property of being
even but five doesn't.

### Predicates Specify Properties

In this way a predicate picks out the subset of parameter values with
a specified *property*. As an example, we can make a list of natural
numbers from 0 to 5, apply *is_even* to each, determine which resulting
propositions are true, and thus *pick out* the natural numbers with the
property of being even.
-/

#reduce is_even 0   -- ✓
#reduce is_even 1   -- ×
#reduce is_even 2   -- ✓
#reduce is_even 3   -- ×
#reduce is_even 4   -- ✓
#reduce is_even 5   -- ×

/-!
Indeed, as we'll see in more depth shortly, we can understand
the *set* of all objects having a particular property as those
objects that satisfy the predicate that specifies the property.
In Lean, we can specify the set of even numbers as follows, and
*evens* here becomes nothing but a shorthand for is_even. We'll
see more of this top when we get to lectures on set theory.
-/

def evens : Set Nat := { n | is_even n }
#reduce evens 4
#reduce evens 5


/-!
### Predicates of Multiple Arguments

Predicates can take any number of arguments. Here are some examples.
-/

/-!
#### Ordered pairs of numbers and their squares
-/

def square_pair : Nat × Nat → Prop
| (n1, n2) => n2 = n1^2

#reduce square_pair (1, 1)   -- ✓
#reduce square_pair (2, 4)   -- ✓
#reduce square_pair (3, 9)   -- ✓
#reduce square_pair (5, 20)  -- ×

def square_pairs : Set (Nat × Nat) := { p : Nat × Nat | square_pair (p.1, p.2) }
#reduce square_pairs
#reduce (3, 9) ∈ square_pairs

/-!
#### Pythagorean triples
-/

def pythagorean_triple : Nat → Nat → Nat → Prop
| h, x, y => h^2 = x^2 + y^2

/-!
### Exercises

- Write a predicate for the property of being an even-length string
- Write an expression for the set of all even length strings
-/

/-!
## Quantifiers

Quantifiers are part of the syntax of predicate logic. They allow one
to assert that every object (∀) of some type has some property, or that
there exists (∃) (there is) at least one object of a given type with a
specified property. The syntax of such propositions is as follows:

- ∀ (x : T), P x
- ∃ (x : T), P x

### Universal Quantification

The first proposition can be read as asserting that every value *x* of
type *T* satisfies predicate *P*. Another way to say this is that for
every *x* there is a proof of the proposition, *P x*. Another way to
say that is that there's a function that when given any *x* returns a
proof of *P x*. Indeed, that's how we prove such a proposition: show
that if given any *x* you can produce and return a proof of *P x*.
-/

/-!
### ∀ (for all)
-/
def zornz (n : Nat) : n = 0 ∨ n ≠ 0 :=
match n with
  | 0       => Or.inl rfl   -- proves an equality
  | n' + 1  => Or.inr (fun _ => nomatch n')

/-!
### ∃ (there exists)
-/

def sl5 : ∃ (s : String), s.length = 5 := ⟨"Hello", rfl ⟩
