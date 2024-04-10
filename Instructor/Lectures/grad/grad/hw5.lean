/-!

#1:

Here's a data type, instances of which
can represent monoids. A monoid, again,
is a set of objects (here all the objects
of any type, α), with an associative binary
operator, op, and a left and right identity
element, id.
-/

structure my_monoid' (α : Type) where
(op : α → α → α)
(id : α)

/-!
Write a version of foldr with just one type
parameter, α, that, instead of taking op and
id as separate arguments instead takes an one,
an instance of this type. Recall that given such
an object you can access its field values using
dot notation.
-/

def foldr' {α : Type} : my_monoid' α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr' m t)


/-!
To test your solution, create an instance for
Nat with addition as the operator and 0 as the
identity element, then pass this instance to your
new version, foldr''', and show that the result
can be used to sum the elements in a list of Nat
values. You can call your function foldr'''.
-/

#eval foldr' (my_monoid'.mk Nat.add 0) [1,2,3,4,5]
#eval foldr' (my_monoid'.mk Nat.mul 1) [1,2,3,4,5]
#eval foldr' (my_monoid'.mk String.append "") []

/-!
Ok, so what does a monoid actually *do* for you?
Consider the following applications of this idea.
-/

def nary_add := foldr' (my_monoid'.mk Nat.add 0)
#eval nary_add [1,2,3,4,5] -- expect 15

def nary_mul := foldr' (my_monoid'.mk Nat.mul 1)
#eval nary_mul [1,2,3,4,5] -- expect 120

def nary_append := foldr' (my_monoid'.mk String.append "")
#eval nary_append ["Hello, ", "Higher ", "Mathematics!"]

/-!
Discuss: So what does a monoid do?

Answer: It extends a binary operator to be a n-ary operator.
-/

/-!
#2: A big problem with this solution is that there
is no way to assure that such an object really does
represent a monoid. What has been forgotten is that
op has to be associative and id needs to be a left
and a right identity for op. Then you have a monoid.
-/

structure my_monoid (α : Type) where
(op : α → α → α)
(id : α)
(left_id: ∀ a, op id a = a)
(right_id: ∀ a, op a id = a)
(op_assoc: ∀ a b c, op a (op b c) = op (op a b) c)

/-!
EXERCISE: Define a version of foldr, called foldr,
that uses this improved structure as an argument.
-/

def foldr {α : Type} : my_monoid α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr m t)

/-!
Here are two instances of this type. One
represents the monoid of natural numbers
under addition, with zero as the identity,
and the other, the same natural numbers
but now under multiplication with identity
element 1.
-/

--
def nat_add_monoid : my_monoid Nat :=
  my_monoid.mk Nat.add 0 sorry sorry sorry

#eval foldr nat_add_monoid [1,2,3,4,5]

/-!
Lean provides a nice notation for constructor application
-/

def nat_add_monoid' : my_monoid Nat :=
  ⟨  Nat.add,
    0,
    λ a => by simp [Nat.add],
    λ a => by simp [Nat.add],
    _
   ⟩

-- The multiplicative monoid of natural numbers
def nat_mul_monoid'' : my_monoid Nat :=
  ⟨ Nat.mul,
    1,
    λ a => by simp,
    λ a => by simp,
    λ a b c => _
  ⟩

/-!
EXERCISE: Apply your better version of foldr
-/

def nary_mul' : List Nat → Nat := foldr (my_monoid.mk Nat.mul 1 sorry sorry sorry)

#eval nary_mul' [1,2,3,4,5]
