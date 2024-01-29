/-!
# Universal Generalization: ∀, Π, →

In the constructive logic of Lean, all functions
are total. That is, a function must return a value
of the specified return type *for all* arguments of
the specified type. For example, the String *length*
function is defined and will return a correct value
for all string-valued arguments.
-/

/-!
## Function Types Are Geberalizations
-/

variable
  (α β : Type)

#check α → β
/-!
In dependent type theory, function arrow α → β
is notation for ∀ (_ : α), β, a special case where
the return type, β, does not depend on the argument
value of type α, as reflected in our use of _ in our
definition of f1.
-/
#check ∀ (_ : α), β
/-!
What we've seen is that function arrow → is a special
case, *∀ (_ : α), β*, where the return type, β, is
independent of the choiceo of an α value.
-/

/-!
The ∀ reflects the totality of any such function.
For *any* string as an argument, such a function
must return some corresponding natural number.
-/
#check ∀ (_ : String), Nat


/-!
To prove *∀ (_ : String), Nat* we show that from
an assumption that argument, s, is any string, we
can derive a corresponding natural number. Here we
return the string length specifically but that is
not essential.
 -/
def f1 : ∀ (_ : String), Nat := fun s => s.length
/-!
We can pronounce the function value as showing that
if we assume we're given *any* string, s, we can in
all cases return a corresponding natural number. It
is again inessentially the string's length.
-/
def f2 : String → Nat  := fun s => s.length


/-!
##
-/

variable
  (γ : α → Type)

#check ∀ (a : α), γ a

variable
  (A B : Prop)
  {C : A → Prop}

#check A → B
#check ∀ (_ : A), B
#check ∀ (_ : False), True
def g1 :  ∀ (_ : False), True := fun _ => True.intro
def g2 :  False → True := fun _ => True.intro

#check ∀ (a : A), C a
/-!

In first-order predicate logic, and Lean's higher
order logic, the *universal quantifier* symbol, ∀,
is used to write propositions about *all* values
of a specified type.



, ∀, pronounced *for all*
or *for any*, to assert that some proposition is
true there is a value or
proof of a corresponding type or proposition


-/
