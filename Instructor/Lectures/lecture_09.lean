/-!
# The Empty Type

Just as there's a type, *Unit*, with just one value, 
we can also define a type, we'll call it *Empty*, with =
no values at all. It sounds useless. We won't find it 
useful for programming but it plays an essential role
in logic. For now we'll see what we can learn by seeing
what kinds of functions we can define involving values 
of this type (a type with no values at all). 
-/

namespace cs2120

inductive Empty : Type

/-!
That it: no constructors, no values. Voila, the Empty type. 

## Introduction Operation

The Empty type has no introduction rule. It has not even a
single constructor.T his type has no values at all. It's 
called an *uninhabited* type. A type that has at least one
value is said to be *inhabited.* The Empty type is clearly
uninhabited. 

Consequently, there's no way to complete the binding of a 
variable to a value of type Empty, since, again, no such 
value exists. 
-/

def e : Empty := _  -- can't define a term of type Empty

/-! 
Nor is there a way to complete the definition of a
function that takes an argument of an inhabited type and
that promises to return a value of type Empty. 
-/

def inhabited_to_empty : Unit → Empty 
| unit => _  -- you just can't create a term of this type     

/-!
If you could complete this function definition, and with 
Unit being inhabited, then you could apply the function to
a value of that type, and that point, you'd be stuck with
having to do the impossible: return a value of type Empty. 
You simply cannot implement a function of a type such as
Unit → Empty, Bool → Empty, etc. 
-/

/-!
## Functions Involving the Empty Type 

On the other hand, elimination (use) of value of the Empty type
is interesting and important. To see the key idea it helpful to
look at whether and if so how we can implement functions of three
different types, each having the *Empty* type as either an input 
argument or an output return value, or both. 

- A function taking a Nat value in and returning an Empty value   
- A function taking an Empty value in and returning a Nat value   
- A function taking an Empty in and returning an Empty value 
-/

/-!
### Nat → Empty
-/

def nat2empty : Nat → Empty 
| n => _      

/-!
There's no way to construct a value of type Empty,
because there are no such values, so we can't finish
this definition. There are values of type Nat, so we
can call this function, but it cannot finish because
there's no way to write a return result term of type
Empty. So not only is there no value of type *Empty*
but there is no function of type *Nat → Empty*. It,
too, is an uninhabited type!

If you try to call it using #reduce, it'll tell you 
that the function is defined using "sorry", which is 
to say that the definition is incomplete. (Yes, the
error message is confusing. Sorry about that.)
-/

#reduce nat2empty 5 -- sorry (doesn't properly reduce)

/-!
### Empty → Nat

Next let's write a function that takes an argument of
type Empty and returns a result of some other type: we
will again just use Nat as an example. 

The absolute essential idea needed to understand what
we're about to say is that *when a function is given a
value of some type as an argument, it has to provide a
result for each possible way in which that input could
have been constructed. If you're given a Bool value, you
have to provide an output value for *true* and and output
value for *false*. If you're given a Unit value, you have
to provide an output value for the single possibility,
*Unit.unit.* For how many cases do you need to produce
an output value for the empty type? The answer is: ____.
You have to see how to fill in this blank. Then you'll
understand the new construct introduced in the following
code. 
-/

def empty2nat : Empty → Nat 
| e => nomatch e

-- Just another way to write the same code
def empty2nat' (e : Empty) : Nat := 
  nomatch e 

/-!
There's something very odd about this function. It
type basically says, "if you give me (e : Empty) I 
can give you a Nat." Suppose, then you do give such
an e. The implementation has to give an result (of 
type Nat) *for each possible case for e*. How many 
cases are there? Zero! So you don't have to give an
answer at all! 

That's the meaning of *nomatch e*. You don't have to 
specify an actual natural number return value for even
a single case.  
-/

-- You can never call it, so it doesn't matter!
def x := (empty2nat _)    -- can't give a value 

/-!
As another example, we can define a function
defined to return a value of type Empty provided 
it gets on as an argment.
-/

def empty2empty : Empty → Empty 
| e => nomatch e

def x' := (empty2empty _) -- we can never call it 

/-!
Indeed, given *any* type whatsoever, call it α, we 
can define a function of type *Empty → α*. This is 
a function that looks like it can return a result 
of any possible type. As an in-class exercise, write
it! 
-/

/-!
Indeed, there's nothing special about Nat or Empty
as return types in these examples. We can write a
function defined to return a value of any type, given 
a value of the Empty type as an argument. Again, the 
reason is that such a function to to return a value 
for each possible constructor/form of e, but there 
are no constructors/forms, so there are no cases to
consider. We can thus define a generalize polymorphic
function defined to return a value of any arbitrary
type, α, if it's given an argument of the Empty type.
-/

def empty2anytype : {α : Type} → Empty → α
| _, e => nomatch e

end cs2120

/-! 
## Summary 

It's worth taking stock of the key ideas you've now learned
in this class. 

### Types

A central idea of course is the notion of a *type*. A type
can be understood as defining and giving a name to a set 
of terms. The set of terms of a type are defined entirely 
by its constructors. A constructor applied to zero or more
arguments (of the right types) is the a value of the given
type. We can say that it belongs to, or has, that type. 

We use terms, in turn, to *represent* meaningful things,
often things in the real world, such as the days of the 
week, possible moves in a game, or possible game outcomes.
The art of programming is largely in making great choices
about how to represent meaningful things in the world as 
terms with specific types in the computing machine.

For example, the terms, *true* and *false* of type *Bool*
in Lean represent the two values in Boolean algebra, also
generally called true and false. A term, *5* of type *Nat*
in Lean represents the abstract natural number, five. A
term, "Hello," of type String, represents the word, Hello.

### Bigger Types from Smaller Types

A second key idea in our work so far is that we can make
bigger types out of smaller types. In particular, if we
have any two types, *α* and *β*, we can form several new
types, and then we can (usually) for values of these new
types. We've seen three major examples. Given the types, 
*α* and *β*, here are three news types we can form.

- (α → β) : the type of a function with α input and β output  
- (α × β) : the produt type, of ordered pairs of α and β values  
- (α ⊕ β) : the sum type, of either an α value or a β value

### Introduction and Elimination Operations

We use the phrase, introduction operation, or sometimes
introduction rule, for constructors that *create* values
of a given type. Conversely, we use the phrase, elimination
operation, or elimination rule, for operations that *use* 
values of a given type. 

As an example, the constructor, *Prod.mk (a : α) (b : β)* 
is an introduction operation. If you apply *Prod.mk* to a
pair of values, as in *(Prod.mk 1 true)* it introduces this 
term as a value of type *Prod Nat Bool*. Please do recall
that the expression *(1, true)* is just standard notation 
for this aconstructor application. 

Conversely, if you want to *use* a term, (Prod.mk 1 true)
will likely want to get at the values, *1* and *true* that
it encapsulates. This is done by pattern matching. As an
example, the following expression matches the *pattern*,
*(Prod.mk f s)* with the term, *(Prod.mk 1 true)*, with
the result that the identifier, *f* is temporarily bound
to the *1* inside the term, and *s* is bound to *true*; 
and it then returns *f*, thereby providing access to the 
first element of the term. (Lean gives a warning that *s*
is not used, which tells you you can replace it with _).
-/

#eval match (Prod.mk 1 true) with -- expect 1
          | (Prod.mk f s) => f    -- pattern matches term

#eval match (Prod.mk 1 true) with -- expect true
          | (Prod.mk _ s) => s    -- no need to name 1

/-!
The types, *α → β, α × β,* and *α ⊕ β* are all formed
from two types, *α* and *β*, but they have very different
meanings: 

- a type of function that *if* it's given a value of type *α* then it returns a value of type *β* 
- a type of ordered pairs each of which contains a value of type *α and* a value of type *β*
- a type of sums, each of which contains *either* a value of type *α* or a value of type *β* 

What fundamentally distinguishes these types are their introduction (construction)
and elimination (usage) operations. For example, a product type has *one* constructor
(introduction operation) that takes an *α* value *and* and *β* value, while a sum type
has two constructors, one of which takes an *α* value and the other a *β* value. In turn
the product type has two elimination operations, one returning the first and the other
the second component of a pair, while there's just one sum elimination rule, that takes
a sum along with functions enabling either case to be reduced to a value of a single 
output type. 

What remains is to explain the introduction and elimination operations for
function types. Recall that a *value* of a function type is essentially a 
function *implementation* that for converting a given argument value (of a
type *α*) into a value of an output type, *β*. That's the introduction rule:
give such a procedure.
-/

def negate : Bool → Bool :=   -- function type
λ b => match b with           -- function value
| false => true
| true => false

/-!
So what's the elimination procedure for a value of a function type? In
other words how do you *use* a function? You *apply* it to an argument!
-/

#eval (negate true)

/-!
## Wrap-Up: Understand the Following

Understand the following types and their introduction 
and elimination operations. You should understand exactly
which introduction (constructor) and elimination operations
correspond to these types, and how to define the types and
these operations, and how to use them, without looking at
notes. 

- {α β : Type} → (a : α) → (b : β) → α × β 
- {α β : Type} → α × β → α
- {α β : Type} → α × β → β 
- {α β : Type} → α → α ⊕ β
- {α β : Type} → β → α ⊕ β
- {α β γ : Type} → α ⊕ β → (α → γ) → (β → γ) → γ
- {α β : Type} → (α → β) → α → β 
- {α β : Type} → [procedure yielding some β given any α] → (α → β) 
- (unit : Unit)
- There's no useful elimination operation for Unit
- There is no introduction operation for *Empty*
- { α : Type } → Empty → α 
-/