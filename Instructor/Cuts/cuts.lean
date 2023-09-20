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