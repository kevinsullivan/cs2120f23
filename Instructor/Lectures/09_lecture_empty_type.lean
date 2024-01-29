/-!
# Data Types: The Empty Type

Just as we've defined the *Bool* type with two values, 
and the *Unit* type with just one value, so we can also
define a type, we'll call it *Empty*, with no values at
all. In this chapter we'll understand this Empty type 
by investigating what kinds of functions we can define
involving (non-existent) values this type.  
-/

namespace cs2120

/-!
## Definition of the Empty Type

Here's how the type is defined in Lean.
-/

inductive Empty : Type

/-!
That's it: no constructors, no values. Voila, the Empty type. 
-/

/-!
## Functions Involving the Empty Type

In the remainder of this chapter we explore whether or not
we can implement certain function types involving Empty as
either an argument or return type. You're not likely to run
into such examples in everyday programming, but understanding
these example will be deeply important as we turn to logical
reasoning.  

### No Introduction (Value Creation) Operation for Empty

The Empty type has no introduction operations. It has not 
even a single constructor so it's impossible to create even 
a single value of this type. Such a type is said to be 
*uninhabited*. A type that has at least one value is said 
to be *inhabited.* The Empty type is an uninhabited type. 

A consequence of having no constructors and thus no values
is that here's no way to complete the binding of a variable 
of the Empty type. There's no way to complete the following
definition. 
-/

def e : Empty := _  -- can't express a term of type Empty

/-! 
### No Functions from Inhabited Types to Empty

Nor is there a way to complete the definition of a
function that takes an argument of an inhabited type
(and which thus can be applied to a value of that type) 
and that promises to return a value of type Empty. In
the following example, we use Unit as a simple example
of an inhabited type.
-/

def inhabited_to_empty : Unit → Empty 
| unit => _  -- can't write a term of the Empty type     

/-!
If you could complete this function definition, and with 
Unit being inhabited, then you could apply the function to
a value of that type; and that point, you'd be stuck with
having to do the impossible: return a value of type Empty. 
You cannot implement a function of type as Unit → Empty, 
Bool → Empty, or from any inhabited type to Empty.  
-/

/-!
### There Is a Function from Empty to Empty

The only way to define a function that returns a value
of the empty type is to have it *assume* that it's given
a value of this type as a parameter. 
-/

def empty_to_empty'' : Empty → Empty
| e => e

def empty_to_empty' (e : Empty) := e -- return type inferred

def empty_to_empty (e : Empty) : Empty := nomatch e


/-!
This definition is subtle. Clearly it *is* possible to 
define a function that promises to return a value of
the Empty type, and does so, assuming you apply it to
a value of this type.  Indeed, the right way to read the
Empty → Empty function type is as saying *if you give me
a value of type Empty, I'll give you back value of type
Empty*. On the other hand, nowhere does this function
definition promise that there's a value of type Empty
it can be applied to. Indeed, it's a function that does
exist but that can *never be applied*. That's how it 
can exist without creating a contradiction.  
-/

def empty_value := empty_to_empty' _ -- no way to apply it

/-!
### Case Analysis on an Argument of Empty Type

Another way to understand why it's ok to define a function
of type Empty → Empty is by considering case analysis on
the argument. If the argument were of type Bool, a function
definition would have to provide results for both true and
false argument values. If the argument were of type Unit,
the function definition would have to provide a result for 
the unit value. But if the argument is of type Empty, the
function needs to provide results for *no argument values
at all!* There are *no* cases to consider. With an assumed 
argument of type Empty, with no cases to consider, one need
do nothing at all to uphold the promise to return a value 
of any type whatsoever.  

Here's how to write our empty-to-empty function in Lean
using case analysis. It's with a new keyword that indicates
an empty match. Consider matching on Bool, Unit, and then
Empty values.
-/

-- First consider case analysis on a Bool argument
def match_bool (b : Bool) : Bool :=
match b with
| true => true
| false => false

-- Now case analysis on a Unit argument 
def match_unit (u : Unit) : Unit :=
match u with
| unit => unit

-- Finally case analysis on an Empty argument -- no cases
def empty2nat (e : Empty) : Empty := 
nomatch e   -- with no cases to consider, we're done

/-!
### A Function from Empty to Any Type Whatsoever
Indeed, there's nothing special about the Empty return
type in the preceding example. The same trick--matching
on Empty requires no further work--works no matter the
return type. We can thus implement a function from Empty
to *any* type whatsoever!
-/

def empty_to_bool :         Empty → Bool := nomatch e
def empty_to_nat :          Empty → Nat  := nomatch e
def empty_to_α (α : Type) : Empty → α    := nomatch e 

/-!
The final example is the general elimination rule
for the Empty type: an empty match is a get out of
jail free card that let's you return a value of any
type, even of a type, such as Empty, that has no
values at all. There's no contradiction as such a
function can never be called, so one need not give
an explicit return value. 

### The Generalized Empty Elimination Operation

We now simply rename the function to empty_elim,
to emphasize it's general nature. It shows that
if a function assumes it's given a value of type 
Empty, then it can promise to return a value of 
any type whatsoever. 
-/

def empty_elim (α : Type) : Empty → α := nomatch e 

/-!
Logically speaking, one can 
say that *from a contradiction (there is a value 
of type Empty), you can deduce anything at all*.  
It's logically true: if I'm a cat (contradiction) 
then gerbils are really tiny neckless giraffes.
-/

/-!
### What Does a Function of Type (α → Empty) Imply?

As a final key idea, suppose you have some type, α,
and you actually *can* implement a function of type 
α → Empty. What indisputible and important fact can 
you conclude about the type, α? What's the only way
you will be able to implement such a function? 
-/

-- You answer here with a brief explanation

/-!
## Exercises

- Can you define some function, nxe2s : Nat × Empty → String 
- Is the type, Nat × Empty → String, inhabited or not?
- How many strings can nxe2s possibly return? Why?
- Can you define a function, noe2s : String ⊕ Empty → Nat 
- Is the type, String ⊕ Empty → Nat, inhabited or not?
- Can noe2s return any Nat? If so, prove it by example.
- Is the function type, (Nat → Empty), inhabited or not?
- Prove your answer (is (Nat → Empty) uninhabited)
- Is the type, {α : Type} → α → Empty, inhabited or not.
- Prove your answer (Is {α : Type} → α → Empty, inhabited?)
- Is the type, Empty → (Nat → Empty) inhabited? Prove it.
- Prove this type uninhabited: {α : Type} → α × (α → Empty)
-/

end cs2120