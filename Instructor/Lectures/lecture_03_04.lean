/-!
Note: These notes are not yet complete. They
current extend the material presented at the
end of lecture 3, August 29, 2023. This section
will be extended as we go forward.

# Generalization and Specialization

Consider the following three functions. 
-/

def id_nat : Nat → Nat
| n => n

def id_string : String → String
| n => n

def id_bool : Bool → Bool
| n => n

/-!
Each one returns the value of its single 
argument. We call such function *identity
functions*. We thus have identity functions
for arguments of types Nat, String, and Bool,
respectively. Here are example applications.
-/

#eval id_nat 7
#eval id_string "Hello"
#eval id_bool true

/-!
Beyond having different names, these
functions vary only in the types of
their argument and return values. 

We wouldn't want to have to write one
such function for each of hundreds of
types. We can avoid such repetition by
"factoring out" the varying part of the
definition into a parameter (argument). 
-/

/-!
## Parametric Polymorphism

A key idea throughout computer science
and mathematics is that we can generalize
families of definitions by turning aspects 
that vary into parameters. Then by giving
specific values for parameters, we recover
the specialied versions.

In the cases above, the main aspect that 
varies is the *type* of objects that are 
being handled: Bools, Strings, Nats. The 
code for each implementation is identical
so we should really only have to write it
once, in a general way, using the idea of
generalization. 

To do this, we introduce a new argument: one
that can take on *any* type value whatsoever. 
We could call this argument, *T : Type*, but in 
Lean it's conventional to use lower-case Greek
letters to name type-valued arguments, so we'll
call it *α : Type.* Here's the code we want.
-/

def id_poly : (α : Type) → α → α 
| _, v => v

def id_poly' (α : Type) : α → α 
| v => v

/-!
The key idea in play here is that we bind a name, 
α, to the value of the (first) type parameter, and,
having done that, we then express the rest of the 
function type in terms of α. In more detail, here
are the elements of the whole function definition:

- def is the keyword for giving a definition
- id_poly is the name of the function being defined
- (α : Type) binds the name α to the first (type) argument 
- in this context, the rest of the function type is α → α 
- the | gives the pattern matching rule for this function
- the names α and v bind to the first and the second arguments
- => separates the pattern on the left from the return value on the right
- v, bound to the second argument, is the return value of this function
- the name α is unused after the => and so can be replaced by _ 
-/

-- And we can see that it works!
#eval (id_poly String) "Hello!"
#eval (id_poly Nat) 7
#eval (id_poly Bool) true



/-!
## Specialization by (partial) application 

For example, if α is Nat, the rest of the function 
is of type Nat → Nat. In the single pattern matching
rule, we bind v to the first unnamed argument, a Nat, 
and the function then returns the value of v. If α is 
String, v will be bound to a String given as a second
argument, and the function will return that value.  
-/

#check (id_poly)          -- generalized definition
#check (id_poly Nat)      -- specialization to Nat
#check (id_poly Bool)     -- specialization to Bool
#check (id_poly String)   -- specialization to String

/-!
We can specialize the generalized function to specific types
by applying it only to a first type argument. 
-/

def id_nat' := id_poly Nat        -- same as id_nat above
def id_string' := id_poly String  -- same as id_string above
def id_bool' := id_poly Bool      -- same as id_bool above

#eval id_nat' 7
#eval id_string' "Hello"
#eval id_bool' true

/-!
What we see here is an example of what, in programming, 
is called *parametric polymorphism*. We have one function
definition that can take arguments of many different types. 
Here the *types* of the second argument and return value 
are given by the *value* (a type!) of the first argument. 

Lean detects type errors in such expressions. For example,
if we pass Bool as the first argument but 7 as the second, 
Lean  will report an error. Let's try. 
-/

#check id_poly Bool 7   -- Lean can't convert 7 into a Bool

#check id_poly Bool true
#check id_poly Nat 7 
#check id_poly String "Hello"


/-!
## Implicit Arguments

You might have noticed that in principle Lean can always infer
the *type value* of the first argument to the id_poly function
from the *data value* passed as the second argument. For example,
if the second argument is "Hello!", the first argument just *has
to be* String. If the second argument is 7, the first has to be 
Nat. If the second is true, the first has to be Bool.

In these cases, you can ask Lean to silently fill in argument
values when it knows what they must be, so that you don't have 
to write them explicitly. To tell Lean you want it to infer the
value of the first *type* argument to id_poly, you specify it as 
an argument when defining the function not using (α : Type) but 
using curly braces instead: {α : Type}. Let's define the function 
again (with the name id_poly') to see this idea in action.
-/

def id_poly'' : {α : Type} → α → α   -- α is an implicit argument 
| _, v => v

/-!
Now we can write applications of id_poly' without giving the
first (*type*) argument explicitly. It's there, but we don't
have to write it. Instead, Lean infers what it's value must
be from context: specifically from the type of the value we
pass as the second argument. The resulting code is beautifully
simple and evidently polymorphic. It also eliminates possible
type mismatches between the first and second arguments, as the
type in question is inferred automatically from the value to 
be returned. 
-/

#eval id_poly'' 7          -- α = Nat, inferred!
#eval id_poly'' "Hello!"   -- α = String, inferred!
#eval id_poly'' true       -- α = Bool, inferred!

#eval id_poly'' Nat 7             -- error
#eval id_poly'' String "Hello!"   -- error
#eval id_poly'' Bool true         -- error

/-!
Sometimes we will have to give type arguments
explicitly, even when they're declared to be
implicit. In these cases, we disable implicit
argument inference, In Lean, by writing an @
before the given expression. Note that in the
following examples we once again can, and must,
give the type argument values explicitly. 
-/

#eval @id_poly'' Nat 7          -- α = Nat, inferred!
#eval @id_poly'' String "Hello!"   -- α = String, inferred!
#eval @id_poly'' Bool true       -- α = Bool, inferred!

/-!
## Extended Example: A polymorphic apply2 function

We'll now work up to defining a *polymorphic* function,
apply2, that takes as its arguments a function, f, 
and a value, a, and that returns the result of applying
f to a twice: that it, it returns the value of f (f a).

### A Natty Example

We'll define apply2_nat as a function that takes a 
function, f, and an argument, a, to that function 
as its arguments, and that then returns the result 
of applying the function f to the argument a twice.
That is, apply will return the value of f (f a).

As an example, if f is the function, Nat.succ, that 
returns *one more than* a given natural number a, the 
result of "applying f twice to 0" is 2. 

Let's write this apply2_nat function where the function
and its argument values are Natty. We define *apply2_nat*
that takes (1) a function, *f : Nat → Nat*, and (2) a 
second argument, *a : Nat*, and that returns a result 
of applying f twice to a: namely *f (f a)*, also a Nat. 
-/

-- This apply2 version is specialized for "Natty" values                         f         a
def apply2_nat : (Nat → Nat) → Nat → Nat
| f, a => f (f a)

/-!
Let's apply this function to some arguments to see 
what we get. First we need some specific function,
f, taking and returning a Nat. The Nat.succ function
will work. This is the *successor* function, which
returns 1 more than any natural number given as an
argument. 
-/

#check (Nat.succ)           -- Nat → Nat
#eval Nat.succ 0            -- 1
#eval apply2_nat Nat.succ 0 -- expect 2
#eval apply2_nat Nat.succ 3 -- expect 5

/-!
Yay, it seems to work. It gets more interesting when we
see that we can use *any* function of type Nat → Nat as
a first argument to this function.  Here are a few little
puzzles for you to complete by defining simple functions.

First, define a function, *double : Nat → Nat* that 
returns twice the argument to which it's applied. So for
example, *double 4* should reduce to *8*.
-/

def double : Nat → Nat
| n => 2 * n

#eval apply2_nat double 4     -- expect 16 (2 * (2 * 4))
#eval apply2_nat double 10    -- expect 40 (2 * (2 * 10))

/-!
Second, define a function, *square : Nat → Nat*, that 
reduces to its argument value squared. Then check to see
that apply2_nat works when you give square as the first
argument? For example squaring 5 gives 25, and squaring 25 
gives 625, so apply2_nat square 5 should reduce to 625. 
Write both the function definition and test cases for a 
few inputs, including 5. Give your answer here:

#A. define the *square* function here:
-/

-- here:

def square : Nat → Nat
| n => n^2

#eval square 4  -- expect 16

/-!
Write test cases for apply2_nat square for several values,
including 5, and use them to develop confidence that your
function definition appears to be working more generally.
-/

#eval apply2_nat square 1   -- expect 1
#eval apply2_nat square 2   -- expect 16
#eval apply2_nat square 3   -- expect 81
#eval apply2_nat square 4   -- expect 256


/-! 
### A Stringy Example

Now if you think about it, we should be able to
write an apply2 function that does the analogous
thing but with Stringy things. Given a function, f, 
from String to String, and an argument, a : String,
we can always compute *f (f a )*. 

Your new puzzle is to write apply2_string; then give
examples of applying this function to two different 
function arguments, and for each of those, to several
string argument values.

You can make up your own String → String functions.
For example, a function, exclaim : String → String,
applied to a string, s, could return (append s "!"). 
There is an infix notation: *s ++ "!"*. 
-/

def exclaim : String → String 
| s => s ++ "!"    

#eval exclaim "Hello"             -- apply it once
#eval exclaim (exclaim "Hello")   -- apply it twice

/-!
Now you can use this function, exclaim, as a first
argument to apply2_string. Defining this function 
is easy, as it's the same as apply2_nat except for
the type of objects being handled: String not Nat.
-/

def apply2_string : (String → String) → String → String
| f, a => f (f a)

#eval apply2_string exclaim "Hello" -- expect "Hello!!"

/-!
It works!
-/

/-!
## Generalizing the Type of Objects Handled

At this point it should be clear, by analogy
with earlier material, that we can generalize
from the specific Nat and String types, in the
previous examples, to write a version of apply2
that can handle objects of any type, α. The
trick, as usual, is to handle the variation in
object types by adding a type *parameter*.
-/

def apply2' : (α : Type) → (α → α) → α → α  
| _, f, a => f (f a)

/-
Let's explain this function in detail:

- def is the keyword for binding names to values
- apply2' is the name of our new function
- the type of the function is give after the :
- the function takes three arguments:
  - a type value, α, such as Nat or String
  - a function of type α → α, such as exclaim
  - a value of type α 
- next is rule for computing the result
  - first we match all three arguments
    - the type value (we don't have to name it)
    - the function (we name it f)
    - the argument (we name it a)
  - after the => is the expression for the result

We can now try it out to see that it works!
-/

#eval apply2' Nat Nat.succ 0         -- expect 2
#eval apply2' Nat double 1           -- expect 4
#eval apply2' Nat square 2           -- expect 16
#eval apply2' String exclaim "Hello" -- "Hello!!" 

/-!
## Type Inference and Implicit Arguments

As a final exercise in good notation, redefine
apply2 (calling it apply2') so that the first
argument, the type value, is implicit. Write the
definition so that Lean infers the value of α 
(the first, type, argument) from the values of 
the remaining arguments. When you get it right, 
the following test cases should work.
-/

-- Answer:

def apply2 : { α : Type } → (α → α) → α → α 
| _, f, a => f (f a)

-- Now the type arguments are implicit!
#eval apply2 Nat.succ 0   -- expect 2
#eval apply2 double 1     -- expect 4
#eval apply2 square 2     -- expect 16
#eval apply2 exclaim "Hello" -- Hello!!

/-!
This example is an important achievement. 
It exhibits the following fundamental concepts:
- every value has a type
- types are values too; their type is Type
- types parameters make definitions polymorphic
- type arguments can be implicit and inferred
- functions are values, too, and can be arguments

With all the work required to get to this point
now in hand, we're ready to introduce a new and
important concept in mathematics. 

Note: The concept is introduced as a homework
assignment, then reviewed in class. Once it's
done, this lecture then continues to completion.
-/ 

/-!
## Combining Functions Into New Functions

We can now highlight first great generalization 
of this course: a function, we call it *compose*,
that combines any two *compatible* functions, *g*
and *f*, into a new function, denoted (g ∘ f), and
pronounced *g after f*, where for any *compatible* 
argument, *a*, *(g ∘ f) a* is defined as *g (f a)*.

By *compatible* we mean that *a* is the input type
of *f*, and the *output* type of *f* is the *input*
type of *g*. When this is the case, we can provide
*a* as an input value to *f* and *(f a)* as an input
value to *g*. Drawing a diagram can be helpful. 
-/ 

/-!
### The apply2 function takes f and returns (f ∘ f).

The *apply2* function takes a function, *f : α → α*,
and an argument, *a : α*, and returns the result of
applying *f* to *a* twice. That is, evaluating *apply2 
f a* return the value of *f (f a)*. Ah ha! Given *f* 
and *a*, we now see that it applies *(f ∘ f)*, to *a*, 
as we've defined (f ∘ f)*, to be *(f (f a))*. 
-/

#eval apply2 double 5   -- (double (double 5)
                        -- (double ∘ double) 5


/-!
Now consider what happens if we leave out the argument 
(*5*). By partial evaluation, which you've now seen quite
a few times, the expression *(apply2 double)* returns a
*function* that then takes a next argument, such as 5, 
which it then doubles twice. 
-/

-- Assign (apply2 double) to a variable
def double_after_double := (apply2 double)

-- It works as expected
#eval double_after_double 0 -- expect 0 (double (double 0))
#eval double_after_double 1 -- expect 4 (double (double 1))
#eval double_after_double 5 -- expect 20(double (double 5))

/-!
Leaving the final argument to be provided later,
we see that (apply2 f) returns the funtion (f ∘ f).
-/

def square_after_square := apply2 square  -- square ∘ square
#eval square_after_square 5               -- expect 625

/-!
Furthermore, because we generalized *apply2* to
make it polymorphic, then for any type, α, it can be 
used to compose any function, *f : α → α* with itself.
-/

def exclaim_after_exclaim := apply2 exclaim -- exclaim ∘ exclaim
#eval exclaim_after_exclaim "I love this stuff"


/-!
Here, then, is the first big idea we can highlight:
Not only can you treat functions as "things"---that
you can "store" in variables, pass as arguments, and
get back as return results---but you now have a way
to *combine* functions into new functions.

Just as in your earlier math classes you've had ways
to combine numbers into new numbers using operators 
such as + and *. You can now combine functions into
new functions. And just as we talk about *addition* 
of numbers, we can now talk about the *composition*
of functions. You're now doing higher mathematics!
-/

/-!
Of course, apply2 is a pretty limited mechanism for
composing functions: it can only compose a function,
f, with itself, to return *(f ∘ f)*. As you saw on
the homework, we can also glue different functions
together, as long as they are compatible: the output
type of the first has to be the same as the input
type of the second. 

On the homework, we worked up to defined *glue_funs*
as a polymorphic function that, given any three types,
α, β, and γ, takes two functions, *g : β → γ* and *f :
α → β* along with an argument *a : α* and that returns 
*(g (f a))*, which we can now write as *(g ∘ f) a*.
-/ 

def glue_funs {α β γ : Type} :
  (β → γ) →
  (α → β) → 
   α → 
   γ 
| g, f, a => g (f a)

/-!
Moreover, if we leave off the third argument, *a*, to
*glue_funs*, we will get back exactly *(g ∘ f)*, which
of course is a function of, ..., well, of what type? 
Hint: What is the associativity of →? Try putting in
a pair of parentheses and then read the function type
of *glue_funs* in a slightly different way.
-/

#eval glue_funs square double 4

/-!
Self-test: What is the type of the function returned 
by *glue_funs* when applied to two function arguments? 
-/

/-!
Insight: glue_funs *is* a general function composition
operation! A better name for it is compose! We'll start
by calling it compose' and then make a final improvement.
-/

def compose' {α β γ : Type} :
  (β → γ) →
  (α → β) → 
   α → 
   γ 
| g, f, a => g (f a)


#eval 5%2 = 1

-- Here's an is_even function for Nat
def is_even : Nat → Bool
| k => k % 2 == 0

/-! 
Self-test: using *compose'*, define a function,
is_even_len' : String → Bool, that takes a string
and returns true if it's of even length and false 
otherwise.
-/

-- Answer here.

def is_even_len := compose' is_even String.length

#eval is_even_len "Love"
#eval is_even_len "Love!"
#eval is_even_len "Love!!"

/-!
## Function (aka lambda) expressions

Our code for *compose'* is a little more complex than
it needs to be. If all we're going to do is use it to
return functions, then in a sense we don't expect to
be getting a final argument value, *a*. Rather, the
normal use will be to apply it to just two function
arguments and get a function value back. We'll now see
how to write an expression for the function we want to 
return. Here it is.
-/

def compose {α β γ : Type} :
  (β → γ) → 
  (α → β) → 
  (α → γ)       
| g, f => (fun a => g (f a)) 


/-!
Read the expression, (fun a => g (f a)), as
*an unnamed function taking an argument, *a*,
and returning the value of *g (f a)*. You can
use an expression like this anywhere you need
to pass a function argument! 
-/

#eval compose (fun (n : Nat) => n%2 == 0) String.length "Love!"


/-!
Self test: Is the function type of compose really any
different than before?
-/


/-!
In Lean4, the *compose* function is *Function.compose*
and the infix notation, ∘, is a convenient way to apply
it.
-/

-- Combining functions as if they were numbers!
def is_even_len'' := (is_even ∘ String.length)


#eval is_even_len'' "Hello Higher Mathematics!"
#eval String.length "Hello Higher Mathematics!"


/-!
Celebrate! Being able to understand, write, apply a
generalized, polymorphic, function-returning function
such as compose is a major milestone in this class. 
You will use the concepts embedded in this beautiful
example for the rest of the semester.

def compose {α β γ : Type} :
  (β → γ) → 
  (α → β) → 
  (α → γ)       
| g, f => (fun a => g (f a)) 
-/
