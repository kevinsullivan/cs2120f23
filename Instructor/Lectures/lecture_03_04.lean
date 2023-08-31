/-!
Note: These notes are not yet complete. They
current extend the material presented at the
end of lecture 3, August 29, 2023. This section
will be extended as we go forward.

# Polymorphic functions

Consider the following three functions. 
Each one simply returns the single value 
given as its single argument. We call these 
function *identity functions*, for arguments
of types Nat, String, and Bool respectively.
-/

def id_nat : Nat → Nat
| n => n

def id_string : String → String
| n => n

def id_bool : Bool → Bool
| n => n

#eval id_nat 7
#eval id_string "Hello"
#eval id_bool true

/-!
## Functions varying in argument types

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
## Abstract type variabilities as parameters

If we bind a name, such as *T* or *α* ,to
a first *type* argument, then we can define
the type of the rest of this function to be
T → T, or α → α. In Lean it's conventional 
to use greek letter names for type values, 
so we will do that from now on.

Let's see how to write a single *polymorphic*
identity function that covers in one definition
an infinitude of identity functions, varying in
the types of their argument and return values. 
Then we'll analyze the definition to understand 
it in detail.
-/

def id_poly (α : Type) : α → α 
| v => v

/-!
Here are the elements of this definition:

- def is the keyword for giving a definition
- id_poly is the name of the function being defined
- (α : Type) binds the name α to the first argument to id_poly: a type value
- the : separates the named arguments from ones as yet not named
- the | is the one and only pattern matching rule for this function
- v matches the second argument *of type α* for whatever value α has
- => separates a pattern on the left from the return value on the righ
- v, bound to the second argument, is the return value of this function 

Now we can see that our single definition provides an identity
function for any type of value.
-/

#eval id_poly String "Hello!"
#eval id_poly Nat 7
#eval id_poly Bool true

/-!
### Parametric Polymorphism

What we're seeing here is called parametric polymorphism! We have 
one function definition that can take arguments of many different 
types. Here the *type* of it's second argument is given by the type
*value* (such as Bool or Nat or String) of its first argument. 

Lean easily detects type errors in such expressions. For example,
if we pass Bool as the first argument but 7 as the second, Lean 
will report an error. Let's try. 
-/

#check id_poly Bool 7   -- Lean says it can't convert 7 into a Bool

/-!
### Implicit Arguments

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

def id_poly' {α : Type} : α → α   -- α is now an implicit argument 
| v => v

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

#eval id_poly' 7
#eval id_poly' "Hello!"
#eval id_poly' true

/-!
## Polymorphic Higher Order Functions

This is getting cosmic!

## An apply2 function for Natty values

Let's start with some high-order but not
polymorphic functions. Each one takes a given
function, f, e.g., from Nat → Nat, along with a
second argument, a, that serves as an argument to 
the first argument function. The result will be of
that same type, e.g., Nat. In particular, the value 
our function returns must be the result of applying
f to a *twice*.

As an example, if f is the function that increments
a natural number a, the result of "applying it twice" 
to 0 is *increment (increment 0)*. The inner expression
reduces to 1, then the partially reduced expression,
increment 1, reduces to 2; and that's the result.

We'll start by writing a function, •apply_twice_nat*,
that takes a function, *f : Nat → Nat*, and a second
argument, *a : Nat*, and that returns a result of type
Nat computed by applying f to the result of applying f
to a. That's what we mean by *apply2): *f (f a)*. Here
is a *formal* definition.
-/

--                         f         a
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

#eval Nat.succ 0    -- 1
#eval Nat.succ 1    -- 2
#eval Nat.succ 2    -- 3

#check (Nat.succ)   -- Nat → Nat

/-!
In addition to such a function we need a natural 
number as a second argument to apply2_nat. The natural
number 0 will do just fine. Now that we have values of
the argument types we can apply the functionto them to
compute a result.

What do we expect as the result of apppling apply2_nat
to Nat.succ (of type Nat → Nat) and 0 (of type Nat)? We
expect it to return the result of applying that function
to the result of applying that function to 0. The result
of applying that function to 0 is 1. The result of then
applying that it to 1 is 2. That is what we expect as a 
result!
-/

#eval apply2_nat Nat.succ 0

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
| _ => _

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

/-!
Write test cases for apply2_nat square for several values,
including 5, and use them to develop confidence that your
function definition appears to be working more generally.
-/

-- here:

/-! 
### Generalizing from Nat to and type, α

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
applied to a string, s, could (append s "!"). There
is a notation for this: *s ++ "!"*. 

Now you can use this function, exclaimm as a first
argument to apply2_string. The result is a function
that is waiting for an argument, s, and that then
returns returns the result of applying the "baked 
in") function, f, to s, to compute (f s), and then 
applies f to that value, for the second time. The
result is the value of *f (f s))*.  

Show that you can write the programs analogous
to the corresponding ones for Natty things but
now for Stringy things, while writing demo and
test cases. Key idea: A test case defines some
value to be computed *and* an expected result.
The passing or failure of a test case reflects
the consistency of expected and compute value.

## Let's Go Poly!

At this point it should be clear, by analogy
with earlier material, that we can generalize
over the specific Nat and String types in the
previous examples to a general type: call it α!
Replace the _ here with the *rest of the type*
of the apply2 function, given that we alrady
have a specific type in hand, such as String
or Nat, to which we've bound α. You can now
use α to specify the rest of the type of the
function.  
-/

def apply2 (α : Type) : _
| f, a => f (f a)


#eval apply2 Nat Nat.succ 0   -- expect 2
#eval apply2 Nat double 1     -- expect 4
#eval apply2 Nat square 2     -- expect 16
#eval apply2                  -- expect "Hello!" 
  String 
  exclaim 
  "Hello" 

/-!
-/
## Type Inference