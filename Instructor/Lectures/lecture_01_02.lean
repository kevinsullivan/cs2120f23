/-!
# Lectures 1 and 2: Types, Terms, Applications
-/

/-!

## Data Types
Here are some basic data types. The #check command
tells you that each of these is a Type.
-/

#check Bool
#check Nat 
#check String

/-!
Here are some terms (values) of these types. 
Every term in Lean has a type. 
#check tells you the type of any term.
-/

#check true               -- "literal" term of type Bool
#check false              -- another one
#check (and true false)   -- a function application term
#check (true && false)    -- using "infix" notation for "and"

/-!
Some terms of type Nat (for "natural number")
-/
#check 0
#check 1
#check 2


/-!
Some terms of type String
-/
#check "" 
#check "Logic is the best!"
#check (String.append "I love DM1" "!")
#check ("I love DM1" ++ "!")

/-!
## Function Types

Given any two types, let's call them α and β,
we can form a new type, written α → β. This is
the type of *functions* that take an argument 
of type α and that return (or *reduce to*) a 
value of type, β. Note, again, that (α → β) is 
a *type*.  
-/

/-!
A function that takes a Boolean argument and that 
returns a Boolean result has this type.
-/
#check Bool → Bool

/-!
Here's the type of function that takes two Boolean 
values as arguments and that and returns a Boolean 
value as a result. 
-/
#check Bool → Bool → Bool

/-!
Here's the type of function that takes a natural number 
and that returns a natural number. 
-/
#check Nat → Nat

/-!
This is the type of any function that takes two natural 
numbers and returns a natural number as a result. 
-/
#check Nat → Nat → Nat

/-!
A function of this type takes two string arguments and 
returns a string result.
-/
#check String → String → String

/-!
## Higher-order functions

In Lean and many other functional languages, a function that
takes two arguments (such as two strings) and that returns a
result (say another string), can be understood instead as a 
function that takes only *one* argument and that returns a 
function that takes the *second* argument and returns a final
result. 

To makes sense of this statement, we just need to know that 
*→* is *right-associative*. Whenever we write a chain of →, 
elements are implicitly grouped *from the right*. So the type 
we just saw, String → String → String, is exactly the same as
this type! 
-/
#check String → (String → String)

/-!
In general, a function that either returns a function as a
result or that takes a function as an argument is called a
higher-order function. A function that takes two arguments 
in a functional language such as Lean is thus a higher-order
function in that it really takes one argument and returns a
function that that takes the second argument and that returns
a final result. 
-/

/-!
Here's the type of any function that takes two arguments, the
first being a *function* (from String to String), the second
being a String, with the function finally returning a String
result. 
-/
#check (String → String) → String → String

/-!
As an example, a function of this type could take
as a first argument a function that takes any string
and adds a "!" to the end. The second argument could
be a string such as "Hello." And the function would
then apply the first argument (that "!" function) to 
the second argument, "Hello," and finally return the
string "Hello!".
-/

/-!
## Function Terms
Let's check the type types of some built-in terms of these 
function types.
-/
#check (not)            -- Boolean negation
#check (and)            -- Boolean and (&&)
#check (String.append)  -- Appends two strings
#check (Nat.succ)       -- Adds 1 to its argument  
#check (Nat.add)        -- Returns sum of two natural numbers

/-!
## Example of a higher-order function involving Strings

Consider, again, the function type, (String → String) → 
String → String. To repeat, a function of this type takes 
a function (that takes a String and returns a String), and 
a String, as its arguments, and returns a string as a result. 

Similarly a function of type String → (String → String)
can be understood either as a function that takes two
String arguments and returns a String, or as a function 
that takes one String and returns a function, of type 
String → String, that takes a second argument, before 
finally returning (reducing to) a String result. 

To make our ideas more concrete, let's analyze the String
append function to see how we can view it as higher-order
function: namely one that, when applied to *one* argument,
returns a function. This will be a function that has its
first argument *baked in* and that takes the second argument 
to append before returning the final result. 
-/

/-!
### Binding of variable names (identifiers) to values

To begin we introduce the idea of giving (or binding) a 
"variable" name (aka identifier, variable name) to a term. 
Here we bind the names, s1 and s2, to the terms (of type 
String), "Hello," and "Lean!" 
-/
def s1 := "Hello, "
def s2 := "Lean!"

/-!
The type of an identifier is the type of the term of
which it is bound.
-/

#check s1
#check s2


/-!
### Evaluating an identifier returns its value 
Evaluating a name yields the result of evaluating
the term to which it is bound.
-/
#eval s1                    -- "Hello, "
#eval s2                    -- "Lean!"
#eval (String.append s1 s2) -- "Hello, Lean!"


/-!
### Identifiers can be passed as arguments

We can use names to pass terms to functions,
as we just saw. Here it is again. 
-/
#eval String.append s1 s2

/-!
### Function *application* terms

Here we have a *function application term*, in
which the string append function is *applied* to
two arguments, s1 and s2. *Evaluating* a function 
application term *reduces* it to the value that 
the function computes given those arguments: 
here, to the string, "Hello, Lean!" 
-/

/-!
We can bind a name to the result of evaluating 
another expression, here a function application. 
-/
def s3 := String.append s1 s2
#check s3
#eval s3

/-!
### Viewing String.append as a higher-order function

Now recall the type of the String.append function.
We'd normally write it as String → String → String.
We understand this to be the type of function that
takes two string arguments and returns a result that
is also a string. 

The → operator is right associative, so this means 
that the type, String → String → String really means
String → (String → String). So append really takes 
*one* string as an argument and returns a function as 
a result: of type String → String. 

You can understand this point by seeing that function 
*application* is *left* associative! The following 
expressions should be, and are, equivalent.
-/

#eval String.append "Hello, " "Lean!"
#eval (String.append "Hello, ") "Lean!"

/-!
The second expression makes it clear what's really
going on: First the append function consumes "Hello, " 
and returns a *function* (without a name) that then 
consumes the second string, "Lean!" and returns the
final result, "Hello, Lean!" From now on, remember
that → ("arrow") is right associative and application
is left associative. 
-/

/-!
So what does the weird, unnamed intermediate function, 
(String.append "Hello, ") do? It appends "Hello, " and
whatever argument is receives: in this example, "Lean!",
and returns the final result. 

Putting all these ideas together, we should be able to 
apply append to one string and get ourselves a function 
(of type String → String), then bind a name to it, and
finally apply *that* function to another string argument! 
Yes, it actually works! Recall that s1 here is the string, 
"Hello, ".
-/
def f1 := String.append s1  -- "Hello, " is baked in to f1
#check (f1) -- f1 is a function of type String → String

/-!
Whoa, so f1 is a some function that takes just one
string as an argument and that returns "Hello, " (which 
is now "baked into" f1) and whatever second string value
s2 has. 
-/

#eval f1 "Lean!"    -- "Hello, Lean!"
#eval f1 "Mary!"    -- "Hello, Mary!"
#eval f1 "Joe!"     -- "Hello, Joe"

/-!
### Some more examples

All multi-argument functions are evaluated in the same
way in Lean: a function consumes its first argument and
returns a function that consumes its second argument and
returns a function that consumes its ... until you get
to the end of the chain of arguments at which point you
get a value: either a function or just a data value. For
example, the natural number *addition* function works in 
the same way.
-/

#eval Nat.add 2 5     -- 7

def add2 := Nat.add 2 -- a function that adds 2 to any Nat!
#eval add2 5          -- 7
#eval add2 10         -- 12
#eval add2 15         -- 17


/-!
### A self-test

To see if you've gotten it, consider these three
function types and answer the following questions.
-/
#check (String → String) → String   -- #1
#check String → (String → String)   -- #2
#check String → String → String     -- #3

/-!
Questions:
- Which two types are equivalent?
- Are #1 and #3 equivalent?
- Give English explanations of these function types
- Give some examples of functions of these types
-/

/-!
## Functions that take functions as arguments
Here's a function that takes two arguments, f and a, 
where f is a function taking a string and returns a
string, where a is a string, and where the result is
a string obtained by applying f to a. 
-/

def crazy (f : String → String) (a : String) : String := (f a) 

/-!
The type of this function is (String → String) → String → String.
If we call the first argument f and the second a, this function
then returns the result of applying f to a, written as (f a).
-/

#check (crazy)  -- (String → String) → String → String

/-!
Note that f1 as defined previously is a function that takes 
and returns a string, so f1 can be used as a first argument 
to crazy.
-/
#eval crazy f1 s1   -- Results in application of f1 to s1

/-!
### Self-test

Question: What is the type of the crazy function? Be
careful. How can you check if your answer is correct?
(Ok, yeah, I've already given you the answer.)
-/

/-!
### Function definition syntax in Lean

Important detail. The preceding definition of crazy uses
a Java-ish syntax to define the function type. It explains
that the first argument, f, is a function; the second, a, 
is a string; the return value is String; and the actual value 
returned is computed by applying f to a. 

There's another syntax in Lean that we can use to define
the same function. It's nice because the function type is
clearer in this notation.
-/

def crazy2 : (String → String) → String → String 
| f, a => (f a)

/-!
On the first line we declare the type of the crazy function
(here called crazy2). On the second line, to the left of the 
=> we bind names to the arguments of the function; and to
the right of the => we provide an expression that computes
the return value.
-/

/-!
### Self-test

What does the following expression evaluate to?
Answer before using Lean to compute it for you. Recall that
f1 is the function defined above that prepends "Hello, " to
its argument, and s2 is the string, "Lean!".
-/
#eval crazy2 f1 s2   

/-!
Good. The crazy2 function *applies* f1 to s2 yielding
the string, "Hello, Lean!" (again).
-/

/-!
## Defining our own (Boolean) functions

Let's now turn to the question of how to define our own
functions more generally. To provide motivation, we'll 
observe that Lean already provides definitions of the 
Boolean functions, *not*, *and*, and *or*, but not of 
*xor*, *nand*, or *nor*.

Here are the names of three built-in Boolean functions in
Lean. You might know them as !, &&, and || from your first
programming class. 
-/
#check (not)
#check (and)
#check (or)

/-!
We can confirm that these functions behave as expected
-/

#check not true         -- false
#check not false        -- true

#check and true true    -- true
#check and true false   -- false
#check and false true   -- false
#check and false false  -- false

#check or true true     -- true
#check or true false    -- true
#check or false true    -- true
#check or false false   -- false

/-!

### Not all Boolean functions are built-in

But xor, nor, and nand are not defined
-/

#check (xor)
#check (nand)
#check (nor)

/-!
### We can define functions ourselves

We can use the second style of function definition
(from above) to define the xor function. Recall that
(xor b1 b2) is true when either b1 or b2 is true but
it is false if both b1 and b2 are either true or false.

The first line of the following definition specifies
the name and type of the function we're defining.
Each of the next four lines defines how the function
behaves *by cases*. The first line, for example, says
if the first argument (to which xor is applied) is true
and the second argument is true then the xor function
will return true. The remaining lines give answers
for the other three cases of possible input pairs.  
-/

def xor : Bool -> Bool -> Bool
| true, true => false
| true, false => true
| false, true => true
| false, false => false

#eval xor true true     -- false
#eval xor true false    -- true
#eval xor false true    -- true
#eval xor false false   -- false 

/-!
### Self-tests

The nand function, short for "not and" gives exactly the
opposite of the answer that the *and* function gives in each case.
Self-test: Fill in the correct output values for this function.
-/

def nand : Bool -> Bool -> Bool
| true, true => _
| true, false => _
| false, true => _
| false, false => _

/-!
Complete this definition of the
nor (not or) function. It must return the
opposite of what the or function returns in
each case.
-/

def nor : Bool -> Bool -> Bool
:= _  -- delete this line and fill in the four cases

/-!
Suppose that a function takes two Boolean inputs and 
returns the "conjunction" (and) of the "negation" (not) 
of each argument. Is this the same function as one we
have already discussed? Which one? Use #eval if you 
need to to figure out its value for each combination
of input values. 
-/

def mystery : Bool -> Bool -> Bool
| b1, b2 => and (not b1) (not b2)

/-!
## Pattern matching

Now there's something perplexing going on here that 
needs explanation. Look at the definition of nand 
above and the definition of mystery here. In the first
(nand) example, the cases "match" possible values of 
the arguments, e.g., if the first is true and the 
second is false then ... The key observation is that
in this example, we're matching on *already defined* 
values. 

In the case of the mystery function, on the other 
hand, b1 and b2 are  *not defined* when they appear 
in the single rule for evaluating this function. Here
these names become bound to the function arguments so
that the result value can be expressed in terms of 
these *now named* argument values. 

In the following "application" for example, b1 is 
bound to true, b2 is bound to false, and in this 
context, the return result is defined to be the value
of the expression, *and (not b1) (not b2).* That in 
turn is *and false true*. And that expression then 
evaluates to false, which is the final result of
applying the mystery function to these arguments. 
-/

#eval mystery true false  -- false
--             b1   b2    (!b1 && !b2)

/-!
Remember, an undefined identifier matches with and
becomes bound to *any* value of the corresponding
argument to a function, while defined values match
only when the argument values are the same. It's a
little more complicated than that in general but 
not much.     
-/

/-!
Finally, a rule in Lean and similar proof assistants
is that functions have to have defined return values
for *all* possible combinations of their argument
values. If you leave out one or more cases, Lean will
give you an error message according.
-/

def error_example : Bool → Bool
| true => true
-- error, missing case for false

/-!
## Abstract and Concrete Syntax 

We've written application expressions, such as (Nat.add 1 2)
placing the function name before its arguments. This we can
call "abstract" syntax. In everyday paper-and-pencil mathematics
we usually shorten function names to symbols and when a function
takes two arguments, we put the symbol in between the arguments.

This is called "concrete" syntax: in particular using "infix"
notation. In some case, we write a concrete symbols before its
single argument, as in !true. That is called prefix notation. 
In some cases, we write a symbol after its single argument, as 
in 10! (ten factorial). That is called postfix notation. But
in all cases henceforth, you should understand that all such
expressions just represent applications of functions to given
arguments. Lean simply translates concrete syntax into abstract
syntax as a first step in evaluating such expressions. 
-/

#eval !true           -- prefix notation for not
#eval !false

#eval true && true    -- infix notation for and
#eval true && false
#eval false && true
#eval false && false

#eval true || true    -- infix notation for or
#eval true || false
#eval false || true
#eval false || false

#eval 0 + 0          -- infix notation for Nat.add

#eval "Hello" ++ ", Logic!" -- infix notation for String.append


/-!
## On the ambiguity of Natural language

Consider a warning sign on escalator: "Shoes must be worn; 
Dogs must be carried." How many different meanings could you
possibly attach to this command? Be creative. 

Now consider what the words "and" and "or" could mean, in English.
-- Example 1: they got married and they had a baby
-- Example 2: they had a baby and they got married
-- Example 3: You can have a candy or you can have a donut

The first two examples illustrate a meaning for "and" that 
involves some notion of temporal ordering. On the other hand,
in the propositional and predicate logic we'll study, "and" has
no such sense, but is true if and only if both arguments are
true. The formal definition of *and* as a function in the same
style as we defined *nand* makes its meaning unambiguous. 

In the third example, the dad almost certainly meant
that you can have one or the other but not both. In the
propositional and predicate logics we'll study, an *or* 
expression is true if either or both of its arguments 
are true. The *exclusive or* (xor) function, on the other
hand, is false when both inputs are true. Is *xor* what
the dad meant?  

Did the dad mean that you can have one or the other but 
not both *and that you must have at least one*? That'd be
xor, again. But he probably didn't really mean that she
*had to* have at least one sweet. What he really meant 
in all likelihood was that it'd be okay ("true") for her 
to have none, or one, or the other, but not both. What
logical function captures that idea precisely? Hint:
Compare the output of this function for each case with
the outputs of the *or* function. How do they relate?

The ambiguity of natural language is resolved by giving 
"formal," which is to say mathematical, definitions of 
terms such as *and* and *or*. And once our informal ideas 
are represented formally, we can then apply the amazing 
tools of logic and mathematics to reason about them very
precisely.  
-/

/-!
### Self-test

Self test: Which mathematical function captures the, most 
plausible interpretation of the snack policy that the Dad 
was communicating to his daughter? (You can have one or the
other or none but not both)?
-/
