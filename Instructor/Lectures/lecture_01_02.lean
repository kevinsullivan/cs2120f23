/-
Here are some basic data types. The #check command
tells you that each of these is a Type.
-/

#check Bool
#check Nat 
#check String

/-
Here are some terms (values) of these types. 
Every term in Lean has a type. 
#check tells you the type of any term.
-/

#check true               -- "literal" term of type Bool
#check false              -- another one
#check (and true false)   -- a function application term
#check (true && false)    -- using "infix" notation for "and"

-- some terms of type Nat (for "natural number")
#check 0
#check 1
#check 2

-- some terms of type String
#check "" 
#check "Logic is the best!"
#check String.append "I love DM1" "!"
#check "I love DM1" ++ "!"

-- Some function types 

/-
A function that takes a Boolean argument and that returns
a Boolean result has this type.
-/
#check Bool → Bool

-- Takes two Booleans and returns a Boolean
#check Bool → Bool → Bool

-- Takes a natural number and returns a natural number
#check Nat → Nat

-- Takes two natural numbers and returns a natural number
#check Nat → Nat → Nat

-- Takes two string arguments and returns a string result
#check String → String → String

-- Takes a string and returns a function that takes a string and returns a string
#check String → (String → String)

-- Takes a function that takes and returns a string, and returns a string
#check (String → String) → String → String

/-
Some terms of these types
-/

#check (not)
#check (and)
#check (String.append)  
#check (Nat.succ) -- thus function adds 1 to its argument  
#check (Nat.add)  -- takes two nats and returns their sum
#check (String.append)  -- appends to strings


/-
What about that last example, (String → String) → String?
A function of this type takes a function (that takes and
returns a String) and a String as its arguments and returns 
a string as a result.
-/

/-
To begin we introduce the idea of giving (or binding) a 
name (aka identifier, variable name) to a term. Here we 
bind the names, s1 and s2, to the terms (of type String), 
"Hello," and "Lean!" 
-/

def s1 := "Hello, "
def s2 := "Lean!"


/- 
Evaluating a name yields the same result as evaluating
the term that it names.
-/
#eval s1


--We can use names to pass terms to functions
#eval String.append s1 s2


/-
We can bind a name to the result of evaluating 
another expression, here a function application. 
-/
def s3 := String.append s1 s2
#eval s3

/-
Now recall the type of the String.append function.
We'd normally write it as String → String → String.
We understand this to be the type of function that
takes two string arguments and returns a result that
is also a string. 

The → operator is right associative, so this really
means the type, String → (String → String). That is
the append function takes *one* string as an argument
and returns a function that takes the second string
and that finally returns the result string.

The following expressions should thus be, and are,
equivalent.
-/

#eval String.append "Hello, " "Lean!"
#eval (String.append "Hello, ") "Lean!"

/-
The second expression makes it clear what's really
going on when the first one is evaluated: First the
append function consumes "Hello, " and it then returns
a *function* (without a name at this point). This 
function then consumes the second string, "Lean!"
and returns "Hello, Lean!" What does the function,
(String.append "Hello, ") do? It returns "Hello, "
appended with whatever argument is receives -- in
this example, "Lean!"
-/

/-
That means that we *should* be able to apply append
to one string and get ourselves a function (of type
String → String), and then bind a name to it. And yes 
it actually works! Recall that s1 here is the string, 
"Hello, ".
-/
def f1 := String.append s1
#check (f1)      

/-
Whoa, so f1 is a some function that takes just one
string as an argument and that returns "Hello, " (which 
is now "baked into" f1) and whatever second string value
s2 has. 
-/

#eval f1 "Lean!"
#eval f1 "Mary!"
#eval f1 "Joe!"

/-
All multi-argument functions are evaluated in the same
way in Lean: a function consumes its first argument and
returns a function that consumes its second argument and
returns a function that consumes its ... until you get
to the end of the chain of arguments at which point you
get a value: either a function or just a data value. For
example, the natural number addition function works in 
the same way.
-/

#eval Nat.add 2 5

def add2 := Nat.add 2
#eval add2 5
#eval add2 10
#eval add2 15


/-
To see if you've gotten it, consider these three
function types and answer the following questions.
-/
#check (String → String) → String   -- #1
#check String → (String → String)   -- #2
#check String → String → String     -- #3

/-
Questions:
- Which two types are equivalent?
- Are #1 and #3 equivalent?
- Give English explanations of these function types
- Give some examples of functions of these types
-/

/-
Here's a function that takes two arguments, f and a, 
where f is a function taking a string and returning a
string, where a is a string, and where the result is
obtained by applying f to a. Note that f1 as defined
above is a function that takes and returns a string,
so f1 can be used as a valid first argument to crazy.
-/

def crazy (f : String → String) (a : String) : String := (f a) 
#eval crazy f1 s1

/-
Question: What is the type of the crazy function? Be
careful. 
-/

/-
Important detail. The preceding definition of crazy uses
a Java-ish syntax to define the function type. It explains
that the argument f is a function; a is a string; the type
of the return value is String; and the actual value returned
is computed by applying f to a. 

There's another syntax in Lean that we can use to define
the same function. It's nice because the function type is
clearer in this notation.
-/

def crazy2 : (String → String) → String → String 
| f, a => (f a)

/-
On the first line we state the type of the crazy function
(here called crazy2). On the second line we bind names to
the arguments of the function to the left of the =>, and to
the right of the => we provide an expression that computes
the return value.
-/

/-
Self test: What does the following expression evaluate to?
Answer before using Lean to compute it for you. Recall that
f1 is a function as defined above and s2 is the string, "Lean!".
-/
#eval crazy2 f1 s2    

/-
Let's now turn to the question of how to define our own
functions. To provide motivation, we'll observe that Lean
provides definitions of the Boolean functions, not, and, 
as well as or, but not of xor, nand, or nor.
-/

-- Terms (function)

#check (not)
#check (and)
#check (or)

-- We can confirm that these functions behave as expected

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

-- But xor, nor, and nand are not defined

#check (xor)
#check (nand)
#check (nor)

/-
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
#eval xor false false   -- true

/-
The nand function, short for "not and" gives exactly the
opposite of the answer that and function gives for each case.
Self-test: Fill in the correct output values for this function.
-/

def nand : Bool -> Bool -> Bool
| true, true => _
| true, false => _
| false, true => _
| false, false => _

/-
Self-test: Complete this definition of the
nor (not or) function. It must return the
opposite of what the or function returns in
each case.
-/

def nor : Bool -> Bool -> Bool
:= _  -- delete this line and fill in the four cases

/-
Self-test. Suppose that a function takes two
Boolean inputs and returns the "conjunction"
(and) of the "negation" (not) of each argument.
Which of the preceding results?
-/

def mystery : Bool -> Bool -> Bool
| b1, b2 => and (not b1) (not b2)

/-
Now there's something rather perplexing going on
here, that needs explanation. Look at the definition
of nand above and the definition of mystery here.
In the former (nand) the cases "match" possible
values of the arguments, e.g., if the first is
true and the second is false then ... The crucial
observation is that we *match* with already defined
values. 

In the case of the mystery function, b1 and b2 are 
not defined when they appear in the single case for
this function. Rather, they are names that are bound
to whatever arguments are provided so that the result
value can be expressed in terms of these names for the
arguments. In the following "application" for example,
b1 is bound to true, b2 is bound to false, and in 
this context, the result is and (not b1) (not b2).
That in turn is and false true. And that expression
finally evaluates to false, which is the result of
the overall application of the mystery function. 
-/

#eval mystery true false  -- false
--             b1   b2    (!b1 && !b2)


/-
We've written application expressions, such as (Nat.add 1 2)
placing the function name before its arguments. This we can
call "abstract" syntax. In everyday paper-and-pencil mathematics
we usually shorten function names to symbols and when a function
takes two arguments, we put the symbox in between the arguments.
This is called "concrete" syntax, in particular using "infix"
notation. In some case, we write a concrete symbols before its
single argument, as in !true. In some cases, we write a concrete
symbol after its single argument, as in 10! (ten factorial). But
in all cases henceforth we should understand that all such
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


/-
On the ambiguity of Natural language

Consider a warning sign on escalator: "Shoes must be worn; 
Dogs must be carried." How many different meanings could you
possible attach to this command? Be creative. 

Now consider what the words "and" and "or" could mean, in English.
-- Example 1: they got married and they had a baby
-- Example 2: they had a baby and they got married
-- Example 3: You can have a candy or you can have a donut

The first two examples illustrate a meaning for "and" that 
involves some notion of temporal ordering. On the other hand,
in the propositional and predicate logic we'll study, "and" has
no such sense, but is true if and only if both arguments are
true, *as formalized in the true table / definition of the 
and function. 

In the third example, the dad almost certainly meant
that you can have one or the other but not both. But in 
propositional and predicate logic, and or expression is
true if either or both of its arguments are true. Now did
the dad mean that you can have one or the other but not 
both and that you must have at least one? That would be
xor. However, he probably didn't really mean that she
*had to* have at least one sweet; so she'd only get the
nope-buzzer (false) if she answered that she wanted both,
while it'd be okay (true) if she asked for one, the other, 
or neither! 

The ambiguity of natural language is resolved by giving 
"formal," which is to say mathematical, definitions of 
such terms. And once our informal ideas are represented
formally, we can then apply the amazing tools of logic
and mathematics to really analyze and reason about them.  
-/

/-
Self test: Which mathematical function captures this, most 
plausible, interpretation of the snack policy that the Dad 
was communicating to his daughter? (You can have either one
or neither but not both)?
-/
