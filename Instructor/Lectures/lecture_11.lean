/-
# Propositional Logic

UNDER CONSTRUCTION (REALLY)

We've now built enough machinery and intuition for basic
logic that not only we can introduce it informally, in the
manner you'd find in almost any textbook, but we can also
formalize it in Lean. Doing so has several major benefits,
including making the ideas precise and concise, while also
enabling *automated logical reasoning*. In this chapter
we'll do exactly that.
-/


/-!
## Formal Languages: Syntax and Semantics

Propositional logic is an example of a formal language
with a syntax and a semantics. A formal language is an
artificial (as opposed to natural) language that has a
mathematical definition. The *syntax* of such a language
specifies its set of well formed expressions (sometimes
called well formed formulae, or *wffs*). The semantics
provides a way to assign a *meaning* to each and every 
*wff*.

The language of arithmetic is a formal language. Its
*wffs* include the following:
- *1 + 113
- 10 = 11* 
- "x * y = 1"

On the other hand, the following strings of symbols
are not in the set of expressions defined by the syntax 
of arithmetic.
- *+ x +* 
- 1 >== 2
- Hello

The semantics of the language of arithmetic in turn
give us a way to assign meanings to the well formed
expressions. 
- In the first example, we interpret *+* as arithmetic addition, and the overall arithmetic expression then *means* 113. 
- In the second case, we interpret *=* as the equality relation, giving us a Boolean expression, the meaning of which in this case is *false*. 
- The third expression means either true or false depending on the meanings of the arithmetic variables, *x* and *y*. 

The third case is the most interesting because it
shows that the semantics of arithmentic is not just
a simple function from wwfs to meanings. We need an
additional piece of information in this case, which
we can call a *valuation*, or *interpretation*, of 
the variables. The meaning of *x * y = 1* is *true*
under the valuation *{x = 2, y = 1/2}*, for example,
but is false under the valuation *{x = 2, y = 1}.*

Speaking informally, the semantics of arithmetic is
thus a function that takes an expression and also a
valuation of the variables that might appear in it 
and that returns a meaning.
-/

/-!
## Propositinal Logic Informally

Propositional logic is among the simplest of useful
formal languages. You already know some version of
it from having learned how to read and write Boolean
expresions when Programming in Python, Java, or any
other ordinary programming language.

### Atomic Propositions

Propositional logic starts with the notion of an
*atomic proposition*. An atomic proposition, *P*, 
is a declarative statement that cannot be broken 
into smaller propositions, and for which it makes 
sense to ask *Is it true or not that P?*. Here are 
some examples of atomic propositions:
- It's raining
- The ground is wet
- x * y = 1

Because atomic propositions don't break up into smaller
elements, and to make it easier to read and write 
expressions, it's the usual practice to use variables,
sometimes called propositional letters, to stand for 
longer propositions. For example, we could define the 
following shorthands.
- a = "it's raining"
- b = "the ground is wet"
- c = "x * y = 1"

Here are some examples of propositions that are 
not atomic. Be sure you see that they are made up
of smaller propositions.
- If it's raining then the ground is wet
- a implies b (using propositional letters)
- x * y = 1 or x * y ≠ 1 (x and y are not propositional letters in this context, but refer to numbers)

Finally, here are some correct expressions
in English that are not propositions at all:
- Is Mary home?
- Get out!
- Please pass the jelly.

None of these expressions pass the simple "Is it true" test for being a proposition:
- Is it true or not that "Is Mary home?"          -- makes no sense
- Is it true or not that "Get out!"               -- makes no sense
- Is it true or not that "Please pass the jelly." -- makes no sense

### Inductively Defined Syntax

The syntax of propositional logic defines the set
of well formed formula (*expressions*), inductively. 
In other words, we can build larger expressions from
smaller ones. Here are the rules.

- If *a* is an atomic formula then *{a}* is an expression
- If *b* and *c* are expressions, then so are the following:
  - ¬b        -- not b
  - b ∧ c     -- b and c
  - b ∨ c     -- b or c
  - b ⇒ c     -- b implies c; if b then c
  - b ↔ c     -- b if and only if c; b and c are equivalent

That's it! Here then are some valid expressions in
propositional logic:
- {a}           -- it's raining
- {b}           -- the ground is wet
- ¬a            -- it's not raining
- a ⇒ b         -- if it's raining then the ground is wet
- a ∨ b         -- it's raining or the ground is wet
- (a ∧ b) ∨ ¬a  -- (raining and wet) or (not raining) 

Note: Most informal (English/natural language) 
definitions of propositional logic don't distinguish 
between atomic formula (represented by a propositional
variables, such as *a* and *b*) and *expressions* that
incorporate them ({a} and {b} in our notation). Rather, 
it's common just to say that if *a* is an atomic 
formula then it's also an expression. 

We distinguish *a* as an atomic variable from from *{a},* 
an (atomic) *expression*. This separation of variables
from single-variable *expressions* will enable us to 
define valuations as functions, from *variables* only
(not from all expressions) to (true/false) values. 

We'll then define the meaning of any *expression* as 
a separate function: that take *any* expression along
with a valuation of any variables it might contain and
that then returns its true or false meaning. Our formal 
specification will clarify this distinction. 

### Semantics

From here on out, we'll write atomic propositions using
single-letter variables such as *a, b*, and *c*. Now to
assign a meaning any possible *expression* we will have
to answer a few questions:
- What does each variables mean?
- What do the *connective* symbols mean?
- How is the meaning of an expression computed from the meaning of its parts?

#### Atomic Propositional Variables

First, we will assigning a true or false the meaning to 
each atomic propositional variable in an expression by way
of a valation. For example, if we only care about one such
variable, say *a*, then there are two possible valuations:
- { a ↦ true }
- { a ↦ false }

If two variables, *a* and *b* might appear in expressions,
then there are *four* interpretations.
- {a ↦ true, b ↦ true}
- {a ↦ true, b ↦ false}
- {a ↦ false, b ↦ true} 
- {a ↦ false, b ↦ false}

You should recognize these lists as the input sides of 
truth tables, with the output column determined by the
expression to be evaluated. Here's an example. See first
that the input (left) side lists variables, while the right
side lists values of expressions. Second, note that that
there are two interpretations for the one input variable,
*a*. 

|variable |expression |
| a       |   ¬{a}    |
|---------|-----------|
| true    |  false    |
| false   |  true     |

The output expression can be more complex, but the number
of interpretations is determined only by the number of
variables that have to be given values to determine the
value of the output expression.


|variable |   expression  |
| a       |   {a} ∨ ¬{a}  |
|---------|---------------|
| true    |      true     |
| false   |      true     |

Finally here's an example of a list of all interpretations,
and the corresponding values, for an expression employing
two propositional variables, *a* and *b*. The row give the
four possible interpretations of the two variables, on the 
left, while the right column gives the values of the logical
formula (expression) *under* each of these interpretations. 

| a      | b      |  {a} ∨ {b}  |
|--------|--------|-------------|
| true   | true   |     true    |
| true   | false  |     true    |
| false  | true   |     true    |
| false  | false  |     false   |

The main conclusions at this point are as follows. First,
a valuation assigns Boolean truth values to propositional
*variables*. Second, a truth table lists each possible 
valuation for a given set of variables. Third, the output 
column of a truth table specifies a logical *expression* 
and gives its truth value for each corresponding valuation.

A final observation is that a single row of a truth table
specifies a *function* from propositional variables to 
to Boolean (truth) values. We could for example write the
preceding truth table as follows:

| a      | b      |  {a} ∨ {b}  |
|--------|--------|-------------|
|        i₃       |     true    |
|        i₂       |     true    |
|        i₁       |     true    |
|        i₀       |     false   |

Here the *i* (for *interpretation* values are functions 
from variables to Bool. For example, *i₃(a) = true* and 
*i₃(b) = true*, while *i₂(a) = true* but *i₂(b) = false.*  

The values on the right (output) side of the truth table 
are then obtained by first applying the correspond *i*
functions to the *variables*, *a* and *b*, from which
the atomic propositional expresssions *{a}* and *{b}*
are constructed to obtain the meanings of these basic
expressions. Then the meaning of ∨ is applied to these
two values to obtain the final result. Here, as you'd
expect, the meaning of ∨ in propositional logic is the
Boolean *or* function.   

You are now ready to use you acquired logic knowledge
and skills formalizing concepts in Lean to define the
formal language of propositional logic, both syntax 
and semantics, within the logic of the Lean prover.
Indeed, one of the main use cases for Lean is exactly
to define *domain-specific languages* (DSLs). You're
now going formally specify your first working DSL!    
-/

/-!
## Propositional Logic Formalized and Automated
-/


/-!
### Syntax

#### Variables

We will represent propositional variables
as terms of a type called *var*. Each var
object will carry a single natural number
as a field value. Different variables will
have different natural number indices. You
can think of the terms of this type as *v₀,
v₁, ...* ad infinitum. We'll use tick marks
on this definition on the way to giving you
a better way to write such type definitions.
-/
inductive var' : Type
| mk (n : Nat)

def v₀' := var'.mk 0
def v₁' := var'.mk 1
def v₂' := var'.mk 2
def v₃' := var'.mk 3

/-!
Here's a new Lean syntactic feature. 
When you define a datatype with just 
a single constructor, you can use the
*structure* keyword. You then think of
the arguments as *fields*. 
-/
structure var : Type := 
(n: Nat)

/-!
The default constructor name for a 
structure type is *mk*. Here we 
construct four propositional logic
variables and give them nice names.
There's nothing special about using
subscripts in the names. It's just 
a *mathy* thing to do, and makes it
easier to write subsequent code/logic.
-/
def v₀ := var.mk 0
def v₁ := var.mk 1
def v₂ := var.mk 2
def v₃ := var.mk 3

/-!
Using the *structure* feature allows
you to use the field names as *getter*
functions, rather than having to write 
your own using pattern matching (as we
did with the *fst* and *snd* functions
for extracting the elements of a pair). 
You can use either function application
or dot notation. 
-/

#eval var.n v₂  -- application notation
open var        -- not a good idea 
#eval n v₂      -- but it works 
#eval v₂.n      -- dot notation

/-!
#### Connectives (Operators)
-/

inductive unary_op : Type
| not

inductive binary_op : Type
| and
| or

/-!
#### Expressions (Sentences) 
-/

inductive Expr : Type
| var_exp (v : var)
| un_exp (op : unary_op) (e : Expr)
| bin_exp (op : binary_op) (e1 e2 : Expr)

open Expr

-- Examples
def s0 := var_exp v₀
def s1 := var_exp v₁
def s2 := un_exp unary_op.not s0
def s3 := un_exp unary_op.not s1
def s4 := bin_exp binary_op.and s0 s3
def s5 := bin_exp binary_op.or s0 s3
def s6 := bin_exp binary_op.or s4 s5

/-!
#### Notations

Lean supports user-defined notations. The notation
system is pretty sophisticated. In general, though,
the idea is that you specify how you want to write
a term using your own notation, along with how that
notation should translate into ordinary Lean terms.
See https://lean-lang.org/lean4/doc/notation.html
for details.

In what follows, we define standard logical 
notations for each of the standard connectives,
or operators, of propositional logic. We start
with one non-standard notation for *lifting*
atomic propositional variables to *expressions*
in the usual language of propositional logic. 

After the first, each notation defines the 
*fixity* of the corresponding operator, which
is to say, where it's placed relative to its
arguments; the associativity of the infix
operators (all of them are "r" for "right")
associative in this case; and the operator
precedence, or binding strength, corresponding
to the same idea in arithmetic, which states
that * applies before +, for example. 
-/

notation "{"v"}" => var_exp v
prefix:max "¬" => un_exp unary_op.not 
infixr:35 " ∧ " => bin_exp binary_op.and  
infixr:30 " ∨ " => bin_exp binary_op.or 
infixr:25 " ⇒ " =>  bin_exp binary_op.imp
infixr:20 " ⇔ " => bin_exp binary_op.iff 

--  Now we have a "concrete" syntax for our language!
def e0 := {v₀}
def e1 := ¬e0
def e2 := e0 ∧ e1
def e3 := e0 ∨ e1
def e4 := (e2 ∧ e3) ∨ e0


/-!
### Semantics
-/

/-!
#### Interpretations/Valuations
-/
def Interp := var → Bool  -- interp is a type

-- examples
def all_true  : Interp := fun _ => true
def all_false : Interp := fun _ => false

/-!
Exercise: Define the *i₂* interpretation from above
as a function in Lean. It will help to give the name
*a* to *v₀* and *b* to *v₁*, then define a valuation
that gives each of these variables the specified value.
It doesn't matter what values you give all the other
variables. Just assign them a default value, such as
*false*.
-/

/-!
#### Operators

The meanings of the operators in proposition logic
are simply the corresponding Boolean functions. Some
of them are unary, taking just one Boolean argument
(e.g., *not*). Others are binary (and as *and*) and
so take two arguments. You can in fact define all
kinds of such functions. And _if_then_else operator
would take three Boolean arguments, and return a
result that uses the first to select on of the
following two values as the result. 

As above, we'll give *semantic* meanings to the 
*syntactic* connectives by defining functions from
the former to the *Boolean functions* that express
their desired meanings. 

-/
def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not

def eval_bin_op : binary_op → (Bool → Bool → Bool)
| binary_op.and => and
| binary_op.or => or

/-!
#### Expressions

And now for the coup de grace: We define a function that
gives each and every expression in the language of 
propositional logic a Boolean meaning. The function is
recursive: derive meanings for subexpressions, if any,
and then combine them using the right Boolean operators.
Atomic expressions are evaluated by interpreting the
variables they contain under an interpretation function
given to the expression evaluation function as an
argument.  
-/

def eval_expr : Expr → Interp → Bool 
| var_exp v, i => i v
| un_exp op e, i => (eval_un_op op) (eval_expr e i)
| bin_exp op e1 e2, i => (eval_bin_op op) (eval_expr e1 i) (eval_expr e2 i)

/-!
#### Demonstration
-/

#eval eval_expr e0 all_true
#eval eval_expr e1 all_true
#eval eval_expr e2 all_true
#eval eval_expr e3 all_true
#eval eval_expr e4 all_true

#eval eval_expr e0 all_false
#eval eval_expr e1 all_false
#eval eval_expr e2 all_false
#eval eval_expr e3 all_false
#eval eval_expr e4 all_false

/-!
## Conclusion

You have implemented the abstract syntax and 
standard concrete syntax for, and the semantics 
of, the formal language of propositional logic.
You have also automated the semantic evaluation
of variables, operators, and arbitrarily complex
expressions in propositional logic. That's cool! 
-/