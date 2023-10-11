/-!

# Propositional Logic: A Satisfiability Solver

You will recall that we say that an expression (formula) in
propositional logic is *valid* if it evaluates to true under
all possible interpretations (Boolean values for the variables
that appear in it). It is *satisfiable* if there is at least 
one intepretation under which it is true. And *unsatisfiable*
if there's not even on interpretation that makes the expression
true.

We can understand these concepts clearly in terms of truth 
tables. As we've seen, each of the *input* columns represents
a variable that can appear in the expression being evaluated.
Each row up to but no including the final column represents 
one of the possible intepretations of the variables in the
column (a function mapping those variables to Boolean values).
The final column lists the values of the expression for each
of the intepretations.

As an example, consider the propositional logic expression, 
*X*. Here's the truth table for it. There's one input column, 
for the one variable. There are two interpretations (rows), 
that we can write as *{X ↦ T}* and *{X ↦ F}*. Finally, the
output column gives the truth value of the expression we're
evaluating, *X*, under each interpretation.

| v₀ | {v₀} |
|----|------|
|  T |   T  |
|  F |   F  |

From such a truth table it's trivial to determine whether a
formula is valid, satisfiable, or unsatisfiable. If all output
values are true, the formula is valid. It is also said to be 
a *tautology*. If at least one output is true, the formula 
is *satisfiable*, and the interpretations that make it true 
are said to be *models* of the formula, or *solutions*. And 
if all the outputs are false, the expression is *unsatisfiable* 
and so has no models/solutions. From the truth table here, we 
can easily see that *X* is not valid, but it is satisfiable, 
with *{X ↦ T}* as a model.

Exercise: Is the propositional logic expression, *X ∧ ¬X*
valid, satisfiable, or unsatisfiable? What are its models,
if any? 

| v₀ | {v₀} ∧ ¬{v₀} |
|----|--------------|
|  T |         _    |
|  F |         _    |

Exercise: Answer the same two questions for *X ∨ ¬X*. To
derive your answers, fill in and analyze the truth tables
for the two expressions. 


| v₀ | {v₀} ∨ ¬{v₀} |
|----|--------------|
|  T |         _    |
|  F |         _    |



## Chapter Plan

In the rest of this chapter we'll see how we can perhaps
automate the generation of truth tables for any expressions,
and thus have what we need to automatically determine its 
validity, satisfiability, or unsatisfiability, and models
if any.

The key element will be a function that, when given the number, 
*v,* of variables (columns) in a truth table, computes a list of 
all *2^v* interpretation functions. By evaluating the expression 
under each interpretation we'll get the list of output values 
in the truth table. We then just analyze that list to determine
whether all, some, or none of the output values is true. The 
models of the expression, if any, are the interpretations in
the rows that have true output values. 

The rest of this chapter is in several sections. First we 
include our specification of the syntax and semantics of 
propositional logic, without commentary. You can skip over
this section unless you need to review the definitions. 

Next, we define a function that when given the number of
variables, *v*, in an expression, computes the input side
of a truth table as a list of *2^v* rows, Each row is a 
distinct list of *v* Boolean values, as would appear in 
a paper-and-pencil truth table, and represents one of the
*2^v* possible interpretations of the variables that might
appear in the expression. The *i'th* entry in each row is
the value assigned by that row/interpretation to the *i'th* 
variable (column), with *i* ranging from *0* to *v-1*. 

Here's an example of the input side of a truth table for
an expression with two variables. Be sure you can explain
precisely what function, from variables to Boolean values,
each row represents. 

|    | v₀ | v₁ |
|----|----|----|
| i₀ |  F |  F |
| i₁ |  F |  T |
| i₂ |  T |  F |
| i₃ |  T |  T |

We can write the interpretation functions, corresponding
to the rows, as follows.

- i₀ = {v₀ ↦ F, v₁ ↦ F}
- i₁ = {v₀ ↦ F, v₁ ↦ T}
- i₂ = {v₀ ↦ T, v₁ ↦ F}
- i₃ = {v₀ ↦ T, v₁ ↦ T}

Next, the trickiest part, we define a function that takes 
as its input a row of Boolean values, *{b₀, ..., bᵥ₋₁}* and 
that returns the corresponding interpretation *function*, of 
type *Interp* (i.e., *var → Bool*). We can then use such a
function as an argument to our semantic function, *eval_expr*
to compute the truth value of a given expression under that
particular interpretation.

Each such interpretation function behaves as follows. For *i* 
in the range of *0* to *v-1*, given the *i'th* variable, *vᵢ* 
*(mk_var i)* as input, it returns *bᵢ*, the Boolean value
in the *i'th* position in the row of Boolean values, as its
output. Otherwise, for variables with *i* indices outside 
the range of interest, it just returns a default value, here 
*false*.

Next, we define a function that takes a list of all *2^v*
rows of a truth table, containing Boolean values, and convert
it into a list of interpretation functions, of type *Interp*.

Finally, from there, we can easily implement the functions that 
we really want: take any propositional logic expression and tell 
us if it's valid, satisfiable, or unsatisfiable.  We will also
want to be able to get a list of models (interpretations) for
any given expression. 
-/

/-!
## Propositional Logic Syntax and Semantics

Here we just repeat our specification of the syntax and semantics
of propositional logic. By know you are expected to understand the
concrete syntax of propositional logic, as defined here, and also
the purpose of the eval_expr semantic evaluator, that takes any
expression in this syntax along with an interpretation and returns
the truth value of the expression under the given interpretation of
its atomic propositional variables. 
-/

structure var : Type :=  (n: Nat)
inductive unary_op : Type | not
inductive binary_op : Type
| and
| or
| imp
inductive Expr : Type
| var_exp (v : var)
| un_exp (op : unary_op) (e : Expr)
| bin_exp (op : binary_op) (e1 e2 : Expr)
notation "{"v"}" => Expr.var_exp v
prefix:max "¬" => Expr.un_exp unary_op.not 
infixr:35 " ∧ " => Expr.bin_exp binary_op.and  
infixr:30 " ∨ " => Expr.bin_exp binary_op.or 
infixr:25 " ⇒ " =>  Expr.bin_exp binary_op.imp
infixr:20 " ⇔ " => Expr.bin_exp binary_op.iff 
def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not
def implies : Bool → Bool → Bool
| true, false => false
| _, _ => true
def eval_bin_op : binary_op → (Bool → Bool → Bool)
| binary_op.and => and
| binary_op.or => or
| binary_op.imp => implies
def Interp := var → Bool  
def eval_expr : Expr → Interp → Bool 
| (Expr.var_exp v),        i => i v
| (Expr.un_exp op e),      i => (eval_un_op op) (eval_expr e i)
| (Expr.bin_exp op e1 e2), i => (eval_bin_op op) (eval_expr e1 i) (eval_expr e2 i)


/-!
## Generating Truth Table Rows

Our first function will take as its input the number of
variables (columns), *v*, for which the input side of a 
truth table is to be generated. We will represent this
value as list of *2^v* rows, each of which is a list list 
of *v* Boolean values. Here, for example, is a table that
represents the input side of a truth table with three 
variables.

|   |  v₀  |  v₁  |  v₃  |
|---|------|------|------|
| 0 |  F   |  F   |  F   |
| 1 |  F   |  F   |  T   |
| 2 |  F   |  T   |  F   |
| 3 |  F   |  T   |  T   |
| 4 |  T   |  F   |  F   |
| 5 |  T   |  F   |  T   |
| 6 |  T   |  T   |  F   |
| 7 |  T   |  T   |  T   |

### Key Insight

Let's see what pattern emerges if we replace each true
and false value in this table with a corresponding binary
digit (bit), *0* for *false* and *1* for *true*. 


|      |  v₀  |  v₁  |  v₃  |
|------|------|------|------|
|  0   |  0   |  0   |  0   |
|  1   |  0   |  0   |  1   |
|  2   |  0   |  1   |  0   |
|  3   |  0   |  1   |  1   |
|  4   |  1   |  0   |  0   |
|  5   |  1   |  0   |  1   |
|  6   |  1   |  1   |  0   |
|  7   |  1   |  1   |  1   |

Do you see it? What's the relationship between
the row index and the sequence of binary digits
in each row? Think about it before reading on.
The answer: each row of binary digits represents
the corresponding row index in binary notation.
In other words, the rows of a truth table really
correspond directly to binary representations of
corresponding row *indices*, ranging from *0* to
*2^v - 1*. The upshot is that we can compute the
*r'th* row of the input side of a truth table
by doing nothing more than representing the row
*index* as a binary numeral, padded with zeros on
the left so that it's at least *v* digits wide,
and then replacing the binary digits with the
corresponding Boolean truth values.  

### Algorithm Design

These insights unlock an algorithm design strategy. 
First, define a function that, when given a number
of variables, *v*, and a row index, *r*, returns the
interpretation that associates the variables in the 
columns to the Boolean represented by the bit values 
in the binary representation of *r*. 

Once we have this function, it'll be straightforward
to take a number, *v*, of variables, *v*, and return 
a list of the *2^v* rows for the input side of a truth
table. 
-/

/-!
### Row Index to List of Binary Digits

We'll start by defining a function that converts a 
given natural number into its binary representation 
as a *list* of binary digits. We'll just the natural
numbers, *0* and *1* to represent binary digits.

The key observations here are (1) the rightmost bit
of a binary representation of a number is *0* if the
number is even and *1* if it's odd; (2) the rest of
the bits are shifted one place to the right, dropping
the rightmost bit, by division by 2. So what we do,
while bits remain is to repeatedly (1) compute the 
rightmost bit, (2) shift the rest of the bits right.

To illustrate, consider row number, *5*. The binary 
representation of *5* is *101*. From *right* to *left*
that's 1*2^0 + 0*2^1 + 1*2^2 = 1 + 0 + 4 = 5.* The 
number is odd so the rightmost bit is *1*, which is 
the remainder, 5 % 2 = 1*. Now recurse on *5* shifted
right by one bit, i.e., on *5/2* using natural number 
division. *5/2* is *2*, so the nexxt bit is *2 % 2 = 0.* 
Recursing on *2 / 2 = 1,* we find the next bit to be
*1 % 2 = 1.* Finally recurse on *1 / 2 = 0*. Zero is
one of the two base cases, so we're done. The result 
is the sequence of bits *[1, 0, 1]*. Exercise: Do it 
yourself for *6*. What's the second base case?   

Here's code. We abstract the computations of the right
bit and shift right operations as named functions. The
recursion, sadly, is not structural. 
-/

def right_bit (n : Nat) := n%2

def shift_right (n : Nat) := n/2

def nat_to_bin : Nat → List Nat
| 0     => [0]
| 1     => [1]
| n' + 2 =>
  have : (shift_right (n' + 2)) < (n' + 2) := sorry
  nat_to_bin (shift_right (n' + 2)) ++ [right_bit (n' + 2)]

/-!
Okay, you're wondering, what's that weird expression,
*have : (shift_right (n' + 2)) < (n' + 2) := sorry?*
To make a long story short, the recursion here is not 
structural. (Why?) That means that Lean won't be able 
to prove to itself that the argument to the recursion is
always decreasing, which is needed to prove that the
recursion always terminates. To avoid Lean giving an 
error, we have to give Lean an explicit proof that the
argument decreases on each recursive call. The mystery 
code tells Lean that we have such a proof. The *sorry*
says, *but we're not going to give it now; just trust 
us.* That's good enough for Lean not to complain. For
now, that's what you need to know. 
-/

#eval nat_to_bin 0  -- expect [0]
#eval nat_to_bin 1  -- expect [1]
#eval nat_to_bin 3  -- expect [1,1]
#eval nat_to_bin 5  -- expect [1,0,1]
#eval nat_to_bin 6  -- expect [1,1,0]

/-!
### Left Pad with Zeros

We represent *F* (false) values in our truth tables
as zeros. One remaining issue is that we have to make
each output list of binary digits *v* digits long, to
include *F* values (zeros) on the left. That is, we
need to left-pad our lists with zeros so that each 
list is at least *v* digits wide. 

To do so, we'll iteratively prepend zeros to a given 
list a number of times equal to *v* minus the length
of a given list. In Lean *v - l* is zero in all cases 
where *l ≥ v* (these are natural numbers), so there is
nothing left to do if the input list is long enough. 

It's a pretty easy recursion. We take this opportunity
to show how you can do a little top-down programming
by writing a top-level program that uses one that is
then provided as a sort of private subroutine. Learn
how to write code like this.

Finally, we note that it's very common to implement a
function as a non-recursive top-level program that in
turn calls a recursive subroutine, as illustrated here.
-/

def zero_pad : Nat → List Nat → List Nat
  | v, l => zero_pad_recursive (v - (l.length)) l
where zero_pad_recursive : Nat → List Nat → List Nat
  | 0, l => l
  | v'+1, l => zero_pad_recursive v' (0::l)

#eval zero_pad 3 [0]
#eval zero_pad 3 [1]
#eval zero_pad 3 [1,1]
#eval zero_pad 3 [0,1,1]
#eval zero_pad 3 [1,0,1]
#eval zero_pad 5 [1,0,1]

/-!
We can now write a function that will produce the
required list of binary digits for the (input part
of the) n'th row of a truth table with v variables
(columns).
-/

def mk_bit_row : (row: Nat) → (cols : Nat) → List Nat
| r, c => zero_pad c (nat_to_bin r)

#eval mk_bit_row 5 6  -- expect [0, 0, 0, 1, 0, 1]

/-!
### List of Bits to List of Bools

Next we need a function to convert a list of bits
(Nats) to a list of corresponding Bools. We will 
convert Nat zero to false, and any other Nat to 
true.
-/

-- Convert nat to bool where 0 ↦ false, ¬0 ↦ true
def bit_to_bool : Nat → Bool
| 0 => false
| _ => true

#eval bit_to_bool 0   -- expect false
#eval bit_to_bool 1   -- expect true

/-!
With this element conversion function we can now define 
our list conversion function. There are two cases. First,'
given an empty list of Nat we return an empty list of Bool. 
Second, we have a bit (Nat) at the head of a non-empty list,
in which case we return a list with that Nat converted to a
Bool at the head, and the conversion of t, the rest of the
list of Nats, into a list of Bools recursively.
-/

def bit_list_to_bool_list : List Nat → List Bool
| [] => []
| h::t => (bit_to_bool h) :: (bit_list_to_bool_list t)

-- expect [false, false, false, true, false, true]
#eval bit_list_to_bool_list [0, 0, 0, 1, 0, 1]

/-!
### Make the *r'th* Row of a Truth Table with *v* Variables
Now we can easily define a function that when given a truth
table row number and the number of variables (columns)
Given row and columns return list of Bools
-/

def mk_row_bools : (row : Nat) → (vars : Nat) → List Bool
| r, v => bit_list_to_bool_list (mk_bit_row r v)

 -- expect [false, false, false, true, false, true]
#eval mk_row_bools 5 6 

/-!
## List Bool → Interp

We now devise an algorithm to convert a list of Booleans,
[b₀, ..., bᵥ₋₁] into an interpretation. Denote *(mk_var i)*,
the *i'th* variable, as *vᵢ*. The idea then is to convert
the Boolean list into an interpretation function with the
following behavior: *{ v₀ ↦ b₀, ..., vᵥ₋₁, vᵢ → false for 
i ≥ v}*.

So how do we turn a list of values into a function from 
variables to Boolean values? In short, we start with some
interpretation, given a variable and a value for it, we
return a new function that's exactly the same as the given
one *except* when the variable argument is the same as the
variable for which we want to return a new value. In that
case, the new function returns the new value when it is
applied to the variable whose value is being overridden. 
The top-level algorithm will then iteratively override the
value of each variable according to the values in a given
row of a truth table. 

The hardest-to-understand function is *override*. Given an
interpretation, a variable whose value is to be overridden,
and a new value for that variable, we return a function that
when given any variable does a case analysis: if the variable
is *other than* the one being override, we just use the given
interpretation to compute and return a result, otherwise the
new function returns the specified new value.
-/

def override : Interp → var → Bool → Interp
| old_interp, var, new_val => 
  (λ v => if (v.n == var.n)     -- when applied to var
          then new_val          -- return new value
          else old_interp v)  -- else retur old value

def v₀ := var.mk 0
def v₁ := var.mk 1
def v₂ := var.mk 2

-- Demonstration

def all_false : Interp := λ _ => false

#eval all_false v₀  -- expect false
#eval all_false v₁  -- expect false
#eval all_false v₂  -- expect false


-- interp for [false, true, false], i.e., [0, 1, 0]
def interp2 := override all_false v₁ true

#eval interp2 v₀  -- expect false
#eval interp2 v₁  -- expect true
#eval interp2 v₂  -- expect false


-- interp for [false, true, true], i.e., [0, 1, 1]
def interp3 := override interp2 v₂ true

#eval interp3 v₀  -- expect false
#eval interp3 v₁  -- expect true
#eval interp3 v₂  -- expect true

/-!
To turn a list of Booleans into an interpretation,
we thus start with some base interpretation, such as
*all_false*, then iterate through the entries in the
list, repeatedly overriding the most recently computed
interpretation with the so-called *maplet, { vᵢ ↦ bᵢ }*. 
The end result will be the interpretation { v₀ ↦ b₀, ..., 
vᵥ₋₁ ↦ bᵥ₋₁, ...}, with all variables after *vᵥ₋₁* being 
mapped to the value given by the starting interpretation
(in practice, *all_false,* for us). 

Note: We introduce a new Lean programming mechanism: the
ability to define a function in terms of a "sub-routine"
that is subsequently defined in a *where* block. It is 
common to define functions this way when the top-level
function is non-recursive and takes or computes some
additional data that it then passes on to a recursive
function that does most of the work.  
-/

def bools_to_interp : List Bool → Interp
  | l => bools_to_interp_helper l.length l
where bools_to_interp_helper : (vars : Nat) → (vals : List Bool) → Interp
  | _, [] => all_false
  | vars, h::t =>
    let len := (h::t).length
    override (bools_to_interp_helper vars t) (var.mk (vars - len)) h 

-- Demonstration
def interp3' := bools_to_interp [false, true, true] 

#eval interp3' v₀  -- expect false
#eval interp3' v₁  -- expect true
#eval interp3' v₂  -- expect true


/-!
## From Number of Variables to List of Interpretations

Building in steps, we next define a function that takes a
number of variables and a row index and that returns the
corresponding interpretation function. It uses *mk_row_bools*
to create the right row of Boolean values then applies the
preceding *bools_to_interp* function to it to return the
corresponding interpretation function. 
-/
def mk_interp_vars_row : (vars: Nat) → (row: Nat) → Interp
| v, r => bools_to_interp (mk_row_bools r v)

def interp3'' :=  mk_interp_vars_row 3 3 -- vars=3, row=3

-- Demonstration
#eval interp3'' v₀  -- expect false
#eval interp3'' v₁  -- expect true
#eval interp3'' v₂  -- expect true


/-!
Finally, now, given nothing but a number of variables, we can
iteratively generate a list of all 2^v interpretations. We use
the same style of function definition above, where the top-level
program computes *2^v* from *v* and then passes *2^v* (the number
of interpretations/rows to generate, along with *v*, the number 
of variables, to a recursive function that does most of the work.
-/
def mk_interps (vars : Nat) : List Interp := 
  mk_interps_helper (2^vars) vars
where mk_interps_helper : (rows : Nat) → (vars : Nat) → List Interp
  | 0, _         => []
  | (n' + 1), v  => (mk_interp_vars_row v n')::mk_interps_helper n' v

/-
Generate list of 8 interpretations for three variables
-/
def interps3 := mk_interps 3

#reduce interps3.length   -- expect 8

/-!
## From List Interp and Expr to List Output Bool Values
Now how about a function that takes a list of interpretations and
an expresssion and that produces a list of output values? 
-/

def eval_expr_interps : List Interp → Expr → List Bool
| [], _ => []
--| h::t, e => (eval_expr e h)::eval_expr_interps t e
| h::t, e => eval_expr_interps t e ++ [eval_expr e h]

/-!
The change in the preceding algorithm puts the list of output
values in the right order with respect to our *enumeration* of
interpretations.
-/

-- Demonstration ]
#reduce eval_expr_interps (mk_interps 2) ({v₀} ∧ {v₁})  -- [F,F,F,T]
#reduce eval_expr_interps (mk_interps 2) ({v₀} ∨ {v₁})  -- [F,T,T,T]

/-!

## From Expr to Number of Variables (Highest Variable Index)

But our interface isn't yet ideal. We're providing an expression as 
an argument, and from it we should be able to figure out how many 
variables are involved. In other words, we shouldn't have to provide 
a list of interpretations as a separate (and here the first) argument.
The observation that leads to a solution is that we can analyze any
expression to determine the highest index of any variable appearing
in it. If we add 1 to that index, we'll have the number of variables
in the expression and thus the number of columns in the truth table.
We can then use mk_interps with that number as an argument to create
the list of interpretations, corresponding to truth table rows, that
ne need to pass to eval_expr_interps to get the list of outputs values.
-/

def highest_variable_index : Expr → Nat
| Expr.var_exp (var.mk i) => i
| Expr.un_exp _ e => highest_variable_index e
| Expr.bin_exp _ e1 e2 => max (highest_variable_index e1) (highest_variable_index e2)

#eval highest_variable_index {v₀}
#eval highest_variable_index ({v₀} ∧ {v₂})

/-!
## Major Result: Expr → List Bool, One For Each Interpretation

Here's a really important function. Given an expression in propositional
logic (using our syntax) it returns the list of outputs values under each
of the possible interpretations of the variables (thus atomic expressions)
in the given expression.
-/

def truth_table_outputs : Expr → List Bool
| e =>  eval_expr_interps (mk_interps (highest_variable_index e + 1)) e

/-!
Demonstration/Tests: Confirm that actual results are as expected by
writing out the truth tables on paper. Note that in the second case,
with the highest variable index being 2 (Z is var.mk 2), we have *3* 
variables/columns, thus 8 rows, and thus a list of 8 output values. 
-/

/-!
Let's give nicer names to three atomic propositions (i.e., variable
expressions).
-/
def X := {v₀}
def Y := {v₁}
def Z := {v₂}


/-!
Now we can produce lists of outputs under all interpretations of variables
from index 0 to the highest index of any variable appearing in the given
expression. Confirm that the results are expected by writing out the
truth tables on paper, computing the expected outputs, and checking them
against what we compute here.
-/
#reduce truth_table_outputs (X ∧ Y)
#reduce truth_table_outputs (X ∨ Z)

-- Write the truth tables on paper then check here
#reduce truth_table_outputs ((X ∧ Y) ∨ (X ∧ Z))
#reduce truth_table_outputs ((X ∨ Y) ∧ (X ∨ Z))

-- Study expression and predict outputs before looking.
-- What names would you give to these particular propositions?
#reduce truth_table_outputs ((¬(X ∧ Y) ⇒ (¬X ∨ ¬Y)))
#reduce truth_table_outputs (((¬X ∨ ¬Y) ⇒ ¬(X ∧ Y)))
#reduce truth_table_outputs ((¬(X ∨ Y ) ⇒ (¬X ∧ ¬ Y)))
#reduce truth_table_outputs (((¬X ∧ ¬ Y) ⇒ ¬(X ∨ Y )))


/-!
## HOMEWORK PART 1:

Write three functions
- sat : Expr → Bool
- unsat: Expr → Bool
- valid: Expr → Bool

Given any expression, *e*, in propositional logic, the first returns true
if *e* is sastisfiable, otherwise false. The second returns true if *e* is
unsatisfiable, otherwise false. The third returns true if *e* is valid, and
otherwise returns false. You can write helper functions if/as needed. Write
short comments to explain what each of your functions does. Write a few test
cases to demonstrate your results.
-/

def reduce_and : List Bool → Bool
| [] => true
| h::t => and h (reduce_and t)

def reduce_or : List Bool → Bool
| [] => false
| h::t => or h (reduce_or t)

def is_valid : Expr → Bool := reduce_and ∘ truth_table_outputs
def is_sat : Expr → Bool := reduce_or ∘ truth_table_outputs
def is_unsat : Expr → Bool := not ∘ reduce_or ∘ truth_table_outputs

-- a few tests
#eval is_valid (X)                      -- expect false
#eval is_sat (X)                        -- exect true
#eval is_sat (X ∧ ¬X)                   -- expect false
#eval is_unsat (X ∧ ¬X)                 -- expect true
#eval is_valid (X ∨ ¬X)                 -- expect true
#eval is_valid ((¬(X ∧ Y) ⇒ (¬X ∨ ¬Y))) -- expect true

-- Test cases



