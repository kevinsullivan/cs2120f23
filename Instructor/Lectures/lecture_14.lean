/-!
# Model Finders and Counterexample Generators

The main topic of this chapter is model and 
counterexample generation: given a proposition
in propositional logic, find models if there are
any, and similarly find counterexamples if there
are any. 

We'll begin by generalizing some patterns we've
been seeing in functions that handle lists. The
first section introduces and illustrates the use
of List map, foldr, and filter functions. 

Second, we'll see that with these functions in 
hand and a better understanding of recursion, we 
can improve our propositional logic satisfiability
checking functions.

Finally, we will introduce the concept of a model 
finder for expressions in propositional logic, also
known as a *SAT solver*, and see how that idea can
also provide a way to generate counterexamples to
propositions that are not always true.

## Higher-Order Functions On Lists

### List.map

The *List.map* function, converts a list of α terms,
into a list of corresponding β values by applying a
given function, *f : α → β*, to each α in turn. E.g.,
*map (λ (s : String) => s.length) ["Hello", "Lean"]* 
returns *[5, 4]*.

Here's the type of List.map in the Lean libraries.
-/

#check @List.map

#eval List.map (λ n => n + 1) [0,1,2,3,4]
#eval List.map String.length ["I", "Love", "Logic!"]


/-!
### List.foldr
-/

/-!
The *foldr* function converts a binary operation along with
its identity element into a generalized n-ary operation that
takes any number of arguments, in a list. As an example, our
*reduce_or* function, taking a list of Bools and reducing it
to just one, indicating whether the list has at least one true
value, is simply an n-ary extension of *or*. Applying such an
n-ary operation on no arguments (an empty list) simply returns
the identity element (base case value).  
-/


#check @List.foldr 

#eval List.foldr Nat.add 0 [1,2,3,4,5]  -- expect 15
#eval List.foldr Nat.mul 0 [1,2,3,4,5]  -- expect 120, oops!
#eval List.foldr Nat.mul 1 [1,2,3,4,5]  -- expect 120, ah!


/-!
### List.filter
-/

/-!
The *List.filter* function takes a list, *l* of α values, and an α → Bool 
predicate function that indicates whether a given α value has a particular
property, and returns the sublist of α values in l that have property, *p*.
-/

#check @List.filter

#eval List.filter (λ (n : Nat) => n%2 == 0) [0,1,2,3,4,5,6,7]

/-!
## Propositional Logic: The Next Generation

Here again is our definition of the syntax and semantics
of propositional logic, now supporting all the connectives,
including ⇔. There's little additional information here to
review, so you may skim this section quickly.
-/


/-!
### Syntax
-/

structure var : Type :=  (n: Nat)

inductive unary_op : Type | not
inductive binary_op : Type
| and
| or
| imp
| iff

inductive Expr : Type
| true_exp 
| false_exp 
| var_exp (v : var)
| un_exp (op : unary_op) (e : Expr)
| bin_exp (op : binary_op) (e1 e2 : Expr)

notation "{"v"}" => Expr.var_exp v
prefix:max "¬" => Expr.un_exp unary_op.not 
infixr:35 " ∧ " => Expr.bin_exp binary_op.and  
infixr:30 " ∨ " => Expr.bin_exp binary_op.or 
infixr:25 " ⇒ " =>  Expr.bin_exp binary_op.imp
infixr:20 " ⇔ " => Expr.bin_exp binary_op.iff 
notation " ⊤ " => Expr.top_exp
notation " ⊥ " => Expr.bot_exp

/-!
### Semantics
-/

def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not

def implies : Bool → Bool → Bool
| true, false => false
| _, _ => true

def iff : Bool → Bool → Bool
| true, true => true
| false, false => true
| _, _ => false

def eval_bin_op : binary_op → (Bool → Bool → Bool)
| binary_op.and => and
| binary_op.or => or
| binary_op.imp => implies
| binary_op.iff => iff

def Interp := var → Bool 

-- main semantic evaluation function
def eval_expr : Expr → Interp → Bool 
| Expr.true_exp,           _ => true
| Expr.false_exp,          _ => false
| (Expr.var_exp v),        i => i v
| (Expr.un_exp op e),      i => (eval_un_op op) (eval_expr e i)
| (Expr.bin_exp op e1 e2), i => (eval_bin_op op) (eval_expr e1 i) (eval_expr e2 i)



/-!
## Satisfiability Properties

Next we present an improved version of or code for checking of 
expressions for validity, satisfiability, and unsatisfiability. 

One significant enhancement, suggested by Mikhail, is replacement
of our rather ponderous approach to generating the input sides of 
truth tables with a single recursive function. We also use our new
map, filter, and reduce functions to replace numerous specialized
instances. 

### Truth Table Input Rows 

We had previousl developed an explanatory but ponderous approach to
generating a list of of all lists of boolean input rows. The idea was
to treat the each (input) row as a binary expansion of the row index
(a lit of bit), convert bits to bools, and add padding on the left. 
Mikhail noticed that we could replace it all with a single recursive
function. 

Exercise: Study this function definition until you understand fully
how it works. Along the way, use it to generate a few outputs then
inspect them to be sure you know what the function does. Figure out 
the recursion works to the point you're confident you could write the
code yourself. To test yourself, erase the implementation then write
it again.
-/

-- Mikhail
def make_bool_lists: Nat → List (List Bool)
| 0 => [[]]
| n' + 1 =>  (List.map (fun L => false::L) (make_bool_lists n')) ++ 
             (List.map (fun L => true::L) (make_bool_lists n'))
-- REVIEW

#eval make_bool_lists 0
#eval make_bool_lists 1
#eval make_bool_lists 2
#eval make_bool_lists 3

/-!
#### Bool List to/from Interpretation Function 

Given a list of *n* Boolean values, [b₀, ..., bₙ₋₁], we have to
be able to turn it into an *interpretation* function, so that we
can evaluate expressions with that interpretation using eval_expr.
The resulting function will be { v₀ ↦ b₀, ..., vₙ₋₁ ↦ bₙ₋₁}, where
each vᵢ means (var.mk i).

Our approach will be to start with a given interpretation (such
as the *all false* interpretation) and then for each *bᵢ* in the
list of Booleans, we will iteratively *override* the function so 
that when it's used to evaluate the value of *vᵢ* it will return
*bᵢ*.
-/

-- Function override
def override : Interp → var → Bool → Interp
| old_interp, var, new_val => 
  (λ v => if (v.n == var.n)     -- when applied to var
          then new_val          -- return new value
          else old_interp v)  -- else retur old value

-- Bool list to interpretation function
-- Uses list length as number of variables to associate with bools
def bool_list_to_interp : List Bool → Interp
  | l => bools_to_interp_helper l.length l
where bools_to_interp_helper : (vars : Nat) → (vals : List Bool) → Interp
  | _, [] => (λ _ => false)
  | vars, h::t =>
    let len := (h::t).length
    -- override recursively computed interp mapping variable to head bool
    override (bools_to_interp_helper vars t) (var.mk (vars - len)) h 

/-!
To think about: smells like some kind of fold. Iteratively combine
bool at head of list with given interpretation by overriding at with
the h
ead value for the *which?* variable
-/


/-!
In addition to converting Boolean lists to interpretations it
will also be useful to turn interpretations back into Boolean
lists, where the length of each list is typically fixed at a
specified number of variables (all variables beyond a certain
point being irrelevant to a given expression).
-/

-- From number of variables, interpretation, to list of Bools
def interp_to_list_bool : (num_vars : Nat) → Interp →  List Bool
| 0, _ => []
| (n' + 1) , i => interp_to_list_bool n' i ++ [(i (var.mk n'))]

-- From number of variables, list of interpretations, to list of Bool lists
def interps_to_list_bool_lists : Nat → List Interp → List (List Bool) 
| vars, is => List.map (interp_to_list_bool vars) is

/-!
#### Maximum Variable Index in Expression

We will consider the number of variables to include in a truth
table for a given expression to be the one plus the zero-based 
index of the highest-indexed variable in any given expression.
For example, if an expression uses only *v₉* explicitly we will
consider it to use all ten variables, *v₀* to *v₉* inclusive.
-/

def max_variable_index : Expr → Nat
  | Expr.true_exp => 0
  | Expr.false_exp => 0
  | Expr.var_exp (var.mk i) => i
  | Expr.un_exp _ e => max_variable_index e
  | Expr.bin_exp _ e1 e2 => max (max_variable_index e1) (max_variable_index e2) 


/-!
#### Number of Variables in Expression

We take the number of variables in an expression to be the index
of the highest-indexed variable in the expression, plus one to
account for the usual zero-based indexing.
-/

def num_vars : Expr → Nat := λ e => max_variable_index e + 1                    

/-!
#### From Expression to List of Interpretations

Given an expression, we compute the number, *n*, of variables it
uses then we generate a list of all *2^n* interpretation functions
for it. Note that we just eliminate a whole raft of ponderous code 
with a single clever recursive function, thanks to Mikhail.  
 
-/
-- Number of variables to interpretations list using Mikhail's code
def mk_interps_vars : Nat → List Interp
| n => List.map bool_list_to_interp (make_bool_lists n) 

-- From expression to a list of interpretations for it
def mk_interps_expr : Expr → List Interp
| e => mk_interps_vars (num_vars e)

/-!
#### Truth Table Outputs

Exercise: Replace the following definition of truth_table_outputs
with a single line of code using List.map. The resulting list of
Boolean values should reflect the values of the given expression
under each interpretation in the list of interpretations. You will
use map to convert a list of interpretations (for e) into a list of
Boolean values. 
-/ 

-- The column of truth table outputs for e
def truth_table_outputs' : Expr → List Bool
| e =>  eval_expr_over_interps e (mk_interps_vars (num_vars e))
where eval_expr_over_interps : Expr → List Interp → List Bool
| _, [] => []
| e, h::t => eval_expr_over_interps e t ++ [eval_expr e h]

-- REVIEW

def truth_table_outputs : Expr → List Bool
| e => List.map (eval_expr e) (mk_interps_vars (num_vars e))



-- | e =>  eval_expr_over_interps e (mk_interps_vars (num_vars e))
-- where eval_expr_over_interps : Expr → List Interp → List Bool
-- | _, [] => []
-- | e, h::t => eval_expr_over_interps e t ++ [eval_expr e h]


/-!
#### n-ary And and Or functions
-/

def reduce_or := List.foldr or false
def reduce_and := List.foldr and true


/-!
#### Satisfiability-Related Properties of Expressions

Finally we can define the API we want to provide for checking
arbitrary propositional logic expressions for their satisfiability
properties: for being satisfiable, valid, or unsatisfiable. 
-/

def is_sat (e : Expr) : Bool := reduce_or (truth_table_outputs e)
def is_valid (e : Expr) : Bool := reduce_and (truth_table_outputs e)
def is_unsat (e : Expr) : Bool := not (is_sat e)


/-!
## Models and Counterexamples

We now turn to the third and last major topic in this chapter.
Given a propositional logic expression, *e*, a model finder finds
a model of *e* if there is one. It returns either a model of e if 
there is one or a signal that there isn't one. 

To return either a model if there is one or a signal that there
isn't one, we could use a sum type: either a model on the left or 
Unit.unit on the right to signal that there is no model.
-/

def SomeInterpOrNone := Interp ⊕ Unit   -- NB: this is a *type*

/-!
A better solution is to use the standard polymorphic Option type.
Its two constructors are *some α* and *none*. The first is used 
to construct an option carrying a value, (a : α). The second is
used (in lieu of *Sum.inr Unit.unit*) to indicate that there's no
value to provide.
-/

def o1 := Option.some true
def o2 := @Option.none Bool -- need to make type argument explicit

/-!
### Model Finder
-/

/-!
Here's the main API for our model finder. Given an expression, *e*,
return *some m*, *m* a model of *e* if there is one, or *none* if not. 
-/
#check @Option

def find_model : Expr → Option Interp
| e =>
  let interps := mk_interps_expr e
  find_model_helper interps e
where find_model_helper : List Interp → Expr → Option Interp
| [], _ => none
| h::t, e => if (eval_expr e h) then some h else find_model_helper t e

-- REVIEW

-- Utility: convert a "Option model" into a list of Bools, empty for none 
def some_model_or_none_to_bools : SomeInterpOrNone → (num_vars : Nat) → List Bool
| Sum.inl i, n => interp_to_list_bool n i
| Sum.inr _, _ => []


/-!
### Model Enumerator
-/

/-!
The main API of our model enumeration section is
the function, *find_models*, that takes an expression,
e,, and returns a list of all models of e. It does so
by generating an exhaustive list of all interpretations
then filtering them to save those that make *e* true.
-/

def find_models (e : Expr) := 
  List.filter                 -- filter on 
    (λ i => eval_expr e i)    -- i makes e true
    (mk_interps_expr e)       -- over all interps


-- Render models of e : Expr as List of Bool Lists (num_vars e long) 
def find_models_bool : Expr → List (List Bool)
| e =>  interps_to_list_bool_lists (num_vars e) (find_models e)

/-!
### Model Counter

A model counter takes an expression and tells you how many models
it has. From a list of all models, it's obviously easy to derive
the number of models: it's just the length of the list. Note that
we use function composition to define our model counting function.
-/

def count_models := List.length ∘ find_models

/-!
### Counter-Example Generator

More interesting, and oft used, is *counter-example finding*. When 
we say we want to *disprove* a proposition, mean is that we want to 
show that it's not *valid*: that there's at least one interpretation
that makes the proposition is false. If that is so, then it makes the
negation of the proposition true. Counterexamples, if there are any,
are models of the negation of a propositio; and we now know how to
find such models using our model finder. Defining a counter-example
finder is thus trivial. 
-/

def find_counterexamples (e : Expr) := find_models (¬e)

def find_counterexamples_bool : Expr → List (List Bool)
| e =>  interps_to_list_bool_lists (num_vars e) (find_counterexamples e)


/-!
## Tests and Demonstrations
-/

def X := {var.mk 0}
def Y := {var.mk 1}
def Z := {var.mk 2}

#eval truth_table_outputs (X ∧ Y)
#eval List.foldr or false (truth_table_outputs (X ∧ Y))
#eval List.foldr and true (truth_table_outputs (X ∧ Y))

/-!
Is it true that if X being true makes Y true, then does X being 
false make Y false?
-/

#check ((X ⇒ Y) ⇒ (¬X ⇒ ¬Y))
#eval is_valid ((X ⇒ Y) ⇒ (¬X ⇒ ¬Y))    
#reduce find_counterexamples_bool ((X ⇒ Y) ⇒ (¬X ⇒ ¬Y)) 
#reduce (implies (implies false true) (implies true false))

/-!
Is it true that if X being true means that Y must be true,
then does Y being false imply X is false?
-/

#check ((X ⇒ Y) ⇒ (¬Y ⇒ ¬X))
#eval is_valid ((X ⇒ Y) ⇒ (¬Y ⇒ ¬X))    
#reduce find_counterexamples_bool ((X ⇒ Y) ⇒ (¬Y ⇒ ¬X)) 


/-!
We can find all the models of an expression.
-/

#eval find_models_bool ((X ⇒ Y) ⇒ (¬X ⇒ ¬Y))


/-!
Simple model counting.
-/
#eval count_models (X ∨ Y)
#eval count_models (X ∧ Y)


/-!
Search for models  (returns list of functions)
-/

#reduce find_models (X ∧ ¬ X)              -- expect []
#reduce (find_models (X ∨ Y)).length       -- expect 3
#reduce (find_models (X ∧ Y)).length       -- expect 1



/-! 
Search for models (returns list of list of bools)
-/ 

#eval find_models_bool (X ∧ ¬ X)                     -- []
#eval find_models_bool (X ∨ ¬ X)                     -- [[false], [true]
#eval find_models_bool (X ∧ Y)                       -- [[true, true]]  
#eval find_models_bool (¬(X ∧ Y) ⇒ ¬X ∨ ¬Y)          -- all four interps
#eval find_models_bool ((X ⇒ Y) ⇒ (Y ⇒ Z) ⇒ (X ⇒ Z)) -- all eight interps


/-!
## Homework

Forthcoming:

- Expand make_bool_lists applied to values 0-3.
- Validate a list of standard inference rules.
- Find the Fallacies, Explain Counterexamples.
- Replace ponderous function definition using map. 
-/