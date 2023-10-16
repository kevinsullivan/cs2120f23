/-!
# Higher-Order Functions and a Model Finder (SAT Solver)

This chapter presents three main topics:

- The generalized List map, foldr, and filter functions
- Improved satisfiability code, in part by using these ideas
- A model finder (*SAT solver*) and enumerator 

## General-Purpose Higher-Order List Functions

### List.map

The *List.map* function, converts a list of α terms,
into a list of corresponding β values by applying a
given function, *f : α → β*, to each α in turn. E.g.,
*map (λ (s : String) => s.length) ["Hello", "Lean"]* 
returns *[5, 4]*.

Here's the type of List.map in the Lean libraries.

@List.map : 
  {α : Type u_1} → 
  {β : Type u_2} → 
  (α → β) → 
  List α → 
  List β
-/

#check @List.map


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
@List.foldr : 
{α : Type u_1} →    -- implicit type
{β : Type u_2} →    -- implicit type
(α → β → β) →       -- combine α value at head with β result for rest of list
β →                 -- identity element / base case answer
List α → 
β

def foldr (f : α → β → β) (init : β) : List α → β
  | []     => init
  | a :: l => f a (foldr f init l)
-/

/-!
### List.filter
-/

/-!
The *List.filter* function takes a list, *l* of α values, and an α → Bool 
predicate function that indicates whether a given α value has a particular
property, and returns the sublist of α values in l that have property, *p*.
-/

#check @List.filter

/-!
@List.filter : 
  {α : Type u_1} → 
  (α → Bool) → 
  List α → 
  List α

def filter (p : α → Bool) : List α → List α
  | [] => []
  | a::as => match p a with
    | true => a :: filter p as
    | false => filter p as
-/

#eval List.filter (λ (n : Nat) => n%2 == 0) [0,1,2,3,4,5,6,7]

/-!
## Propositional Logic: The Next Generation
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

We next automate checking of expressions for three key properties:
validity, satisfiability, and unsatisfiability. We begin by defining
a function that generates the standard input side of a truth table
with a given number of variables. (In our system that's the index of
the highest indexed variable in a given expression.)

### Truth Table Input Rows 

We had previousl developed an explanatory but ponderous approach to
generating a list of of all lists of boolean input rows. Mikhail 
noticed and sent me a note say that we could replace it all with a
single clever recursive function. So here that is. Studying it is a
part of the homework. 
-/

-- Thank you, Mikhail
def make_bool_lists: Nat → List (List Bool)
| 0 => [[]]
| n + 1 =>  (List.map (fun L => false::L) (make_bool_lists n)) ++ 
            (List.map (fun L => true::L) (make_bool_lists n))

/-!
#### Bool List to/from Interpretation Function 
-/

-- Function override
def override : Interp → var → Bool → Interp
| old_interp, var, new_val => 
  (λ v => if (v.n == var.n)     -- when applied to var
          then new_val          -- return new value
          else old_interp v)  -- else retur old value

-- Bool list to interpretation function
def bool_list_to_interp : List Bool → Interp
  | l => bools_to_interp_helper l.length l
where bools_to_interp_helper : (vars : Nat) → (vals : List Bool) → Interp
  | _, [] => (λ _ => false)
  | vars, h::t =>
    let len := (h::t).length
    override (bools_to_interp_helper vars t) (var.mk (vars - len)) h 

-- From number of variables, interpretation, to list of Bools
def interp_to_list_bool : (num_vars : Nat) → Interp →  List Bool
| 0, _ => []
| (n' + 1) , i => interp_to_list_bool n' i ++ [(i (var.mk n'))]

-- From number of variables, list of interpretations, to list of Bool lists
def interps_to_list_bool_lists : Nat → List Interp → List (List Bool) 
| vars, is => List.map (interp_to_list_bool vars) is

/-!
#### Maximum Variable Index in Expression
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
#### Lists of Interpretation Functions
-/
-- Mikhail's suggestion: number of variables to list of interpretations
def mk_interps_vars : Nat → List Interp
| n => List.map bool_list_to_interp (make_bool_lists n) 

-- Sullivan adds this: from expression to list of interpretations
def mk_interps_expr : Expr → List Interp
| e => mk_interps_vars (num_vars e)


/-!
#### Truth Table Outputs
-/ 

-- The column of truth table outputs for e
def truth_table_outputs : Expr → List Bool
| e =>  eval_expr_over_interps e (mk_interps_vars (num_vars e))
where eval_expr_over_interps : Expr → List Interp → List Bool
| _, [] => []
| e, h::t => eval_expr_over_interps e t ++ [eval_expr e h]

/-!
#### n-ary And and Or functions
-/

def reduce_or := List.foldr or false
def reduce_and := List.foldr and true


/-!
#### Satisfiability-Related Properties of Expressions

Finally we can define the API we provide: given an expression
in propositional logic (our concrete notation) we can check it
for being satisfiable, valid, unsatisfiable. The algorithms is
best-case exponential time, so it won't work for any but minimal
problem sizes.
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

def find_model : Expr → Option Interp
| e =>
  let interps := mk_interps_expr e
  find_model_helper interps e
where find_model_helper : List Interp → Expr → Option Interp
| [], _ => none
| h::t, e => if (eval_expr e h) then some h else find_model_helper t e


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
it has. From a list of all models, it's obviously even to derive
the number of models, as the length of the list.  
-/

def count_models (e : Expr) := List.length (find_models e)

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


