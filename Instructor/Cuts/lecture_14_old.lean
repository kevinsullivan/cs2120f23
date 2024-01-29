/-!
# Higher-Order Functions and a Model Finder (SAT Solver)

This chapter presents three main topics:

- The generalized List map, foldr, and filter functions
- Improvements in our satisfiability code using these ideas
- A model finder, a.k.a., a *SAT solver*, and a model enumerator 

## General-Purpose Higher-Order List Functions

### List.map

Here's the type of List.map in the Lean libraries.

@List.map : 
  {α : Type u_1} → 
  {β : Type u_2} → 
  (α → β) → 
  List α → 
  List β
-/

#check @List.map

-- List of Bools indicates which Nats are even
def mark_evens : List Nat → List Bool :=  
  List.map (λ a : Nat => a % 2 == 0)
#eval mark_evens [0,1,2,3,4,5]

-- Add "!" to each String in a list of Strings
def add_excls : List String → List String :=
  List.map add_excl
where add_excl (s : String) := s ++ "!"
#eval add_excls ["Hi", "Yo", "Boo"]

-- Compute a list of lengths from a list of strings
def str_lens := List.map String.length 
#eval str_lens ["Hi", "Yo", "Boo"]


/-!
### List.foldr

-/

#eval List.foldr Nat.add 0 [1,2,3,4,5]

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

#check @List.foldr
#eval List.foldr or false [false, true, false, false]
#eval List.foldr (λ s b => s.length%2 == 0) false ["Hi", "there"]
#eval List.foldr (λ s b => s.length%2 == 0) false ["Hi!", "Lean!"]

/-!
We now see reduce_or and reduce_and to differ only in the
combination of operator and identity element, and are just
two of innumerable specializations of foldr.
-/

def reduce_or := List.foldr or false
def reduce_and := List.foldr and true

def reduce_string_length : String → Nat → Nat := λ s n => s.length + n
#eval List.foldr reduce_string_length 0 ["Hello,", "Logic!"]

/-!
Study this example to understand when the function passed to 
reduce is, in general, of some type α → β → β. Here α is String
and β is Nat.
-/

/-! NEW

If you think about it, what foldr reall does is to extend
a binary operator, such as or taking two bools, to an n-ary
operator, taking any number of arguments. Reduce_or is thus
a mult-argument or, and reduce_and a multi-argument and. The
key idea, again, is that foldr extends a binary operator to
be an n-ary operator, taking a list of arguments instead of
just exactly one. 
-/
def reduce_or := List.foldr or false
def reduce_and := List.foldr and true


/-!
### List.filter

The list map function turns one list into another list of the same size
but with elements replaced by their *images* under a given transformation.
The list foldr function turns one list into a single value by applying a
binary operation between each element of the list and remaining elements, 
grouping from the right. 

Now we turn to the filter function. It's job is to take a list and return 
the sub-list of elements that satisfy a given predicate function. Here is
the function type. It takes a list element type, α, a predicate function 
that, for any given α returns true if and only it has the property that 
the predicate function tests for, and a list of α elements; it then returns
the sub-list of α elements that satisfy the predicate.

@List.filter : 
  {α : Type u_1} → 
  (α → Bool) → 
  List α → 
  List α
-/

#check @List.filter

/-!
The implementation is straightforward. For an empty list
return an empty list. For a list h::t return a list that
has h at its head if it satisfies the predicate and the
filtered tail as its tail, or just the filtered tail if
h doesn't satisfy the predicate. Here's the code, straight
from Lean's libraries. Notice something new: matching on
the *result* of applying a function (p) to a value (a). 

def filter (p : α → Bool) : List α → List α
  | [] => []
  | a::as => match p a with
    | true => a :: filter p as
    | false => filter p as
-/

-- Filter to extract even elements of list of Nats
#eval List.filter (λ n => n % 2 == 0) [0,1,2,3,4,5]

-- Filter to extra even-length strings in list of strings
#eval List.filter (λ s => s.length %2 == 0) ["Hi", "there", "Mary"]


/-!
## Improving our Propositional Logic Implementation 

In this section, we apply the ideas above, along with a suggestion
by a student to replace our icky code for generating truth table input
lists with a compact and beautiful recursive function. 

- Redefine bit_list_to_bool_list using List.map
- Redefine reduce_or and reduce_and using List.foldr
- Improve our validity/sat/unsat checking code substantially

To start, here is our most recent version of our specification of the 
syntax and semantics of proposition logic. There are no changes to be 
made here. If you've thoroughly grasped these definitions, skip forward.
If you're still unsure what *eval_expr* does, you need to not go on
until you've really understood that function.

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
### Satisfiability

A satisfiability checker for propositional logic.

#### Truth Table Input Rows 
-/

-- replace it all!
def right_bit (n : Nat) := n%2
def shift_right (n : Nat) := n/2
def nat_to_bin : Nat → List Nat
| 0     => [0]
| 1     => [1]
| n' + 2 =>
  have : (shift_right (n' + 2)) < (n' + 2) := sorry
  nat_to_bin (shift_right (n' + 2)) ++ [right_bit (n' + 2)]

def zero_pad : Nat → List Nat → List Nat
  | v, l => zero_pad_recursive (v - (l.length)) l
where zero_pad_recursive : Nat → List Nat → List Nat
  | 0, l => l
  | v'+1, l => zero_pad_recursive v' (0::l)

def mk_bit_row : (row: Nat) → (cols : Nat) → List Nat
| r, c => zero_pad c (nat_to_bin r)

def bit_to_bool : Nat → Bool
| 0 => false
| _ => true

def bit_list_to_bool_list : List Nat → List Bool
| [] => []
| h::t => (bit_to_bool h) :: (bit_list_to_bool_list t)

def mk_bool_row : (row : Nat) → (vars : Nat) → List Bool
| r, v => bit_list_to_bool_list (mk_bit_row r v)

/-!
Mikhail replaced all the preceding code with one recursion.
Exercise: explain in clear English how this recursion works
-/

-- def make_bool_lists: Nat → List (List Bool)
-- | 0 => [[]]
-- | n + 1 =>  (List.map (fun L => false::L) (make_bool_lists n)) ++ 
--             (List.map (fun L => true::L) (make_bool_lists n))

/-!
#### Count Distinct Variables in Expression
-/

-- Note the zeros. Why?
def max_variable_index : Expr → Nat
  | Expr.true_exp => 0
  | Expr.false_exp => 0
  | Expr.var_exp (var.mk i) => i
  | Expr.un_exp _ e => max_variable_index e
  | Expr.bin_exp _ e1 e2 => max (max_variable_index e1) (max_variable_index e2) 

def num_vars : Expr → Nat := λ e => max_variable_index e + 1                    

/-!
#### Interpretations
-/

def override : Interp → var → Bool → Interp
| old_interp, var, new_val => 
  (λ v => if (v.n == var.n)     -- when applied to var
          then new_val          -- return new value
          else old_interp v)  -- else retur old value

def bool_list_to_interp : List Bool → Interp
  | l => bools_to_interp_helper l.length l
where bools_to_interp_helper : (vars : Nat) → (vals : List Bool) → Interp
  | _, [] => (λ _ => false)
  | vars, h::t =>
    let len := (h::t).length
    override (bools_to_interp_helper vars t) (var.mk (vars - len)) h 

/-!
We can also replace the following two functions with one simpler one.
-/
def mk_interp_vars_row : (vars: Nat) → (row: Nat) → Interp
| v, r => bool_list_to_interp (mk_bool_row r v)

def mk_interps (vars : Nat) : List Interp := 
  mk_interps_helper (2^vars) vars
where mk_interps_helper : (rows : Nat) → (vars : Nat) → List Interp
  | 0, _         => []
  | (n' + 1), v  => (mk_interp_vars_row v n')::mk_interps_helper n' v

/-! 
Mikhail's version 
-/

-- def mk_interps : Nat → List Interp
-- | n => List.map bool_list_to_interp (make_bool_lists n) 


/-!
My slight improvement.
-/
def mk_expr_interps : Expr → List Interp
| e => mk_interps (num_vars e)


/-!
#### Truth Table Output Column
-/ 

def eval_expr_interps : List Interp → Expr → List Bool
| [], _ => []
| h::t, e => eval_expr_interps t e ++ [eval_expr e h]


def truth_table_outputs' : Expr → List Bool
| e =>  eval_expr_interps (mk_interps (num_vars e)) e


def truth_table_outputs : Expr → List Bool
| e => 
  let interps := mk_interps (num_vars e)
  eval_expr_under_all_interps_helper e interps 
where  eval_expr_under_all_interps_helper (e : Expr) : List Interp → List Bool 
  | [] => []
  | h::t => eval_expr_under_all_interps_helper e t ++ [eval_expr e h]

/-!
### Satisfiability Checkers

Immplementing these functions was part of Homework #7
-/

-- Three main functions: test given expression for satsfiability properties
def is_sat : Expr → Bool := λ e : Expr => reduce_or (truth_table_outputs e)
def is_valid : Expr → Bool := λ e : Expr => reduce_and (truth_table_outputs e)
def is_unsat : Expr → Bool := λ e : Expr => not (is_sat e)



/-!
## A Model Finder, i.e., SAT Solver

A SAT solver takes an expression, e, and returns a value of 
the sum type, *SomeOrNone*, an instance of which which holds 
either *some model,* if there is at least one, or *nothing*.
In other words, 

### Using a Sum Type to Implement a Partial Function
A partial function is a function that is not defined for all
possible input values. For example, a function, *model* that
takes an expression and returns a model will not always have
a model to return (if the expression is unsatisfiable). But
in Lean, every function must be total. 

The way out is with a function that returns a value of a sum 
type, let's say, *Interp ⊕ Unit*. If there is a model, *m*, 
the function will return *(Sum.inl m)*. If there's not model, 
it will return *Sum.inr Unit.unit*. The unit option signals
the absence of a model.

This approach effectively extends the *Interp* type with one 
additional  value, here, *Unit.unit*, which we use to signal 
that the partial function (here from expression, e, to model
of e) is undefined for e. It just has no model to be returned. 
-/

def SomeInterpOrNone := Interp ⊕ Unit   -- This is a *type*

/-!
### An Option Model Finder for an Expression

Here's the function. Note thus use of several "let bindings"
in this code. They bind names, as shorthands, to given terms, 
so a final return value can be expressed more succinctly and 
clearly. 

This is a common style of coding in many functional programming
languages. You should spend a few minutes here to internalize 
it; then start to use it. Here we bind names to two terms then 
we evaluate *find_model_helper interps e*. It iterates down the
list of interpretations, checking each to determine if it makes
the expression true. If one, i, does, the result is Sum.inl i;
if none of the interpretations make e true, the result is Sum.inr 
unit, on the right.
-/
def find_model : Expr → SomeInterpOrNone
| e =>
  let interps := mk_expr_interps e
  find_model_helper interps e
where find_model_helper : List Interp → Expr → SomeInterpOrNone
| [], _ => Sum.inr Unit.unit
| h::t, e => if (eval_expr e h) then Sum.inl h else find_model_helper t e

-- Tests
def X := {var.mk 0}
def Y := {var.mk 1}
def Z := {var.mk 2}

#reduce find_model (X)       -- expect Sum.inl _ (a function)
#reduce find_model (X ∧ ¬X)  -- expect Sum.inr Unit.unit

/-!
### Convenience Function to Print an Interpretation 
-/

-- Given interpretation return values assigned to first num_vars variables 
def interp_to_bools : Interp → (num_vars : Nat) → List Bool
| _,  0 => []
| i, (n' + 1) => interp_to_bools i n' ++ [(i (var.mk n'))]

/-!
Given some model or no model (a sum type object) return an empty 
list of Bools if there's no model, and a list of Boolean values for 
its first *num_vars* variables, otherwise. 
-/
def some_model_or_none_to_bools : SomeInterpOrNone → (num_vars : Nat) → List Bool
| Sum.inl i, n => interp_to_bools i n
| Sum.inr _, _ => []

-- Test cases

#reduce some_model_or_none_to_bools (find_model (X ∧ ¬Y)) 2    -- expect [true, false]
#reduce some_model_or_none_to_bools (find_model (X ∧ ¬X)) 2    -- expect [] (unsat)
#reduce some_model_or_none_to_bools (find_model (¬X ∨ ¬Y)) 2   -- expect some model

/-!
New function: 

Given an expression and a list of interpretations, derive
the number, v, of relevant variables from the expression, and 
return a list Boolean lists of all 2^v interpretations, each
list being v Bools in length. 
-/

def get_interps_bools_lists : Expr → List Interp → List (List Bool) 
| e, is =>
  let vars := num_vars e
  match is with
    | [] => []
    | h::t => interp_to_bools h vars::get_interps_bools_lists e t

-- Tests TBD

/-!
### Exercises

#1. Define a function, *all_models*, that takes an expression 
and returns a list, possibly empty, of all of its models, i.e.,
of interpretation functions that make the expression true. Use 
*filter* in your answer. The challenge is to write the filter 
predicate function.
-/

def all_models : Expr → List Interp
| e => List.filter (λ i => eval_expr e i) (mk_expr_interps e)

-- tests
#reduce all_models (X ∧ ¬ X)              -- expect []
#reduce (all_models (X ∨ Y)).length       -- expect 3
#reduce (all_models (X ∧ Y)).length       -- expect 1


/-!
#2. Define a function that reduces a list to a list of  an expression, e, return a list of all of its 
models, each represented as a truth table row, i.e., 
as a list of Bools.
-/
def all_models_bool : Expr → List (List Bool)
| e =>  get_interps_bools_lists e (all_models e)

-- tests
#eval all_models_bool (X ∧ ¬ X) 
#eval all_models_bool (X ∨ ¬ X) 
#eval all_models_bool (X ∧ Y)
#eval all_models_bool (¬(X ∧ Y) ⇒ ¬X ∨ ¬Y)
#eval all_models_bool ((X ⇒ Y) ⇒ (Y ⇒ Z) ⇒ (X ⇒ Z))

/-!
Define a function that takes a *list* of interpretations and that returns a list
of Bool *lists*, one sublist for each interpretation in the list thereofs. Use map.
-/


/-!
Define a utility (low-level) function that takes a list of interpretations 
and a number of variables to display and that returns a *list of lists* of 
Boolean values, one list reflecting each interpretation, with Boolean values 
indicating the values the interpretation assigns to corresponding variables. 
-/


/-!
Write a function that takes an expression and returns the number of models it has
(restricting to the number of distinct variables). Wait, is there a bug in our code
for counting the number of distinct variables in an expression?! Uh oh.
-/

