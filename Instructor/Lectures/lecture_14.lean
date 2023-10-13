/-!
# A Few Things

UNDER CONSTRUCTION. HIGHER-ORDER FUNCTIONS OK. REST IS IN FLUX.

## Some General-Purpose Higher-Order functions

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

/-!
Give types, α and β, and a function, *m*, for converting 
an α value to a β value, this function converts a list of 
α values into into a list of β values using *m* to convert
each (a: α) in the input list into a corresponding β value
in the returned list. 

We take a quick moment to explain the *u_1* and *u_2* notations. 
They are called *type universe levels*. They range from 0 on up. 
This definition of map will work for lists of objects of types 
not just in Type, but also in Type 1, Type 2, all the way up. We
will mostly ignore universe levels for now.
-/

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

Whereas the purpose of List.map is to convert one list into another
list, the purpose of List.foldr is to *reduce* a list to a single value
by applying some operator between each pair of elements in a list. The
arguments are (1) a binary operator, (2) an answer for the empty list,
(3) a list of elements to reduce. The following example reduces the list
[1,2,3,4,5] to the sum of its elements, namely 15. 
-/

#eval List.foldr Nat.add 0 [1,2,3,4,5]

/-!
Here's the type

@List.foldr : 
  {α : Type u_1} →    -- implicit type
  {β : Type u_2} →    -- implicit type
  (α → β → β) →       -- combine α value at head with β result for rest of list
  β →                 -- identity element / base case answer
  List α → 
  β

The arguments are: (1) types α and β; (2) a function that that takes 
an element of type α (it'll be a list head element) and a value of 
type β (it'll be the partial result of reducing the rest of the list), 
and that returns the answer for the list with that head and result
for the tail; (3) an answer for the empty list; and (4) a list of α 
values to reduce. The returned result is the list reduced to a final
value, again of type β. 

Here's the implementation.

def foldr (f : α → β → β) (init : β) : List α → β
  | []     => init
  | a :: l => f a (foldr f init l)

The function returns to answer for [] in that case, and otherwise,
it applies the function to the head and the result of folding the
rest of the list to a partial result, again of type β. 
-/

#check @List.foldr
#eval List.foldr or false [false, true, false, false]
#eval List.foldr (λ s b => s.length%2 == 0) false ["Hi", "there"]
#eval List.foldr (λ s b => s.length%2 == 0) false ["Hi!", "Lean!"]

-- Specialize foldr to define reduce_or
def reduce_or := List.foldr or false
#eval reduce_or [false, false, true]

-- Specialize foldr to define reduce_and
def reduce_and := List.foldr and true
#eval reduce_and [false, false, true]

/-!
As an exercise, define a function using foldr that computes
the sum lengths of all strings in a list. What function when
used by foldr which accomplish such a reduction? Well, it will
have to take a String (list head) and a partial result (a Nat)
for the rest of the list, and return an updated answer.
-/

def reduce_string_length : String → Nat → Nat := λ s n => s.length + n
#eval List.foldr reduce_string_length 0 ["Hello,", "Logic!"]

/-!
Study this example to understand when the function passed to 
reduce is, in general, of some type α → β → β. Here α is String
and β is Nat.
-/

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


- Redefine bit_list_to_bool_list function while keeping its name and type, using List.map
- Redefine reduce_or and reduce_and while keeping their names, using List.foldr
-/


/-!# Propositional Logic: SAT Solving With a SAT Solver

## Propositional Logic 

We include these definitions with minimal explanation.

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

/- OBSOLETED
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
-/

-- Replaces all of the preceding code
def make_bool_lists: Nat → List (List Bool)
| 0 => [[]]
| n + 1 =>  (List.map (fun L => false::L) (make_bool_lists n)) ++ 
            (List.map (fun L => true::L) (make_bool_lists n))


/-!
The first 2 functions are standalone, but mk_interps uses functions defined in lecture_13.lean. 
END NEW STUFF
-/

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

/-! Obsoleted
def mk_interp_vars_row : (vars: Nat) → (row: Nat) → Interp
| v, r => bools_to_interp (mk_bool_row r v)

def mk_interps (vars : Nat) : List Interp := 
  mk_interps_helper (2^vars) vars
where mk_interps_helper : (rows : Nat) → (vars : Nat) → List Interp
  | 0, _         => []
  | (n' + 1), v  => (mk_interp_vars_row v n')::mk_interps_helper n' v
-/

-- improved version
def mk_interps : Nat → List Interp
| n => List.map bool_list_to_interp (make_bool_lists n) 

def max_variable_index : Expr → Nat
  | Expr.true_exp => 0
  | Expr.false_exp => 0
  | Expr.var_exp (var.mk i) => i
  | Expr.un_exp _ e => max_variable_index e
  | Expr.bin_exp _ e1 e2 => max (max_variable_index e1) (max_variable_index e2)

def num_vars : Expr → Nat := λ e => max_variable_index e + 1

/-!
#### Truth Table Output Column
-/ 

def eval_expr_interps : List Interp → Expr → List Bool
| [], _ => []
| h::t, e => eval_expr_interps t e ++ [eval_expr e h]

-- Given expression, return truth table outputs by ascending row index
def truth_table_outputs : Expr → List Bool
| e =>  eval_expr_interps (mk_interps (num_vars e)) e

/-!
### Satisfiability Checkers
-/

/-! Obsoleted

def reduce_or : List Bool → Bool 
| [] => false
| h::t => or h (reduce_or t)

def reduce_and : List Bool → Bool 
| [] => true
| h::t => and h (reduce_and t)
-/

def reduce_or := List.foldr or false 
def reduce_and := List.foldr and true

-- Three main functions: test given expression for satsfiability properties
def is_sat : Expr → Bool := λ e : Expr => reduce_or (truth_table_outputs e)
def is_valid : Expr → Bool := λ e : Expr => reduce_and (truth_table_outputs e)
def is_unsat : Expr → Bool := λ e : Expr => not (is_sat e)

/-!
## A SAT Solver

A SAT solver takes an expression, e, and returns a value of 
the sum type, *SomeOrNone*, an instance of which which holds 
either *some model,* if there is at least one, or *nothing*.
We use a sum type, Interp ⊕ Unit: *(Sum.inl m)* returns the
model, *m*, while *Sum.inr Unit.unit* signals that there is
no model to return. 
-/

def SomeInterpOrNone := Interp ⊕ Unit   -- This is a *type*

/-
Here's the function. Note thus use of several "let bindings"
in this code. They bind names, as shorthands, to given terms, 
so a final return value can be expressed more succinctly and 
clearly. This is a common style of coding in most functional
programming languages. Here we bind names to two terms, then
the expression, *find_model interps e*, defines the return
value. 
-/
def get_model_fun : Expr → SomeInterpOrNone
| e =>
  let num_vars := num_vars e
  let interps := (mk_interps num_vars)
  find_model interps e
where find_model : List Interp → Expr → SomeInterpOrNone
| [], _ => Sum.inr Unit.unit
| h::t, e => if (eval_expr e h) then Sum.inl h else find_model t e

-- Tests
def X := {var.mk 0}
def Y := {var.mk 1}
#reduce get_model_fun (X)       -- expect Sum.inl _ (a function)
#reduce get_model_fun (X ∧ ¬X)  -- expect Sum.inr Unit.unit

-- List of Booleans for first *num_vars* variables under given Interp 
def interp_to_bools : Interp → (num_vars : Nat) → List Bool
| _,  0 => []
| i, (n' + 1) => interp_to_bools i n' ++ [(i (var.mk n'))]

/-!
Given some model, return list of Boolean values of first *num_vars* 
variables, or in the case of no model, just return an empty list.
-/
def some_model_or_none_to_bools : SomeInterpOrNone → (num_vars : Nat) → List Bool
| Sum.inl i, n => interp_to_bools i n
| Sum.inr _, _ => []


-- Test cases
def Y := {var.mk 1}

#reduce some_model_or_none_to_bools (get_model_fun (X ∧ ¬Y)) 2
#reduce some_model_or_none_to_bools (get_model_fun (X ∧ ¬X)) 2
#reduce some_model_or_none_to_bools (get_model_fun (¬X ∨ ¬Y)) 2

