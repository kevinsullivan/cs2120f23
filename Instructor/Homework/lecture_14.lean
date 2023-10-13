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

Give types, α and β, and a function, m, for converting an α value to a β value,
this function  converts a list of α values into into a list of corresponding β 
values. 

We take a quick moment to explain the *u_1* and *u_2* notations. They are *type
universe levels*. They range from 0 on up. Type 0 is just Type. It in turn is of 
type 1. And so on. So this definition of map will work for lists of things not 
just in Type, but also in Type 1, Type 2, etc., all the way up.

Here's an example where we map a function (what does it do?) over a list of Nat
to derive a list of Bool.
-/

#check @List.map
#eval List.map        -- expect [false, true, true]
        (λ a => 
          if (a ≠ 0) 
          then true 
          else false) 
        [0,1,2]


/-!
### List.foldr

Here's the type of the List.foldr function in Lean's libraries.
Whereas the purpose of List.map is to convert one list into another
list, the purpose of List.foldr is to collapse a list down to a 
single value. 

The way that this reduction occurs is by the application of a
given binary operation between every two elements of the list,
with an additional application between the final element and the
result for the empty list.

Consider our *reduce_or* function. It takes a list, such as 
*[true, false, true]* and, in computes *true or false or true 
or false*, where the last *or false* ends the recursion without
changing the prior result. The *reduce_or* function is a special 
case of *List.foldr.* So, of course, is *reduce_and*.


In general, the foldr function can take a list of elements of
one type and reduce them to a value of another type. For example,
foldr could be used to reduce a list of strings to a Boolean that
indicates whether the list contains any even-length strings. 

Here's the type

@List.foldr : 
  {α : Type u_1} →    -- implicit type
  {β : Type u_2} →    -- implicit type
  (α → β → β) →       -- combine α value at head with β result for rest of list
  β →                 -- identity element / base case answer
  List α → 
  β

The arguments are types α and β; a function, let's call it an *operator*, 
that takes a list head element of type α, and a partial result, of type
β, obtained by recursively solving the rest of the list, and returns an 
answer for the list with both that head element and the already reduced
tail;  along with a β-valued result for the empty list. This function 
then reduces a list of α's into a final value of type β.

Here's the implementation.

def foldr (f : α → β → β) (init : β) : List α → β
  | []     => init
  | a :: l => f a (foldr f init l)
-/

#check @List.foldr
#eval List.foldr or false [false, true, false, false]
#eval List.foldr (λ s b => if (s.length%2=0) then true else false) false ["Hi", "there"]
#eval List.foldr (λ s b => if (s.length%2=0) then true else false) false ["Hi!", "Lean!"]

-- Specialize foldr to reduce_or
def reduce_or := List.foldr or false
#eval reduce_or [false, false, false]

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

-- Filter to extract the even elements of [0,1,2,3,4,5]
#eval List.filter (λ n => n % 2 = 0) [0,1,2,3,4,5]

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

