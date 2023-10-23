/-!
# UVa CS2120-002 F23 Midterm Exam




## Propositional Logic: Syntax, Sematics, Satisfiability

This section of the exam simply includes our formal 
definition of the syntax and semantics of propositional
logic and of functions that determine whether a given 
expression is valid, satisfiable, or unsatisfiable.

### Syntax
-/

-- variables
structure var : Type :=  (n: Nat)

-- connectives/operators
inductive unary_op : Type | not
inductive binary_op : Type
| and
| or
| imp
| iff

-- expressions (abstract syntax)
inductive Expr : Type
| var_exp (v : var)
| un_exp (op : unary_op) (e : Expr)
| bin_exp (op : binary_op) (e1 e2 : Expr)

-- concrete syntax 
notation "{"v"}" => Expr.var_exp v
prefix:max "¬" => Expr.un_exp unary_op.not 
infixr:35 " ∧ " => Expr.bin_exp binary_op.and  
infixr:30 " ∨ " => Expr.bin_exp binary_op.or 
infixr:25 " ⇒ " =>  Expr.bin_exp binary_op.imp
infixr:20 " ⇔ " => Expr.bin_exp binary_op.iff 

/-!
### Semantics
-/

-- meanings of unary operators
def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not

-- missing binary Boolean operators
def implies : Bool → Bool → Bool
| true, false => false
| _, _ => true

def iff : Bool → Bool → Bool
| true, true => true
| false, false => true
| _, _ => false

-- meanings of binary operators
def eval_bin_op : binary_op → (Bool → Bool → Bool)
| binary_op.and => and
| binary_op.or => or
| binary_op.imp => implies
| binary_op.iff => iff

-- The interpretation type
def Interp := var → Bool 

-- The meanings of expressions "under" given interpretations
def eval_expr : Expr → Interp → Bool 
| (Expr.var_exp v),        i => i v
| (Expr.un_exp op e),      i => (eval_un_op op) (eval_expr e i)
| (Expr.bin_exp op e1 e2), i => (eval_bin_op op) (eval_expr e1 i) (eval_expr e2 i)

/-!
### Satisfiability

We built a satisfiability checker for propositional logic,
in several pieces. This subsection includes all definitions.

#### Truth Table Input Rows 
-/

-- Nat to Binary
-- You don't need to worry about the "have" part
def right_bit (n : Nat) := n%2
def shift_right (n : Nat) := n/2
def nat_to_bin : Nat → List Nat
| 0     => [0]
| 1     => [1]
| n' + 2 =>
  have : (shift_right (n' + 2)) < (n' + 2) := sorry
  nat_to_bin (shift_right (n' + 2)) ++ [right_bit (n' + 2)]

-- Left pad with zeros
def zero_pad : Nat → List Nat → List Nat
  | v, l => zero_pad_recursive (v - (l.length)) l
where zero_pad_recursive : Nat → List Nat → List Nat
  | 0, l => l
  | v'+1, l => zero_pad_recursive v' (0::l)

-- Make row of bits at index "row" padded out to "cols" wide 
def mk_bit_row : (row: Nat) → (cols : Nat) → List Nat
| r, c => zero_pad c (nat_to_bin r)

-- Convert list of bits to list of bools
def bit_to_bool : Nat → Bool
| 0 => false
| _ => true

def bit_list_to_bool_list : List Nat → List Bool
| [] => []
| h::t => (bit_to_bool h) :: (bit_list_to_bool_list t)

-- Make row'th row of truth table with vars variables
def mk_row_bools : (row : Nat) → (vars : Nat) → List Bool
| r, v => bit_list_to_bool_list (mk_bit_row r v)

/-!
#### Interpretations
-/

-- Convert list of bools to interpretation
def override : Interp → var → Bool → Interp
| old_interp, var, new_val => 
  (λ v => if (v.n == var.n)     -- when applied to var
          then new_val          -- return new value
          else old_interp v)  -- else retur old value

def bools_to_interp : List Bool → Interp
  | l => bools_to_interp_helper l.length l
where bools_to_interp_helper : (vars : Nat) → (vals : List Bool) → Interp
  | _, [] => (λ _ => false)
  | vars, h::t =>
    let len := (h::t).length
    override (bools_to_interp_helper vars t) (var.mk (vars - len)) h 

-- Make an interpretation for given row with "vars" variables
def mk_interp_vars_row : (vars: Nat) → (row: Nat) → Interp
| v, r => bools_to_interp (mk_row_bools r v)

-- Given number of variables, return list of interpretations
def mk_interps (vars : Nat) : List Interp := 
  mk_interps_helper (2^vars) vars
where mk_interps_helper : (rows : Nat) → (vars : Nat) → List Interp
  | 0, _         => []
  | (n' + 1), v  => (mk_interp_vars_row v n')::mk_interps_helper n' v

-- Count the number of variables in a given expression
def max_variable_index : Expr → Nat
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

-- functions to check if bool list has any, resp. all, values true
def reduce_or : List Bool → Bool 
| [] => false
| h::t => or h (reduce_or t)

def reduce_and : List Bool → Bool 
| [] => true
| h::t => and h (reduce_and t)

-- Three main functions: test given expression for satsfiability properties
def is_sat : Expr → Bool := λ e : Expr => reduce_or (truth_table_outputs e)
def is_valid : Expr → Bool := λ e : Expr => reduce_and (truth_table_outputs e)
def is_unsat : Expr → Bool := λ e : Expr => not (is_sat e)

/-!
### Quick Demo
-/

-- some atomic/variable expressions
def Bread  : Expr := {var.mk 0}
def Cheese : Expr := {var.mk 1}
def Jam    : Expr := {var.mk 2}

#eval is_sat (Bread)
#eval is_sat (Bread ∧ ¬Bread)
#eval is_valid (Bread ∧ ¬Bread)
#eval is_valid (Bread ∨ ¬Bread)
#eval is_unsat (Bread ∧ ¬Bread)