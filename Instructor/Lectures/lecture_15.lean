/-!
# Satifiability Modulo Theories

At the end of the last chapter, we saw first-hand the 
magnificence of automated satisfiability and validity 
checking for propositional logic. Most recently we met
model-finding algorithms. As usual lately, this chapter
starts by presenting an updated and compressed version
of our specifications for proposition logic, properties
of expressions, and model finding. We'll briefly review
this material at the start of class. We'll then turn to 
our main new topic: *satisfiability modulo theories*. 
-/

/-!
## Review and Extensions
-/

/-! 
Higher-order functions in lists
-/
#check @List.map
#check @List.foldr 
#check @List.filter

/-!
### Language of Propositional Logic
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

def implies : Bool → Bool → Bool
| true, false => false
| _, _ => true
def iff : Bool → Bool → Bool
| true, true => true
| false, false => true
| _, _ => false

def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not
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
### Interpretations and Truth Tables
-/
def reduce_or := List.foldr or false
def reduce_and := List.foldr and true
def make_bool_lists: Nat → List (List Bool)
| 0 => [[]]
| n + 1 =>  (List.map (fun L => false::L) (make_bool_lists n)) ++ 
            (List.map (fun L => true::L) (make_bool_lists n))
def override : Interp → var → Bool → Interp
| old_interp, var, new_val => 
  (λ v => if (v.n == var.n)   
          then new_val        
          else old_interp v)  
def bool_list_to_interp : List Bool → Interp
  | l => bools_to_interp_helper l.length l
where bools_to_interp_helper : (vars : Nat) → (vals : List Bool) → Interp
  | _, [] => (λ _ => false)
  | vars, h::t =>
    let len := (h::t).length
    override (bools_to_interp_helper vars t) (var.mk (vars - len)) h 
def interp_to_list_bool : (num_vars : Nat) → Interp →  List Bool
| 0, _ => []
| (n' + 1) , i => interp_to_list_bool n' i ++ [(i (var.mk n'))]
def interps_to_list_bool_lists : Nat → List Interp → List (List Bool) 
| vars, is => List.map (interp_to_list_bool vars) is
def max_variable_index : Expr → Nat
  | Expr.true_exp => 0
  | Expr.false_exp => 0
  | Expr.var_exp (var.mk i) => i
  | Expr.un_exp _ e => max_variable_index e
  | Expr.bin_exp _ e1 e2 => max (max_variable_index e1) (max_variable_index e2) 
def mk_interps_vars : Nat → List Interp
| n => List.map bool_list_to_interp (make_bool_lists n) 
-- main api
def num_vars : Expr → Nat := λ e => max_variable_index e + 1                    
def mk_interps_expr : Expr → List Interp
| e => mk_interps_vars (num_vars e)
def truth_table_outputs : Expr → List Bool
| e =>  eval_expr_over_interps e (mk_interps_vars (num_vars e))
where eval_expr_over_interps : Expr → List Interp → List Bool
| _, [] => []
| e, h::t => eval_expr_over_interps e t ++ [eval_expr e h]

/-!
### Satisfiability Properties of Expressions
-/
def is_sat (e : Expr) : Bool := reduce_or (truth_table_outputs e)
def is_valid (e : Expr) : Bool := reduce_and (truth_table_outputs e)
def is_unsat (e : Expr) : Bool := not (is_sat e)

/-!
### Finding Models and Counterexamples
-/
def find_model : Expr → Option Interp
| e =>
  let interps := mk_interps_expr e
  find_model_helper interps e
where find_model_helper : List Interp → Expr → Option Interp
| [], _ => none
| h::t, e => if (eval_expr e h) then some h else find_model_helper t e
def find_models (e : Expr) := 
  List.filter                 -- filter on 
    (λ i => eval_expr e i)    -- i makes e true
    (mk_interps_expr e)       -- over all interps
def find_models_bool : Expr → List (List Bool)
| e =>  interps_to_list_bool_lists (num_vars e) (find_models e)
def count_models := List.length ∘ find_models
def find_counterexamples (e : Expr) := find_models (¬e)
def find_counterexamples_bool : Expr → List (List Bool)
| e =>  interps_to_list_bool_lists (num_vars e) (find_counterexamples e)

/-!
### Examples and Practice
-/

def X := {var.mk 0}
def Y := {var.mk 1}
def Z := {var.mk 2}

-- If X being true makes Y true, then does X being false make Y false?
#check ((X ⇒ Y) ⇒ (¬X ⇒ ¬Y))
#eval is_valid ((X ⇒ Y) ⇒ (¬X ⇒ ¬Y))    
#reduce find_counterexamples_bool ((X ⇒ Y) ⇒ (¬X ⇒ ¬Y)) 
#reduce (implies (implies false true) (implies true false))

-- If X implies Y, then does not Y false imply not X?
#check ((X ⇒ Y) ⇒ (¬Y ⇒ ¬X))
#eval is_valid ((X ⇒ Y) ⇒ (¬Y ⇒ ¬X))    
#reduce find_counterexamples_bool ((X ⇒ Y) ⇒ (¬Y ⇒ ¬X)) 

-- Find all the models of an expression.
#eval find_models_bool ((X ⇒ Y) ⇒ (¬X ⇒ ¬Y))

-- Simple model counting.
#eval count_models (X ∨ Y)
#eval count_models (X ∧ Y)

-- Find all models, return list of functions
#reduce find_models (X ∧ ¬ X)              -- expect []
#reduce (find_models (X ∨ Y)).length       -- expect 3
#reduce (find_models (X ∧ Y)).length       -- expect 1

-- Find all models, returns list of bool lists
#eval find_models_bool (X ∧ ¬ X)                     -- []
#eval find_models_bool (X ∨ ¬ X)                     -- [[false], [true]
#eval find_models_bool (X ∧ Y)                       -- [[true, true]]  
#eval find_models_bool (¬(X ∧ Y) ⇒ ¬X ∨ ¬Y)          -- all four interps
#eval find_models_bool ((X ⇒ Y) ⇒ (Y ⇒ Z) ⇒ (X ⇒ Z)) -- all eight interps


/-!
## Satisfiability Modulo Theories

If you're impressed that we can have software that
automatically solves systems of Boolean constraint, you
will be especially delighted to learn that SMT solvers
also solve systems where atomic propositions can be
elaborated in other formal languages, such as that 
of everyday arithmetic. Solvers are now need to handle 
things like systems of linear inequalities. 

In the language of a typical SMT solver, like DeMoura's
Z3, atomic propositions in propositional logic can be 
expanded into formulas in a variety of other formal 
languages, e.g., the language of linear inequalities, 
for which fully automated solvers, that can find values
for arithmetic variables that make expressions true, 
do exist.

So, whereas in propositional logic, you can write *X ∧ Y*, 
in propositional logic extended with the "theory" called 
*everyday arithmetic*, you can write (X > Y + 2) ∧ (Y ≤ 7). 

Question: You solve it! What's the smallest integer value of 
X for which there's some value of Y so that together X and Y
satisfy the overall formula?

So let's crank up Z3! Open lecture_15.py. Read and and run
it using the run icon at the top of the Python editing panel.

More to come. UNDER CONSTRUCTION.
-/