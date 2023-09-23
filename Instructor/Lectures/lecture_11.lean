/-
# Propositional Logic

UNDER CONSTRUCTION
-/


/-!
## Informal Presentation of PL
-/

/-!
## Formalization of PL
-/

/-!
### Syntax
-/


/-!
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
### Expressions (Sentences) 
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
-/

notation "{"v"}" => var_exp v
notation "¬" e => un_exp unary_op.not e 
notation e1 "∧" e2 => bin_exp binary_op.and e1 e2 
notation e1 "∨" e2 => bin_exp binary_op.or e1 e2 

def e0 := {v₀}
def e1 := ¬e0
def e2 := e0 ∧ e1
def e3 := e0 ∨ e1
def e4 := (e2 ∧ e3) ∨ e0


/-!
### Semantics
-/

/-!
#### Variables
-/
def Interp := var → Bool  -- interp is a type

-- examples
def all_true  : Interp := fun _ => true
def all_false : Interp := fun _ => false

/-!
#### Operators
-/
def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not

def eval_bin_op : binary_op → (Bool → Bool → Bool)
| binary_op.and => and
| binary_op.or => or

/-!
#### Expressions
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