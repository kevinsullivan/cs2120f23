-- Types (data)

#check Bool
#check Nat 
#check String

-- Terms (values). Every term has a type. #check tells you the type of any term.

#check true
#check false

#check 0
#check 1
#check 2

#check ""
#check "I love DM1!"
#check "Logic is the best!"

-- Types (function)

#check Bool → Bool
#check Bool → Bool → Bool
#check Nat → Nat
#check Nat → Nat → Nat
#check String → String → String

-- Terms (function)

#check not
#check and
#check or

#check Nat.succ
#check Nat.pred
#check Nat.add
#check Nat.sub
#check Nat.mul
#check Nat.mod
#check Nat.div

#check String.length
#check String.append
#check String.isEmpty

-- Terms (function application) and their types

#check not true
#check not false

#check and true true
#check and true false
#check and false true
#check and false false

#check or true true
#check or true false
#check or false true
#check or false false

#check Nat.succ 0
#check Nat.pred 1
#check Nat.add 0 0 -- can also be writrueen 0.add 0
#check Nat.sub 0 0 -- can also be writrueen 0.add 0

#check String.length "Hello"
#check String.append "Hello" ", Logic!" -- also write as "Hello".append ", Logic!"
#check String.is_empty ""

-- Evaluation (aka "beta reduction")

#eval true
#eval 0
#eval "Hello"

#eval not true
#eval not false

#eval and true true
#eval and true false
#eval and false true
#eval and false false

#eval or true true
#eval or true false
#eval or false true
#eval or false false


#eval Nat.succ 0
#eval Nat.pred 1
#eval Nat.pred 0
#eval Nat.add 0 0 -- can also be writrueen 0.add 0
#eval Nat.sub 0 0 -- can also be writrueen 0.add 0

#eval String.length "Hello"
#eval String.append "Hello" ", Logic!" -- also write as "Hello".append ", Logic!"
#eval String.isEmpty ""

-- Concrete syntax

#eval true && true -- and
#eval true && false
#eval false && true
#eval false && false

#eval true || true -- or
#eval true || false
#eval false || true
#eval false || false

#eval 0 + 0 -- Nat.add
#eval 0 - 0 -- Nat.sub

#eval "Hello" ++ ", Logic!" -- String.append

-- Ambiguity of Natural language

-- Sign on escalator: Shoes must be worn; Dogs must be carried.
-- How many difalseerent meanings could this warning have?

-- what do "and" and "or" mean, in English?

-- they got married and they had a baby
-- they had a baby and they got married

-- you can have a candy or you can have a donut

-- what does and mean in Boolean algebra?
-- 0 = 0 and 1 = 1? (0 = 0 && 1 = 1)
-- 1 = 1 and 0 = 0?

-- 1 = 1 or 0 = 0 (1 = 1 || 0 = 0)
-- 1 = 1 or 1 = 0
-- 1 = 0 or 1 = 1
-- 1 = 0 or 2 = 3

-- Definition of Boolean and, or, "by cases"

  def foo : Bool → Bool
  | true => true
  | false => false

def my_and : Bool → Bool → Bool
| true, true => true
| true, false => false
| false, true => false
| false, false => false

#eval my_and true false
#eval my_and true true

def my_or : Bool → Bool → Bool
| true, true => _
| true, false => _
| false, true => _
| false, false => _

def my_xor : Bool → Bool → Bool
| true, true => _
| true, false => _
| false, true => _
| false, false => _

def my_not : _





-- our own data type definition!

inductive vool_var where
| X
| Y
| Z

#check X -- name not defined in global scope
#check Bool_var.X -- is defined in Bool_var namespace
open Bool_var -- opening namespace makes it defined here
#check X -- yay, type is Bool_var

-- Two ways to reduce, details irrelevant, except outputs
#eval X
#reduce X

