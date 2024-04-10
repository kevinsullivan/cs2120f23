
/-!
We defined a function that takes a function, f, and that
returns a function that applies f four times to a given
argument. We saw how to use *composition notation* to this
end.
-/
def comp4 {α : Type} : (α → α) → (α → α)
| f => (λ a => (f ∘ f ∘ f ∘ f) a)

/-!
We then defibed a generalized function that takes a function,
f, and a natural number, n, as arguments and that returns a
function that applies the function, f, *n* times, to a given
argument. But we didn't use function composition notation in
this definition. Exercise: improve the code by using function
composition notation.
-/

def my_comp {α β γ : Type} : (β → γ) → (α → β) → (α → γ)
-- | g, f => g ∘ f
| g, f => λ (a : α) => g (f a)


def compn' {α : Type} : Nat → (α → α) → (α → α)
| Nat.zero, _ => λ a => a
| (Nat.succ n'), f => (λ a => f (compn' n' f a))

def compn {α : Type} : Nat → (α → α) → (α → α)
| Nat.zero, _ => (λ a => a)
| (Nat.succ n'), f => f ∘ (compn n' f)

#eval (compn 5 Nat.succ) 0
def sq (n : Nat) := n * n
#eval (compn 5 sq) 2

/-!
Next let's review the homework assignment.
-/

/-!
Natural number addition, using (n + (m + 1)) = 1 + (n + m).
-/

/-!
List append.
-/

/-!
Here't the list code from last class.

inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α
-/

def e : List Nat := List.nil
def e' : List Nat := []         -- List NOTATION

def l1 : List Nat := List.cons 1 e
def l1' : List Nat := 1::e      -- notation for cons
def l1'' : List Nat := [1]

def l2 : List Nat := List.cons 0 l1
#reduce l2

def list_len {α : Type} : List α → Nat
| List.nil => 0
| (List.cons _ t) => 1 + list_len t

#eval list_len l2

def add : Nat → Nat → Nat
| n, 0 => n
| n, (m' + 1) => Nat.succ (add n m')

#eval add 4 5

def mul : Nat → Nat → Nat
| _, 0 => 0
| n, (m' + 1) => add n (mul n m')

#eval mul 5 4

def exp : Nat → Nat → Nat
| _, 0 => 1
| n, (m' + 1) => mul n (exp n m')

#eval exp 2 0

/-!
And now let's introduce a range of fundamental data types,
along with functions involving values of these types.
-/

#check Bool
/-
inductive Bool : Type where
  | false : Bool
  | true : Bool
-/

#check Unit
/-
inductive Unit : Type where
  | unit : PUnit
-/

-- empty
#check (@Empty)

/-!
inductive Empty : Type
-/

def e2e : Empty → Empty
| e => e

#eval e2e _

def n2e : Nat → Empty
| n => _

inductive MyEmpty

-- unit
#check (Unit)

-- Product
#check (@Prod)

-- Sum
#check (@Sum)
