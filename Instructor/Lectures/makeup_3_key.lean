/-!
Here are a few types.
-/

inductive Cuke : Type
| c

inductive Pickle : Type
| p

inductive Slices : Type
| s

/-!
Define a function, f, that takes an
argument (input) of type Cuke and that
returns a value of type Pickle.
-/

def f (_ : Cuke) : Pickle := Pickle.p

/-!
Use #reduce to show the result of applying f
to a cuke.
-/

#reduce f Cuke.c

/-!
Define a function, g, that takes an
argument (input) of type Pickle and that
returns a value of type Slices.
-/

def g (_ : Pickle) : Slices := Slices.s

/-!
Use #reduce to show the result of applying g
to a pickle.
-/

#reduce g Pickle.p

/-!
Define a function, h, as the *composition* of
g and f, that takes a cuke as an input argument
and that returns slices as a result. Use Lean's
function composition operation, ∘, in giving an
answer.
-/

def h := g ∘ f

/-!
Use #reduce to show the result of applying h
to a cuke.
-/

#reduce h Cuke.c
