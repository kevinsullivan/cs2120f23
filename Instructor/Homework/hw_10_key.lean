/-!
1. Every dog likes some cat.

2. If any dog, d, likes any dog, g, and that dog, g, likes any dog, w, then d likes w.

3. If any cat, c, likes any cat, d, then d also likes c.

4. Every cat, c, likes itself.

5. If every cat likes every other cat, and c and d are cats, then c likes d.

Finally, give a formal proof in Lean of the proposition in problem #5.
-/

-- #1
variable
  (Dog Cat : Type)
  (Likes₁ : Dog → Cat → Prop)

#check ∀ (d : Dog), ∃ (c : Cat), Likes₁ d c


-- #2
variable (Likes₂ : Dog → Dog → Prop)
         ( x y z : Dog)
         (pf1 : Likes₂ x y)
         (pf2 : Likes₂ y z)
         (pf : ∀ (d g w : Dog), Likes₂ d g → Likes₂ g w → Likes₂ d w)

example : Likes₂ x z := pf x y z pf1 pf2
#check pf x y z pf1 pf2

-- Transitivity
example
  (Likes₂ : Dog → Dog → Prop)
  ( x y z : Dog)
  (pf1 : Likes₂ x y)
  (pf2 : Likes₂ y z)
  (pf: ∀ (d g w : Dog), Likes₂ d g → Likes₂ g w → Likes₂ d w)
: Likes₂ x z :=
  pf x y z pf1 pf2

#check
  ∀ (x y z : Dog)
  (Likes : Dog → Dog → Prop),
  (Likes x y) ∧ (Likes y z) → (Likes x z)

example: ∀ (x y z : Dog)
  (Likes : Dog → Dog → Prop),
  (Likes x y) ∧ (Likes y z) → (Likes x z) := _


-- #3 Symmetric

#check ∀ (Likes : Cat → Cat → Prop), ∀ (c d : Cat), Likes c d → Likes d c


-- #4 Reflexivity

#check ∀ (c : Cat) (Likes₃ : Cat → Cat → Prop), Likes₃ c c


-- #5 If every cat likes every other cat, and c and d are cats, then c likes d.

example :
  ∀ (Likes: Cat → Cat → Prop)
  (c d : Cat), Likes c d →
  (x y : Cat) →
  Likes x y :=
λ likes c d lcd x y => _
