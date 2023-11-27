/-!
Put your answers in a file called hw10.lean.

Express the following propositions formally in Lean.

1. Every dog likes some cat.
-/

variable
  (Dog Cat : Type)
  (Likes₁ : Dog → Cat → Prop)

#check ∀ (d : Dog) (c: Cat), Likes₁ d c

/-!
2. If any dog, d, likes any dog, g, and that dog, g, likes any dog, w, then d likes w.
-/

variable
  (Likes₂ : Dog → Dog → Prop)

#check ∀ (d g w : Dog), Likes₂ d g → Likes₂ g w → Likes₂ d w

/-!
3. If any cat, c, likes any cat, d, then d also likes c.
-/

variable
  (Likes₃ : Cat → Cat → Prop)

#check ∀ (c d : Cat), Likes₃ c d → Likes₃ d c

/-!
4. Every cat, c, likes itself.
-/

#check ∀ (c : Cat), Likes₃ c c


/-!
5. If every cat likes every other cat, and c and d are cats, then c likes d.
-/

#check (∀ (x y : Cat), Likes₃ x y) → (∀ (c d : Cat), Likes₃ c d)

/-!
Finally, give a formal proof in Lean of the proposition in problem #5.
-/

example : (∀ (x y : Cat), Likes₃ x y) → (c d : Cat) → Likes₃ c d
| h, c, d => h c d
