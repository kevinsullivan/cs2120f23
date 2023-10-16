# Discrete Mathematics Through Type Theory

This course is by Kevin Sullivan, University of Virginia Department of Computer Science. It is intended for second year undergraduate computer science majors. It assumes that students have had one course in general programming, e.g., in Python or Java.

## Goals

The goal of this course is to provide early students of computer science with a firm grasp of formal reasoning (formal logic, set theory, properties of relations, proof theory, etc.) in a way that both leverages and resonates with their intrinsic interests in programming and computation.

## Hypothesis

The hypothesis behind the design of this course is that for students in computer science, in particular, the most natural and rewarding path to understanding abtract mathematical logic and proof starts from their interest in and intuition for programing. As an example, a milestone in this course is a *proof* of several of DeMorgan's lawsthrough the construction of general polymorphic programs operating on product, sum, and function-typed values.

## Method

This course adopts dependent type theory as an underlying framework for teaching discrete mathematics. We use the Lean prover as supported in a Docker image accessed through the VS Code IDE. The choice of Lean is based in part on its validated capacity for expressive formalization of abstract mathematics and on the fact that it's emerging as a capable general-purpose functional programming language and system, as well.

We introduce constructive reasoning by way of programming with product, sum, and function types. We cover inductive data definitions and recursive functions. On that foundation, we embed propositional logic syntax and semantics and automated semantic evaluation and SAT solving in Lean. We then gives students a fun break at the mi-term point solving puzzles in Logic using the Z3 SMT solver. 

The course then shifts to teaching predicate logic using its embedding in Lean. Topics include universal and existential quantification and associated reasoning principles. New concept at this point include the Prop type universe and dependent pairs and, to encode predicates, dependent function types. We introduce tactic-based construction of terms at this point as well.

From there, on the foundation constructed so far, the course moves into proof strategies (direct, by negation, by induction), then to set theory (membership predicates) and properties of relations. For example, from the basic axioms of equality, we derive proofs of symmetry and transitivity.

Stay tuned for additional updates as the course continues through the Fall 2023 semester.

## Copyright

Copyright 2023 Kevin J Sullivan. All Rights Reserved.

If you wish to use these materials, for teaching, profit, or other prupose, please contact the author, Kevin Sullivan, at <sullivan@virginia.edu>. He is open to others' use of these materials but at a minimum wishes to track their use.

Cite as: Sullivan, K., Discrete Mathematics Through Type Theory, 2023, currently available at URL, <https://computingfoundations.org>.
