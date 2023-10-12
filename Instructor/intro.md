# Discrete Mathematics Through Type Theory and Computation

This course is by Kevin Sullivan, University of Virginia Department of Computer Science. It is intended for second year undergraduate computer science majors. It assumes that students have had one course in general programming, e.g., in Python or Java.

## Goals

The goal of this unique course is to provide early students of computer science with a firm grasp of formal reasoning (formal logic, set theory, properties of relations, proof theory, etc.) in a way that both leverages and resonates with their demonstrated intrinsic interest in programming and automated computation.

## Pedagogical Hypothesis

The working hypothesis behind the design of this course is that for students in computer science, in particular, the easiest path to understanding abtract mathematical logic and proof starts from their interest in and understanding of programing. As an example, one milestone in this course is the "proof" of several of DeMorgan's laws and most of the usual introduction and elimination principles through the construction of general polymorphic programs operating on product, sum, and special function-typed values.

## Pedagogical Method

To this end, the course adopts dependent type theory as an underlying framework. We use the Lean prover as supported in a Docker image accessed through the VS Code IDE.

We sneak in constructive reasoning by way of programming with product, sum, and function types; cover inductive data definitions and recursive functions; embed propositional logic syntax and semantics and automated SAT solving in Lean; and then gives students a fun break solving puzzles in Logic using the Z3 SMT solver. That takes the course to the mid-term.

From there, having established intuition for constructive logic through programming, the course shifts to teaching predicate logic using its embedding in Lean. Topics include universal and existential quantification. Students already understand function and product types and really only need to learn about dependent pair types. We introduce tactic-based construction of terms at this point as well.

From there, on the foundation constructed so far, the course moves into proof strategies (direct, by negation, by induction), then to set theory (membership predicates) and properties of relations.

Stay tuned for additional updates.

## Copyright

Copyright 2023 Kevin J Sullivan. All Rights Reserved.

If you wish to use these materials whether for teaching, profit, or other prupose, please contact the author, Kevin Sullivan, at <sullivan@virginia.edu>. He is open to others' use of these materials but at a minimum wishes to track their use and establish paths for feedback.

Cite as: Sullivan, K., Discrete Mathematics Through Type Theory and Computation, 2023, currently available at URL, <https://computingfoundations.org>.
