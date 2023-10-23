from z3 import *

# Propositional Logic (Boolean) Variables
# Python name, variable type, string name

X = Bool('X')
Y = Bool('Y')
Z = Bool('Z')

# Propositional logic expressions
# Iff is represented by equality ==

print("And expression: ", (And(X,Y)))
print("Or expression: ", (Or(X,Y)))
print("Not expression: ", Not(X))
print("Implies expression: ", Implies(X, Y))
print("Iff expression: ", (X == Y))
print("True expression: ", True)
print("False expression: ", False)


# In Propositional Logic in Z3, True and False are Constant Expressions 

print("Simplifying X /\ True: ", simplify(And(X, True)))
print("Simplifying X \/ False: ", simplify(Or(X, False)))

# Satisfiability Solving

print ("Solving X /\ Y")
solve(And(X,Y))

print ("Solving X \/ Y")
solve(Or(X,Y))

print ("Solving X /\ ~X")
solve(And(X,(Not(X))))

print ("Solving X \/ ~X")
solve(Or(X, Not(X)))

# Think about this one. The implication being true says what about X?
print("Solving X => False")
solve(Implies(X, False))

print ("Solving (X => False) /\ X")
solve(And(Implies(X, False)), X)

print("Solve (X => Y) /\ (Y => Z)")
solve(And(Implies(X,Y),Implies(Y,Z)))

print("Solve a set of constraints")
solve(Implies(X, Y), 
      Or(Not(X), Z), 
      Z == Not(Y))

# There's no validity checker, but it's easy to make one
# Expression e is valid if true under every interpretation
# That's equivalent to ~e being false under every interpretation
# Z3 will tell us if an expression is "unsat"
# Just check to see if ~e is unsat; if so then e is valid

print("Unsatisfiability of negation, ~(X \/ ~X), means (X \/ ~X) is valid.")
solve(Not(Or(X,Not(X))))

# Simplification

print ("Simplify X and Y and X")
print (simplify (And(X, Y, X)))

X = Int("X")
Y = Int("Y")
solve (X > 2, X < 10, Y == X + 1)

