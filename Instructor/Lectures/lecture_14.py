from z3 import *

# Propositional Logic (Boolean) Variables
# Python name, variable type, string name

X = Bool('X')
Y = Bool('Y')
Z = Bool('Y')

# Propositional logic expressions
# Iff is represented by equality ==

print("And expression: ", (And(X,Y)))
print("Or expression: ", (Or(X,Y)))
print("Not expression: ", Not(X))
print("Implies expression: ", Implies(X, Y))
print("Iff expression: ", (X == Y))

# In Z3, True and False are Constants

print("True is a propositional constant: ", True)
print("False is a propositional constant: ", False)

# Satisfiability Solving

print ("Solve X And Y")
solve(And(X,Y))

print ("Solve X Or Y")
solve(Or(X,Y))

print ("Solve X And Not X")
solve(And(X,(Not(X))))

print ("Solve X Or Not X")
solve(Or(X, Not(X)))

print("Solve X => False")
solve(Implies(X, False))

print ("Solve (X => False) /\ X")
solve(And(Implies(X, False)), X)

print("Solve (X => Y) /\ (Y => Z)")
solve(And(Implies(X,Y),Implies(Y,Z)))

print("Solve implicit conjunction of constraints")
solve(Implies(X, Y), 
      Or(Not(X), Z), 
      Z == Not(Y))

# Simplification

print ("Simplify X and Y and X")
print (simplify (And(X, Y, X)))

