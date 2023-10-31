from z3 import *

X = Real('X')
Y = Real('Y')
s = Solver()
s.add(X**2 + Y**2 == 1)
if (s.check() == sat):
    m = s.model()
print(m)