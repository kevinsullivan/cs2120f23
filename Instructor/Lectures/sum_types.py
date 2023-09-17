# Credit https://stackoverflow.com/questions/16258553/how-can-i-define-algebraic-data-types-in-python

from dataclasses import dataclass

@dataclass
class Alpha:
    a: float


@dataclass
class Beta:
    b: int

@dataclass
class Gamma:
    c: bool

Either = Alpha | Beta

def sum_elim (one_of : Either, a2c, b2c) : 
    match one_of :
        case Alpha(a): 
            return a2c(a)
        case Beta(b): 
            return b2c(b)

# demo:

#  Boolean-returning predicate on float values (f >= 5.0)
def fge5(f) : return (f >=5.0)

# Boolean-returning predicate on int values (i < 5)
def ilt5(i) : return (i < 5)

def bool2goodbad(b):
    if (b):
        return ("good")
    else:
        return("bad")
  
f5 = Alpha(5.0)
f4 = Alpha(4.0)
i1 = Beta(4)
i2 = Beta(5)

print(bool2goodbad(sum_elim(f5, fge5, ilt5)))  # expect good
print(bool2goodbad(sum_elim(f4, fge5, ilt5)))  # expect bad
print(bool2goodbad(sum_elim(i1, fge5, ilt5)))  # expect good
print(bool2goodbad(sum_elim(i2, fge5, ilt5)))  # expect bad
