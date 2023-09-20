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

# DEMO

## functions to "handle either case"
# f : float -> bool: (f >= 5.0)
# i : int -> bool:(i < 5)
def fge5(f) : return (f >=5.0)
def ilt5(i) : return (i < 5)

# Create four objects of our Alpha | Beta sum type
six_oh_ge_five_oh = Alpha(6.0)
four_oh_ge_five_oh = Alpha(4.0)
four_lt_five = Beta(4)
five_lt_five = Beta(5)

print(sum_elim(six_oh_ge_five_oh,  fge5, ilt5))  # expect True
print(sum_elim(four_oh_ge_five_oh, fge5, ilt5))  # expect False
print(sum_elim(four_lt_five,       fge5, ilt5))  # expect True
print(sum_elim(five_lt_five,       fge5, ilt5))  # expect False
