# This file introduces the NoneType type and its single value, None

# None is a (and is the only) value of class NoneType
print(type(None))               # expect NoneType

# Functions without explicit returns implicitly return None
def return_nothing (x : str) :
    print(x)                    # no return statement here
print(return_nothing("Hi!"))    # expect "Hi!" then None

# You can use None to represent an error value
# For example, here's a natural number predecessor function
# that returns None to signal error if its argument is <= 0
def nat_pred (n : int) :
    if (n <= 0) :
        return None
    else :
        return (n - 1)
print(nat_pred(2))              # expect 1
print(nat_pred(1))              # expect 0
print(nat_pred(0))              # expect None (undefined)