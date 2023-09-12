# The usual way to define a square function
def squar(x) : return(x**2)
print(squar(5))

# Defining square with a Python lambda expression
square = lambda x : x**2
print(square(5))  # Expect: 25

# You can write function expression inline!
print((lambda x : x**2)(6))

# Functions are passable values in Python, too
# Here's our apply2 function in Python
def apply2(f) :
# "A function that takes x and returns f(f(x))"
    return lambda x : f(f(x))

# A function that cubes its argument twice (grows fast!)
print(apply2(lambda x: x**3)(2))

# The composition function in Python! 
def compose(g,f) :
# Returns a function that takes an argument a and returns g(f(a))
    return (lambda a : g(f(a)))
# Compare this with the final definition in class notes Chapter 5

# Composition of functions square after cube
# The cube function is passed as an anonymous (unnamed) lambda
square_after_cube = compose(square, (lambda x : x**3))
print(square_after_cube(2))

# Composition of functions, cube after square
cube_after_square = compose((lambda x : x**3),(lambda x : x**2))
print(square_after_cube(3))