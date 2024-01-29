
'''
This code shows how you can take what you've
learned using general type theory in Lean and
apply it in everyday programming in Python. In
particular, we introduce lambda expressions and
higher-order functions in Lean and show how to
implement the apply2 and compose functions we
developed in lean. 
'''

# The usual way to define a square function
def square(x) : return(x**2)
print(square(5))                # expect 25

# Here's square with a Python lambda expression
square = lambda x : x**2
print(square(5))                # Expect: 25

# We apply an anonymous lambda to 6; expect 36 
print((lambda x : x**2)(6))

# Here's apply2 in Python; f is a function argument
def apply2(f) :
# we return a function that applies f twice to its argument
    return lambda x : f(f(x))

# A function that cubes its argument twice (grows fast!)
print(apply2(lambda x: x**3)(2))  # Expect (2^3)^3 = 512

# Here then is compose in Python; g and f are functions 
def compose(g,f) :
    return (lambda a : g(f(a)))


# Examples
square_after_cube = compose(square, (lambda x : x**3))
print(square_after_cube(2))         # Expect 64 

cube_after_square = compose((lambda x : x**3),(lambda x : x**2))
print(square_after_cube(3))         # Expect (3^2)^3 = 729

'''
We expect that the programming and reasoning principles
you learn in Discrete Math and Theory will prove to be
exceptionally valuable to you no matter what languages 
you are ultimately expected to program in.
'''