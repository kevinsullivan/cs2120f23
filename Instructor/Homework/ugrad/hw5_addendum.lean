/-!
# A few words on destructured argument declarations

Sometimes one needs to express a function as a lambda 
expression, with an an ordered pair (p : α x β) as an 
argument. To use p, one will often have to destructure
it: to *analyze* it as *(a, b)*. With names for the two
parts of (the term representing) the ordered pair, you 
can define such functions as *fst*  (just return a), 
*snd* (just return b), and *swap* (return (b, a)). 
-/


/-!
## Argument Not Analyzed

This function takes a pair; doesn't analyze it; and in
this simple example, just returns, it. Polymorphic
functions, capable of handling objects of any type,
often handle object without ever *inspecting* them.
-/
#check fun {α β : Type} (p : α × β) => p 


/-!
## Pair Analyzed As (a, b) By match Expression  

If a function has to take as an argument a single 
product object, p, that's fine; you just destructure 
p explicitly using a *match expression*. Hare are
examples using a lamdba expression for the ordered
pair swap function, taking each (a,b) pair to (b,a).
-/

#check λ {α β : Type} 
         (p : α × β)            -- pair object
         =>
        match p with            -- analyze p ...
        | (a, b) =>             -- ... as (a, b)
          (b, a)                -- return (b,a) 

-- Application of function. Expect ("Dolly", " Hello ")
#eval (λ {α β : Type}          -- function
         (p : α × β) 
         =>
        match p with
        | (a, b) => (b, a)
      )                         -- end function
      (" Hello ", "Dolly")      -- argument 


/-!
## Destructured Arguments

A great trick is to express a pair argument in already
destructured form, (a,b). Here's the swap function 
written using this syntactic feature. Note that we
have replaced *p* with *(a, b)*. That's the trick.
-/

#check fun 
        {α β : Type}          -- implicit type arguments
        ((a, b) : α × β )     -- *destructured pair, (a, b)*
        => 
        (b, a)                -- swap function is now trivial

-- And here's an example application
#eval (λ {α β : Type}         -- Expect ("Dolly", " Hello ")
      (a, b) 
      => 
      (b, a))  
      (" Hello ", "Dolly")   


/-!
## The TL;DR Takeaway

You can write function (lambda) expressions with 
ordered pairs objects as arguments, but *expressed 
in the their destructured form, *(a, b)*. You can
then write return values as functions of a and b.
-/

