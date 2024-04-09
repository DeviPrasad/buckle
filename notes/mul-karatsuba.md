
### GNU GMP Chapter on Karatsuba Multiplication
https://gmplib.org/manual/Karatsuba-Multiplication#Karatsuba-Multiplication

### Karatsuba's multiplication
https://www.more-magic.net/posts/numeric-tower-part-3.html#karatsubas-multiplication
Let's say we want to multiply two big-nums of two limbs, x[1,2] and y[1,2] in base B. 
The result is of course xy. Rephrased as an equation:

`` xy = (x₁·B + x₂) · (y₁·B + y₂)``

This can be written as
`` xy = (x₁·y₁)·B² + (x₁·y₂ + x₂·y₁)·B + x₂·y₂ ``
if we call these three components a, b and c, then xy = a·B² + b·B + c.


https://github.com/rvelthuis/DelphiBigNumbers/blob/master/Source/Velthuis.BigIntegers.pas
