
### Good Explanation and Description of Implementation
https://www.more-magic.net/posts/numeric-tower-part-3.html


## Algorithmica
https://en.algorithmica.org/

### Number Theory
https://en.algorithmica.org/hpc/number-theory/
https://en.algorithmica.org/hpc/number-theory/montgomery/

### Integer Division
https://en.algorithmica.org/hpc/arithmetic/division/

### libdivide
https://github.com/ridiculousfish/libdivide
libdivide.h is a header-only C/C++ library for optimizing integer division.


https://mail.openjdk.org/pipermail/core-libs-dev/2013-November/023501.html
BigInteger Burnikel-Ziegler division algorithm crossover heuristic

Dmitry Nadezhin dmitry.nadezhin at gmail.com
Sat Nov 23 12:04:57 UTC 2013

Time complexity of Knuth divide a/b=q approximately the same as
complexity of school multiplication b*q and is
length(b)*length(q) = length(b) * (length(a) - length(b)).
So the new heuristic seems reasonable for me.

