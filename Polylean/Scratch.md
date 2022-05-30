Free module over a ring `R` over a set `X`. It is assumed that both `R` and `X` have decidable equality. This is to obtain decidable equality for the elements of the module, which we do. We choose our definition to allow both such computations and to prove results.

The definition is as a quotient of *Formal Sums*, which are simply lists of pairs `(a,x)` where `a` is a coefficient in `R` and `x` is a term in `X`. We associate to such a formal sum a coordinate function `X → R`. We see that having the same coordinate functions gives an equivalence relation on the formal sums. The free module is then defined as the corresponding quotient of such formal sums.

We also define the module structure, which we will use to define *Group Rings*.