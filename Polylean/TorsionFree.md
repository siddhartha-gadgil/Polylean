# Proving `P` is torsion free

This is a mostly mathematical sketch of a way of proving that `P` is torsion-free. Here we use the following definition.

__Definition:__ We say that a group $G$ is torsion free if for all $n\in\mathbb{N}$, $g\in G$, $g^n = e$ implies $g= e$.

The proof can be viewed as having three main parts.

1. Formula for the action of `Q` on `K`.
2. Formula for square, including special form.
3. Formula for the power of an element of the form `((a, b, c), (0, 0))`.
4. Deduction of torsion freeness for `P`.

## Formula for the action of `Q` on `K`

There are two approaches one can take:

### First Approach

* Show that the formulas for `action` give homomorphisms.
* Using `uniqueExtension, show that `action = action'` - perhaps `by decide` will work here after introducing instances.

### Second Approach

For a homomorphism $f: K \to K$, show:

* `f(a, b, c) = f(a, 0, 0) + f(0, b, 0) + f(0, 0, c)`
* If `f(1, 0, 0) = (a, b, c)`, then for an integer `n`, `f(n, 0, 0) = (na, nb, nc)` and the analogues. These can be proved by induction for natural numbers `n` and negation to extend to integers.
* Deduce the formulas for the action for the 4 elements of `Q`.

## Formula for square

* From the action, the formula for square can be deduced.
* This is best expressed as a function  `s: Q → K → K` so that the square of an element `(k, q)` is `(f q k, 0)`. 

## Formula for the power of  `((a, b, c), (0, 0))`

## First approach

* Note that the action by `(0, 0)` is the identity (for instance this is part of the definition of a group action).
* Also note that the `c(0, 0)= (0, 0, 0)`.
* Conclude that `((a, b, c), (0, 0)) ⬝ ((a', b', c'), (0, 0)) = ((a + a', b + b', c + c'), (0, 0))`.
* By induction deduce that the `n`th power of `((a, b, c), (0, 0))` is `((na, nb, nc), (0, 0))`

## Second approach

### Show that $\mathbb{Z}$ is an integral domain.

#### The sign function

Define the sign function $$\sigma : \mathbb{Z} \to \mathbb{Z}/3\mathbb{Z}$$ and show that it is multiplicative with the pre-image of zero in $\mathbb{Z}/3\mathbb{Z}$ being the singleton zero set in $\mathbb{Z}$. An analysis by cases on $\mathbb{Z}/3\mathbb{Z}$ will show that $$0 = \sigma(m \cdot n) = \sigma(m) \cdot \sigma(n) \implies \sigma(m) = 0 \wedge \sigma(n) = 0 \implies m = 0 \wedge n = 0$$.

#### Induction on the structure of $$\mathbb{Z}$$.

Proving the corresponding fact for natural numbers may be easier with help from facts about natural numbers known to Lean. With a helper lemma stating that `Int.negSucc m * a = 0 <--> Int.ofNat (m + 1) * a`, it should be possible to easily prove all the cases by induction. 

### Show as a direct corollary that $\mathbb{Z}$ is torsion-free.

### Show that the product of torsion-free groups is torsion-free.

### Define kernels, images and isomorphisms of groups.

### Show that any group isomorphic to a torsion-free group is torsion-free.

### Show that the kernel `K` in the cocycle construction is isomorphic to its image in `K x Q`.

In particular, this shows that the sub-group of square elements is isomorphic to $\mathbb{Z}^3$.

### Deduce that the image of `K` in `K x Q` is torsion-free.

This will be an `inferInstance` that will follow from the previous results. 


## Deduction of torsion freeness


* Suppose we have the `n`th power of `g` trivial, let `h= ((a, b, c), (0, 0))` be the square of `g`. Then the `n`th power of `h` vanishes.
* Deduce from the power formula that `h` is trivial.
* Deduce from the squaring formula that `g` is trivial; consider cases and use `mod 2` in the non-trivial cases.
