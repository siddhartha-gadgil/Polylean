import Mathlib.Algebra.Ring.Basic

/-
Free module over a ring `R` which may be assumed to be commutative, will eventually be $Z/2`$. 

Outline:

* Define formal sums; coordinates of formal sums.
* Define the relation corresponding to equal coordinates and prove that it is an equivalence relation.
* Define the free module as a quotient of the above relation, via setoids.
* Introduce an inductive type giving the elementary relations, i.e., single moves.
* Define an auxiliary quotient by this relation (which is not an equivalence relation); and an auxiliary equivalence relation corresponding to this quotient.
* Show that coefficients are equal if and only if formal sums satisfy the auxiliary relation.
* Deduce that the auxiliary relation is the original relation (may not need to make this explicit).
* Deduce a universal property and construct the sum and product operations : these depend on each other, so one may need a weaker version of the universal property first. Alternatively, the operations may be constructed as special cases of the universal property.
-/

