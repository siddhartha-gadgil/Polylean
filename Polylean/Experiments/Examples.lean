import Polylean.Experiments.FreeAbelianMeta

/-
This file contains examples of the abelian group simplification tactic in action.

This is still work in progress, so the verbose proofs below will eventually be bundled up together into a tactic and completely automated.

The purpose of this tactic is to simplify expressions in Abelian groups and prove basic equations.
The key idea here is that to prove an equation such as `{A : Type} → [AddCommGroup A] → ∀ x y : A, x + y - x - y + x = x` involving $n$ variables for all Abelian groups,
it suffices to verify it by direct computation in `ℤⁿ` for the $n$ basis elements `{(0, 0, …, i, 0, 0)}`. The reason is that `ℤⁿ` is a free group,
so given any elements `x₁, x₂, …, xₙ` in a specific group `A`, there is a unique homomorphism taking the generators of `ℤⁿ` to the chosen elements.

In the example above, it is easy to verify that `(1, 0) + (0, 1) - (1, 0) - (0, 1) + (1, 0) = (1, 0)` by a computation. Given any elements `a` and `b` in an Abelian group `A`,
applying the unique homomorphism `ϕ : ℤ² → A` taking `(1, 0)` to `a` and `(0, 1)` to `b` to this equation yields a proof that `a + b - a - b + a = a`. This allows one to prove equations in
Abelian groups without any explicit commutativity and associativity rewrites, and consequently the resulting proofs are quite short.
-/


/- This example shows that the expression on the left reduces to the one on the right -/
example {x y z : ℤ} : x + x + y - x - y + z - x = z := by
    have p := freeGroupEq# (x + x + y - x - y + z - x) -- a proof that the term is the image of the free group element `(0, 0, 1)`
    rw [p, map_free_elem] -- remove the induced homomorphism from the picture
    -- expand out and simplify (routine steps that can be automated)
    simp [List.sum]
    rw [SubNegMonoid.gsmul_zero', zero_add, SubNegMonoid.gsmul_zero', zero_add, SubNegMonoid.gsmul_one]


/- An example in a general Abelian group -/
example {A : Type _} [AddCommGroup A] {a b : A} : (a + b) - (b - a) - a = a := by
  have p := freeGroupEq# ((a + b) - (b - a) - a) -- a proof that the term is the image of the free group element `(1, 0)`
  rw [p, map_free_elem] -- remove the induced homomorphism from the picture
  -- routine simplification
  simp [List.sum, SubNegMonoid.gsmul_one]


/- An example where both sides of the equality are unreduced (not completely implemented) -/
example {a b : ℤ} : a + b - a - b = b - b + a - a := by
  have pₗ := freeGroupEq# (a + b - a - b) -- a simpler expression for the left side
  have pᵣ := freeGroupEq# (b - b + a - a) -- a simpler expression for the right side
  rw [pₗ, pᵣ, map_free_elem, map_free_elem] -- remove the induced homomorphisms from the picture
  -- routine simplification
  simp [List.sum]
  rw [SubNegMonoid.gsmul_zero', SubNegMonoid.gsmul_zero']


/- A more complicated example involving five variables -/
example {A : Type _} [AddCommGroup A] {a b c d e : A} : a + b - c - d + e - a + b + c - a - e + a - b + d - b = 0 := by
  have p := freeGroupEq# (a + b - c - d + e - a + b + c - a - e + a - b + d - b) -- a proof that the given expression is the image of `0 : ℤ⁵`
  rw [p, map_free_elem] -- removing the induced homomorphism from the picture
  -- routine simplification
  simp [List.sum]
