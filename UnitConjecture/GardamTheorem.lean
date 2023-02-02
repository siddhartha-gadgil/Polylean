import Mathlib.Algebra.Field.Basic
import UnitConjecture.TorsionFree
import UnitConjecture.GroupRing


/-!

## Giles Gardam's result

The proof of the theorem `𝔽₂[P]` has non-trivial units. Together with the main result of `TorsionFree` -- that `P` is torsion-free, 
this completes the formal proof of Gardam's theorem that Kaplansky's Unit Conjecture is false.
-/


section Preliminaries

/-! ### Preliminaries -/

/-- The definition of an element of a free module being trivial, i.e., of the form `k•x` for `x : X` and `k ≠ 0`. -/
def trivialElem {R X : Type _} [Ring R] [DecidableEq X] (a : FreeModule R X) : Prop :=
  ∃! x : X, FreeModule.coordinates x a ≠ 0

/-- The statement of Kaplansky's Unit Conjecture:
The only units in a group ring, when the group is torsion-free and the ring is a field, are the trivial units. -/
def UnitConjecture : Prop :=
  ∀ {F : Type _} [Field F] [DecidableEq F] 
  {G : Type _} [Group G] [DecidableEq G] [TorsionFree G],
    ∀ u : (F[G])ˣ, trivialElem (u : F[G])

/-- The finite field on two elements. -/
abbrev 𝔽₂ := Fin 2

instance : Field 𝔽₂ where
  inv := id
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := fun
        | 0, h => by contradiction
        | 1, _ => rfl
  inv_zero := rfl
  div_eq_mul_inv := by decide

instance ringElem : Coe P (𝔽₂[P]) where
    coe g := ⟦[(1, g)]⟧

end Preliminaries

section Constants

namespace P

/-!
The main constants of the group `P`.
-/

abbrev x : P := (K.x, Q.e)
abbrev y : P := (K.y, Q.e)
abbrev z : P := (K.z, Q.e)
abbrev a : P := ((0, 0, 0), Q.a)
abbrev b : P := ((0, 0, 0), Q.b)

end P

namespace Gardam

open P

/-! The components of the non-trivial unit `α`. -/
def p : 𝔽₂[P] := (1 : 𝔽₂[P]) +  x +  y +  x*y +  z⁻¹ + x*z⁻¹ + y*z⁻¹ + x*y*z⁻¹
def q : 𝔽₂[P] := (x⁻¹*y⁻¹ : 𝔽₂[P]) + x + y⁻¹*z + z
def r : 𝔽₂[P] := (1 : 𝔽₂[P]) + x + y⁻¹*z + x*y*z
def s : 𝔽₂[P] := (1 : 𝔽₂[P]) + x*z⁻¹ + x⁻¹*z⁻¹ + y*z⁻¹ + y⁻¹*z⁻¹

/-- The non-trivial unit `α`. -/
def α : 𝔽₂[P] := p + (q * a) + (r * b) + (s * a * b)
 
/-! The components of the inverse `α'` of the non-trivial unit `α`. -/
def p' : 𝔽₂[P] := x⁻¹ * (a⁻¹  * p * a)
def q' : 𝔽₂[P] := -(x⁻¹ * q)
def r' : 𝔽₂[P] := -(y⁻¹ * r)
def s' : 𝔽₂[P] := z⁻¹ * (a⁻¹ * s * a)

/-- The inverse `α'` of the non-trivial unit `α`. -/
def α' : 𝔽₂[P] := p' + (q' * a) + (r' * b) + (s' * a * b)

end Gardam

end Constants


section Verification

/-! 
### Verification

The main verification of Giles Gardam's result. 
-/

namespace Gardam

open P

/-- A proof that `α` is non-trivial. -/
theorem α_nonTrivial : ¬ (trivialElem α) := by
    intro ⟨g, _, (eqg : ∀ y, α.coordinates y ≠ 0 → y = g)⟩
    have : z⁻¹ = g := by
      apply eqg; native_decide
    have : x * y = g := by
      apply eqg; native_decide
    have : z⁻¹ = x * y := by
      refine' Eq.trans _ (Eq.symm _) <;> assumption
    simp at this

/-! The fact that the counter-example `α` is in fact a unit of the group ring `𝔽₂[P]` is verified by 
  computing the product of `α` with its inverse `α'` and checking that the result is `(1 : 𝔽₂[P])`.

  The computational aspects of the group ring implementation and the Metabelian construction are used here. -/

/-- A proof of the existence of a non-trivial unit in `𝔽₂[P]`. -/
def Counterexample : {u : (𝔽₂[P])ˣ // ¬(trivialElem u.val)} := 
  ⟨⟨α, α', by native_decide, by native_decide⟩, α_nonTrivial⟩

/-- Giles Gardam's result - Kaplansky's Unit Conjecture is false. -/
theorem GardamTheorem : ¬ UnitConjecture :=
   fun conjecture => Counterexample.prop <| 
    conjecture (F := 𝔽₂) (G := P) Counterexample.val

end Gardam

end Verification