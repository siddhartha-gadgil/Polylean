import Mathlib.Algebra.Field.Basic
import Polylean.TorsionFree
import Polylean.GroupRing


/-
The proof of the theorem `𝔽₂[P]` has non-trivial units. Together with the main result of `TorsionFree` -- that `P` is torsion-free, 
this completes the formal proof of Gardam's theorem that Kaplansky's Unit Conjecture is false.
-/


section Preliminaries

/-- definition of being trivial, i.e., of the form `a⬝g` for `g` a group element and `a ≠ 0` -/
def trivialElem {R G : Type _} [Ring R] [DecidableEq R] [Group G] [DecidableEq G] (x : FreeModule R G) : Prop :=
  ∃! g : G, FreeModule.coordinates g x ≠ 0

abbrev 𝔽₂ := Fin 2

instance : Field 𝔽₂ where
  inv := id
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := fun
        | 0, h => by contradiction
        | 1, _ => rfl
  inv_zero := rfl
  div_eq_mul_inv := by decide

instance ringElem: Coe P.P (𝔽₂[P.P]) where
    coe g := ⟦[(1, g)]⟧

end Preliminaries

section Constants

namespace P

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

end Gardam

end Constants


section Verification

namespace Gardam

open P

/-- the inverse `α'` of the non-trivial unit `α` -/
def α' := p' + (q' * a) + (r' * b) + (s' * a * b)

/-- `α` is  non-trivial -/
theorem α_nonTrivial : ¬ (trivialElem α) := by
    intro contra
    let ⟨g, p⟩ := contra
    let eqg := p.right
    have eq₁ : -z = g := by 
      apply eqg
      native_decide
    have eq₂ : x * y = g := by
      apply eqg
      native_decide
    rw [← eq₂] at eq₁
    contradiction

/-- The statement of Kaplansky's Unit Conjecture. -/
def UnitConjecture : Prop :=
  ∀ {F : Type _} [Field F] [DecidableEq F] 
  {G : Type _} [Group G] [DecidableEq G] [TorsionFree G],
    ∀ u : (F[G])ˣ, trivialElem (u : F[G])

/-- The existence of a non-trivial unit in `𝔽₂[P]`. -/
theorem Counterexample : {u : (𝔽₂[P])ˣ // ¬(trivialElem u.val)} := 
  ⟨⟨α, α', by native_decide, by native_decide⟩, α_nonTrivial⟩

/-- Giles Gardam's result - Kaplansky's Unit Conjecture is false. -/
theorem Result : ¬ UnitConjecture :=
   λ conjecture => Counterexample.prop <| conjecture (F := 𝔽₂) (G := P) Counterexample.val

end Gardam

end Verification