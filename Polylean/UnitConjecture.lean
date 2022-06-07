import Polylean.GardamGroup
import Polylean.GroupRing


/-
The proof of the theorem `𝔽₂[P]` has non-trivial units. Together with the main result of `TorsionFree` -- that `P` is torsion-free, this completes the formal proof of Gardam's theorem that Kaplansky's Unit Conjecture is false.
-/


section preliminaries

/-- definition of a unit -/
def unit {R : Type _} [Ring R] (u : R) := ∃ v : R, v * u = (1 : R)

/-- definition of being trivial, i.e., of the form `a⬝g` for `g` a group element and `a ≠ 0`-/
def trivial_element {R G : Type _} [CommRing R] [DecidableEq R] [Group G] [DecidableEq G] (x : FreeModule R G) : Prop :=
  ∃ g : G, ¬(FreeModule.coordinates g x = 0) ∧ (∀ h : G, ¬(FreeModule.coordinates h x = 0) → h = g)

abbrev P := P.P

instance ringElem {G : Type _} [Group G] [DecidableEq G] {R : Type _} [Ring R] [DecidableEq R] : Coe G (FreeModule R G) where
    coe g :=  ⟦[(1, g)]⟧

-- action of the group on the group ring by conjugation
instance {G : Type _} [Group G] [DecidableEq G] {R : Type _} [Ring R] [DecidableEq R] : SMul G (FreeModule R G) where
  sMul g x := g⁻¹ * x * g

end preliminaries

section groupelements

abbrev x : P := (P.x, P.e)
abbrev y : P := (P.y, P.e)
abbrev z : P := (P.z, P.e)
abbrev a : P := ((0, 0, 0), P.a)
abbrev b : P := ((0, 0, 0), P.b)

end groupelements

namespace Gardam

section constants

abbrev R := Fin 2

abbrev RP := FreeModule R P

/-! The components of the non-trivial unit `α` -/
abbrev one : RP := 1
def p : RP := one +  x +  y +  x*y +  z⁻¹ + x*z⁻¹ + y*z⁻¹ + x*y*z⁻¹
def q : RP := (x⁻¹*y⁻¹ : RP) + x + y⁻¹*z + z
def r: RP := one + x + y⁻¹*z + x*y*z
def s : RP  := one + x*z⁻¹ + x⁻¹*z⁻¹ + y*z⁻¹ + y⁻¹*z⁻¹

/-- the non-trivial unit `α` -/
def α := p + (q * a) + (r * b) + (s * a * b)
 
/-! The components of the inverse `α'` of the non-trivial unit `α` -/
def p' : RP := x⁻¹ * (a • p)
def q' : RP := -(x⁻¹ * q)
def r' : RP := -(y⁻¹ * r)
def s' : RP := z⁻¹ * (a • s)

end constants


section verification

/-- the inverse `α'` of the non-trivial unit `α` -/
def α' := p' + (q' * a) + (r' * b) + (s' * a * b)


/-- `α` is a unit -/
theorem α_is_unit : unit α := ⟨α', by native_decide⟩

/-- `α` is  non-trivial -/
theorem α_non_trivial : ¬ (trivial_element α) := by
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
    have ineq : -z ≠  x * y := by native_decide
    contradiction

/-- the existence of a non-trivial unit in `𝔽₂[P]` -/
theorem Gardam : ∃ g : RP, unit g ∧ ¬ (trivial_element g) := 
  ⟨α, And.intro α_is_unit α_non_trivial⟩

end verification

end Gardam

namespace Murray

abbrev R := Fin 3

abbrev RP := FreeModule R P

def one : RP := 1
def p : RP  := (one + x) * (one + y) * (z⁻¹ - z)
def q : RP := ((one + x) * (x⁻¹ + y⁻¹) * (one - z⁻¹)) + ((one + y⁻¹) * (z - z⁻¹))
def r : RP := ((one + y⁻¹) * (x + y) * (z - one)) + ((one + x) * (z - z⁻¹))
def s : RP := -one * z + ((one + x + x⁻¹ + y + y⁻¹) * (z⁻¹- one))

def p' := x⁻¹ * (a • p)
def q' := -(x⁻¹ * q)
def r' := -(y⁻¹ * r)
def s' := z⁻¹ * (a • s)

def α : RP := p + (q * a) + (r * b) + (s * a * b)
def α' : RP := p' + (q' * a) + (r' * b) + (s' * a * b)

-- works
theorem α_is_unit : unit α := ⟨α', by native_decide⟩

end Murray
