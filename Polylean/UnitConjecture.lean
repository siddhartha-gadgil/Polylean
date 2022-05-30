import Polylean.GardamGroup
import Polylean.GroupRing

/-
The proof of the theorem `𝔽₂[P]` has non-trivial units.
-/

class Field (F : Type _) extends CommRing F, Inv F where
  left_inv : ∀ a : F, a⁻¹ * a = (1 : F)

theorem right_inv {F : Type _} [Field F] : ∀ a : F, a * a⁻¹ = (1 : F) := by
  intro a
  have left_inv : a⁻¹ * a = (1 : F) := Field.left_inv a
  rw [mul_comm] at left_inv
  assumption

def unit {R : Type _} [Ring R] (u : R) := ∃ v : R, u * v = (1 : R)

def trivial_element {R G : Type _} [CommRing R] [DecidableEq R] [Group G] [DecidableEq G] (x : FreeModule R G) : Prop :=
  ∃ g : G, ¬(FreeModule.coordinates g x = 0) ∧ (∀ h : G, ¬(FreeModule.coordinates h x = 0) → h = g)

def KaplanskyUnitConjecture (F G : Type _) [Field F] [DecidableEq F] [Group G] [DecidableEq G] := ∀ g : FreeModule F G, unit g → trivial_element g

abbrev R := Fin 2

abbrev P := P.P

abbrev RP := FreeModule R P

instance ringElem: Coe P (RP) where
    coe g :=  ⟦[(1, g)]⟧

abbrev x : P := (P.x, P.e)
abbrev y : P := (P.y, P.e)
abbrev z : P := (P.z, P.e)
abbrev a : P := ((0, 0, 0), P.a)
abbrev b : P := ((0, 0, 0), P.b)
abbrev one : RP := 1

def p : RP := one +  x +  y +  x*y +  z⁻¹ + x*z⁻¹ + y*z⁻¹ + x*y*z⁻¹
def q : RP := (x⁻¹*y⁻¹ : RP) + x + y⁻¹*z + z
def r: RP := one + x + y⁻¹*z + x*y*z
def s : RP  := one + x*z⁻¹ + x⁻¹*z⁻¹ + y*z⁻¹ + y⁻¹*z⁻¹

def α := p + (q * a) + (r * b) + (s * a * b)
 
def p' : RP := x⁻¹ * (a⁻¹  * p * a)
def q' : RP := -(x⁻¹ * q)
def r' : RP := -(y⁻¹ * r)
def s' : RP := z⁻¹ * (a⁻¹ * s * a)

def α' := p' + (q' * a) + (r' * b) + (s' * a * b)

def unitsProd := α' * α 

theorem units : unitsProd = 1 := by native_decide

theorem non_trivial : α ≠ 1 := by native_decide

theorem Gardam : ¬(KaplanskyUnitConjecture) := by admit
