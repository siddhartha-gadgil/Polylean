import Polylean.GardamGroup
import Polylean.GroupRing

/-
The proof of the theorem `P` has non-trivial units.
-/

abbrev R := Fin 2

abbrev P := P.P

abbrev RP := FreeModule R P

instance ringElem: Coe P (RP) where
    coe g :=  ⟦[(1, g)]⟧

abbrev x : P := (P.x, P.e)
abbrev y : P := (P.y, P.e)
abbrev z : P := (P.z, P.e)
abbrev a : P := ((0, 0, 0), P.a)
abbrev b : P := ((0, 0, 1), P.b)

def eg : RP := x * x + y⁻¹ * b

#eval eg * eg