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
abbrev one : RP := 1

#eval (one + x⁻¹) * (one + y) = one + x⁻¹ + y + x⁻¹ * y

def eg : RP := x * x + y⁻¹ * b

#eval eg * eg

def p : RP := one +  x +  y +  x*y +  z⁻¹ + x*z⁻¹ + y*z⁻¹ + x*y*z⁻¹
def q : RP := (x⁻¹*y⁻¹ : RP) + x + y⁻¹*z + z
def r: RP := one + x + y⁻¹*z + x*y*z
def s : RP  := one + x*z⁻¹ + x⁻¹*z⁻¹ + y*z⁻¹ + y⁻¹*z⁻¹

def poly := p + q * a + r * b + s * a * b

def p' : RP := x⁻¹ * (a⁻¹ * p * a)
def q' : RP := -x⁻¹ * q
def r' : RP := -y⁻¹ * r
def s' : RP := z⁻¹ * (a⁻¹ * s * a)

def poly' := p' + q' * a + r' * b + s' * a * b

#eval a
#eval a * a
#eval q
#eval q * a -- []; wrong
#eval q * a = 0 -- false ; correct but contradicts above
#eval (q * a).normBound
#eval poly
#eval poly'
#eval poly * poly' 
#eval q
#eval q'
#eval x⁻¹
#eval y
#eval a⁻¹ * y * a
#eval p