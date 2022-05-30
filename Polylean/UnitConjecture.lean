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

def α := p + (q * a) + (r * b) + (s * a * b)
 
def p' : RP := x⁻¹ * (a * p * a⁻¹)
def q' : RP := -(x⁻¹ * q)
def r' : RP := -(y⁻¹ * r)
def s' : RP := z⁻¹ * (a* s * a⁻¹)

def α' := p' + (q' * a) + (r' * b) + (s' * a * b)

#eval α' * α -- not 1

#eval (a * b)⁻¹ * p * (a * b) = x⁻¹ * y⁻¹ * p -- true
#eval (a * b)⁻¹ * q * (a * b) = y * q -- true
#eval (a * b)⁻¹ * r * (a * b) = x⁻¹  * r -- true
#eval (a * b)⁻¹ * s * (a * b) = s -- true

#eval b * p * b⁻¹ = x⁻¹ * y * (a * p * a⁻¹) -- true
#eval b * q * b⁻¹ = y⁻¹  * (a * q * a⁻¹) -- true
#eval b * r * b⁻¹ = x⁻¹  * (a * r * a⁻¹) -- true
#eval b * s * b⁻¹ = (a * s * a⁻¹) -- true

def lhs₁ : RP := (x⁻¹ * (a *p * a⁻¹) * q) - (x⁻¹ *  q * (a * p * a⁻¹)) - (x⁻¹ * z⁻¹ * y⁻¹ * r * (a * s  * a⁻¹)) + (y⁻¹ * z⁻¹ * (a * s * a⁻¹) * x⁻¹ * r) 
#eval lhs₁ -- [] ; correct
def lhsTerms : List RP :=  [(x⁻¹ * (a *p * a⁻¹) * q), - (x⁻¹ *  q * (a * p * a⁻¹)), - (x⁻¹ * z⁻¹ * y⁻¹ * r * (a * s  * a⁻¹)),  (y⁻¹ * z⁻¹ * (a * s * a⁻¹) * x⁻¹ * r)] 
#eval lhsTerms 
def lhsMulA  := lhsTerms.map (fun x : RP => x * a)
#eval (p' * q) ∈ lhsTerms -- true
#eval (p' * q * a) ∈ lhsMulA -- true
#eval (q' * a * p) ∈ lhsMulA -- true
#eval (r' * b * s * a * b) ∈ lhsMulA

#eval a * b * a
#eval a
#eval a * a
#eval q
#eval (y, a⁻¹ * y * a)
#eval q * a 
#eval (x * a)
#eval α
#eval α'

#eval q
#eval q'
#eval x⁻¹
#eval y
#eval a⁻¹ * y * a

