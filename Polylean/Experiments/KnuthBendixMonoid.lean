import Aesop
import Mathlib.Init.Algebra.Order

abbrev FreeMonoid (α : Type _) [LinearOrder α] := List α

namespace FreeMonoid

variable (α : Type _) [LinearOrder α]

def lexOrder : FreeMonoid α → FreeMonoid α → Prop
  | _ , [] => False
  | [],  _ => True
  | List.cons h t, List.cons h' t' =>
    if h < h' then
      True
    else if h' < h then
      False
    else
      lexOrder t t'

end FreeMonoid
