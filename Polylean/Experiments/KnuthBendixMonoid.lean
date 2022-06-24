import Aesop
import Mathlib.Init.Algebra.Order

abbrev FreeMonoid (α : Type _) [LinearOrder α] := List α

namespace FreeMonoid

variable (α : Type _) [LinearOrder α] [DecidableEq α]

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

namespace List

variable {α : Type _} [DecidableEq α]

def isPrefix : List α → List α → Bool
  | [], _ => true
  | _::_, [] => false
  | hp :: tp, hl :: tl => (hp = hl) && (isPrefix tp tl)

#eval isPrefix [1, 3] [1, 2, 3]

def prefixTail : List α → List α → Option (List α)
  | [], l => Option.some l
  | _::_, [] => Option.none
  | hp :: tp, hl :: tl =>
    if hp = hl then
      prefixTail tp tl
    else
      Option.none

theorem prefixTailMatch : ∀ (p l t : List α), (prefixTail p l = Option.some t) ↔ (isPrefix p l ∧ (l = p ++ t)) := sorry

def unify : List α → List α → List α × List α × List α
  | [], l => ([], [], l)
  | l, [] => (l, [], [])
  | h :: t, l =>
    match prefixTail (h :: t) l with
      | Option.some tl => ([], h :: t, tl)
      | Option.none =>
        match unify t l with
          | (a, b, c) => (h :: a, b, c)

theorem unifySplit : ∀ p l : List α,
  match unify p l with
    | (a, b, c) => (a ++ b = p) ∧ (b ++ c = l) := sorry


end List
