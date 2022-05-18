import Polylean.GroupAction

/-
Metabelian groups are group extensions `1 → K → G → Q → 1` with both the kernel and the quotient abelian. Such an extension is determined by data:

* a group action of `Q` on `K`
* a cocyle `c: Q → Q → K`

We have to define the cocycle condition and construct a group structure on a structure extending `K × Q`. The main step is to show that the cocyle condition implies associativity.
-/

class Cocycle {Q K : Type _} [AddCommGroup Q] [AddCommGroup K] [α : AddCommGroup.ActionByAutomorphisms Q K]
  (c : Q → Q → K) where
  leftId : ∀ q : Q, c 0 q = (0 : K)
  rightId : ∀ q : Q, c q 0 = (0 : K)
  invEq : ∀ q : Q, c q (-q) = c (-q) q
  cocycleCondition : ∀ q q' q'' : Q, c q q' + c (q + q') q'' = q • c q' q'' + c q (q' + q'')
