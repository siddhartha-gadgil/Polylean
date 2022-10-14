import Polylean.Complexes.TwoComplex

instance FundamentalGroupoid {V : Type _} [CV : TwoComplex V] : Groupoid V where
  hom := λ u v => Quotient $ Path.Homotopy.setoid u v
  id := λ v => .mk' .nil
  comp := .lift₂ (λ p q => .mk' $ .append p q) $ λ _ _ _ _ h h' => 
            Quotient.sound $ Path.Homotopy.mul_sound h h'
  inv := .lift (λ p => .mk' p.inverse) λ _ _ h => 
            Quotient.sound $ Path.Homotopy.inv_sound h

  idComp := sorry
  compId := sorry
  compAssoc := sorry
  invComp := sorry
  compInv := sorry
