namespace EnumDecide

def decideBelow (p:Nat → Prop)[DecidablePred p](bound: Nat):
  Decidable (∀ n : Nat, n < bound → p n) := 
    match bound with
    | 0 => by
      apply Decidable.isTrue
      intro n bd 
      contradiction
    | k + 1 => 
      let prev := decideBelow p k
      match prev with
      | Decidable.isTrue hyp => 
        if c:p k then 
          by
          apply Decidable.isTrue
          intro n bd
          cases Nat.eq_or_lt_of_le bd with
          | inl eql => 
            have eql' : n = k := by
                injection eql
                assumption
            simp [eql']
            assumption
          | inr lt => 
            have lt' : n < k := by
                apply Nat.le_of_succ_le_succ
                assumption
            exact hyp n lt'
        else 
          by
          apply Decidable.isFalse
          intro contra
          have lem : p k := by
            apply contra k
            apply Nat.le_refl
          contradiction
      | Decidable.isFalse hyp => by
        apply Decidable.isFalse
        intro contra
        have lem : ∀ (n : Nat), n < k → p n := by
          intro n bd
          have bd' : n < k + 1 := by
            apply Nat.le_step
            exact bd
          exact contra n bd'
        contradiction

        