Look for `P.PGrp.proof_1` on the two sides

```
@Eq.{1} P.P
  (@Prod.mk.{0, 0} P.K P.Q
    (@HAdd.hAdd.{0, 0, 0} P.K P.K P.K
      (@instHAdd.{0} P.K
        (@AddZeroClass.toAdd.{0} P.K
          (@AddMonoid.toAddZeroClass.{0} P.K
            (@SubNegMonoid.toAddMonoid.{0} P.K
              (@AddGroup.toSubNegMonoid.{0} P.K
                (@AddCommGroup.toAddGroup.{0} P.K
                  (@DirectSum.directSum.{0, 0} Int (Prod.{0, 0} Int Int)
                    (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
                    (@DirectSum.directSum.{0, 0} Int Int
                      (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
                      (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))))))))))
      (@HAdd.hAdd.{0, 0, 0} P.K P.K P.K
        (@instHAdd.{0} P.K
          (@AddZeroClass.toAdd.{0} P.K
            (@AddMonoid.toAddZeroClass.{0} P.K
              (@SubNegMonoid.toAddMonoid.{0} P.K
                (@AddGroup.toSubNegMonoid.{0} P.K
                  (@AddCommGroup.toAddGroup.{0} P.K
                    (@DirectSum.directSum.{0, 0} Int (Prod.{0, 0} Int Int)
                      (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
                      (@DirectSum.directSum.{0, 0} Int Int
                        (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
                        (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))))))))))
        k
        (@SMul.sMul.{0, 0} P.Q P.K
          (@AddCommGroup.Action.toSMul.{0, 0} P.Q P.K
            (@DirectSum.directSum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Ring.toAddCommGroup.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@CommRing.toRing.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@instCommRingFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) P.PGrp.proof_1)))
              (@Ring.toAddCommGroup.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@CommRing.toRing.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@instCommRingFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) P.PGrp.proof_1))))
            (@AddCommGroup.ActionByAutomorphisms.toAction.{0, 0} P.Q P.K
              (@DirectSum.directSum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@Ring.toAddCommGroup.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@CommRing.toRing.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@instCommRingFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) P.PGrp.proof_1)))
                (@Ring.toAddCommGroup.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@CommRing.toRing.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@instCommRingFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) P.PGrp.proof_1))))
              (@DirectSum.directSum.{0, 0} Int (Prod.{0, 0} Int Int)
                (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
                (@DirectSum.directSum.{0, 0} Int Int
                  (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
                  (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))))
              P.P_action))
          q k'))
      (P.cocycle q q'))
    (@HAdd.hAdd.{0, 0, 0} P.Q P.Q P.Q
      (@instHAdd.{0} P.Q
        (@AddZeroClass.toAdd.{0} P.Q
          (@AddMonoid.toAddZeroClass.{0} P.Q
            (@SubNegMonoid.toAddMonoid.{0} P.Q
              (@AddGroup.toSubNegMonoid.{0} P.Q
                (@AddCommGroup.toAddGroup.{0} P.Q
                  (@DirectSum.directSum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                    (@Ring.toAddCommGroup.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@CommRing.toRing.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@instCommRingFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) P.PGrp.proof_1)))
                    (@Ring.toAddCommGroup.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@CommRing.toRing.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                        (@instCommRingFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) P.PGrp.proof_1))))))))))
      q q'))
  (@Prod.mk.{0, 0} P.K P.Q
    (@HAdd.hAdd.{0, 0, 0} P.K P.K P.K
      (@instHAdd.{0} P.K
        (@AddZeroClass.toAdd.{0} P.K
          (@AddMonoid.toAddZeroClass.{0} P.K
            (@SubNegMonoid.toAddMonoid.{0} P.K
              (@AddGroup.toSubNegMonoid.{0} P.K
                (@AddCommGroup.toAddGroup.{0} P.K
                  (@DirectSum.directSum.{0, 0} Int (Prod.{0, 0} Int Int)
                    (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
                    (@DirectSum.directSum.{0, 0} Int Int
                      (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
                      (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))))))))))
      (@HAdd.hAdd.{0, 0, 0} P.K P.K P.K
        (@instHAdd.{0} P.K
          (@AddZeroClass.toAdd.{0} P.K
            (@AddMonoid.toAddZeroClass.{0} P.K
              (@SubNegMonoid.toAddMonoid.{0} P.K
                (@AddGroup.toSubNegMonoid.{0} P.K
                  (@AddCommGroup.toAddGroup.{0} P.K
                    (@DirectSum.directSum.{0, 0} Int (Prod.{0, 0} Int Int)
                      (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
                      (@DirectSum.directSum.{0, 0} Int Int
                        (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
                        (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))))))))))
        k
        (@SMul.sMul.{0, 0} P.Q P.K
          (@AutAction.toSMul.{0, 0} P.Q P.K
            (@DirectSum.directSum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
              (@Ring.toAddCommGroup.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@CommRing.toRing.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@instCommRingFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    (@instNonempty.{1} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Fin.instInhabitedFinHAddNatInstHAddInstAddNatOfNat
                        (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
              (@Ring.toAddCommGroup.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                (@CommRing.toRing.{0} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                  (@instCommRingFin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
                    (@instNonempty.{1} (Fin (@OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
                      (@Fin.instInhabitedFinHAddNatInstHAddInstAddNatOfNat
                        (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))))
            (@DirectSum.directSum.{0, 0} Int (Prod.{0, 0} Int Int)
              (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
              (@DirectSum.directSum.{0, 0} Int Int
                (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))
                (@Ring.toAddCommGroup.{0} Int (@CommRing.toRing.{0} Int Int.instCommRingInt))))
            P.instAutActionQKDirectSumFinOfNatNatInstOfNatNatToAddCommGroupToRingInstCommRingFinInstNonemptyInstInhabitedFinHAddNatInstHAddInstAddNatOfNatIntProdInstCommRingInt)
          q k'))
      (P.cocycle q q'))
    (@HAdd.hAdd.{0, 0, 0} P.Q P.Q P.Q (@instHAdd.{0} P.Q EnumDecide.instAddQ) q q'))
```