import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable abbrev Erdos666.hypercubeGraph :
    (n : Nat) →
      SimpleGraph.{0} (Fin n → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  := by
  sorry

noncomputable def Erdos666.HasCycleOfLength :
    {V : Type u_1} → SimpleGraph.{u_1} V → Nat → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos666.not_erdos_666 :
    Not
      (∀ (ε : Real),
        @GT.gt.{0} Real Real.instLT ε
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Exists.{1} Nat fun (N : Nat) ↦
            ∀ (n : Nat),
              @GE.ge.{0} Nat instLENat n N →
                ∀
                  (G :
                    SimpleGraph.{0}
                      (Fin n → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))),
                  @LE.le.{0}
                      (SimpleGraph.{0}
                        (Fin n → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@SimpleGraph.instLE.{0}
                        (Fin n → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      G (Erdos666.hypercubeGraph n) →
                    @GE.ge.{0} Real Real.instLE
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0}
                            (Sym2.{0}
                              (Fin n →
                                ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (@SimpleGraph.edgeFinset.{0}
                              (Fin n →
                                ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              G
                              (@SimpleGraph.fintypeEdgeSet.{0}
                                (Fin n →
                                  ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                G
                                (@Sym2.instFintype.{0}
                                  (Fin n →
                                    ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@Pi.instFintype.{0, 0} (Fin n)
                                    (fun (a : Fin n) ↦
                                      ZMod
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (instDecidableEqFin n) (Fin.fintype n) fun (a : Fin n) ↦
                                    @ZMod.fintype
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                fun
                                  (a b :
                                    Fin n →
                                      ZMod
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                                Classical.propDecidable
                                  (@SimpleGraph.Adj.{0}
                                    (Fin n →
                                      ZMod
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    G a b)))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
                            (@Nat.cast.{0} Real Real.instNatCast n))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat
                              (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                      @Erdos666.HasCycleOfLength.{0}
                        (Fin n → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) G
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
  := by
  sorry
