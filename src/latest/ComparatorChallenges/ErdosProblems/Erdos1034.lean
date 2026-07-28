import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Clique

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos1034.Y_set :
    {V : Type u_1} →
      [Fintype.{u_1} V] →
        [DecidableEq.{u_1 + 1} V] →
          (G : SimpleGraph.{u_1} V) →
            [@DecidableRel.{u_1 + 1, u_1 + 1} V V (@SimpleGraph.Adj.{u_1} V G)] →
              Finset.{u_1} V → Finset.{u_1} V
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos1034.MaTangGraph :
    (n : Nat) → Real → Nat → SimpleGraph.{0} (Fin n)
  := by
  sorry

noncomputable instance Erdos1034.instDecidableRel_MaTangGraphAdj :
    (n : Nat) →
      (α : Real) →
        (s : Nat) →
          @DecidableRel.{1, 1} (Fin n) (Fin n)
            (@SimpleGraph.Adj.{0} (Fin n) (Erdos1034.MaTangGraph n α s))
  := by
  sorry

noncomputable def Erdos1034.alpha_star :
    Real
  := by
  sorry

noncomputable def Erdos1034.s_func_robust :
    Nat → Real → Nat
  := by
  sorry

theorem Erdos1034.MaTang_main :
    ∀ (ε : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        @Exists.{1} Nat fun (N : Nat) ↦
          ∀ (n : Nat),
            @GE.ge.{0} Nat instLENat n N →
              let G :=
                Erdos1034.MaTangGraph n Erdos1034.alpha_star
                  (Erdos1034.s_func_robust n Erdos1034.alpha_star);
              And
                (@GT.gt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Finset.card.{0} (Sym2.{0} (Fin n))
                      (@SimpleGraph.edgeFinset.{0} (Fin n) G
                        (@SimpleGraph.fintypeEdgeSet.{0} (Fin n) G
                          (@Sym2.instFintype.{0} (Fin n) (Fin.fintype n))
                          (Erdos1034.instDecidableRel_MaTangGraphAdj n Erdos1034.alpha_star
                            (Erdos1034.s_func_robust n Erdos1034.alpha_star))))))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat
                        (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                      (@Nat.cast.{0} Real Real.instNatCast n)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (∀ (T : Finset.{0} (Fin n)),
                  @Membership.mem.{0, 0} (Finset.{0} (Fin n)) (Finset.{0} (Finset.{0} (Fin n)))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} (Fin n)))
                        (Finset.{0} (Fin n)) (@Finset.instSetLike.{0} (Finset.{0} (Fin n))))
                      (@SimpleGraph.cliqueFinset.{0} (Fin n) G (Fin.fintype n) (instDecidableEqFin n)
                        (Erdos1034.instDecidableRel_MaTangGraphAdj n Erdos1034.alpha_star
                          (Erdos1034.s_func_robust n Erdos1034.alpha_star))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      T →
                    @LE.le.{0} Real Real.instLE
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Finset.card.{0} (Fin n)
                          (@Erdos1034.Y_set.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n) G
                            (Erdos1034.instDecidableRel_MaTangGraphAdj n Erdos1034.alpha_star
                              (Erdos1034.s_func_robust n Erdos1034.alpha_star))
                            T)))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real
                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 5)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                          (instOfNatNat (nat_lit 3)))))))
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                          (instOfNatNat (nat_lit 0)))))))).sqrt)
                          ε)
                        (@Nat.cast.{0} Real Real.instNatCast n)))
  := by
  sorry

noncomputable def Erdos1034.erdos_1034 :
    Prop
  := by
  sorry

theorem Erdos1034.not_erdos_1034 :
    Not Erdos1034.erdos_1034
  := by
  sorry
