import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Pow.Real

attribute [local instance] Classical.propDecidable

theorem Erdos134.erdos_134 :
    ∀ {ε δ : Real},
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ →
          @Exists.{1} Nat fun (N : Nat) ↦
            ∀ (n : Nat),
              @GE.ge.{0} Nat instLENat n N →
                ∀ (G : SimpleGraph.{0} (Fin n)),
                  @SimpleGraph.CliqueFree.{0} (Fin n) G
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    (∀ (v : Fin n),
                        @LT.lt.{0} Real Real.instLT
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@SimpleGraph.degree.{0} (Fin n) G v
                              (@Subtype.fintype.{0} (Fin n)
                                (@Membership.mem.{0, 0} (Fin n) (Set.{0} (Fin n))
                                  (@Set.instMembership.{0} (Fin n))
                                  (@SimpleGraph.neighborSet.{0} (Fin n) G v))
                                (fun (a : Fin n) ↦
                                  @SimpleGraph.neighborSet.memDecidable.{0} (Fin n) G v
                                    (fun (a b : Fin n) ↦
                                      Classical.propDecidable (@SimpleGraph.Adj.{0} (Fin n) G a b))
                                    a)
                                (Fin.fintype n))))
                          ((@Nat.cast.{0} Real Real.instNatCast n).rpow
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real
                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                  (@One.toOfNat1.{0} Real Real.instOne))
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                          (instOfNatNat (nat_lit 0))))))))
                              ε))) →
                      @Exists.{1} (SimpleGraph.{0} (Fin n)) fun (H : SimpleGraph.{0} (Fin n)) ↦
                        And (@LE.le.{0} (SimpleGraph.{0} (Fin n)) (@SimpleGraph.instLE.{0} (Fin n)) G H)
                          (And
                            (@SimpleGraph.CliqueFree.{0} (Fin n) H
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (And
                              (∀ (x y : Fin n),
                                @Ne.{1} (Fin n) x y →
                                  Or (@SimpleGraph.Adj.{0} (Fin n) H x y)
                                    (@Exists.{1} (Fin n) fun (z : Fin n) ↦
                                      And (@SimpleGraph.Adj.{0} (Fin n) H x z)
                                        (@SimpleGraph.Adj.{0} (Fin n) H z y)))
                              (@LE.le.{0} Real Real.instLE
                                (@Nat.cast.{0} Real Real.instNatCast
                                  (@Finset.card.{0} (Sym2.{0} (Fin n))
                                    (@SDiff.sdiff.{0} (Finset.{0} (Sym2.{0} (Fin n)))
                                      (@Finset.instSDiff.{0} (Sym2.{0} (Fin n))
                                        fun (a b : Sym2.{0} (Fin n)) ↦
                                        @Sym2.instDecidableEq.{0} (Fin n) (instDecidableEqFin n) a b)
                                      (@SimpleGraph.edgeFinset.{0} (Fin n) H
                                        (@SimpleGraph.fintypeEdgeSet.{0} (Fin n) H
                                          (@Sym2.instFintype.{0} (Fin n) (Fin.fintype n))
                                          fun (a b : Fin n) ↦
                                          Classical.propDecidable (@SimpleGraph.Adj.{0} (Fin n) H a b)))
                                      (@SimpleGraph.edgeFinset.{0} (Fin n) G
                                        (@SimpleGraph.fintypeEdgeSet.{0} (Fin n) G
                                          (@Sym2.instFintype.{0} (Fin n) (Fin.fintype n))
                                          fun (a b : Fin n) ↦
                                          Classical.propDecidable
                                            (@SimpleGraph.Adj.{0} (Fin n) G a b))))))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) δ
                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                    (@instHPow.{0, 0} Real Nat
                                      (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                    (@Nat.cast.{0} Real Real.instNatCast n)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
  := by
  sorry
