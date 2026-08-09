import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.Clique
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1034

noncomputable section

def Y_set {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (T :
  Finset V) : Finset V :=
  Finset.univ.filter (fun v => 2 ≤ (G.neighborFinset v ∩ T).card)
def MaTangGraph (n : ℕ) (α : ℝ) (s : ℕ) : SimpleGraph (Fin n) where
  Adj u v :=
    let b := ⌊α * n⌋₊
    let uB := (u : ℕ) < b
    let vB := (v : ℕ) < b
    (uB ≠ vB) ∨ (uB ∧ vB ∧ (u : ℕ) / s = (v : ℕ) / s ∧ u ≠ v)
  symm := by
    constructor
    intro u v h
    dsimp at h ⊢
    rcases h with h | ⟨huB, hvB, hdiv, huv⟩
    · exact Or.inl (Ne.symm h)
    · exact Or.inr ⟨hvB, huB, hdiv.symm, Ne.symm huv⟩
  loopless := by
    constructor
    intro u
    simp
instance instDecidableRel_MaTangGraphAdj (n : ℕ) (α : ℝ) (s : ℕ) :
    DecidableRel (MaTangGraph n α s).Adj := by
  intro u v
  dsimp [MaTangGraph]
  exact instDecidableOr
noncomputable def alpha_star : ℝ := 1 - 1 / Real.sqrt 10
noncomputable def c1 (α : ℝ) : ℝ := 2 * α - Real.sqrt (2 - 4 * (α - 1)^2)
section AristotleLemmas

noncomputable def s_func_robust (n : ℕ) (α : ℝ) : ℕ := Nat.ceil (c1 α * n) + 100
end AristotleLemmas

def erdos_1034 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ n0 : ℕ,
      ∀ n ≥ n0,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (G.edgeFinset.card : ℝ) > ((n : ℝ)^2 / 4) →
          ∃ T ∈ G.cliqueFinset 3,
            ((Y_set G T).card : ℝ) > (((1 : ℝ) / 2) - ε) * (n : ℝ)
end

end Erdos1034

attribute [local instance] Classical.propDecidable

universe u_1

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
theorem Erdos1034.not_erdos_1034 :
    Not Erdos1034.erdos_1034
  := by
  sorry
