/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma611Full
import ErdosProblems.Erdos547b.Claim618

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma611Claim618Adapter

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoLemma615

universe u v w

variable {K : Type u} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]

/-- All matching-index inputs of Claim 6.18, extracted from the actual
Lemma-6.11 decomposition. -/
theorem claim618_indexing_of_decomposition
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA)
    (hlarge : ∀ e : MatchingEdge C67.M,
      e.1.out.1 ∈ L ∨ e.1.out.2 ∈ L) :
    Function.Injective
        (fun ec : MatchingEdge C67.M × Fin 2 ↦
          orientedEndpoint C67.M L ec.1 ec.2) ∧
      (∀ e ∈ allMatchingEdges C67.M,
        C67.M.Adj (orientedEndpoint C67.M L e 0)
          (orientedEndpoint C67.M L e 1)) ∧
      (∀ e ∈ allMatchingEdges C67.M,
        orientedEndpoint C67.M L e 0 ∈ L) ∧
      (∀ e ∈ allMatchingEdges C67.M,
        orientedEndpoint C67.M L e 0 ∈ D.V2 ↔
          orientedEndpoint C67.M L e 1 ∈ D.V2) ∧
      (∀ v ∈ D.V2, v ∈ matchingSupport C67.M →
        v ∈ indexedMatchingSupport (allMatchingEdges C67.M)
          (orientedEndpoint C67.M L)) ∧
      (∀ C ∈ D.L1,
        D.edgeOf C ∈ allMatchingEdges C67.M ∧
          orientedEndpoint C67.M L (D.edgeOf C) 0 = C ∧
          orientedEndpoint C67.M L (D.edgeOf C) 1 ∈ D.S1) := by
  refine ⟨orientedEndpoint_injective C67.M C67.isMatching L, ?_, ?_, ?_, ?_, ?_⟩
  · intro e _
    exact orientedEndpoint_adj C67.M L e
  · intro e _
    exact orientedEndpoint_zero_mem C67.M L hlarge e
  · intro e _
    exact D.endpoint_mem_V2_iff e
  · intro v _ hv
    obtain ⟨e, he, hv0 | hv1⟩ :=
      MatchingDecomposition.support_covered (R := R) (L := L)
        (C67 := C67) v hv
    exact mem_indexedMatchingSupport.mpr ⟨e, he, Or.inl hv0⟩
    exact mem_indexedMatchingSupport.mpr ⟨e, he, Or.inr hv1⟩
  · intro C hC
    exact D.edgeOf_spec hlarge hC

/-- Convert the strict natural Claim-6.17 count to the real source scale
without requiring an impossible exact equality `r = ρk`. -/
theorem claim617_real_of_nat_bound
    (S₁ V₂ : Finset K) (k r : ℕ) (rho : ℝ)
    (hnat : (R.interedges S₁ V₂).card < 16 * r * k)
    (hscale : (r : ℝ) ≤ rho * (k : ℝ)) :
    ((R.interedges S₁ V₂).card : ℝ) <
      16 * rho * (k : ℝ) ^ 2 := by
  calc
    ((R.interedges S₁ V₂).card : ℝ) < 16 * (r : ℝ) * (k : ℝ) := by
      exact_mod_cast hnat
    _ ≤ 16 * (rho * (k : ℝ)) * (k : ℝ) := by
      gcongr
    _ = 16 * rho * (k : ℝ) ^ 2 := by ring

/-- The literal reduced cut attached to a matching decomposition. -/
theorem reducedCut_of_decomposition
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA) :
    Disjoint D.V1 D.V2 ∧ D.V1 ∪ D.V2 = Finset.univ ∧
      D.V1 ⊆ D.S1 ∪ D.L1 := by
  refine ⟨Finset.disjoint_sdiff, Finset.union_sdiff_of_subset
    (Finset.subset_univ D.V1), ?_⟩
  intro x hx
  by_cases hs : x ∈ D.S1
  · exact Finset.mem_union_left _ hs
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hs⟩)

/-- The two source bounds from Claims 6.17 and 6.18 cover the complete
`V1`--`V2` cut. -/
theorem reducedCross_lt_of_claim617_claim618
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA)
    (R' : SimpleGraph K) [DecidableRel R'.Adj] (hR'R : R' ≤ R)
    (rho rho₁ : ℝ) (k : ℕ)
    (h617 : ((R.interedges D.S1 D.V2).card : ℝ) <
      16 * rho * (k : ℝ) ^ 2)
    (h618 : ((R'.interedges D.L1 D.V2).card : ℝ) <
      16 * rho₁ * (k : ℝ) ^ 2) :
    ((R'.interedges D.V1 D.V2).card : ℝ) <
      16 * (rho + rho₁) * (k : ℝ) ^ 2 := by
  let A := R.interedges D.S1 D.V2
  let B := R'.interedges D.L1 D.V2
  have hsub : R'.interedges D.V1 D.V2 ⊆ A ∪ B := by
    intro p hp
    have hp' := (SimpleGraph.mem_interedges_iff R').mp hp
    have hpSide := (reducedCut_of_decomposition D).2.2 hp'.1
    rcases Finset.mem_union.mp hpSide with hpS | hpL
    · exact Finset.mem_union_left B <|
        (SimpleGraph.mem_interedges_iff R).mpr
          ⟨hpS, hp'.2.1, hR'R hp'.2.2⟩
    · exact Finset.mem_union_right A <|
        (SimpleGraph.mem_interedges_iff R').mpr
          ⟨hpL, hp'.2.1, hp'.2.2⟩
  have hcard : (R'.interedges D.V1 D.V2).card ≤ A.card + B.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  have hcardR : ((R'.interedges D.V1 D.V2).card : ℝ) ≤
      (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcard
  dsimp only [A, B] at hcardR
  calc
    ((R'.interedges D.V1 D.V2).card : ℝ) ≤
        ((R.interedges D.S1 D.V2).card : ℝ) +
          ((R'.interedges D.L1 D.V2).card : ℝ) := hcardR
    _ < 16 * rho * (k : ℝ) ^ 2 + 16 * rho₁ * (k : ℝ) ^ 2 :=
      add_lt_add h617 h618
    _ = 16 * (rho + rho₁) * (k : ℝ) ^ 2 := by ring

/-- Claim 6.17 specialized to the literal `Min`, `Mb`, `S1`, and `V2` of a
Lemma-6.11 decomposition. -/
theorem claim617_of_matchingDecomposition
    {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate R L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA)
    (k r q h : ℕ) (rho : ℝ)
    (hV2 : upperV2 ≤ k + 8 * h)
    (hMb : mbBound ≤ 4 * q)
    (hV1 : upperV1 ≤ k)
    (herrors : 80 * r * h + 4 * q * k < r * k)
    (hscale : (r : ℝ) ≤ rho * k)
    (hnoSwitch : ¬ Erdos547b.ZhaoClaim617.HasZhaoSwitch R D.S1
      (D.V2 \ matchingSupport D.Mb) (5 * r)) :
    ((R.interedges D.S1 D.V2).card : ℝ) <
      16 * rho * (k : ℝ) ^ 2 := by
  have hV2' : D.V2.card ≤ k + 8 * h := D.V2_card_upper.trans hV2
  have hMb' : (matchingSupport D.Mb).card ≤ 4 * q :=
    D.Mb_support_card.trans hMb
  have hV1' : (matchingSupport D.Min).card ≤ k := by
    exact D.V1_card_upper.trans hV1
  have h617 := Erdos547b.ZhaoClaim617.zhaoClaim617_realScale
    D.Min D.Mb L k r q h rho hV2' hMb' hV1' herrors hscale
      (by simpa only [MatchingDecomposition.S1, sourceS1,
          MatchingDecomposition.V2, MatchingDecomposition.V1] using
        hnoSwitch)
  simpa only [MatchingDecomposition.S1, sourceS1,
    MatchingDecomposition.V2, MatchingDecomposition.V1] using h617

/-- Claim 6.18 with all matching-index bookkeeping discharged by the actual
Lemma-6.11 decomposition.  No copy or embedding conclusion is a premise. -/
theorem claim618_of_matchingDecomposition
    {TreeVertex : Type v} [Fintype TreeVertex] [DecidableEq TreeVertex]
    {HostVertex : Type w} [Fintype HostVertex] [DecidableEq HostVertex]
    (T : SimpleGraph TreeVertex) [DecidableRel T.Adj]
    (globalRoot : TreeVertex) (small : ℕ)
    (P : Erdos547b.TreePartition.ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (R' : SimpleGraph K) [DecidableRel R'.Adj] (hR'R : R' ≤ R)
    {L : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    (C67 : Claim67Certificate R L miss)
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L C67.O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA)
    (hlarge : ∀ e : MatchingEdge C67.M,
      e.1.out.1 ∈ L ∨ e.1.out.2 ∈ L)
    (density : K → K → ℝ)
    (eta rho rho₁ : ℝ) (k a b q t u z : ℕ)
    (hrho₁ : rho₁ = Real.rpow rho (1 / 3 : ℝ))
    (heta : 0 < eta) (hk : 0 < k) (haNat : 0 < a) (hq : 0 < q)
    (ha : (a : ℝ) ≤ 8 * rho₁ * k)
    (hcutCard : D.L1.card + D.V2.card ≤ 2 * k)
    (hlocalArithmetic : 2 * (b + q + 1) + miss ≤ a)
    (hpartnerArithmetic : u + q ≤ t)
    (hdoubleCountArithmetic : z * a + D.V2.card * t ≤ a * b)
    (hfinalArithmetic : 16 * rho * (k : ℝ) ^ 2 ≤ (z * u : ℕ))
    (h617 : ((R.interedges D.S1 D.V2).card : ℝ) <
      16 * rho * (k : ℝ) ^ 2)
    (hR'dense : ∀ ⦃A B⦄, R'.Adj A B → 2 * eta ≤ density A B)
    (hRdense : ∀ ⦃A B⦄, R.Adj A B → eta ≤ density A B)
    (hdenseR : ∀ ⦃A B⦄, eta ≤ density A B → R.Adj A B)
    (hnonadjZero : ∀ ⦃A B⦄, ¬ R.Adj A B → density A B = 0)
    (hUcard : ∀ A ∈ L ∩ C67.O,
      (unbalancedEdges (allMatchingEdges C67.M)
        (fun e c ↦ density A
          (orientedEndpoint C67.M L e c)) eta).card ≤ q) :
    ((R'.interedges D.L1 D.V2).card : ℝ) <
      16 * rho₁ * (k : ℝ) ^ 2 := by
  classical
  obtain ⟨hendpoint, hMedge, hlargeEnd, hV2pair, hV2covered, hedgeOf⟩ :=
    claim618_indexing_of_decomposition D hlarge
  exact zhaoClaim618 T globalRoot small P G R R' hR'R
    L D.L1 D.V2 D.S1 (allMatchingEdges C67.M)
    (orientedEndpoint C67.M L) D.edgeOf density eta rho rho₁
    k a b q miss t u z C67 hrho₁ heta hk haNat hq ha hcutCard
    hlocalArithmetic hpartnerArithmetic hdoubleCountArithmetic
    hfinalArithmetic h617 (D.L1_subset_large_inter hlarge)
    hendpoint hMedge hlargeEnd hV2pair hV2covered hedgeOf
    hR'dense hRdense hdenseR hnonadjZero hUcard

#print axioms claim618_indexing_of_decomposition
#print axioms claim617_real_of_nat_bound
#print axioms reducedCut_of_decomposition
#print axioms reducedCross_lt_of_claim617_claim618
#print axioms claim617_of_matchingDecomposition
#print axioms claim618_of_matchingDecomposition

end Erdos547b.ZhaoLemma611Claim618Adapter
