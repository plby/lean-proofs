/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RegularRowConcentration
import ErdosProblems.Erdos547b.HierarchicalCanonicalCleaning

/-! # Small root exclusions and aggregate capacity of target subreservoirs -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoRegularTargetRowConcentration

open Finset SimpleGraph Erdos547EC2 Erdos547b.ZhaoSourceRootIncidence
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable (H : SimpleGraph V) [DecidableRel H.Adj]
variable (A : Finset V) (J : Finset I) (whole raw : I → Finset V) (ε δ : ℝ)

def targetBad : Finset V :=
  manyBadRoots A J (fun j => targetLowDegreeVertices H ε A (whole j) A (raw j)) δ

theorem card_targetBad_le (hε : ε ≤ 1) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (huniform : ∀ j ∈ J, H.IsUniform ε A (whole j))
    (hraw : ∀ j ∈ J, raw j ⊆ whole j)
    (hrawLarge : ∀ j ∈ J, ε * (whole j).card ≤ (raw j).card) :
    ((targetBad H A J whole raw ε δ).card : ℝ) ≤ δ * A.card := by
  apply card_manyBadRoots_le A J _ ε δ hδ hεδ
  intro j hj
  exact card_targetLowDegreeVertices_le H (huniform j hj) (Finset.Subset.refl _)
    (hraw j hj) (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg A.card)) (hrawLarge j hj)

omit [Fintype V] [DecidableEq I] in
theorem degreeInto_biUnion (z : V)
    (hdis : (J : Set I).PairwiseDisjoint raw) :
    degreeInto H z (J.biUnion raw) = ∑ j ∈ J, degreeInto H z (raw j) := by
  have hfiltered : (J : Set I).PairwiseDisjoint (fun j => (raw j).filter (H.Adj z)) := by
    intro i hi j hj hij
    exact (hdis hi hj hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  unfold degreeInto
  rw [Finset.filter_biUnion, Finset.card_biUnion hfiltered]

theorem degree_union_lower (c L : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hdis : (J : Set I).PairwiseDisjoint raw)
    (hdensity : ∀ j ∈ J, c ≤ (H.edgeDensity A (whole j) : ℝ) - ε)
    (hsize : ∀ j ∈ J, L ≤ (raw j).card)
    {z : V} (hz : z ∈ A) (hzBad : z ∉ targetBad H A J whole raw ε δ) :
    c * L * (1 - δ) * J.card ≤ (degreeInto H z (J.biUnion raw) : ℝ) := by
  let D := badTargets J (fun j => targetLowDegreeVertices H ε A (whole j) A (raw j)) z
  have hD : D ⊆ J := Finset.filter_subset _ _
  have hcount : (D.card : ℝ) ≤ δ * J.card := by
    apply le_of_not_gt
    intro h
    exact hzBad (Finset.mem_filter.mpr ⟨hz, h⟩)
  have hgood (j : I) (hj : j ∈ J \ D) : c * L ≤ (degreeInto H z (raw j) : ℝ) := by
    have hjJ := (Finset.mem_sdiff.mp hj).1
    have hnot : z ∉ targetLowDegreeVertices H ε A (whole j) A (raw j) := by
      intro h
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr ⟨hjJ, h⟩)
    have hdeg := target_degree_ge_of_not_mem_lowDegree H ε A (whole j) A (raw j) z hz hnot
    exact ((mul_le_mul_of_nonneg_left (hsize j hjJ) hc).trans
      (mul_le_mul_of_nonneg_right (hdensity j hjJ) (Nat.cast_nonneg (raw j).card))).trans hdeg
  have hsum := Finset.sum_le_sum hgood
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hsumAll : (∑ j ∈ J \ D, (degreeInto H z (raw j) : ℝ)) ≤
      ∑ j ∈ J, (degreeInto H z (raw j) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
  have hpartition : ((J \ D).card : ℝ) + D.card = J.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hD
  have hgoodCount : (1 - δ) * J.card ≤ ((J \ D).card : ℝ) := by
    nlinarith only [hpartition, hcount]
  have hscaled := mul_le_mul_of_nonneg_left hgoodCount (mul_nonneg hc hL)
  rw [degreeInto_biUnion H J raw z hdis, Nat.cast_sum]
  nlinarith only [hsum, hsumAll, hscaled]

end Erdos547b.ZhaoRegularTargetRowConcentration

#print axioms Erdos547b.ZhaoRegularTargetRowConcentration.card_targetBad_le
#print axioms Erdos547b.ZhaoRegularTargetRowConcentration.degreeInto_biUnion
#print axioms Erdos547b.ZhaoRegularTargetRowConcentration.degree_union_lower
