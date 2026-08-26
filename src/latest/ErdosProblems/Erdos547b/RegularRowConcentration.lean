/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceRootIncidence
import ErdosProblems.Erdos547b.ClusterDegreeAccounting

/-! # Aggregate upper and lower degree concentration over regular rows -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoRegularRowConcentration

open Finset SimpleGraph Erdos547EC2 Erdos547b.ZhaoSourceRootIncidence

variable {I : Type*} [DecidableEq I]

theorem sum_le_sum_add_of_few_bad
    (J D : Finset I) (w v : I → ℝ) (N ε δ : ℝ)
    (hD : D ⊆ J) (hcount : (D.card : ℝ) ≤ δ * J.card)
    (hN : 0 ≤ N) (hε : 0 ≤ ε)
    (hw : ∀ j ∈ D, w j ≤ N) (hv : ∀ j ∈ J, 0 ≤ v j)
    (hgood : ∀ j ∈ J \ D, w j ≤ v j + ε * N) :
    (∑ j ∈ J, w j) ≤ (∑ j ∈ J, v j) + (ε + δ) * N * J.card := by
  have hsplit := sum_le_truncated_add_budget J D w δ N hD hcount hN hw
  have hsum := Finset.sum_le_sum hgood
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  have hsub : (∑ j ∈ J \ D, v j) ≤ ∑ j ∈ J, v j :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun j hj _ => hv j hj)
  have hcard : ((J \ D).card : ℝ) ≤ J.card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : J \ D ⊆ J)
  have hcost := mul_le_mul_of_nonneg_right hcard (mul_nonneg hε hN)
  nlinarith only [hsplit, hsum, hsub, hcost]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]
variable (A : Finset V) (J : Finset I) (whole : I → Finset V) (ε δ : ℝ)

def upperBad : Finset V :=
  manyBadRoots A J (fun j => upperAtypicalVertices H ε A (whole j)) δ

def lowerBad : Finset V :=
  manyBadRoots A J (fun j => lowerAtypicalVertices H ε A (whole j)) δ

omit [Fintype V] in
theorem card_upperBad_le (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (huniform : ∀ j ∈ J, H.IsUniform ε A (whole j)) :
    ((upperBad H A J whole ε δ).card : ℝ) ≤ δ * A.card := by
  apply card_manyBadRoots_le A J _ ε δ hδ hεδ
  intro j hj
  simpa only [mul_comm] using (huniform j hj).card_upperAtypicalVertices_le

omit [Fintype V] in
theorem card_lowerBad_le (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (huniform : ∀ j ∈ J, H.IsUniform ε A (whole j)) :
    ((lowerBad H A J whole ε δ).card : ℝ) ≤ δ * A.card := by
  apply card_manyBadRoots_le A J _ ε δ hδ hεδ
  intro j hj
  simpa only [mul_comm] using (huniform j hj).card_lowerAtypicalVertices_le

def rowMean (N : ℕ) : ℝ := ∑ j ∈ J, (H.edgeDensity A (whole j) : ℝ) * N

theorem upper_sum_le (N : ℕ) (hN : ∀ j ∈ J, (whole j).card = N)
    (hε : 0 ≤ ε) {z : V} (hz : z ∈ A) (hbad : z ∉ upperBad H A J whole ε δ) :
    (∑ j ∈ J, (degreeInto H z (whole j) : ℝ)) ≤
      rowMean H A J whole N + (ε + δ) * N * J.card := by
  let D := badTargets J (fun j => upperAtypicalVertices H ε A (whole j)) z
  have hcount : (D.card : ℝ) ≤ δ * J.card := by
    apply le_of_not_gt
    intro h
    exact hbad (Finset.mem_filter.mpr ⟨hz, h⟩)
  apply sum_le_sum_add_of_few_bad J D _ _ N ε δ (Finset.filter_subset _ _) hcount
    (Nat.cast_nonneg _) hε
  · intro j hj
    exact_mod_cast (degreeInto_le_card H z (whole j)).trans_eq (hN j (Finset.mem_filter.mp hj).1)
  · intro j _
    exact mul_nonneg (by exact_mod_cast H.edgeDensity_nonneg A (whole j)) (Nat.cast_nonneg N)
  · intro j hj
    have hnj : z ∉ upperAtypicalVertices H ε A (whole j) := by
      intro h
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1, h⟩)
    have hdeg : (degreeInto H z (whole j) : ℝ) ≤
        ((H.edgeDensity A (whole j) : ℝ) + ε) * (whole j).card := by
      exact le_of_not_gt (fun h => hnj (Finset.mem_filter.mpr ⟨hz, h⟩))
    rw [hN j (Finset.mem_sdiff.mp hj).1] at hdeg
    nlinarith only [hdeg]

omit [Fintype V] in
theorem lower_sum_le (N : ℕ) (hN : ∀ j ∈ J, (whole j).card = N)
    (hε : 0 ≤ ε) {z : V} (hz : z ∈ A) (hbad : z ∉ lowerBad H A J whole ε δ) :
    rowMean H A J whole N ≤
      (∑ j ∈ J, (degreeInto H z (whole j) : ℝ)) + (ε + δ) * N * J.card := by
  let D := badTargets J (fun j => lowerAtypicalVertices H ε A (whole j)) z
  have hcount : (D.card : ℝ) ≤ δ * J.card := by
    apply le_of_not_gt
    intro h
    exact hbad (Finset.mem_filter.mpr ⟨hz, h⟩)
  apply sum_le_sum_add_of_few_bad J D _ _ N ε δ (Finset.filter_subset _ _) hcount
    (Nat.cast_nonneg _) hε
  · intro j _
    have hden : (H.edgeDensity A (whole j) : ℝ) ≤ 1 := by exact_mod_cast H.edgeDensity_le_one A (whole j)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hden (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  · intro j _
    exact Nat.cast_nonneg _
  · intro j hj
    have hnj : z ∉ lowerAtypicalVertices H ε A (whole j) := by
      intro h
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1, h⟩)
    have hdeg : ((H.edgeDensity A (whole j) : ℝ) - ε) * (whole j).card ≤
        (degreeInto H z (whole j) : ℝ) := by
      exact le_of_not_gt (fun h => hnj (Finset.mem_filter.mpr ⟨hz, h⟩))
    rw [hN j (Finset.mem_sdiff.mp hj).1] at hdeg
    nlinarith only [hdeg]

end Erdos547b.ZhaoRegularRowConcentration

#print axioms Erdos547b.ZhaoRegularRowConcentration.card_upperBad_le
#print axioms Erdos547b.ZhaoRegularRowConcentration.card_lowerBad_le
#print axioms Erdos547b.ZhaoRegularRowConcentration.upper_sum_le
#print axioms Erdos547b.ZhaoRegularRowConcentration.lower_sum_le
