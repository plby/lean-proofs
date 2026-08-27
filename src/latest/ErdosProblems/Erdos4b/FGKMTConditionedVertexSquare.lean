/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedPairMass

/-! # Exact and relative conditional second moments of the raw vertex degree -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ] [DecidableEq α]

def pinnedGeometricSecond (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (e : Finset α) (v : α) : ℝ := F.pinnedPairAverage v
  (fun A B => survivalProduct P (e ∪ A ∪ B) /
    (survivalProduct P e * survivalProduct P A * survivalProduct P B))

theorem rawVertexDegree_second_moment (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (v : α) :
    (∑ s, ρ s * F.rawVertexDegree P (W s) v ^ 2) =
      F.pinnedPairAverage v (fun A B => containmentMass ρ W (A ∪ B) /
        (survivalProduct P A * survivalProduct P B)) := by
  have hex (s : Ξ) : F.rawVertexDegree P (W s) v ^ 2 =
      ∑ i, ∑ w ∈ F.vertexOutcomes i v, ∑ j, ∑ z ∈ F.vertexOutcomes j v,
        F.rawReweightMass P (W s) i w * F.rawReweightMass P (W s) j z := by
    simp only [rawVertexDegree, rawEventMass, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro w _hw
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro z _hz
    exact mul_comm _ _
  calc
    _ = ∑ i, ∑ w ∈ F.vertexOutcomes i v, ∑ j, ∑ z ∈ F.vertexOutcomes j v,
        ∑ s, ρ s * (F.rawReweightMass P (W s) i w * F.rawReweightMass P (W s) j z) := by
      simp_rw [hex]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _hw
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      exact Finset.sum_comm
    _ = _ := by
      simp only [pinnedPairAverage, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro w _hw
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro z _hz
      rw [F.rawReweightMass_pair_mean]
      ring

theorem rawVertexDegree_conditioned_second_moment (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (e : Finset α) (v : α) :
    (∑ s, conditionedStateMass ρ W e s * F.rawVertexDegree P (W s) v ^ 2) =
      F.pinnedPairAverage v (fun A B => containmentMass ρ W (e ∪ A ∪ B) /
        (containmentMass ρ W e * survivalProduct P A * survivalProduct P B)) := by
  rw [F.rawVertexDegree_second_moment]
  congr 1
  funext A B
  rw [conditionedState_containment, ← Finset.union_assoc]
  ring

theorem rawVertexDegree_conditioned_second_relative_error (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} (hP : ∀ u ∈ F.vertices, 0 < P u)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (he : |containmentMass ρ W e - survivalProduct P e| ≤ η * survivalProduct P e)
    (hU : ∀ i w, v ∈ F.edge i w → ∀ j z, v ∈ F.edge j z →
      |containmentMass ρ W (e ∪ F.edge i w ∪ F.edge j z) -
        survivalProduct P (e ∪ F.edge i w ∪ F.edge j z)| ≤
        η * survivalProduct P (e ∪ F.edge i w ∪ F.edge j z)) :
    |(∑ s, conditionedStateMass ρ W e s * F.rawVertexDegree P (W s) v ^ 2) -
        F.pinnedGeometricSecond P e v| ≤ 4 * η * F.pinnedGeometricSecond P e v := by
  rw [F.rawVertexDegree_second_moment, pinnedGeometricSecond, ← F.pinnedPairAverage_sub]
  apply (F.pinnedPairAverage_abs_le v _).trans
  rw [← F.pinnedPairAverage_const_mul]
  apply F.pinnedPairAverage_mono
  intro i w hvw j z hvz
  have hPA := survivalProduct_pos (fun u hu => hP u (F.edge_subset i w hu))
  have hPB := survivalProduct_pos (fun u hu => hP u (F.edge_subset j z hu))
  have hAB : ∀ u ∈ F.edge i w ∪ F.edge j z, 0 < P u := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hP u (F.edge_subset i w hu)
    · exact hP u (F.edge_subset j z hu)
  have hc := conditionedState_containment_error hρ (fun u hu => hP u (heV hu))
    hAB hη0 hη he (by simpa only [← Finset.union_assoc] using hU i w hvw j z hvz)
  have hscaled := div_le_div_of_nonneg_right hc (mul_pos hPA hPB).le
  have hsub :
      containmentMass (conditionedStateMass ρ W e) W (F.edge i w ∪ F.edge j z) /
          (survivalProduct P (F.edge i w) * survivalProduct P (F.edge j z)) -
        survivalProduct P (e ∪ F.edge i w ∪ F.edge j z) /
          (survivalProduct P e * survivalProduct P (F.edge i w) *
            survivalProduct P (F.edge j z)) =
      (containmentMass (conditionedStateMass ρ W e) W (F.edge i w ∪ F.edge j z) -
          survivalProduct P (e ∪ (F.edge i w ∪ F.edge j z)) / survivalProduct P e) /
        (survivalProduct P (F.edge i w) * survivalProduct P (F.edge j z)) := by
    rw [← Finset.union_assoc]
    ring
  rw [hsub, abs_div, abs_of_pos (mul_pos hPA hPB)]
  simp only [← Finset.union_assoc] at hscaled ⊢
  calc
    _ ≤ 4 * η * (survivalProduct P (e ∪ F.edge i w ∪ F.edge j z) / survivalProduct P e) /
        (survivalProduct P (F.edge i w) * survivalProduct P (F.edge j z)) := hscaled
    _ = _ := by ring

end

end Erdos4b.FGKMT.FiniteEdgeFamily
