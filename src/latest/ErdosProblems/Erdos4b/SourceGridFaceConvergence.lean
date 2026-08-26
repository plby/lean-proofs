/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceGridConvergence
import ErdosProblems.Erdos4b.SourceFaceIntegration

/-!
# Every face functional converges along the finite grids

For regular off-pin coordinates, only countably many inserted values and
one simplex-boundary value need be excluded. Dominated convergence is
applied first to this inserted coordinate and then to the off-pin cube.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory BoundedGaps.Maynard
open scoped BigOperators Topology

theorem ae_tendsto_sourceGridValue_insert {K : ℕ} {A : ℝ} (hA : 0 < A) (h : Fin K)
    (t : maynardFaceIndex K h → ℝ) (ht : ∀ i, SourceGridRegular (t i)) :
    ∀ᵐ x : ℝ, Tendsto (fun n ↦ sourceGridValue K A n (maynardInsertCoordinate h x t)) atTop
      (𝓝 (VariableMaynard.candidate K A (maynardInsertCoordinate h x t))) := by
  have hboundary : ∀ᵐ x : ℝ, x ≠ 1 - ∑ i, t i :=
    compl_mem_ae_iff.mpr (measure_singleton _)
  filter_upwards [ae_sourceGridRegular, hboundary] with x hx hxb
  apply tendsto_sourceGridValue hA
  · intro i
    by_cases hi : i = h
    · subst i
      rw [maynardInsertCoordinate_at]
      exact hx
    · rw [maynardInsertCoordinate_off h x t i hi]
      exact ht ⟨i, hi⟩
  · rw [sum_maynardInsertCoordinate]
    intro heq
    apply hxb
    linarith

theorem tendsto_sourceGridFaceIntegral {K : ℕ} {A : ℝ} (hA : 0 < A) (h : Fin K)
    (t : maynardFaceIndex K h → ℝ) (ht : ∀ i, SourceGridRegular (t i)) :
    Tendsto (fun n ↦ ∫ x : ℝ in Set.Icc 0 1,
      sourceGridValue K A n (maynardInsertCoordinate h x t)) atTop
      (𝓝 (∫ x : ℝ in Set.Icc 0 1,
        VariableMaynard.candidate K A (maynardInsertCoordinate h x t))) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ ↦ (1 : ℝ))
  · intro n
    exact ((measurable_sourceGridValue K A n).comp
      (VariableMaynard.measurable_insertCoordinate_left h t)).aestronglyMeasurable
  · exact integrableOn_const measure_Icc_lt_top.ne
  · intro n
    exact ae_of_all _ fun x ↦ sourceGridValue_norm_le_one hA _
  · exact ae_restrict_of_ae (ae_tendsto_sourceGridValue_insert hA h t ht)

theorem tendsto_maynardJ_sourceGridValue {K : ℕ} {A : ℝ} (hA : 0 < A) (h : Fin K) :
    Tendsto (fun n ↦ maynardJ K h (sourceGridValue K A n)) atTop
      (𝓝 (maynardJ K h (VariableMaynard.candidate K A))) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ : maynardFaceIndex K h → ℝ ↦ (1 : ℝ))
  · intro n
    have hm := (measurable_maynardFaceIntegral (measurable_sourceGridValue K A n) h).pow_const 2
    exact hm.aestronglyMeasurable
  · exact integrableOn_const (maynardCubeOf_measure_lt_top _).ne
  · intro n
    apply ae_of_all _
    intro t
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _)
      (maynardFaceIntegral_norm_le_one (sourceGridValue_norm_le_one (n := n) hA) h t)
  · filter_upwards [ae_restrict_of_ae
      (ae_sourceGridRegular_coordinates (ι := maynardFaceIndex K h))] with t ht
    exact (tendsto_sourceGridFaceIntegral hA h t ht).pow 2

theorem tendsto_maynardRatio_sourceGridValue {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    Tendsto (fun n ↦ maynardRatio K (sourceGridValue K A n)) atTop
      (𝓝 (maynardRatio K (VariableMaynard.candidate K A))) := by
  have hi := tendsto_maynardI_sourceGridValue (K := K) hA
  have hj := tendsto_finsetSum (Finset.univ : Finset (Fin K))
    (fun h _ ↦ tendsto_maynardJ_sourceGridValue hA h)
  exact hj.div hi (VariableMaynard.maynardI_candidate_pos hK hA).ne'

theorem exists_sourceGridValue_positive_and_ratio {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A)
    (hJ : ∀ h : Fin K, 0 < maynardJ K h (VariableMaynard.candidate K A))
    {L : ℝ} (hL : L < maynardRatio K (VariableMaynard.candidate K A)) :
    ∃ n : ℕ, 0 < maynardI K (sourceGridValue K A n) ∧
      (∀ h : Fin K, 0 < maynardJ K h (sourceGridValue K A n)) ∧
      L < maynardRatio K (sourceGridValue K A n) := by
  have hi := (tendsto_maynardI_sourceGridValue (K := K) hA).eventually
    (Ioi_mem_nhds (VariableMaynard.maynardI_candidate_pos hK hA))
  have hj := eventually_all.mpr fun h : Fin K ↦
    (tendsto_maynardJ_sourceGridValue hA h).eventually (Ioi_mem_nhds (hJ h))
  have hl := (tendsto_maynardRatio_sourceGridValue hK hA).eventually (Ioi_mem_nhds hL)
  exact (hi.and (hj.and hl)).exists

end

end Erdos4b
