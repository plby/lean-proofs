import ErdosProblems.Erdos1038.WeakPotentialL1
import ErdosProblems.Erdos1038.SignSetStability

/-!
# Convergence of negative sublevel sets of logarithmic potentials

This file joins the two analytic interfaces developed for the compactness
argument.  Convergence in `L¹` gives convergence in measure, while stability
of strict sign sets turns that convergence into convergence of the measures
of the negative sublevel sets, provided that the limiting zero set is null.
-/

open scoped ENNReal
open Filter MeasureTheory Set Topology

namespace Erdos1038

noncomputable section

variable {α : Type*}

/-- Convergence in `L¹` implies convergence of the measures of the strict
negative sets, as soon as the limiting representative has null zero set. -/
theorem tendsto_measure_negativeSet_of_tendsto_Lp
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {u : ℕ → Lp ℝ 1 μ} {v : Lp ℝ 1 μ}
    (huv : Tendsto u atTop (𝓝 v))
    (hv_zero : μ {x | v x = 0} = 0) :
    Tendsto (fun n ↦ μ (negativeSet fun x ↦ u n x)) atTop
      (𝓝 (μ (negativeSet fun x ↦ v x))) := by
  exact tendsto_measure_negativeSet
    (fun n ↦ (Lp.stronglyMeasurable (u n)).measurable)
    (Lp.stronglyMeasurable v).measurable
    (tendstoInMeasure_of_tendsto_Lp huv) hv_zero

/-- Interval form of `tendsto_measure_negativeSet_of_tendsto_Lp`, written
with ordinary Lebesgue measure rather than a restricted measure. -/
theorem tendsto_volume_negativeSetOn_Icc_of_tendsto_Lp
    {a b : ℝ} {u : ℕ → Lp ℝ 1 (volume.restrict (Icc a b))}
    {v : Lp ℝ 1 (volume.restrict (Icc a b))}
    (huv : Tendsto u atTop (𝓝 v))
    (hv_zero : volume {x | x ∈ Icc a b ∧ v x = 0} = 0) :
    Tendsto (fun n ↦ volume {x | x ∈ Icc a b ∧ u n x < 0}) atTop
      (𝓝 (volume {x | x ∈ Icc a b ∧ v x < 0})) := by
  have hv_zero_restrict :
      (volume.restrict (Icc a b)) {x | v x = 0} = 0 := by
    rw [Measure.restrict_apply
      (measurableSet_eq_fun (Lp.stronglyMeasurable v).measurable measurable_const)]
    rw [← hv_zero]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, and_comm]
  have h := tendsto_measure_negativeSet_of_tendsto_Lp huv hv_zero_restrict
  have hu_measure (n : ℕ) :
      (volume.restrict (Icc a b)) (negativeSet fun x ↦ u n x) =
        volume {x | x ∈ Icc a b ∧ u n x < 0} := by
    rw [Measure.restrict_apply
      (measurableSet_negativeSet (Lp.stronglyMeasurable (u n)).measurable)]
    congr 1
    ext x
    simp only [negativeSet, mem_inter_iff, mem_ofPred_eq, and_comm]
  have hv_measure :
      (volume.restrict (Icc a b)) (negativeSet fun x ↦ v x) =
        volume {x | x ∈ Icc a b ∧ v x < 0} := by
    rw [Measure.restrict_apply
      (measurableSet_negativeSet (Lp.stronglyMeasurable v).measurable)]
    congr 1
    ext x
    simp only [negativeSet, mem_inter_iff, mem_ofPred_eq, and_comm]
  simpa only [hu_measure, hv_measure] using! h

/-- Weak convergence of root measures supported on `[-1,1]` implies
convergence of the Lebesgue measures of the negative sets of their
logarithmic potentials on any bounded observation interval, if the limiting
potential has null zero set. -/
theorem tendsto_volume_negativeSetOn_Icc_logarithmicPotentialLp_of_weak
    {P : ℕ → ProbabilityMeasure ℝ} {P₀ : ProbabilityMeasure ℝ}
    (hP : Tendsto P atTop (𝓝 P₀))
    (hs : ∀ n, IsRootIntervalSupported (P n))
    (hs₀ : IsRootIntervalSupported P₀)
    {a b : ℝ} (hab : a ≤ b)
    (hzero : volume {x | x ∈ Icc a b ∧
      logarithmicPotentialLp a b hab P₀ hs₀ x = 0} = 0) :
    Tendsto
      (fun n ↦ volume {x | x ∈ Icc a b ∧
        logarithmicPotentialLp a b hab (P n) (hs n) x < 0})
      atTop
      (𝓝 (volume {x | x ∈ Icc a b ∧
        logarithmicPotentialLp a b hab P₀ hs₀ x < 0})) := by
  exact tendsto_volume_negativeSetOn_Icc_of_tendsto_Lp
    (tendsto_logarithmicPotentialLp_of_weak hP hs hs₀ hab) hzero

/-- The observation interval `[-2,2]` used in the Erdős 1038 application. -/
theorem tendsto_volume_negativeSetOn_negTwo_two_logarithmicPotentialLp_of_weak
    {P : ℕ → ProbabilityMeasure ℝ} {P₀ : ProbabilityMeasure ℝ}
    (hP : Tendsto P atTop (𝓝 P₀))
    (hs : ∀ n, IsRootIntervalSupported (P n))
    (hs₀ : IsRootIntervalSupported P₀)
    (hzero : volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      logarithmicPotentialLp (-2) 2 (by norm_num) P₀ hs₀ x = 0} = 0) :
    Tendsto
      (fun n ↦ volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
        logarithmicPotentialLp (-2) 2 (by norm_num) (P n) (hs n) x < 0})
      atTop
      (𝓝 (volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
        logarithmicPotentialLp (-2) 2 (by norm_num) P₀ hs₀ x < 0})) := by
  exact tendsto_volume_negativeSetOn_Icc_logarithmicPotentialLp_of_weak
    hP hs hs₀ (by norm_num) hzero

end

end Erdos1038
