import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform left Riemann sums on the unit interval

The platform reference refinement samples its quantile at left endpoints of
equal-mass subcells.  This file supplies the corresponding convergence
theorem for every continuous scalar integrand on `[0,1]`.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

def uniformLeftGridPoint (N j : ℕ) : ℝ :=
  j / N

def uniformLeftRiemannSum (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (1 / (N : ℝ)) * ∑ j ∈ Finset.range N, f (uniformLeftGridPoint N j)

lemma uniformLeftGridPoint_zero (N : ℕ) :
    uniformLeftGridPoint N 0 = 0 := by
  simp [uniformLeftGridPoint]

lemma uniformLeftGridPoint_self {N : ℕ} (hN : 0 < N) :
    uniformLeftGridPoint N N = 1 := by
  simp [uniformLeftGridPoint, Nat.ne_of_gt hN]

lemma uniformLeftGridPoint_succ_sub
    {N j : ℕ} (hN : 0 < N) :
    uniformLeftGridPoint N (j + 1) - uniformLeftGridPoint N j =
      1 / (N : ℝ) := by
  unfold uniformLeftGridPoint
  push_cast
  field_simp [Nat.ne_of_gt hN]
  ring

lemma uniformLeftGridPoint_mem_Icc
    {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    uniformLeftGridPoint N j ∈ Icc (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · exact div_nonneg (by positivity) hNr.le
  · rw [uniformLeftGridPoint, div_le_one hNr]
    exact_mod_cast hj

lemma uniformLeftGridPoint_mono
    {N i j : ℕ} (hN : 0 < N) (hij : i ≤ j) :
    uniformLeftGridPoint N i ≤ uniformLeftGridPoint N j := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold uniformLeftGridPoint
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hNr.le

theorem uniformLeftRiemannSum_sub_integral_eq
    (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    uniformLeftRiemannSum f N - (∫ x in (0 : ℝ)..1, f x) =
      ∑ j ∈ Finset.range N,
        ∫ x in uniformLeftGridPoint N j..
            uniformLeftGridPoint N (j + 1),
          (f (uniformLeftGridPoint N j) - f x) := by
  have hwhole : IntervalIntegrable f volume (0 : ℝ) 1 :=
    hf.intervalIntegrable_of_Icc zero_le_one
  have hcell (j : ℕ) (hj : j < N) : IntervalIntegrable f volume
      (uniformLeftGridPoint N j) (uniformLeftGridPoint N (j + 1)) := by
    apply hwhole.mono_set
    rw [uIcc_of_le zero_le_one,
      uIcc_of_le (uniformLeftGridPoint_mono hN (Nat.le_succ j))]
    exact Icc_subset_Icc
      (uniformLeftGridPoint_mem_Icc hN (Nat.le_of_lt hj)).1
      (uniformLeftGridPoint_mem_Icc hN (Nat.succ_le_iff.mpr hj)).2
  have hsumIntegral :
      ∑ j ∈ Finset.range N,
          ∫ x in uniformLeftGridPoint N j..
            uniformLeftGridPoint N (j + 1), f x =
        ∫ x in (0 : ℝ)..1, f x := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun j ↦ uniformLeftGridPoint N j)
      (f := f) (μ := volume) (n := N) hcell
    simpa only [uniformLeftGridPoint_zero,
      uniformLeftGridPoint_self hN] using! hsum
  symm
  calc
    ∑ j ∈ Finset.range N,
          ∫ x in uniformLeftGridPoint N j..
              uniformLeftGridPoint N (j + 1),
            (f (uniformLeftGridPoint N j) - f x) =
        ∑ j ∈ Finset.range N,
          ((1 / (N : ℝ)) * f (uniformLeftGridPoint N j) -
            ∫ x in uniformLeftGridPoint N j..
              uniformLeftGridPoint N (j + 1), f x) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjN : j < N := Finset.mem_range.mp hj
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        (hcell j hjN), intervalIntegral.integral_const,
        uniformLeftGridPoint_succ_sub hN]
      simp only [smul_eq_mul]
    _ = (1 / (N : ℝ)) *
          ∑ j ∈ Finset.range N, f (uniformLeftGridPoint N j) -
        ∑ j ∈ Finset.range N,
          ∫ x in uniformLeftGridPoint N j..
            uniformLeftGridPoint N (j + 1), f x := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = uniformLeftRiemannSum f N - (∫ x in (0 : ℝ)..1, f x) := by
      rw [hsumIntegral]
      rfl

theorem tendsto_uniformLeftRiemannSum
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ ↦ uniformLeftRiemannSum f (n + 1)) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rcases Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε) with
    ⟨δ, hδ, hmod⟩
  have hmesh : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ :=
    (tendsto_order.mp tendsto_one_div_add_atTop_nhds_zero_nat).2 δ hδ
  filter_upwards [hmesh] with n hn
  have hN : 0 < n + 1 := Nat.succ_pos n
  rw [Real.dist_eq, uniformLeftRiemannSum_sub_integral_eq f hN hf]
  calc
    |∑ j ∈ Finset.range (n + 1),
          ∫ x in uniformLeftGridPoint (n + 1) j..
              uniformLeftGridPoint (n + 1) (j + 1),
            (f (uniformLeftGridPoint (n + 1) j) - f x)| =
        ‖∑ j ∈ Finset.range (n + 1),
          ∫ x in uniformLeftGridPoint (n + 1) j..
              uniformLeftGridPoint (n + 1) (j + 1),
            (f (uniformLeftGridPoint (n + 1) j) - f x)‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∑ j ∈ Finset.range (n + 1),
          ‖∫ x in uniformLeftGridPoint (n + 1) j..
              uniformLeftGridPoint (n + 1) (j + 1),
            (f (uniformLeftGridPoint (n + 1) j) - f x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (n + 1),
          (ε / 2) * (1 / ((n + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN : j < n + 1 := Finset.mem_range.mp hj
      have hleft := uniformLeftGridPoint_mem_Icc hN (Nat.le_of_lt hjN)
      have hright := uniformLeftGridPoint_mem_Icc hN (Nat.succ_le_iff.mpr hjN)
      have hmono := uniformLeftGridPoint_mono hN (Nat.le_succ j)
      calc
        ‖∫ x in uniformLeftGridPoint (n + 1) j..
              uniformLeftGridPoint (n + 1) (j + 1),
            (f (uniformLeftGridPoint (n + 1) j) - f x)‖ ≤
            (ε / 2) *
              |uniformLeftGridPoint (n + 1) (j + 1) -
                uniformLeftGridPoint (n + 1) j| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro x hx
          rw [uIoc_of_le hmono] at hx
          have hxIcc : x ∈ Icc (0 : ℝ) 1 :=
            ⟨hleft.1.trans hx.1.le, hx.2.trans hright.2⟩
          have hdist : dist (uniformLeftGridPoint (n + 1) j) x < δ := by
            rw [Real.dist_eq, abs_sub_comm,
              abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
            calc
              x - uniformLeftGridPoint (n + 1) j ≤
                  uniformLeftGridPoint (n + 1) (j + 1) -
                    uniformLeftGridPoint (n + 1) j := sub_le_sub_right hx.2 _
              _ = 1 / ((n + 1 : ℕ) : ℝ) :=
                uniformLeftGridPoint_succ_sub hN
              _ = 1 / ((n : ℝ) + 1) := by norm_num
              _ < δ := hn
          exact le_of_lt (by
            simpa [Real.dist_eq] using! hmod _ hleft _ hxIcc hdist)
        _ = (ε / 2) * (1 / ((n + 1 : ℕ) : ℝ)) := by
          rw [abs_of_nonneg (sub_nonneg.mpr hmono),
            uniformLeftGridPoint_succ_sub hN]
    _ = ε / 2 := by
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      norm_num [Nat.cast_add]
      field_simp
    _ < ε := half_lt_self hε

end

end Erdos1038
