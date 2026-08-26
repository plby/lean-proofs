/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceProfileConditions
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# One fixed companion profile with strictly positive derivative energy

The same compact smooth bump works in every dimension. Positivity of its
energy follows from the fundamental theorem of calculus, not a numerical
estimate of the bump's derivative.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff

theorem integral_sq_deriv_Ioi_pos {G : ℝ → ℝ}
    (hcompact : HasCompactSupport G) (hsmooth : ContDiff ℝ ∞ G)
    (hzero : G 0 ≠ 0) : 0 < ∫ t : ℝ in Set.Ioi 0, deriv G t ^ 2 := by
  have hcont : Continuous (fun t ↦ deriv G t ^ 2) :=
    (hsmooth.continuous_deriv (by simp)).pow 2
  have hint : IntegrableOn (fun t ↦ deriv G t ^ 2) (Set.Ioi 0) :=
    (hcont.integrable_of_hasCompactSupport
      (hcompact.deriv.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num))).integrableOn
  apply lt_of_le_of_ne (integral_nonneg fun _ ↦ sq_nonneg _) ?_
  intro heq
  have hae := (integral_eq_zero_iff_of_nonneg (fun t ↦ sq_nonneg (deriv G t)) hint).mp heq.symm
  have hderiv : deriv G =ᵐ[volume.restrict (Set.Ioi 0)] 0 := by
    filter_upwards [hae] with t ht
    exact sq_eq_zero_iff.mp ht
  have hi := HasCompactSupport.integral_Ioi_deriv_eq (hsmooth.of_le (by simp)) hcompact 0
  rw [integral_eq_zero_of_ae hderiv] at hi
  exact hzero (neg_eq_zero.mp hi.symm)

def sourceCompanionBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def sourceCompanionProfile : ℝ → ℝ := sourceCompanionBump

theorem sourceCompanionProfile_compact : HasCompactSupport sourceCompanionProfile :=
  sourceCompanionBump.hasCompactSupport

theorem sourceCompanionProfile_smooth : ContDiff ℝ ∞ sourceCompanionProfile :=
  sourceCompanionBump.contDiff

theorem sourceCompanionProfile_zero : sourceCompanionProfile 0 = 1 := by
  exact sourceCompanionBump.one_of_mem_closedBall (by
    change dist (0 : ℝ) 0 ≤ (1 : ℝ) / 4
    norm_num)

theorem sourceCompanionProfile_support {t : ℝ}
    (ht : 0 ≤ t) (h : sourceCompanionProfile t ≠ 0) : t ≤ 1 := by
  have hmem : t ∈ Function.support sourceCompanionBump := h
  rw [sourceCompanionBump.support_eq, Metric.mem_ball, Real.dist_eq,
    sub_zero, abs_of_nonneg ht] at hmem
  change t < (1 : ℝ) / 2 at hmem
  linarith

def sourceCompanionEnergy : ℝ :=
  ∫ t : ℝ in Set.Ioi 0, deriv sourceCompanionProfile t ^ 2

theorem sourceCompanionEnergy_pos : 0 < sourceCompanionEnergy :=
  integral_sq_deriv_Ioi_pos sourceCompanionProfile_compact sourceCompanionProfile_smooth
    (by rw [sourceCompanionProfile_zero]; norm_num)

theorem sourceCompanionProfile_main_pos (K : ℕ) :
    0 < sourceCompanionVariationalIntegral K sourceCompanionProfile :=
  pow_pos sourceCompanionEnergy_pos K

theorem sourceCompanionProfile_pinned_pos (K : ℕ) :
    0 < sourcePinnedCompanionVariationalIntegral K sourceCompanionProfile := by
  simp only [sourcePinnedCompanionVariationalIntegral, sourceCompanionProfile_zero, one_pow,
    one_mul]
  exact sourceCompanionProfile_main_pos (K - 1)

theorem sourceCompanionProfile_ratio {K : ℕ} (hK : 0 < K) :
    sourcePinnedCompanionVariationalIntegral K sourceCompanionProfile /
      sourceCompanionVariationalIntegral K sourceCompanionProfile = 1 / sourceCompanionEnergy := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  simp only [sourcePinnedCompanionVariationalIntegral, sourceCompanionVariationalIntegral,
    sourceCompanionProfile_zero, one_pow, one_mul, pow_succ]
  change sourceCompanionEnergy ^ k / (sourceCompanionEnergy ^ k * sourceCompanionEnergy) = _
  field_simp [(pow_pos sourceCompanionEnergy_pos k).ne', sourceCompanionEnergy_pos.ne']

end

end Erdos4b
