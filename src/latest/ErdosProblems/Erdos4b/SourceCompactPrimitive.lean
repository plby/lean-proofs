/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceCompanionProfile
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Compact smooth primitives with exact positive-half-line derivatives

The negative-side cutoff is identically one near every nonnegative point.
Consequently it does not change the values or derivatives used by the
source variational functionals.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ContDiff Topology

def sourceTailPrimitive (b : ℝ) (ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in t..b, ψ u

theorem sourceTailPrimitive_hasDerivAt {b : ℝ} {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) (t : ℝ) :
    HasDerivAt (sourceTailPrimitive b ψ) (-ψ t) t := by
  exact intervalIntegral.integral_hasDerivAt_left (hψ.intervalIntegrable _ _)
    (hψ.stronglyMeasurableAtFilter _ _) hψ.continuousAt

theorem sourceTailPrimitive_smooth {b : ℝ} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (sourceTailPrimitive b ψ) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t ↦ (sourceTailPrimitive_hasDerivAt hψ.continuous t).differentiableAt, ?_⟩
  have heq : deriv (sourceTailPrimitive b ψ) = fun t ↦ -ψ t :=
    funext fun t ↦ (sourceTailPrimitive_hasDerivAt hψ.continuous t).deriv
  rw [heq]
  exact hψ.neg

theorem sourceTailPrimitive_eq_zero {b t : ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ u, b ≤ u → ψ u = 0) (ht : b ≤ t) : sourceTailPrimitive b ψ t = 0 := by
  unfold sourceTailPrimitive
  rw [intervalIntegral.integral_symm]
  have hi : (∫ u in b..t, ψ u) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply ae_of_all _
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    exact hψ u hu.1.le
  rw [hi, neg_zero]

def sourceCompactPrimitive (b : ℝ) (ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition (2 * t + 2) * sourceTailPrimitive b ψ t

theorem sourceCompactPrimitive_smooth {b : ℝ} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (sourceCompactPrimitive b ψ) := by
  unfold sourceCompactPrimitive
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul (sourceTailPrimitive_smooth hψ)

theorem sourceCompactPrimitive_eq_zero_of_le {b t : ℝ} {ψ : ℝ → ℝ}
    (ht : t ≤ -1) : sourceCompactPrimitive b ψ t = 0 := by
  unfold sourceCompactPrimitive
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem sourceCompactPrimitive_eq_zero_of_ge {b t : ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ u, b ≤ u → ψ u = 0) (ht : b ≤ t) : sourceCompactPrimitive b ψ t = 0 := by
  unfold sourceCompactPrimitive
  rw [sourceTailPrimitive_eq_zero hψ ht, mul_zero]

theorem sourceCompactPrimitive_compact {b : ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ u, b ≤ u → ψ u = 0) : HasCompactSupport (sourceCompactPrimitive b ψ) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := b))
  intro t ht
  have hh : t < -1 ∨ b < t := by simpa only [Set.mem_Icc, not_and_or, not_le] using ht
  rcases hh with hh | hh
  · exact sourceCompactPrimitive_eq_zero_of_le hh.le
  · exact sourceCompactPrimitive_eq_zero_of_ge hψ hh.le

theorem sourceCompactPrimitive_eventuallyEq {b t : ℝ} {ψ : ℝ → ℝ}
    (ht : 0 ≤ t) : sourceCompactPrimitive b ψ =ᶠ[𝓝 t] sourceTailPrimitive b ψ := by
  filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) / 2 < t by linarith)] with u hu
  unfold sourceCompactPrimitive
  rw [Real.smoothTransition.one_of_one_le (by change -1 / 2 < u at hu; linarith), one_mul]

theorem sourceCompactPrimitive_deriv {b t : ℝ} {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) (ht : 0 ≤ t) : deriv (sourceCompactPrimitive b ψ) t = -ψ t := by
  rw [(sourceCompactPrimitive_eventuallyEq ht).deriv_eq]
  exact (sourceTailPrimitive_hasDerivAt hψ t).deriv

theorem sourceCompactPrimitive_zero (b : ℝ) (ψ : ℝ → ℝ) :
    sourceCompactPrimitive b ψ 0 = ∫ t in (0 : ℝ)..b, ψ t := by
  unfold sourceCompactPrimitive sourceTailPrimitive
  rw [Real.smoothTransition.one_of_one_le (by norm_num), one_mul]

theorem sourceCompactPrimitive_zero_eq_integral {b : ℝ} {ψ : ℝ → ℝ}
    (hb : 0 ≤ b) (hψ : ∀ u, b ≤ u → ψ u = 0) :
    sourceCompactPrimitive b ψ 0 = ∫ t : ℝ in Set.Ioi 0, ψ t := by
  rw [sourceCompactPrimitive_zero, intervalIntegral.integral_of_le hb]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Set.Ioc_subset_Ioi_self
  intro t ht
  apply hψ t
  have hh : ¬t ≤ b := fun h ↦ ht.2 ⟨ht.1, h⟩
  exact (lt_of_not_ge hh).le

theorem sourceCompactPrimitive_ceiling {b t : ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ u, b ≤ u → ψ u = 0) (hne : sourceCompactPrimitive b ψ t ≠ 0) : t < b := by
  by_contra ht
  exact hne (sourceCompactPrimitive_eq_zero_of_ge hψ (le_of_not_gt ht))

theorem sourceCompactPrimitive_simplex {ι J : Type*} [Fintype ι]
    (S : Finset J) (b : J → ι → ℝ) (ψ : J → ι → ℝ → ℝ)
    (hsupport : ∀ j ∈ S, ∀ i t, b j i ≤ t → ψ j i t = 0)
    (hbudget : ∀ j ∈ S, (∑ i, b j i) ≤ (1 : ℝ) / 10)
    {j : J} (hj : j ∈ S) (t : ι → ℝ)
    (hne : ∀ i, sourceCompactPrimitive (b j i) (ψ j i) (t i) ≠ 0) :
    (∑ i, t i) ≤ (1 : ℝ) / 10 := by
  apply le_trans (Finset.sum_le_sum fun i _ ↦ ?_) (hbudget j hj)
  exact (sourceCompactPrimitive_ceiling (hsupport j hj i) (hne i)).le

end

end Erdos4b
