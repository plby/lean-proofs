/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCutoffTest
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# The fixed smooth cutoff for the growing-dimensional profile

The cutoff is chosen once, before the dimension. Its derivative bound
comes from a single fixed compact interval, not from varying profiles.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped Topology

def sieveCutoff (t : ℝ) : ℝ := 1 - Real.smoothTransition (10 * t - 9)

theorem sieveCutoff_contDiff {n : ℕ∞} : ContDiff ℝ n sieveCutoff := by
  unfold sieveCutoff
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem sieveCutoff_nonneg (t : ℝ) : 0 ≤ sieveCutoff t :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem sieveCutoff_le_one (t : ℝ) : sieveCutoff t ≤ 1 := by
  unfold sieveCutoff
  linarith [Real.smoothTransition.nonneg (10 * t - 9)]

theorem sieveCutoff_one_of_le {t : ℝ} (ht : t ≤ 9 / 10) : sieveCutoff t = 1 := by
  rw [sieveCutoff, Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem sieveCutoff_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) : sieveCutoff t = 0 := by
  rw [sieveCutoff, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem sieveCutoff_antitone : Antitone sieveCutoff := by
  intro t u htu
  have h := Real.smoothTransition.monotone (show 10 * t - 9 ≤ 10 * u - 9 by linarith)
  dsimp only [sieveCutoff]
  linarith

theorem sieveCutoff_deriv_zero_of_lt {t : ℝ} (ht : t < 9 / 10) :
    deriv sieveCutoff t = 0 := by
  have h : HasDerivAt sieveCutoff 0 t := (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
    (by
      filter_upwards [gt_mem_nhds ht] with u hu
      exact sieveCutoff_one_of_le hu.le)
  exact h.deriv

theorem sieveCutoff_deriv_zero_of_gt {t : ℝ} (ht : 1 < t) :
    deriv sieveCutoff t = 0 := by
  have h : HasDerivAt sieveCutoff 0 t := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    (by
      filter_upwards [lt_mem_nhds ht] with u hu
      exact sieveCutoff_zero_of_one_le hu.le)
  exact h.deriv

theorem exists_sieveCutoff_bounded : ∃ K : ℝ, 1 ≤ K ∧ BoundedCutoff sieveCutoff K := by
  have hψ : ContDiff ℝ 1 sieveCutoff := sieveCutoff_contDiff
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (9 / 10 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hψ.continuous_deriv_one.continuousOn
  refine ⟨max 1 C, le_max_left _ _, hψ, ?_, ?_⟩
  · intro t
    rw [abs_of_nonneg (sieveCutoff_nonneg t)]
    exact (sieveCutoff_le_one t).trans (le_max_left _ _)
  · intro t
    rcases lt_or_ge t (9 / 10) with ht | ht
    · rw [sieveCutoff_deriv_zero_of_lt ht, abs_zero]
      exact zero_le_one.trans (le_max_left _ _)
    · rcases le_or_gt t 1 with ht' | ht'
      · have hbound : |deriv sieveCutoff t| ≤ C := by
          simpa only [Real.norm_eq_abs] using hC t ⟨ht, ht'⟩
        exact hbound.trans (le_max_right _ _)
      · rw [sieveCutoff_deriv_zero_of_gt ht', abs_zero]
        exact zero_le_one.trans (le_max_left _ _)

theorem sieveCutoff_sq_bounded {K : ℝ} (hK : 1 ≤ K) (hψ : BoundedCutoff sieveCutoff K) :
    BoundedCutoff (fun t => sieveCutoff t ^ 2) (2 * K) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨hψ.smooth.pow 2, ?_, ?_⟩
  · intro t
    rw [abs_of_nonneg (sq_nonneg _)]
    have h0 := sieveCutoff_nonneg t
    have h1 := sieveCutoff_le_one t
    nlinarith [sq_nonneg (1 - sieveCutoff t)]
  · intro t
    have h0 := sieveCutoff_nonneg t
    have hd : deriv (fun t => sieveCutoff t ^ 2) t =
        2 * sieveCutoff t * deriv sieveCutoff t := by
      simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] using!
        ((hψ.smooth.differentiable_one t).hasDerivAt.pow 2).deriv
    rw [hd]
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sieveCutoff_nonneg t)]
    calc
      _ ≤ 2 * sieveCutoff t * K :=
        mul_le_mul_of_nonneg_left (hψ.deriv_bound t) (by positivity)
      _ ≤ 2 * K := by nlinarith [sieveCutoff_le_one t]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_sieveCutoff_bounded
#print axioms Erdos4b.FGKMT.sieveCutoff_sq_bounded
