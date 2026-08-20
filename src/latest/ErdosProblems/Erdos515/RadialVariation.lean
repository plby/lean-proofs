/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.Prawitz
import ErdosProblems.Erdos515.ShortPathPrinciple
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Variation of a normalized radial curve

This file turns the two pointwise quantities used in the Hall--Prawitz argument into a bound for
the variation of a radial image curve.  The proof is entirely local: the fundamental theorem of
calculus bounds every chord by the integral of the speed, and the half-open intervals associated
to a monotone finite sample are pairwise disjoint.
-/

open Metric MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace Erdos515

namespace RadialVariation

/-- The variation on a half-open interval is bounded by the `lintegral` of the speed.  This form
does not require the integral to be finite. -/
theorem eVariationOn_Ico_le_lintegral_enorm_deriv {f : ℝ → ℂ} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Ico a b)) :
    eVariationOn f (Ico a b) ≤ ∫⁻ x in Ioc a b, ‖deriv f x‖ₑ := by
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, humem⟩
  let t : ℕ → Set ℝ := fun i ↦ Ioc (u i) (u (i + 1))
  have ht_disjoint : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint t := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · change Disjoint (t i) (t j)
      rw [Set.disjoint_left]
      intro x hxi hxj
      have huij : u (i + 1) ≤ u j := hu (by omega)
      exact (not_lt_of_ge (hxi.2.trans huij)) hxj.1
    · change Disjoint (t i) (t j)
      rw [Set.disjoint_left]
      intro x hxi hxj
      have huji : u (j + 1) ≤ u i := hu (by omega)
      exact (not_lt_of_ge (hxj.2.trans huji)) hxi.1
  have ht_measurable : ∀ i ∈ Finset.range n, MeasurableSet (t i) := by
    intro i hi
    exact measurableSet_Ioc
  have ht_subset : ⋃ i ∈ Finset.range n, t i ⊆ Ioc a b := by
    rintro x hx
    simp only [mem_iUnion] at hx
    rcases hx with ⟨i, hi, hxi⟩
    exact ⟨lt_of_le_of_lt (humem i).1 hxi.1,
      hxi.2.trans (humem (i + 1)).2.le⟩
  calc
    ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) =
        ∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖ₑ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact edist_eq_enorm_sub _ _
    _ ≤ ∑ i ∈ Finset.range n, ∫⁻ x in t i, ‖deriv f x‖ₑ := by
      gcongr with i hi
      have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
      have hIcc : Icc (u i) (u (i + 1)) ⊆ Ico a b := by
        intro x hx
        exact ⟨(humem i).1.trans hx.1, hx.2.trans_lt (humem (i + 1)).2⟩
      have hchord := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (hf.mono hIcc) hui
      change ‖f (u (i + 1)) - f (u i)‖ₑ ≤
        ∫⁻ x, ‖deriv f x‖ₑ ∂volume.restrict (Ioc (u i) (u (i + 1)))
      rw [restrict_Ioc_eq_restrict_Icc]
      exact hchord
    _ = ∫⁻ x in ⋃ i ∈ Finset.range n, t i, ‖deriv f x‖ₑ := by
      exact (lintegral_biUnion_finset ht_disjoint ht_measurable _).symm
    _ ≤ ∫⁻ x in Ioc a b, ‖deriv f x‖ₑ := lintegral_mono_set ht_subset

lemma circlePoint_eq_shortPathRadialPoint (r theta : ℝ) :
    Prawitz.circlePoint r theta = shortPathRadialPoint r theta := by
  unfold Prawitz.circlePoint shortPathRadialPoint
  congr 2
  ring

lemma hasDerivAt_shortPathRadialPoint (r theta : ℝ) :
    HasDerivAt (fun s ↦ shortPathRadialPoint s theta)
      (Complex.exp (Complex.I * theta)) r := by
  simpa [shortPathRadialPoint] using
    ((hasDerivAt_id r).ofReal_comp.mul_const (Complex.exp (Complex.I * theta)))

lemma hasDerivAt_shortPathRadialCurve {G : ℂ → ℂ} {r theta : ℝ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hr : r ∈ Ico (0 : ℝ) 1) :
    HasDerivAt (shortPathRadialCurve G theta)
      (Complex.exp (Complex.I * theta) * deriv G (shortPathRadialPoint r theta)) r := by
  have hz : shortPathRadialPoint r theta ∈ ball (0 : ℂ) 1 :=
    shortPathRadialPoint_mem_unitDisk hr
  have houter : HasDerivAt G (deriv G (shortPathRadialPoint r theta))
      (shortPathRadialPoint r theta) :=
    (hG _ hz).differentiableAt.hasDerivAt
  change HasDerivAt (G ∘ fun s ↦ shortPathRadialPoint s theta)
    (Complex.exp (Complex.I * theta) * deriv G (shortPathRadialPoint r theta)) r
  simpa only [one_mul, smul_eq_mul] using
    houter.scomp r (hasDerivAt_shortPathRadialPoint r theta)

lemma norm_deriv_shortPathRadialCurve {G : ℂ → ℂ} {r theta : ℝ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hr : r ∈ Ico (0 : ℝ) 1) :
    ‖deriv (shortPathRadialCurve G theta) r‖ =
      ‖deriv G (shortPathRadialPoint r theta)‖ := by
  rw [(hasDerivAt_shortPathRadialCurve hG hr).deriv, norm_mul,
    Complex.norm_exp]
  simp

/-- The radial maximal quotient and radial logarithmic-derivative mass control the variation of
a normalized univalent map. -/
theorem normalized_radialCurve_eVariation_le {G : ℂ → ℂ} {theta K J : ℝ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (hquot : ∀ r ∈ Ioo (0 : ℝ) 1, Prawitz.radialQuotient G r theta ≤ K)
    (hlog : (∫⁻ r in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (r * ‖deriv G (Prawitz.circlePoint r theta)‖ /
        ‖G (Prawitz.circlePoint r theta)‖)) ≤ ENNReal.ofReal J) :
    eVariationOn (shortPathRadialCurve G theta) (Ico (0 : ℝ) 1) ≤
      ENNReal.ofReal (K * J) := by
  have _hKJ : 0 ≤ K * J := mul_nonneg hK hJ
  have hcurve : ContDiffOn ℝ 1 (shortPathRadialCurve G theta) (Ico (0 : ℝ) 1) := by
    have hGreal : ContDiffOn ℝ 1 G (ball (0 : ℂ) 1) :=
      (hG.contDiffOn_of_completeSpace (n := 1)).restrict_scalars ℝ
    have hpoint : ContDiff ℝ 1 (fun r : ℝ ↦ shortPathRadialPoint r theta) := by
      have hc : ContDiff ℝ 1 (fun _ : ℝ ↦ Complex.exp (Complex.I * theta)) := contDiff_const
      simpa [shortPathRadialPoint] using Complex.ofRealCLM.contDiff.mul hc
    exact hGreal.comp hpoint.contDiffOn (fun r hr ↦ shortPathRadialPoint_mem_unitDisk hr)
  refine (eVariationOn_Ico_le_lintegral_enorm_deriv hcurve).trans ?_
  have hspeed : (∫⁻ r in Ioc (0 : ℝ) 1,
      ‖deriv (shortPathRadialCurve G theta) r‖ₑ) ≤
      ∫⁻ r in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (K * (r * ‖deriv G (Prawitz.circlePoint r theta)‖ /
          ‖G (Prawitz.circlePoint r theta)‖)) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hzmem : Prawitz.circlePoint r theta ∈ ball (0 : ℂ) 1 := by
      rw [circlePoint_eq_shortPathRadialPoint]
      exact shortPathRadialPoint_mem_unitDisk ⟨hr.1.le, hr.2⟩
    have hz0 : Prawitz.circlePoint r theta ≠ 0 := by
      unfold Prawitz.circlePoint
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.1.ne') (Complex.exp_ne_zero _)
    have hGne : G (Prawitz.circlePoint r theta) ≠ 0 := by
      intro hzero
      exact hz0 (hinj hzmem (by simp) (hzero.trans hG0.symm))
    have hLnonneg : 0 ≤
        r * ‖deriv G (Prawitz.circlePoint r theta)‖ /
          ‖G (Prawitz.circlePoint r theta)‖ := by
      exact div_nonneg (mul_nonneg hr.1.le (norm_nonneg _)) (norm_nonneg _)
    have hreal : ‖deriv G (Prawitz.circlePoint r theta)‖ ≤
        K * (r * ‖deriv G (Prawitz.circlePoint r theta)‖ /
          ‖G (Prawitz.circlePoint r theta)‖) := by
      calc
        ‖deriv G (Prawitz.circlePoint r theta)‖ =
            (‖G (Prawitz.circlePoint r theta)‖ / r) *
              (r * ‖deriv G (Prawitz.circlePoint r theta)‖ /
                ‖G (Prawitz.circlePoint r theta)‖) := by
          field_simp [hr.1.ne', norm_ne_zero_iff.mpr hGne]
        _ ≤ K * (r * ‖deriv G (Prawitz.circlePoint r theta)‖ /
              ‖G (Prawitz.circlePoint r theta)‖) :=
          mul_le_mul_of_nonneg_right (hquot r hr) hLnonneg
    rw [← ofReal_norm,
      norm_deriv_shortPathRadialCurve hG ⟨hr.1.le, hr.2⟩,
      circlePoint_eq_shortPathRadialPoint]
    simpa only [circlePoint_eq_shortPathRadialPoint] using ENNReal.ofReal_le_ofReal hreal
  calc
    (∫⁻ r in Ioc (0 : ℝ) 1, ‖deriv (shortPathRadialCurve G theta) r‖ₑ) ≤
        ∫⁻ r in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (K * (r * ‖deriv G (Prawitz.circlePoint r theta)‖ /
            ‖G (Prawitz.circlePoint r theta)‖)) := hspeed
    _ = ENNReal.ofReal K * (∫⁻ r in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (r * ‖deriv G (Prawitz.circlePoint r theta)‖ /
            ‖G (Prawitz.circlePoint r theta)‖)) := by
      simp_rw [ENNReal.ofReal_mul hK]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal J := by gcongr
    _ = ENNReal.ofReal (K * J) := (ENNReal.ofReal_mul hK).symm

end RadialVariation

end Erdos515
