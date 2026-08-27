/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Averaging the sum-dependent cutoff over one coordinate

For a nonnegative profile of unit mass, averaging a cutoff over the unit
interval preserves its uniform value and derivative bounds. All
differentiation and continuity of the parameterized integral are proved
here, rather than assumed by the multivariate induction.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory Filter
open scoped Topology

def cutoffAverage (G Φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) 1, G t * Φ (u + t)

theorem cutoffAverage_eq_interval (G Φ : ℝ → ℝ) (u : ℝ) :
    cutoffAverage G Φ u = ∫ t in (0 : ℝ)..1, G t * Φ (u + t) := by
  rw [cutoffAverage, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

theorem cutoffAverage_continuous {G Φ : ℝ → ℝ}
    (hG : Continuous G) (hΦ : Continuous Φ) : Continuous (cutoffAverage G Φ) := by
  have h : Continuous (fun z : ℝ × ℝ => G z.2 * Φ (z.1 + z.2)) :=
    (hG.comp continuous_snd).mul (hΦ.comp (continuous_fst.add continuous_snd))
  exact continuous_parametric_integral_of_continuous h isCompact_Icc

theorem cutoffAverage_hasDerivAt {G Φ : ℝ → ℝ} (hG : Continuous G)
    (hΦ : ContDiff ℝ 1 Φ) {V : ℝ} (hV : ∀ u : ℝ, |deriv Φ u| ≤ V) (u : ℝ) :
    HasDerivAt (cutoffAverage G Φ) (cutoffAverage G (deriv Φ) u) u := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let F : ℝ → ℝ → ℝ := fun x t => G t * Φ (x + t)
  let F' : ℝ → ℝ → ℝ := fun x t => G t * deriv Φ (x + t)
  let bound : ℝ → ℝ := fun t => |G t| * V
  have hFc (x : ℝ) : Continuous (F x) :=
    hG.mul (hΦ.continuous.comp (continuous_const.add continuous_id))
  have hF'c (x : ℝ) : Continuous (F' x) :=
    hG.mul (hΦ.continuous_deriv_one.comp (continuous_const.add continuous_id))
  have hFmeas : ∀ᶠ x in 𝓝 u, AEStronglyMeasurable (F x) μ :=
    Eventually.of_forall (fun x => (hFc x).aestronglyMeasurable)
  have hFint : Integrable (F u) μ := (hFc u).integrableOn_Icc
  have hF'meas : AEStronglyMeasurable (F' u) μ := (hF'c u).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ x ∈ (Set.univ : Set ℝ), ‖F' x t‖ ≤ bound t := by
    apply Eventually.of_forall
    intro t x hx
    dsimp only [F', bound]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hV (x + t)) (abs_nonneg _)
  have hboundInt : Integrable bound μ := (hG.abs.mul continuous_const).integrableOn_Icc
  have hdiff : ∀ᵐ t ∂μ, ∀ x ∈ (Set.univ : Set ℝ), HasDerivAt (fun x => F x t) (F' x t) x := by
    apply Eventually.of_forall
    intro t x hx
    have h := ((hΦ.differentiable_one (x + t)).hasDerivAt.comp x
      ((hasDerivAt_id x).add_const t)).const_mul (G t)
    simpa only [F, F', Function.comp_apply, id_eq, mul_one] using! h
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (by simp) hFmeas hFint hF'meas hbound hboundInt hdiff).2

theorem cutoffAverage_deriv {G Φ : ℝ → ℝ} (hG : Continuous G)
    (hΦ : ContDiff ℝ 1 Φ) {V : ℝ} (hV : ∀ u : ℝ, |deriv Φ u| ≤ V) :
    deriv (cutoffAverage G Φ) = cutoffAverage G (deriv Φ) := by
  funext u
  exact (cutoffAverage_hasDerivAt hG hΦ hV u).deriv

theorem cutoffAverage_contDiff {G Φ : ℝ → ℝ} (hG : Continuous G)
    (hΦ : ContDiff ℝ 1 Φ) {V : ℝ} (hV : ∀ u : ℝ, |deriv Φ u| ≤ V) :
    ContDiff ℝ 1 (cutoffAverage G Φ) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun u => (cutoffAverage_hasDerivAt hG hΦ hV u).differentiableAt, ?_⟩
  rw [cutoffAverage_deriv hG hΦ hV]
  exact cutoffAverage_continuous hG hΦ.continuous_deriv_one

theorem cutoffAverage_abs_le {G Φ : ℝ → ℝ} (hG : Continuous G)
    (hΦ : Continuous Φ) (hG0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G t)
    {V : ℝ} (hV : ∀ u : ℝ, |Φ u| ≤ V) (u : ℝ) :
    |cutoffAverage G Φ u| ≤ V * (∫ t in (0 : ℝ)..1, G t) := by
  rw [cutoffAverage_eq_interval]
  have hcont : Continuous (fun t : ℝ => G t * Φ (u + t)) :=
    hG.mul (hΦ.comp (continuous_const.add continuous_id))
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |G t * Φ (u + t)| :=
      intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, V * G t :=
      intervalIntegral.integral_mono_on zero_le_one (hcont.abs.intervalIntegrable 0 1)
        ((continuous_const.mul hG).intervalIntegrable 0 1) (fun t ht => by
          rw [abs_mul, abs_of_nonneg (hG0 t ht)]
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hV (u + t)) (hG0 t ht))
    _ = _ := intervalIntegral.integral_const_mul _ _

structure BoundedCutoff (Φ : ℝ → ℝ) (K : ℝ) : Prop where
  smooth : ContDiff ℝ 1 Φ
  value_bound : ∀ u : ℝ, |Φ u| ≤ K
  deriv_bound : ∀ u : ℝ, |deriv Φ u| ≤ K

theorem BoundedCutoff.constant_nonneg {Φ : ℝ → ℝ} {K : ℝ}
    (hΦ : BoundedCutoff Φ K) : 0 ≤ K := (abs_nonneg _).trans (hΦ.value_bound 0)

theorem BoundedCutoff.average_mass {G Φ : ℝ → ℝ} {K : ℝ}
    (hΦ : BoundedCutoff Φ K) (hG : Continuous G)
    (hG0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G t) :
    BoundedCutoff (cutoffAverage G Φ) (K * (∫ t in (0 : ℝ)..1, G t)) := by
  refine ⟨cutoffAverage_contDiff hG hΦ.smooth hΦ.deriv_bound, ?_, ?_⟩
  · exact cutoffAverage_abs_le hG hΦ.smooth.continuous hG0 hΦ.value_bound
  · intro u
    rw [cutoffAverage_deriv hG hΦ.smooth hΦ.deriv_bound]
    exact cutoffAverage_abs_le hG hΦ.smooth.continuous_deriv_one hG0 hΦ.deriv_bound u

theorem BoundedCutoff.average {G Φ : ℝ → ℝ} {K : ℝ}
    (hΦ : BoundedCutoff Φ K) (hG : Continuous G)
    (hG0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G t)
    (hmass : (∫ t in (0 : ℝ)..1, G t) = 1) : BoundedCutoff (cutoffAverage G Φ) K := by
  refine ⟨cutoffAverage_contDiff hG hΦ.smooth hΦ.deriv_bound, ?_, ?_⟩
  · intro u
    simpa only [hmass, mul_one] using cutoffAverage_abs_le hG hΦ.smooth.continuous
      hG0 hΦ.value_bound u
  · intro u
    rw [cutoffAverage_deriv hG hΦ.smooth hΦ.deriv_bound]
    simpa only [hmass, mul_one] using cutoffAverage_abs_le hG hΦ.smooth.continuous_deriv_one
      hG0 hΦ.deriv_bound u

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.BoundedCutoff.average
