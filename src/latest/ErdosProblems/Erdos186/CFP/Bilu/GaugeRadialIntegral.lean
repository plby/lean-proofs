/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# The radial gauge integral used in Bilu's section inequality

For a closed convex neighbourhood `D` of the origin in `m`-dimensional
Euclidean space, the sublevel set of its gauge at height `a > 0` is
exactly `a • D`.  Layer cake and the beta integral therefore give

`∫_D (1 - gauge D x)^l dx = m! l! / (m+l)! · volume D`.

This is the analytic radial-integration input in Bilu's proof of (6.7).
-/

namespace Erdos186.CFP.Bilu.GaugeRadialIntegral

open MeasureTheory MeasureTheory.Measure Set intervalIntegral Module Filter
open scoped ENNReal Pointwise Topology

/-- The beta integral with positive natural second exponent, evaluated by
Mathlib's complex beta function. -/
theorem real_beta_nat (m l : ℕ) (hl : 0 < l) :
    (∫ x in (0 : ℝ)..1, x ^ (l - 1) * (1 - x) ^ m) =
      (m.factorial : ℝ) * (l - 1).factorial / (m + l).factorial := by
  have hbeta := show
      Complex.betaIntegral (l : ℂ) (m + 1) =
        (m.factorial : ℂ) * (l - 1).factorial / (m + l).factorial from
    by
      rw [Complex.betaIntegral_eval_nat_add_one_right]
      · have hprod :
            (∏ j ∈ Finset.range (m + 1), ((l : ℂ) + j)) =
              (l.ascFactorial (m + 1) : ℂ) := by
            norm_cast
            exact (Nat.ascFactorial_eq_prod_range l (m + 1)).symm
        rw [hprod]
        have hasc : (l - 1).factorial * l.ascFactorial (m + 1) =
            (m + l).factorial := by
          rw [Nat.factorial_mul_ascFactorial' l (m + 1) hl]
          congr 1
          omega
        have hasc0 : (l.ascFactorial (m + 1) : ℂ) ≠ 0 := by
          have hp : 0 < l.ascFactorial (m + 1) := by
            simpa [Nat.sub_add_cancel hl] using Nat.ascFactorial_pos (l - 1) (m + 1)
          exact_mod_cast hp.ne'
        have hfac0 : ((m + l).factorial : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero (m + l)
        field_simp
        have hmul := congrArg (fun x : ℕ ↦ m.factorial * x) hasc.symm
        norm_cast
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
      · norm_num
        exact_mod_cast hl
  have hexp1 : (l : ℂ) - 1 = ((l - 1 : ℕ) : ℂ) := by
    have h1l : 1 ≤ l := by omega
    calc
      (l : ℂ) - 1 = (l : ℂ) - ((1 : ℕ) : ℂ) := by norm_num
      _ = ((l - 1 : ℕ) : ℂ) := (Nat.cast_sub h1l).symm
  have hexp2 : (m : ℂ) + 1 - 1 = (m : ℂ) := by ring
  rw [Complex.betaIntegral, hexp1, hexp2] at hbeta
  simp_rw [Complex.cpow_natCast, ← Complex.ofReal_pow] at hbeta
  have hcast :
      (fun x : ℝ ↦ (↑(x ^ (l - 1)) : ℂ) * (1 - (x : ℂ)) ^ m) =
        fun x : ℝ ↦ (↑(x ^ (l - 1) * (1 - x) ^ m) : ℂ) := by
    funext x
    push_cast
    rfl
  rw [hcast, intervalIntegral.integral_ofReal] at hbeta
  apply Complex.ofReal_injective
  push_cast
  exact hbeta

/-- `ℝ≥0∞` form of the natural beta integral on `(0,1)`. -/
theorem lintegral_beta_nat (m l : ℕ) (hl : 0 < l) :
    (∫⁻ t in Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((1 - t) ^ m * t ^ (l - 1))) =
      ENNReal.ofReal
        ((m.factorial : ℝ) * (l - 1).factorial / (m + l).factorial) := by
  let f : ℝ → ℝ := fun t ↦ (1 - t) ^ m * t ^ (l - 1)
  have hfcont : Continuous f := by fun_prop
  have hfintIoc : Integrable f (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (hfcont.intervalIntegrable 0 1)
  have hfintIoo : Integrable f (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rwa [restrict_Ioo_eq_restrict_Ioc]
  have hfnn : (fun _ : ℝ ↦ (0 : ℝ)) ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr ht.2.le) m)
      (pow_nonneg ht.1.le (l - 1))
  calc
    (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ m * t ^ (l - 1))) =
        ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, f t) := by
      exact (ofReal_integral_eq_lintegral_ofReal hfintIoo hfnn).symm
    _ = ENNReal.ofReal (∫ t in (0 : ℝ)..1, f t) := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      congr 2
      exact restrict_Ioo_eq_restrict_Ioc
    _ = ENNReal.ofReal
        ((m.factorial : ℝ) * (l - 1).factorial / (m + l).factorial) := by
      congr 1
      simpa only [f, mul_comm] using real_beta_nat m l hl

/-- Every positive sublevel of the gauge of a closed convex neighbourhood
is the corresponding dilation of the body. -/
theorem gauge_sublevel_eq_smul {m : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ D) (hclosed : IsClosed D) (hnhds : D ∈ 𝓝 0)
    {a : ℝ} (ha : 0 < a) :
    {x | gauge D x ≤ a} = a • D := by
  ext x
  constructor
  · intro hx
    have hzGauge : gauge D (a⁻¹ • x) ≤ 1 := by
      rw [gauge_smul_of_nonneg (inv_nonneg.mpr ha.le), smul_eq_mul]
      rwa [inv_mul_le_one₀ ha]
    have hz : a⁻¹ • x ∈ D := by
      rw [← hclosed.closure_eq, ← gauge_le_one_iff_mem_closure hconv hnhds]
      exact hzGauge
    rwa [mem_smul_set_iff_inv_smul_mem₀ ha.ne']
  · exact fun hx ↦ gauge_le_of_mem ha.le hx

/-- The distribution function of `1 - gauge D` on `D`: at every
`t ∈ (0,1)` it is `(1-t)^m · volume D`. -/
theorem restrict_volume_gauge_tail {m : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ D) (hclosed : IsClosed D) (hnhds : D ∈ 𝓝 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (volume.restrict D) {x | t ≤ 1 - gauge D x} =
      ENNReal.ofReal ((1 - t) ^ m) * volume D := by
  have hgcont : Continuous (gauge D) := continuous_gauge hconv hnhds
  have hmeas : MeasurableSet {x | t ≤ 1 - gauge D x} :=
    measurableSet_le measurable_const (continuous_const.sub hgcont).measurable
  have hpred : {x | t ≤ 1 - gauge D x} = {x | gauge D x ≤ 1 - t} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor <;> intro hx <;> linarith
  have hscale : 0 < 1 - t := sub_pos.mpr ht.2
  have hsubset : (1 - t) • D ⊆ D := by
    rintro _ ⟨y, hy, rfl⟩
    exact hconv.smul_mem_of_zero_mem (mem_of_mem_nhds hnhds) hy
      ⟨sub_nonneg.mpr ht.2.le, by linarith [ht.1]⟩
  rw [Measure.restrict_apply hmeas, hpred,
    gauge_sublevel_eq_smul D hconv hclosed hnhds hscale,
    inter_eq_left.mpr hsubset,
    addHaar_smul_of_nonneg volume hscale.le]
  simp

/-- Exact radial gauge integral.  This includes `m = 0` and `l = 0`;
in particular no nondegeneracy or positive-volume hypothesis is needed. -/
theorem lintegral_one_sub_gauge_pow {m l : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ D) (hclosed : IsClosed D) (hnhds : D ∈ 𝓝 0) :
    (∫⁻ y in D, ENNReal.ofReal ((1 - gauge D y) ^ l)) =
      ENNReal.ofReal
          ((m.factorial : ℝ) * l.factorial / (m + l).factorial) * volume D := by
  by_cases hl0 : l = 0
  · subst l
    simp only [pow_zero, ENNReal.ofReal_one, setLIntegral_one,
      Nat.factorial_zero, Nat.cast_one, Nat.add_zero, mul_one]
    rw [div_self (by positivity : (m.factorial : ℝ) ≠ 0)]
    simp
  have hl : 0 < l := Nat.pos_of_ne_zero hl0
  let f : EuclideanSpace ℝ (Fin m) → ℝ := fun y ↦ 1 - gauge D y
  have hfcont : Continuous f := continuous_const.sub (continuous_gauge hconv hnhds)
  have hfnn : 0 ≤ᵐ[volume.restrict D] f := by
    filter_upwards [ae_restrict_mem hclosed.measurableSet] with y hy
    exact sub_nonneg.mpr (gauge_le_one_of_mem hy)
  have hlreal : (0 : ℝ) < l := by exact_mod_cast hl
  have hlayer := lintegral_rpow_eq_lintegral_meas_le_mul
    (volume.restrict D) hfnn hfcont.measurable.aemeasurable hlreal
  have hexp : ((l : ℝ) - 1) = ((l - 1 : ℕ) : ℝ) := by
    have h1l : 1 ≤ l := by omega
    simpa using (Nat.cast_sub h1l).symm
  have hrestrict :
      (∫⁻ t in Ioi (0 : ℝ),
          (volume.restrict D) {y | t ≤ f y} * ENNReal.ofReal (t ^ ((l : ℝ) - 1))) =
        ∫⁻ t in Ioo (0 : ℝ) 1,
          (volume.restrict D) {y | t ≤ f y} * ENNReal.ofReal (t ^ ((l : ℝ) - 1)) := by
    rw [← lintegral_indicator measurableSet_Ioi,
      ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr_ae
    filter_upwards
      [compl_mem_ae_iff.mpr (by simp : volume ({1} : Set ℝ) = 0)] with t htne
    by_cases ht0 : 0 < t
    · by_cases ht1 : t < 1
      · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht0)]
        rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht0, ht1⟩)]
      · have h1t : 1 < t := lt_of_le_of_ne (not_lt.mp ht1) (Ne.symm htne)
        have hempty : {y : EuclideanSpace ℝ (Fin m) | t ≤ f y} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          change t ≤ 1 - gauge D y at hy
          linarith [gauge_nonneg (s := D) y]
        rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht0)]
        rw [indicator_of_notMem
          (show t ∉ Ioo (0 : ℝ) 1 by exact fun ht ↦ ht1 ht.2)]
        rw [hempty, measure_empty, zero_mul]
    · have htIoi : t ∉ Ioi (0 : ℝ) := fun ht ↦ ht0 ht
      have htIoo : t ∉ Ioo (0 : ℝ) 1 := fun ht ↦ ht0 ht.1
      simp only [indicator_of_notMem htIoi, indicator_of_notMem htIoo]
  have hprofile : Measurable fun t : ℝ ↦
      ENNReal.ofReal ((1 - t) ^ m * t ^ (l - 1)) := by fun_prop
  have htail :
      (∫⁻ t in Ioo (0 : ℝ) 1,
          (volume.restrict D) {y | t ≤ f y} * ENNReal.ofReal (t ^ ((l : ℝ) - 1))) =
        volume D *
          ∫⁻ t in Ioo (0 : ℝ) 1,
            ENNReal.ofReal ((1 - t) ^ m * t ^ (l - 1)) := by
    calc
      (∫⁻ t in Ioo (0 : ℝ) 1,
          (volume.restrict D) {y | t ≤ f y} * ENNReal.ofReal (t ^ ((l : ℝ) - 1))) =
          ∫⁻ t in Ioo (0 : ℝ) 1,
            volume D * ENNReal.ofReal ((1 - t) ^ m * t ^ (l - 1)) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        dsimp only [f]
        rw [restrict_volume_gauge_tail D hconv hclosed hnhds ht, hexp,
          Real.rpow_natCast]
        rw [ENNReal.ofReal_mul (pow_nonneg (sub_nonneg.mpr ht.2.le) m)]
        ac_rfl
      _ = ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal ((1 - t) ^ m * t ^ (l - 1)) * volume D := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t _
        change volume D * _ = _ * volume D
        rw [mul_comm]
      _ = (∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal ((1 - t) ^ m * t ^ (l - 1))) * volume D := by
        exact lintegral_mul_const'' (volume D) hprofile.aemeasurable.restrict
      _ = volume D * ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal ((1 - t) ^ m * t ^ (l - 1)) := by rw [mul_comm]
  have hcoeff :
      (l : ℝ) * ((m.factorial : ℝ) * (l - 1).factorial / (m + l).factorial) =
        (m.factorial : ℝ) * l.factorial / (m + l).factorial := by
    have hfac : (l : ℝ) * ((l - 1).factorial : ℝ) = (l.factorial : ℝ) := by
      exact_mod_cast Nat.mul_factorial_pred hl0
    rw [← hfac]
    ring
  calc
    (∫⁻ y in D, ENNReal.ofReal ((1 - gauge D y) ^ l)) =
        ∫⁻ y, ENNReal.ofReal (f y ^ (l : ℝ)) ∂volume.restrict D := by
      apply lintegral_congr
      intro y
      simp only [f, Real.rpow_natCast]
    _ = ENNReal.ofReal (l : ℝ) *
        ∫⁻ t in Ioi (0 : ℝ),
          (volume.restrict D) {y | t ≤ f y} * ENNReal.ofReal (t ^ ((l : ℝ) - 1)) :=
      hlayer
    _ = ENNReal.ofReal (l : ℝ) *
        (volume D * ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal ((1 - t) ^ m * t ^ (l - 1))) := by
      rw [hrestrict, htail]
    _ = ENNReal.ofReal (l : ℝ) *
        (volume D * ENNReal.ofReal
          ((m.factorial : ℝ) * (l - 1).factorial / (m + l).factorial)) := by
      rw [lintegral_beta_nat m l hl]
    _ = ENNReal.ofReal
          ((m.factorial : ℝ) * l.factorial / (m + l).factorial) * volume D := by
      calc
        ENNReal.ofReal (l : ℝ) *
            (volume D * ENNReal.ofReal
              ((m.factorial : ℝ) * (l - 1).factorial / (m + l).factorial)) =
            (ENNReal.ofReal (l : ℝ) * ENNReal.ofReal
              ((m.factorial : ℝ) * (l - 1).factorial / (m + l).factorial)) * volume D := by
          ac_rfl
        _ = ENNReal.ofReal
              ((l : ℝ) *
                ((m.factorial : ℝ) * (l - 1).factorial / (m + l).factorial)) * volume D := by
          rw [ENNReal.ofReal_mul hlreal.le]
        _ = _ := by rw [hcoeff]

/-- Binomial-coefficient form of the radial identity, matching the
coefficient in Bilu's inequality (6.7). -/
theorem choose_mul_lintegral_one_sub_gauge_pow {m l : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ D) (hclosed : IsClosed D) (hnhds : D ∈ 𝓝 0) :
    (Nat.choose (m + l) l : ℝ≥0∞) *
        (∫⁻ y in D, ENNReal.ofReal ((1 - gauge D y) ^ l)) = volume D := by
  rw [lintegral_one_sub_gauge_pow D hconv hclosed hnhds]
  have hnat := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left l m)
  have hreal :
      ((Nat.choose (m + l) l : ℕ) : ℝ) *
          ((m.factorial : ℝ) * l.factorial / (m + l).factorial) = 1 := by
    have hfac0 : ((m + l).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    exact_mod_cast (by
      simpa [Nat.add_sub_cancel_left, mul_assoc, mul_comm, mul_left_comm] using hnat)
  have hchoose : (Nat.choose (m + l) l : ℝ≥0∞) =
      ENNReal.ofReal ((Nat.choose (m + l) l : ℕ) : ℝ) := by norm_num
  rw [hchoose]
  calc
    ENNReal.ofReal ((Nat.choose (m + l) l : ℕ) : ℝ) *
        (ENNReal.ofReal
          ((m.factorial : ℝ) * l.factorial / (m + l).factorial) * volume D) =
        (ENNReal.ofReal ((Nat.choose (m + l) l : ℕ) : ℝ) *
          ENNReal.ofReal
            ((m.factorial : ℝ) * l.factorial / (m + l).factorial)) * volume D := by
      ac_rfl
    _ = ENNReal.ofReal
          (((Nat.choose (m + l) l : ℕ) : ℝ) *
            ((m.factorial : ℝ) * l.factorial / (m + l).factorial)) * volume D := by
      rw [ENNReal.ofReal_mul (by positivity)]
    _ = volume D := by rw [hreal]; simp

end Erdos186.CFP.Bilu.GaugeRadialIntegral

#print axioms Erdos186.CFP.Bilu.GaugeRadialIntegral.lintegral_one_sub_gauge_pow
#print axioms Erdos186.CFP.Bilu.GaugeRadialIntegral.choose_mul_lintegral_one_sub_gauge_pow
