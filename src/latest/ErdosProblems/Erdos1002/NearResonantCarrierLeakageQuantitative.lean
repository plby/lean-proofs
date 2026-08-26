import ErdosProblems.Erdos1002.NearResonantCarrierAnnuli
import ErdosProblems.Erdos1002.NearResonantGevreyL2
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative leakage for the physical near-resonant carriers

This file connects the formal derivative energy in the carrier leakage
lemma to the actual `L²` derivative of the smooth reduced-cell function.
The bridge is Parseval plus the Fourier transform identity for every
classical derivative.  Compact support inside the fundamental interval is
proved first, so no periodic boundary term is tacitly discarded.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal FourierTransform

namespace Erdos1002

noncomputable section

private theorem paperExp_eq_fourierChar_carrierLeakage (t : ℝ) :
    paperExp t = (Real.fourierChar t : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold paperExp
  congr 1
  push_cast
  ring

/-- Every derivative of the finite reduced-cell representative is supported
inside the chosen unit fundamental interval. -/
theorem support_iteratedDeriv_smoothNearPrimitivePoleSum_subset_unit
    (a ε : ℝ) (p j : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    Function.support
        (iteratedDeriv j (smoothNearPrimitivePoleSum a ε p)) ⊆
      Ioc (0 : ℝ) 1 := by
  intro alpha halpha
  change iteratedDeriv j (smoothNearPrimitivePoleSum a ε p) alpha ≠ 0
    at halpha
  rw [iteratedDeriv_smoothNearPrimitivePoleSum a ε p j ha haε alpha]
    at halpha
  have hex : ∃ q ∈ reducedResidues p,
      iteratedDeriv j (nearPoleCell a ε p q) alpha ≠ 0 := by
    by_contra hnot
    push_neg at hnot
    apply halpha
    exact Finset.sum_eq_zero fun q hq ↦ hnot q hq
  obtain ⟨q, hq, hqne⟩ := hex
  have hnormSupport : alpha ∈ Function.support (fun beta : ℝ ↦
      ‖iteratedDeriv j (nearPoleCell a ε p q) beta‖ ^ 2) := by
    change ‖iteratedDeriv j (nearPoleCell a ε p q) alpha‖ ^ 2 ≠ 0
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hqne)
  exact nearestCell_interval_subset_unit hp hq
    (support_norm_iteratedDeriv_nearPoleCell_sq_subset
      a ε p q j (by omega) ha hε haε hεhalf hnormSupport)

/-- Global integrability of every derivative; compact support, rather than
periodic integration by parts, is the boundary justification. -/
theorem integrable_iteratedDeriv_smoothNearPrimitivePoleSum
    (a ε : ℝ) (p j : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    Integrable (iteratedDeriv j (smoothNearPrimitivePoleSum a ε p)) := by
  have hcont : Continuous
      (iteratedDeriv j (smoothNearPrimitivePoleSum a ε p)) := by
    rw [iteratedDeriv_eq_iterate]
    exact (smoothNearPrimitivePoleSum_contDiff a ε p ha haε).iterate_deriv j
      |>.continuous
  have hsupp : Function.support
      (iteratedDeriv j (smoothNearPrimitivePoleSum a ε p)) ⊆
      Icc (0 : ℝ) 1 :=
    (support_iteratedDeriv_smoothNearPrimitivePoleSum_subset_unit
      a ε p j hp ha hε haε hεhalf).trans Ioc_subset_Icc_self
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp)

private theorem unitFourierCoefficientInt_eq_fourier_of_support_unit
    (f : ℝ → ℂ) (n : ℤ)
    (hsupp : Function.support f ⊆ Ioc (0 : ℝ) 1) :
    unitFourierCoefficientInt f n = 𝓕 f (n : ℝ) := by
  let g : ℝ → ℂ := fun x ↦ f x * paperExp (-(n : ℝ) * x)
  have hgsupp : Function.support g ⊆ Ioc (0 : ℝ) 1 := by
    intro x hx
    apply hsupp
    intro hzero
    apply hx
    simp [g, hzero]
  calc
    unitFourierCoefficientInt f n = ∫ x in (0 : ℝ)..1, g x := rfl
    _ = ∫ x : ℝ, g x :=
      intervalIntegral.integral_eq_integral_of_support_subset hgsupp
    _ = 𝓕 f (n : ℝ) := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards with x
      change f x * paperExp (-(n : ℝ) * x) =
        (Real.fourierChar (-inner ℝ x (n : ℝ)) : ℂ) • f x
      rw [paperExp_eq_fourierChar_carrierLeakage]
      simp only [smul_eq_mul]
      rw [show inner ℝ x (n : ℝ) = x * (n : ℝ) by simp [mul_comm]]
      change f x * (Real.fourierChar (-(n : ℝ) * x) : ℂ) =
        (Real.fourierChar (-(x * (n : ℝ))) : ℂ) * f x
      rw [show -(n : ℝ) * x = -(x * (n : ℝ)) by ring]
      ring

/-- Exact multiplier identity for every integer Fourier coefficient of every
derivative of the physical pole. -/
theorem unitFourierCoefficientInt_iteratedDeriv_smoothNearPrimitivePoleSum
    (a ε : ℝ) (p j : ℕ) (n : ℤ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    unitFourierCoefficientInt
        (iteratedDeriv j (smoothNearPrimitivePoleSum a ε p)) n =
      (2 * Real.pi * Complex.I * (n : ℝ)) ^ j *
        unitFourierCoefficientInt
          (smoothNearPrimitivePoleSum a ε p) n := by
  have hall : ∀ r : ℕ, Integrable
      (iteratedDeriv r (smoothNearPrimitivePoleSum a ε p)) := fun r ↦
    integrable_iteratedDeriv_smoothNearPrimitivePoleSum
      a ε p r hp ha hε haε hεhalf
  have hfour := congrFun
    (Real.fourier_iteratedDeriv
      (smoothNearPrimitivePoleSum_contDiff a ε p ha haε)
      (fun r _hr ↦ hall r)
      (show (j : ℕ∞) ≤ ⊤ from le_top)) (n : ℝ)
  have hsupp0 : Function.support (smoothNearPrimitivePoleSum a ε p) ⊆
      Ioc (0 : ℝ) 1 := by
    simpa only [iteratedDeriv_zero] using!
      (support_iteratedDeriv_smoothNearPrimitivePoleSum_subset_unit
        a ε p 0 hp ha hε haε hεhalf)
  rw [unitFourierCoefficientInt_eq_fourier_of_support_unit
      _ n (support_iteratedDeriv_smoothNearPrimitivePoleSum_subset_unit
        a ε p j hp ha hε haε hεhalf),
    unitFourierCoefficientInt_eq_fourier_of_support_unit
      _ n hsupp0]
  simpa only [smul_eq_mul, iteratedDeriv_zero] using! hfour

/-- Norm-squared version of the exact derivative multiplier identity. -/
theorem fourier_weight_mul_norm_sq_eq_deriv_coefficient_norm_sq
    (a ε : ℝ) (p j : ℕ) (n : ℤ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    (2 * Real.pi * |(n : ℝ)|) ^ (2 * j) *
        ‖unitFourierCoefficientInt
          (smoothNearPrimitivePoleSum a ε p) n‖ ^ 2 =
      ‖unitFourierCoefficientInt
          (iteratedDeriv j (smoothNearPrimitivePoleSum a ε p)) n‖ ^ 2 := by
  rw [unitFourierCoefficientInt_iteratedDeriv_smoothNearPrimitivePoleSum
    a ε p j n hp ha hε haε hεhalf, norm_mul, norm_pow]
  have hnorm : ‖(2 * Real.pi * Complex.I * (n : ℝ) : ℂ)‖ =
      2 * Real.pi * |(n : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    norm_num [abs_of_pos Real.pi_pos]
  rw [hnorm]
  ring

private theorem fourierCoeffOn_zero_one_eq_unitFourierCoefficientInt
    (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n =
      unitFourierCoefficientInt f n := by
  rw [fourierCoeffOn_eq_integral]
  unfold unitFourierCoefficientInt
  norm_num [fourier_coe_apply, paperExp]
  apply intervalIntegral.integral_congr
  intro alpha _halpha
  have hstar :
      (starRingEnd ℂ)
          (Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * n * alpha)) =
        Complex.exp
          (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) * alpha))) := by
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp [map_mul, map_ofNat, Complex.conj_I]
    ring
  change
    (starRingEnd ℂ)
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * alpha)) *
      f alpha =
    f alpha *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) * alpha)))
  rw [hstar]
  ring

private theorem memLp_two_iteratedDeriv_smoothNearPrimitivePoleSum_Ioc
    (a ε : ℝ) (p j : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    MemLp (iteratedDeriv j (smoothNearPrimitivePoleSum a ε p)) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hcont : Continuous
      (iteratedDeriv j (smoothNearPrimitivePoleSum a ε p)) := by
    rw [iteratedDeriv_eq_iterate]
    exact (smoothNearPrimitivePoleSum_contDiff a ε p ha haε).iterate_deriv j
      |>.continuous
  have hmeas : AEStronglyMeasurable
      (iteratedDeriv j (smoothNearPrimitivePoleSum a ε p))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hcont.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  exact hcont.norm.pow 2 |>.integrableOn_Ioc

/-- Parseval identifies the complete formal derivative energy with the
physical derivative mass, before the Gevrey estimate is inserted. -/
theorem tsum_fourierDerivativeWeight_smoothNearPrimitivePoleSum_eq
    (a ε : ℝ) (p j : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    (∑' n : ℤ, (2 * Real.pi * |(n : ℝ)|) ^ (2 * j) *
        ‖unitFourierCoefficientInt
          (smoothNearPrimitivePoleSum a ε p) n‖ ^ 2) =
      ∫ alpha in (0 : ℝ)..1,
        ‖iteratedDeriv j
          (smoothNearPrimitivePoleSum a ε p) alpha‖ ^ 2 := by
  have hparseval := tsum_sq_fourierCoeffOn
    (by norm_num : (0 : ℝ) < 1)
    (memLp_two_iteratedDeriv_smoothNearPrimitivePoleSum_Ioc
      a ε p j ha haε)
  norm_num at hparseval
  rw [← hparseval]
  apply tsum_congr
  intro n
  rw [fourier_weight_mul_norm_sq_eq_deriv_coefficient_norm_sq
      a ε p j n hp ha hε haε hεhalf,
    fourierCoeffOn_zero_one_eq_unitFourierCoefficientInt]

/-- The formal derivative energy of one physical Bernoulli carrier is
bounded by the exact Gevrey derivative mass. -/
theorem fourierDerivativeEnergy_physicalNearCarrier_le_gevrey
    (p j : ℕ) (ell : ℤ) (a ε : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    fourierDerivativeEnergy j
        (fun k ↦ bernoulliMarkFourierCoefficient ell *
          unitFourierCoefficientInt
            (smoothNearPrimitivePoleSum a ε p) k) ≤
      ENNReal.ofReal
        (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
            (((p : ℝ) ^ 2) ^ j) ^ 2 *
              ((2 * nearGevreyProfileConstant * 192 ^ j *
                (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a)))) := by
  let d : ℤ → ℝ := fun k ↦
    ‖unitFourierCoefficientInt
      (iteratedDeriv j (smoothNearPrimitivePoleSum a ε p)) k‖ ^ 2
  have hsum : Summable d := by
    have hparseval := hasSum_sq_fourierCoeffOn
      (by norm_num : (0 : ℝ) < 1)
      (memLp_two_iteratedDeriv_smoothNearPrimitivePoleSum_Ioc
        a ε p j ha haε)
    have hrewritten : (fun k : ℤ ↦
        ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
          (iteratedDeriv j (smoothNearPrimitivePoleSum a ε p)) k‖ ^ 2) = d := by
      funext k
      rw [fourierCoeffOn_zero_one_eq_unitFourierCoefficientInt]
    rw [hrewritten] at hparseval
    exact hparseval.summable
  have henergy : fourierDerivativeEnergy j
        (fun k ↦ bernoulliMarkFourierCoefficient ell *
          unitFourierCoefficientInt
            (smoothNearPrimitivePoleSum a ε p) k) =
      ENNReal.ofReal
        (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          (∫ alpha in (0 : ℝ)..1,
            ‖iteratedDeriv j
              (smoothNearPrimitivePoleSum a ε p) alpha‖ ^ 2)) := by
    unfold fourierDerivativeEnergy
    calc
      (∑' k : ℤ, ENNReal.ofReal
        ((2 * Real.pi * |(k : ℝ)|) ^ (2 * j) *
          ‖bernoulliMarkFourierCoefficient ell *
            unitFourierCoefficientInt
              (smoothNearPrimitivePoleSum a ε p) k‖ ^ 2)) =
        ∑' k : ℤ, ENNReal.ofReal
          (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 * d k) := by
          apply tsum_congr
          intro k
          apply congrArg ENNReal.ofReal
          rw [norm_mul]
          calc
            (2 * Real.pi * |(k : ℝ)|) ^ (2 * j) *
                (‖bernoulliMarkFourierCoefficient ell‖ *
                  ‖unitFourierCoefficientInt
                    (smoothNearPrimitivePoleSum a ε p) k‖) ^ 2 =
              ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
                ((2 * Real.pi * |(k : ℝ)|) ^ (2 * j) *
                  ‖unitFourierCoefficientInt
                    (smoothNearPrimitivePoleSum a ε p) k‖ ^ 2) := by ring
            _ = ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 * d k := by
              rw [fourier_weight_mul_norm_sq_eq_deriv_coefficient_norm_sq
                a ε p j k hp ha hε haε hεhalf]
      _ = ENNReal.ofReal (‖bernoulliMarkFourierCoefficient ell‖ ^ 2) *
          ∑' k : ℤ, ENNReal.ofReal (d k) := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro k
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      _ = ENNReal.ofReal (‖bernoulliMarkFourierCoefficient ell‖ ^ 2) *
          ENNReal.ofReal (∑' k : ℤ, d k) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hsum]
      _ = ENNReal.ofReal
          (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
            (∫ alpha in (0 : ℝ)..1,
              ‖iteratedDeriv j
                (smoothNearPrimitivePoleSum a ε p) alpha‖ ^ 2)) := by
        have htsumd : (∑' k : ℤ, d k) =
            ∫ alpha in (0 : ℝ)..1,
              ‖iteratedDeriv j
                (smoothNearPrimitivePoleSum a ε p) alpha‖ ^ 2 := by
          rw [← tsum_fourierDerivativeWeight_smoothNearPrimitivePoleSum_eq
            a ε p j hp ha hε haε hεhalf]
          apply tsum_congr
          intro k
          exact (fourier_weight_mul_norm_sq_eq_deriv_coefficient_norm_sq
            a ε p j k hp ha hε haε hεhalf).symm
        rw [htsumd, ← ENNReal.ofReal_mul (sq_nonneg _)]
  rw [henergy]
  apply ENNReal.ofReal_le_ofReal
  have hmass :=
    integral_unit_norm_iteratedDeriv_smoothNearPrimitivePoleSum_sq_le_gevrey
      j p a ε hp ha hε haε hεhalf
  exact mul_le_mul_of_nonneg_left hmass (sq_nonneg _)

/-- Fully physical annular leakage bound for one denominator and one
nonzero Bernoulli mode.  The annular separation, Fourier leakage estimate,
Parseval identity, disjoint-cell scaling, and Gevrey bound are all composed
here without an intervening formal hypothesis. -/
theorem coefficientEnergy_physicalNearCarrier_annulus_scaled_le_gevrey
    (N p P j : ℕ) (ell : ℤ) (a ε : ℝ)
    (hN : 0 < N) (hP : 0 < P) (hp : 2 ≤ p) (hell : ell ≠ 0)
    (hpLower : P < 2 * p) (hpUpper : p ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    ENNReal.ofReal
        ((2 * Real.pi * (nearCarrierScale N ell P / 4)) ^ (2 * j)) *
      coefficientEnergy (fun n ↦
        unitFourierCoefficientInt
            (smoothNearPrimitivePoleCarrierTerm N ell a ε p) n -
          projectCoefficients (nearCarrierAnnulus N ell P)
            (unitFourierCoefficientInt
              (smoothNearPrimitivePoleCarrierTerm N ell a ε p)) n) ≤
      ENNReal.ofReal
        (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
            (((p : ℝ) ^ 2) ^ j) ^ 2 *
              ((2 * nearGevreyProfileConstant * 192 ^ j *
                (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a)))) := by
  calc
    ENNReal.ofReal
          ((2 * Real.pi * (nearCarrierScale N ell P / 4)) ^ (2 * j)) *
        coefficientEnergy (fun n ↦
          unitFourierCoefficientInt
              (smoothNearPrimitivePoleCarrierTerm N ell a ε p) n -
            projectCoefficients (nearCarrierAnnulus N ell P)
              (unitFourierCoefficientInt
                (smoothNearPrimitivePoleCarrierTerm N ell a ε p)) n) ≤
      fourierDerivativeEnergy j
        (fun k ↦ bernoulliMarkFourierCoefficient ell *
          unitFourierCoefficientInt
            (smoothNearPrimitivePoleSum a ε p) k) := by
      exact coefficientEnergy_physicalNearCarrier_le_derivativeEnergy
        N p ell a ε (nearCarrierAnnulus N ell P)
        (nearCarrierScale N ell P / 4) j
        (div_nonneg (nearCarrierScale_pos hN hP hell).le (by norm_num))
        (fun k hk ↦ nearCarrier_annulus_separation
          hN hP hell hpLower hpUpper k hk)
    _ ≤ ENNReal.ofReal
        (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
            (((p : ℝ) ^ 2) ^ j) ^ 2 *
              ((2 * nearGevreyProfileConstant * 192 ^ j *
                (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a)))) :=
      fourierDerivativeEnergy_physicalNearCarrier_le_gevrey
        p j ell a ε hp ha hε haε hεhalf

/-! ## A complete dyadic denominator block -/

/-- Cauchy--Schwarz in the finite summation index, followed by summation in
frequency.  This is the squared form of the triangle estimate used for the
leakage of a denominator block. -/
theorem coefficientEnergy_finset_sum_le_card_mul_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℤ → ℂ) :
    coefficientEnergy (fun n ↦ ∑ i ∈ s, c i n) ≤
      s.card * ∑ i ∈ s, coefficientEnergy (c i) := by
  have hoverlap : ∀ n : ℤ,
      frequencyOverlapCount s (fun _i ↦ (Set.univ : Set ℤ)) n ≤ s.card := by
    intro n
    simp [frequencyOverlapCount]
  simpa only [projectCoefficients, Set.mem_univ, if_true] using!
    (coefficientEnergy_sum_projected_le_overlap
      s (fun _i ↦ (Set.univ : Set ℤ)) c s.card hoverlap)

/-- A scaled version in which a common derivative-loss factor is absorbed
by a separate estimate for each summand. -/
theorem coefficientEnergy_finset_sum_scaled_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℤ → ℂ)
    (scale : ENNReal) (R : ι → ENNReal)
    (hindividual : ∀ i ∈ s,
      scale * coefficientEnergy (c i) ≤ R i) :
    scale * coefficientEnergy (fun n ↦ ∑ i ∈ s, c i n) ≤
      s.card * ∑ i ∈ s, R i := by
  calc
    scale * coefficientEnergy (fun n ↦ ∑ i ∈ s, c i n) ≤
        scale * (s.card * ∑ i ∈ s, coefficientEnergy (c i)) :=
      mul_le_mul_right
        (coefficientEnergy_finset_sum_le_card_mul_sum s c) scale
    _ = s.card * (scale * ∑ i ∈ s, coefficientEnergy (c i)) := by
      ac_rfl
    _ = s.card * ∑ i ∈ s, scale * coefficientEnergy (c i) := by
      rw [Finset.mul_sum]
    _ ≤ s.card * ∑ i ∈ s, R i := by
      gcongr with i hi
      exact hindividual i hi

/-- Coefficient sequence leaking from the common annulus of the dyadic
denominator block `(P/2,P]`. -/
def physicalNearCarrierBlockLeakageCoefficients
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (P : ℕ) (n : ℤ) : ℂ :=
  ∑ p ∈ Finset.Ioc (P / 2) P,
    (unitFourierCoefficientInt
        (smoothNearPrimitivePoleCarrierTerm N ell a ε p) n -
      projectCoefficients (nearCarrierAnnulus N ell P)
        (unitFourierCoefficientInt
          (smoothNearPrimitivePoleCarrierTerm N ell a ε p)) n)

/-- Exact dyadic-block leakage estimate.  The right side is a finite,
fully explicit sum; no unrecorded `j`-dependent constant remains. -/
theorem coefficientEnergy_physicalNearCarrierBlock_scaled_le_gevrey
    (N P j : ℕ) (ell : ℤ) (a ε : ℝ)
    (hN : 0 < N) (hP : 4 ≤ P) (hell : ell ≠ 0)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    ENNReal.ofReal
        ((2 * Real.pi * (nearCarrierScale N ell P / 4)) ^ (2 * j)) *
      coefficientEnergy
        (physicalNearCarrierBlockLeakageCoefficients N ell a ε P) ≤
      (Finset.Ioc (P / 2) P).card *
        ∑ p ∈ Finset.Ioc (P / 2) P,
          ENNReal.ofReal
            (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
              ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
                (((p : ℝ) ^ 2) ^ j) ^ 2 *
                  ((2 * nearGevreyProfileConstant * 192 ^ j *
                    (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 *
                      (32 / a)))) := by
  let s := Finset.Ioc (P / 2) P
  let scale : ENNReal := ENNReal.ofReal
    ((2 * Real.pi * (nearCarrierScale N ell P / 4)) ^ (2 * j))
  let c : ℕ → ℤ → ℂ := fun p n ↦
    unitFourierCoefficientInt
        (smoothNearPrimitivePoleCarrierTerm N ell a ε p) n -
      projectCoefficients (nearCarrierAnnulus N ell P)
        (unitFourierCoefficientInt
          (smoothNearPrimitivePoleCarrierTerm N ell a ε p)) n
  let R : ℕ → ENNReal := fun p ↦ ENNReal.ofReal
    (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
      ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
        (((p : ℝ) ^ 2) ^ j) ^ 2 *
          ((2 * nearGevreyProfileConstant * 192 ^ j *
            (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a))))
  have hindividual : ∀ p ∈ s,
      scale * coefficientEnergy (c p) ≤ R p := by
    intro p hpMem
    have hpBounds := Finset.mem_Ioc.mp hpMem
    have hpTwo : 2 ≤ p := by
      have hhalf : 2 ≤ P / 2 :=
        (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 (by omega)
      omega
    have hpLower : P < 2 * p := by
      have hdecomp := Nat.mod_add_div P 2
      have hmod := Nat.mod_lt P (by omega : 0 < 2)
      omega
    exact coefficientEnergy_physicalNearCarrier_annulus_scaled_le_gevrey
      N p P j ell a ε hN (by omega) hpTwo hell hpLower hpBounds.2
      ha hε haε hεhalf
  have hblock := coefficientEnergy_finset_sum_scaled_le
    s c scale R hindividual
  simpa only [s, scale, c, R,
    physicalNearCarrierBlockLeakageCoefficients] using! hblock

private theorem dyadic_totient_derivative_factor_le
    (p P j : ℕ) (hp : 0 < p) (hP : 0 < P)
    (hpLower : P < 2 * p) (hpUpper : p ≤ P) :
    (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
        (((p : ℝ) ^ 2) ^ j) ^ 2 ≤
      (2 / (P : ℝ)) * (P : ℝ) ^ (4 * j) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hPR : 0 < (P : ℝ) := by exact_mod_cast hP
  have htot : (Nat.totient p : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast Nat.totient_le p
  have hfirst : (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) ≤
      1 / (p : ℝ) := by
    calc
      (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) ≤
          (p : ℝ) * (1 / (p : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right htot (by positivity)
      _ = 1 / (p : ℝ) := by field_simp
  have hrecip : 1 / (p : ℝ) ≤ 2 / (P : ℝ) := by
    rw [div_le_div_iff₀ hpR hPR]
    have hcast : (P : ℝ) < 2 * (p : ℝ) := by exact_mod_cast hpLower
    nlinarith
  have hpow : (((p : ℝ) ^ 2) ^ j) ^ 2 ≤
      (P : ℝ) ^ (4 * j) := by
    rw [show (((p : ℝ) ^ 2) ^ j) ^ 2 = (p : ℝ) ^ (4 * j) by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hpUpper) _
  exact mul_le_mul (hfirst.trans hrecip) hpow (by positivity) (by positivity)

/-- A scalar majorant for the preceding exact finite sum.  Its shape is
the squared paper bound: after division by the displayed carrier scale it
is a constant times `(P/(Na))^(2j) (P/a)`. -/
theorem coefficientEnergy_physicalNearCarrierBlock_scaled_le_scalarGevrey
    (N P j : ℕ) (ell : ℤ) (a ε : ℝ)
    (hN : 0 < N) (hP : 4 ≤ P) (hell : ell ≠ 0)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    ENNReal.ofReal
        ((2 * Real.pi * (nearCarrierScale N ell P / 4)) ^ (2 * j)) *
      coefficientEnergy
        (physicalNearCarrierBlockLeakageCoefficients N ell a ε P) ≤
      (P : ENNReal) ^ 2 *
        ENNReal.ofReal
          (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
            ((2 / (P : ℝ)) * (P : ℝ) ^ (4 * j)) *
              ((2 * nearGevreyProfileConstant * 192 ^ j *
                (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a))) := by
  let s := Finset.Ioc (P / 2) P
  let G : ℝ :=
    (2 * nearGevreyProfileConstant * 192 ^ j *
      (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a)
  let C : ℝ := ‖bernoulliMarkFourierCoefficient ell‖ ^ 2
  let M : ENNReal := ENNReal.ofReal
    (C * ((2 / (P : ℝ)) * (P : ℝ) ^ (4 * j)) * G)
  have hG : 0 ≤ G := by
    dsimp [G]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hterm : ∀ p ∈ s,
      ENNReal.ofReal
          (C * ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
            (((p : ℝ) ^ 2) ^ j) ^ 2) * G) ≤ M := by
    intro p hpMem
    have hpBounds := Finset.mem_Ioc.mp hpMem
    have hpPos : 0 < p := by omega
    have hpLower : P < 2 * p := by
      have hdecomp := Nat.mod_add_div P 2
      have hmod := Nat.mod_lt P (by omega : 0 < 2)
      omega
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (dyadic_totient_derivative_factor_le
          p P j hpPos (by omega) hpLower hpBounds.2) hC) hG
  have hblock :=
    coefficientEnergy_physicalNearCarrierBlock_scaled_le_gevrey
      N P j ell a ε hN hP hell ha hε haε hεhalf
  have hcardNat : s.card ≤ P := by
    dsimp [s]
    rw [Nat.card_Ioc]
    omega
  have hcard : (s.card : ENNReal) ≤ (P : ENNReal) := by
    exact_mod_cast hcardNat
  calc
    ENNReal.ofReal
          ((2 * Real.pi * (nearCarrierScale N ell P / 4)) ^ (2 * j)) *
        coefficientEnergy
          (physicalNearCarrierBlockLeakageCoefficients N ell a ε P) ≤
      s.card * ∑ p ∈ s, ENNReal.ofReal
        (C * ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
          (((p : ℝ) ^ 2) ^ j) ^ 2) * G) := by
      simpa only [s, C, G, mul_assoc] using! hblock
    _ ≤ s.card * ∑ _p ∈ s, M := by
      gcongr with p hpMem
      exact hterm p hpMem
    _ = (s.card : ENNReal) ^ 2 * M := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (P : ENNReal) ^ 2 * M := by
      gcongr
    _ = (P : ENNReal) ^ 2 *
        ENNReal.ofReal
          (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
            ((2 / (P : ℝ)) * (P : ℝ) ^ (4 * j)) *
              ((2 * nearGevreyProfileConstant * 192 ^ j *
                (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a))) := by
      rfl

end

end Erdos1002
