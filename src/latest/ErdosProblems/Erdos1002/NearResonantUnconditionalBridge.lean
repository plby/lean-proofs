import ErdosProblems.Erdos1002.ChanKumchevElementaryNearTail
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Unconditional analytic bridge for the near-resonant multiplier

The arithmetic estimate in `ChanKumchevElementaryNearTail` already crosses
the square-root denominator threshold without a Chan--Kumchev hypothesis.
This file supplies the complementary large-frequency fact used when the
denominator lies below the principal band: the multiplier `nearJ` tends to
zero at infinity and admits an explicit `1 / (a t)` bound.

The proof is direct.  Riemann--Lebesgue gives the terminal value of `nearJ`,
the fundamental theorem of calculus writes `nearJ t` as the integral of its
derivative over `(t, infinity)`, and the previously proved two-scale
derivative envelope is integrated exactly.  No analytic-number-theory input
appears in this file.
-/

open Filter MeasureTheory Set

namespace Erdos1002

noncomputable section

/-! ## Decay of the real-line multiplier -/

/-- The near-resonant multiplier tends to zero along the positive real
half-line. -/
theorem nearJ_tendsto_atTop_zero (a ε : ℝ) :
    Tendsto (nearJ a ε) atTop (nhds 0) := by
  exact (Real.zero_at_infty_fourier (nearW a ε)).mono_left
    atTop_le_cocompact

/-- Exact tail mass of one scale-normalized reciprocal-square envelope. -/
theorem integral_scaleDecayEnvelope_Ioi_tail
    (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    ∫ u in Ioi t, scaleDecayEnvelope s u = 1 / (1 + s * t) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := t) (m := (0 : ℝ))
    (fun u hu => hasDerivAt_scaleDecayPrimitive s u hs (ht.trans hu))
    ((scaleDecayEnvelope_integrableOn_Ioi s hs).mono_set
      (fun u hu => ht.trans_lt hu))
    (scaleDecayPrimitive_tendsto_atTop_zero s hs)
  simpa [scaleDecayPrimitive] using! h

/-- Exact tail mass of the two-scale envelope controlling `nearJ'`. -/
theorem integral_nearRhoEnvelope_Ioi_tail
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (ht : 0 ≤ t) :
    ∫ u in Ioi t, nearRhoEnvelope a ε u =
      4 * nearProfileDecayConstant *
        (1 / (1 + (ε / 2) * t) + 1 / (1 + a * t)) := by
  have hout := (scaleDecayEnvelope_integrableOn_Ioi (ε / 2) (by positivity)).mono_set
    (fun u hu => ht.trans_lt hu)
  have hin := (scaleDecayEnvelope_integrableOn_Ioi a ha).mono_set
    (fun u hu => ht.trans_lt hu)
  have heq : nearRhoEnvelope a ε =ᵐ[volume.restrict (Ioi t)]
      fun u => 4 * nearProfileDecayConstant *
        (scaleDecayEnvelope (ε / 2) u + scaleDecayEnvelope a u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact nearRhoEnvelope_eq_scaleDecay_of_nonneg a ε u (ht.trans hu.le)
  have hsplit :
      (∫ u in Ioi t,
        (scaleDecayEnvelope (ε / 2) u + scaleDecayEnvelope a u)) =
        (∫ u in Ioi t, scaleDecayEnvelope (ε / 2) u) +
          ∫ u in Ioi t, scaleDecayEnvelope a u :=
    MeasureTheory.integral_add hout hin
  rw [integral_congr_ae heq, integral_const_mul, hsplit,
    integral_scaleDecayEnvelope_Ioi_tail (ε / 2) t (by positivity) ht,
    integral_scaleDecayEnvelope_Ioi_tail a t ha ht]

/-- The derivative of `nearJ` is integrable on every positive tail. -/
theorem nearJ_deriv_integrableOn_Ioi
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (ht : 0 ≤ t) :
    IntegrableOn (fun u => deriv (nearJ a ε) u) (Ioi t) := by
  have henv : IntegrableOn
      (fun u => 2 * Real.pi * nearRhoEnvelope a ε u) (Ioi t) :=
    ((nearRhoEnvelope_integrableOn_Ioi a ε ha hε).mono_set
      (fun u hu => ht.trans_lt hu)).const_mul (2 * Real.pi)
  apply henv.mono'
  · exact (nearJ_deriv_continuous a ε ha hε haε).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _hu
    exact norm_nearJ_deriv_le a ε u ha hε haε

/-- Fundamental-theorem-of-calculus representation of the multiplier by
the tail of its derivative. -/
theorem nearJ_eq_neg_integral_deriv_Ioi
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (ht : 0 ≤ t) :
    nearJ a ε t = -∫ u in Ioi t, deriv (nearJ a ε) u := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := t) (m := (0 : ℂ))
    (fun u _hu => (nearJ_differentiableAt a ε u ha hε haε).hasDerivAt)
    (nearJ_deriv_integrableOn_Ioi a ε t ha hε haε ht)
    (nearJ_tendsto_atTop_zero a ε)
  have h' : (∫ u in Ioi t, deriv (nearJ a ε) u) = -nearJ a ε t := by
    simpa using! h
  rw [h']
  simp

/-- Explicit two-scale large-frequency bound for the near multiplier. -/
theorem norm_nearJ_le_twoScaleTail
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (ht : 0 ≤ t) :
    ‖nearJ a ε t‖ ≤
      8 * Real.pi * nearProfileDecayConstant *
        (1 / (1 + (ε / 2) * t) + 1 / (1 + a * t)) := by
  rw [nearJ_eq_neg_integral_deriv_Ioi a ε t ha hε haε ht, norm_neg]
  have henv : IntegrableOn
      (fun u => 2 * Real.pi * nearRhoEnvelope a ε u) (Ioi t) :=
    ((nearRhoEnvelope_integrableOn_Ioi a ε ha hε).mono_set
      (fun u hu => ht.trans_lt hu)).const_mul (2 * Real.pi)
  calc
    ‖∫ u in Ioi t, deriv (nearJ a ε) u‖ ≤
        ∫ u in Ioi t, 2 * Real.pi * nearRhoEnvelope a ε u := by
      apply norm_integral_le_of_norm_le henv
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _hu
      exact norm_nearJ_deriv_le a ε u ha hε haε
    _ = 2 * Real.pi *
        (4 * nearProfileDecayConstant *
          (1 / (1 + (ε / 2) * t) + 1 / (1 + a * t))) := by
      rw [integral_const_mul,
        integral_nearRhoEnvelope_Ioi_tail a ε t ha hε ht]
    _ = 8 * Real.pi * nearProfileDecayConstant *
        (1 / (1 + (ε / 2) * t) + 1 / (1 + a * t)) := by ring

/-- Simplified `1 / (a t)` decay.  This is the estimate needed below the
principal denominator band, where `t = n / p^2` is large. -/
theorem norm_nearJ_le_inv_mul
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (ht : 0 < t) :
    ‖nearJ a ε t‖ ≤
      16 * Real.pi * nearProfileDecayConstant / (a * t) := by
  have hat : 0 < a * t := mul_pos ha ht
  have houterScale : a ≤ ε / 2 := by linarith
  have houterDen : a * t ≤ 1 + (ε / 2) * t := by
    have := mul_le_mul_of_nonneg_right houterScale ht.le
    linarith
  have hinnerDen : a * t ≤ 1 + a * t := by linarith
  have houter : 1 / (1 + (ε / 2) * t) ≤ 1 / (a * t) := by
    exact one_div_le_one_div_of_le hat houterDen
  have hinner : 1 / (1 + a * t) ≤ 1 / (a * t) := by
    exact one_div_le_one_div_of_le hat hinnerDen
  calc
    ‖nearJ a ε t‖ ≤
        8 * Real.pi * nearProfileDecayConstant *
          (1 / (1 + (ε / 2) * t) + 1 / (1 + a * t)) :=
      norm_nearJ_le_twoScaleTail a ε t ha hε haε ht.le
    _ ≤ 8 * Real.pi * nearProfileDecayConstant *
          (1 / (a * t) + 1 / (a * t)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add houter hinner)
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
          nearProfileDecayConstant_nonneg)
    _ = 16 * Real.pi * nearProfileDecayConstant / (a * t) := by ring

/-- Supremum bound for the sampled multiplier on `K < n ≤ 2K` when a
positive denominator `U` lies below the principal band.  The decay factor is
displayed as `U² / (a K)`, exactly the form used in the low-denominator shell
argument. -/
theorem norm_nearJDyadicMultiplierVector_le_lowDenominator
    (a ε : ℝ) (K U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hU : 0 < U) :
    ‖nearJDyadicMultiplierVector a ε K (U : ℝ)‖ ≤
      16 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
        (a * (K : ℝ)) := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hUR : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  have hconstant : 0 ≤ 16 * Real.pi * nearProfileDecayConstant :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
      nearProfileDecayConstant_nonneg
  have hnum : 0 ≤
      16 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 :=
    mul_nonneg hconstant (sq_nonneg _)
  have hbound : 0 ≤
      16 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
        (a * (K : ℝ)) :=
    div_nonneg hnum (mul_nonneg ha.le hKR.le)
  apply (pi_norm_le_iff_of_nonneg hbound).mpr
  intro n
  have hnBounds := Finset.mem_Ioc.mp n.property
  have hnR : (0 : ℝ) < ((n : ℕ) : ℝ) := by
    exact_mod_cast hK.trans hnBounds.1
  have hKn : (K : ℝ) ≤ ((n : ℕ) : ℝ) := by
    exact_mod_cast hnBounds.1.le
  have ht : 0 < ((n : ℕ) : ℝ) / (U : ℝ) ^ 2 := by positivity
  have hden : a * (K : ℝ) ≤ a * ((n : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hKn ha.le
  have hrearrange :
      16 * Real.pi * nearProfileDecayConstant /
          (a * (((n : ℕ) : ℝ) / (U : ℝ) ^ 2)) =
        16 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
          (a * ((n : ℕ) : ℝ)) := by
    field_simp [ha.ne', hUR.ne', hnR.ne']
  calc
    ‖nearJDyadicMultiplierVector a ε K (U : ℝ) n‖ =
        ‖nearJ a ε (((n : ℕ) : ℝ) / (U : ℝ) ^ 2)‖ := rfl
    _ ≤ 16 * Real.pi * nearProfileDecayConstant /
          (a * (((n : ℕ) : ℝ) / (U : ℝ) ^ 2)) :=
      norm_nearJ_le_inv_mul a ε _ ha hε haε ht
    _ = 16 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
          (a * ((n : ℕ) : ℝ)) := hrearrange
    _ ≤ 16 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
          (a * (K : ℝ)) :=
      div_le_div_of_nonneg_left hnum (mul_pos ha hKR) hden

/-! ## Localized variation below the principal denominator band -/

theorem scaleReciprocalDecayEnvelope_le_linear
    (K s x : ℝ) (hK : 0 < K) (hs : 0 < s) (hx : 0 ≤ x) :
    scaleReciprocalDecayEnvelope K s x ≤ 2 * x / (K * s) := by
  unfold scaleReciprocalDecayEnvelope
  have hKs : 0 < K * s := mul_pos hK hs
  have hden : 0 < (x ^ 2 + K * s) ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  rw [div_mul_eq_mul_div, le_div_iff₀ hKs]
  have hbase : K * s ≤ x ^ 2 + K * s := by nlinarith [sq_nonneg x]
  have hsquare : (K * s) ^ 2 ≤ (x ^ 2 + K * s) ^ 2 :=
    pow_le_pow_left₀ hKs.le hbase 2
  calc
    2 * K * s * x * (K * s) = 2 * x * (K * s) ^ 2 := by ring
    _ ≤ 2 * x * (x ^ 2 + K * s) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)

theorem nearJReciprocalSquareEnvelope_le_lowDenominator
    (a ε K x : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hK : 0 < K) (hx : 0 ≤ x) :
    nearJReciprocalSquareEnvelope a ε K x ≤
      64 * Real.pi * nearProfileDecayConstant * x / (K * a) := by
  have hout := scaleReciprocalDecayEnvelope_le_linear
    K (ε / 2) x hK (by positivity) hx
  have hin := scaleReciprocalDecayEnvelope_le_linear K a x hK ha hx
  have hscale : K * a ≤ K * (ε / 2) := by
    apply mul_le_mul_of_nonneg_left _ hK.le
    linarith
  have hnum : 0 ≤ 2 * x := by positivity
  have houterDen : 0 < K * a := mul_pos hK ha
  have houter : 2 * x / (K * (ε / 2)) ≤ 2 * x / (K * a) :=
    div_le_div_of_nonneg_left hnum houterDen hscale
  unfold nearJReciprocalSquareEnvelope
  calc
    16 * Real.pi * nearProfileDecayConstant *
        (scaleReciprocalDecayEnvelope K (ε / 2) x +
          scaleReciprocalDecayEnvelope K a x) ≤
      16 * Real.pi * nearProfileDecayConstant *
        (2 * x / (K * (ε / 2)) + 2 * x / (K * a)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hout hin)
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
          nearProfileDecayConstant_nonneg)
    _ ≤ 16 * Real.pi * nearProfileDecayConstant *
        (2 * x / (K * a) + 2 * x / (K * a)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add houter le_rfl)
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
          nearProfileDecayConstant_nonneg)
    _ = 64 * Real.pi * nearProfileDecayConstant * x / (K * a) := by ring

/-- The variation on a finite denominator interval below the principal band
retains the factor `U²/(aK)`; using only total variation here would lose a
logarithm in the global zero-carrier sum. -/
theorem sum_norm_nearJDyadicMultiplierVector_sub_succ_le_lowDenominator
    (a ε : ℝ) (K P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hP : 0 < P) (hPU : P ≤ U) :
    ∑ p ∈ Finset.Ico P U,
        ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
          nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
      32 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
        (a * (K : ℝ)) := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hUR : (0 : ℝ) ≤ (U : ℝ) := by positivity
  have hPUR : (P : ℝ) ≤ (U : ℝ) := by exact_mod_cast hPU
  have hmaxInt : IntervalIntegrable
      (nearJReciprocalSquareDyadicMax a ε K) volume (P : ℝ) (U : ℝ) := by
    rw [intervalIntegrable_iff, uIoc_of_le hPUR]
    exact (nearJReciprocalSquareDyadicMax_integrableOn_Ioi
      a ε K ha hε haε hK).mono_set (fun x hx ↦ hPR.trans hx.1)
  have hlinearInt : IntervalIntegrable
      (fun x : ℝ ↦ 64 * Real.pi * nearProfileDecayConstant * x /
        ((K : ℝ) * a)) volume (P : ℝ) (U : ℝ) := by
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      64 * Real.pi * nearProfileDecayConstant * x / ((K : ℝ) * a))).intervalIntegrable _ _
  calc
    ∑ p ∈ Finset.Ico P U,
        ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
          nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
      ∫ x : ℝ in (P : ℝ)..(U : ℝ),
        nearJReciprocalSquareDyadicMax a ε K x :=
      sum_norm_nearJDyadicMultiplierVector_sub_succ_le_intervalIntegral
        a ε K P U ha hε haε hK hP hPU
    _ ≤ ∫ x : ℝ in (P : ℝ)..(U : ℝ),
        64 * Real.pi * nearProfileDecayConstant * x / ((K : ℝ) * a) := by
      apply intervalIntegral.integral_mono_on hPUR hmaxInt hlinearInt
      intro x hx
      exact (nearJReciprocalSquareDyadicMax_le_envelope
        a ε K ha hε haε hK (hPR.trans_le hx.1)).trans
          (nearJReciprocalSquareEnvelope_le_lowDenominator
            a ε (K : ℝ) x ha hε haε hKR (hPR.le.trans hx.1))
    _ = 32 * Real.pi * nearProfileDecayConstant *
        (((U : ℝ) ^ 2 - (P : ℝ) ^ 2) / ((K : ℝ) * a)) := by
      rw [show (fun x : ℝ ↦
          64 * Real.pi * nearProfileDecayConstant * x / ((K : ℝ) * a)) =
        (fun x : ℝ ↦
          (64 * Real.pi * nearProfileDecayConstant / ((K : ℝ) * a)) * x) by
        funext x
        ring,
        intervalIntegral.integral_const_mul, integral_id]
      ring
    _ ≤ 32 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
        (a * (K : ℝ)) := by
      have hconst : 0 ≤ 32 * Real.pi * nearProfileDecayConstant := by
        exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
          nearProfileDecayConstant_nonneg
      have hden : 0 < (K : ℝ) * a := mul_pos hKR ha
      have hdiff : (U : ℝ) ^ 2 - (P : ℝ) ^ 2 ≤ (U : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (P : ℝ)]
      rw [show a * (K : ℝ) = (K : ℝ) * a by ring]
      calc
        32 * Real.pi * nearProfileDecayConstant *
            (((U : ℝ) ^ 2 - (P : ℝ) ^ 2) / ((K : ℝ) * a)) =
          (32 * Real.pi * nearProfileDecayConstant *
            ((U : ℝ) ^ 2 - (P : ℝ) ^ 2)) / ((K : ℝ) * a) := by ring
        _ ≤ (32 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2) /
            ((K : ℝ) * a) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdiff hconst) hden.le

theorem nearJDyadicMultiplierVector_terminal_add_variation_le_lowDenominator
    (a ε : ℝ) (K P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hP : 0 < P) (hPU : P ≤ U) :
    ‖nearJDyadicMultiplierVector a ε K (U : ℝ)‖ +
        ∑ p ∈ Finset.Ico P U,
          ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
            nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
      48 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
        (a * (K : ℝ)) := by
  have hterminal := norm_nearJDyadicMultiplierVector_le_lowDenominator
    a ε K U ha hε haε hK (hP.trans_le hPU)
  have hvariation :=
    sum_norm_nearJDyadicMultiplierVector_sub_succ_le_lowDenominator
      a ε K P U ha hε haε hK hP hPU
  calc
    ‖nearJDyadicMultiplierVector a ε K (U : ℝ)‖ +
        ∑ p ∈ Finset.Ico P U,
          ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
            nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
      16 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
          (a * (K : ℝ)) +
        32 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
          (a * (K : ℝ)) := add_le_add hterminal hvariation
    _ = 48 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
        (a * (K : ℝ)) := by ring

/-- One complete denominator shell below the principal band.  The
Ramanujan partial sum contributes `sqrt(K)/Q`, while localized multiplier
variation contributes `Q²/(aK)`. -/
theorem norm_finiteNearRamanujanMultiplierVector_dyadic_le_lowDenominator
    (a ε : ℝ) (K Q : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hQ : 0 < Q) (hQK : Q ^ 2 ≤ K) :
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) (2 * Q)‖ ≤
      Real.sqrt (42 * (K : ℝ) / (Q : ℝ) ^ 2) *
        (48 * Real.pi * nearProfileDecayConstant * (2 * Q : ℕ) ^ 2 /
          (a * (K : ℝ))) := by
  have hQU : Q + 1 ≤ 2 * Q := by omega
  have hraw := norm_euclidean_vector_sum_coordinateMul_le
    (nearRamanujanVectorTerm K)
    (fun p ↦ nearJDyadicMultiplierVector a ε K (p : ℝ))
    hQU (Real.sqrt (42 * (K : ℝ) / (Q : ℝ) ^ 2))
    (fun R hR ↦
      norm_euclideanIntervalPartialSum_nearRamanujan_dyadic_le_lowRange
        K Q R hQ hQK hR)
  rw [show
      (∑ n ∈ Finset.Icc (Q + 1) (2 * Q),
        euclideanCoordinateMul (nearRamanujanVectorTerm K n)
          (nearJDyadicMultiplierVector a ε K (n : ℝ))) =
        finiteNearRamanujanMultiplierVector a ε K (Q + 1) (2 * Q) by
      rfl] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (nearJDyadicMultiplierVector_terminal_add_variation_le_lowDenominator
      a ε K (Q + 1) (2 * Q) ha hε haε hK (by omega) hQU)
    (Real.sqrt_nonneg _))

theorem norm_finiteNearRamanujanMultiplierVector_dyadic_le_lowDenominator_normalized
    (a ε : ℝ) (K Q : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hQ : 0 < Q) (hQK : Q ^ 2 ≤ K) :
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) (2 * Q)‖ ≤
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
        (a * Real.sqrt (K : ℝ)) := by
  have hraw :=
    norm_finiteNearRamanujanMultiplierVector_dyadic_le_lowDenominator
      a ε K Q ha hε haε hK hQ hQK
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hsqrtK : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.2 hKR
  have hKsqrt : (K : ℝ) = Real.sqrt (K : ℝ) ^ 2 :=
    (Real.sq_sqrt hKR.le).symm
  calc
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) (2 * Q)‖ ≤
      Real.sqrt (42 * (K : ℝ) / (Q : ℝ) ^ 2) *
        (48 * Real.pi * nearProfileDecayConstant * (2 * Q : ℕ) ^ 2 /
          (a * (K : ℝ))) := hraw
    _ = 192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
        (a * Real.sqrt (K : ℝ)) := by
      rw [hKsqrt, Real.sqrt_div (by positivity),
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (Real.sqrt_nonneg _),
        Real.sqrt_sq (by positivity)]
      push_cast
      field_simp [hQR.ne', hsqrtK.ne', ha.ne']
      ring

end

end Erdos1002
