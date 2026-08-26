import ErdosProblems.Erdos1002.ChanKumchevElementaryLongRange

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# An unconditional high-denominator near-resonant tail

The near-resonant argument does not in fact require a uniform
Chan--Kumchev prefix estimate beyond the square-root range.  The principal
multiplier band is `sqrt (a K) <= p <= sqrt (epsilon K)`, hence lies below
`sqrt K` when `epsilon <= 1`.  Above `sqrt K`, the identity `J_a(0)=0`
supplies the extra factor `K / p^2`; combined with the elementary dyadic
Ramanujan estimate, this makes the denominator shells geometrically
summable.

This file proves the high-denominator half of that observation with all
constants explicit.  It introduces no analytic-number-theory assumption.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal

namespace Erdos1002

noncomputable section

/-! ## Small-frequency bounds for `J_a` -/

/-- At a nonnegative frequency, the explicit derivative envelope is at
most its value at the origin. -/
theorem nearRhoEnvelope_le_zero
    (a ε t : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    nearRhoEnvelope a ε t ≤
      4 * nearProfileDecayConstant * (ε / 2 + a) := by
  rw [nearRhoEnvelope_eq_scaleDecay_of_nonneg a ε t ht]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by norm_num) nearProfileDecayConstant_nonneg)
  unfold scaleDecayEnvelope
  have houtDen : 1 ≤ (1 + (ε / 2) * t) ^ 2 := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ ε / 2) ht]
  have hinDen : 1 ≤ (1 + a * t) ^ 2 := by
    nlinarith [mul_nonneg ha ht]
  have hout : (ε / 2) / (1 + (ε / 2) * t) ^ 2 ≤ ε / 2 := by
    apply (div_le_iff₀ (by positivity)).2
    simpa only [mul_one] using!
      mul_le_mul_of_nonneg_left houtDen (by positivity : 0 ≤ ε / 2)
  have hin : a / (1 + a * t) ^ 2 ≤ a := by
    apply (div_le_iff₀ (by positivity)).2
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left hinDen ha
  linarith

/-- Linear vanishing of the near multiplier at the origin, with its two
cutoff scales displayed, on the nonnegative half-line. -/
theorem norm_nearJ_le_linear_of_nonneg
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    0 ≤ t →
    ‖nearJ a ε t‖ ≤
      (8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)) * |t| := by
  intro ht
  have hderiv := nearJ_deriv_continuous a ε ha hε haε
  have hftc :
      ∫ u : ℝ in (0 : ℝ)..t, deriv (nearJ a ε) u =
        nearJ a ε t - nearJ a ε 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun u _hu => nearJ_differentiableAt a ε u ha hε haε)
      (hderiv.intervalIntegrable 0 t)
  rw [nearJ_zero, sub_zero] at hftc
  calc
    ‖nearJ a ε t‖ =
        ‖∫ u : ℝ in (0 : ℝ)..t, deriv (nearJ a ε) u‖ := by rw [hftc]
    _ ≤ ∫ u : ℝ in (0 : ℝ)..t, ‖deriv (nearJ a ε) u‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht
    _ ≤ ∫ _u : ℝ in (0 : ℝ)..t,
        8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) := by
      apply intervalIntegral.integral_mono_on ht
        (hderiv.intervalIntegrable 0 t).norm
        (intervalIntegrable_const : IntervalIntegrable
          (fun _u : ℝ =>
            8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a))
          volume 0 t)
      intro u hu
      calc
        ‖deriv (nearJ a ε) u‖ ≤
            2 * Real.pi * nearRhoEnvelope a ε u :=
          norm_nearJ_deriv_le a ε u ha hε haε
        _ ≤ 2 * Real.pi *
            (4 * nearProfileDecayConstant * (ε / 2 + a)) := by
          gcongr
          exact nearRhoEnvelope_le_zero a ε u ha.le hε.le hu.1
        _ = 8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) := by ring
    _ = (8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)) * |t| := by
      rw [intervalIntegral.integral_const, smul_eq_mul, abs_of_nonneg ht]
      ring

/-- Linear vanishing of the near multiplier at the origin, for every real
frequency. -/
theorem norm_nearJ_le_linear
    (a ε t : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    ‖nearJ a ε t‖ ≤
      (8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)) * |t| := by
  by_cases ht : 0 ≤ t
  · exact norm_nearJ_le_linear_of_nonneg a ε t ha hε haε ht
  · have hmt : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    have hlin := norm_nearJ_le_linear_of_nonneg a ε (-t) ha hε haε hmt
    rw [norm_nearJ_neg] at hlin
    simpa only [abs_neg] using! hlin

/-- Small-frequency bound for the sampled dyadic multiplier. -/
theorem norm_nearJDyadicMultiplierVector_le_highRange
    (a ε : ℝ) (K U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hU : 0 < U) :
    ‖nearJDyadicMultiplierVector a ε K (U : ℝ)‖ ≤
      16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) *
        (K : ℝ) / (U : ℝ) ^ 2 := by
  have hUreal : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hU
  have hscale : 0 ≤ ε / 2 + a := by positivity
  have hconst : 0 ≤
      16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) *
        (K : ℝ) / (U : ℝ) ^ 2 := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
            nearProfileDecayConstant_nonneg) hscale)
        (Nat.cast_nonneg K))
      (sq_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hconst).mpr
  intro n
  have hnBounds := Finset.mem_Ioc.mp n.property
  have hnReal : ((n : ℕ) : ℝ) ≤ 2 * (K : ℝ) := by
    exact_mod_cast hnBounds.2
  have htNonneg : 0 ≤ ((n : ℕ) : ℝ) / (U : ℝ) ^ 2 := by positivity
  calc
    ‖nearJDyadicMultiplierVector a ε K (U : ℝ) n‖ =
        ‖nearJ a ε (((n : ℕ) : ℝ) / (U : ℝ) ^ 2)‖ := rfl
    _ ≤ (8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)) *
          |((n : ℕ) : ℝ) / (U : ℝ) ^ 2| :=
      norm_nearJ_le_linear a ε _ ha hε haε
    _ = (8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)) *
          (((n : ℕ) : ℝ) / (U : ℝ) ^ 2) := by rw [abs_of_nonneg htNonneg]
    _ ≤ (8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)) *
          ((2 * (K : ℝ)) / (U : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
            nearProfileDecayConstant_nonneg) hscale)
      exact div_le_div_of_nonneg_right hnReal (sq_nonneg _)
    _ = 16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) *
          (K : ℝ) / (U : ℝ) ^ 2 := by ring

/-! ## Exact tails of the derivative envelope -/

/-- Exact mass of one reciprocal-square envelope above a positive lower
endpoint. -/
theorem integral_scaleReciprocalDecayEnvelope_Ioi_tail
    (K s P : ℝ) (hK : 0 < K) (hs : 0 < s) (hP : 0 ≤ P) :
    ∫ x in Ioi P, scaleReciprocalDecayEnvelope K s x =
      K * s / (P ^ 2 + K * s) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x hx => hasDerivAt_scaleReciprocalDecayPrimitive K s x hK hs)
    ((scaleReciprocalDecayEnvelope_integrableOn_Ioi K s hK hs).mono_set
      (fun x hx => hP.trans_lt hx))
    (scaleReciprocalDecayPrimitive_tendsto_atTop_zero K s hK hs)
  simpa [scaleReciprocalDecayPrimitive] using! h

/-- The explicit derivative envelope has a quadratic high-denominator
tail. -/
theorem integral_nearJReciprocalSquareEnvelope_Ioi_tail_le
    (a ε K P : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hK : 0 < K) (hP : 0 < P) :
    ∫ x in Ioi P, nearJReciprocalSquareEnvelope a ε K x ≤
      16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) *
        K / P ^ 2 := by
  have hout := scaleReciprocalDecayEnvelope_integrableOn_Ioi K (ε / 2)
    hK (by positivity)
  have hin := scaleReciprocalDecayEnvelope_integrableOn_Ioi K a hK ha
  have hP0 : 0 ≤ P := hP.le
  have houtP := hout.mono_set (fun x hx => hP0.trans_lt hx)
  have hinP := hin.mono_set (fun x hx => hP0.trans_lt hx)
  have hsplit :
      ∫ x in Ioi P,
          (scaleReciprocalDecayEnvelope K (ε / 2) x +
            scaleReciprocalDecayEnvelope K a x) =
        (∫ x in Ioi P, scaleReciprocalDecayEnvelope K (ε / 2) x) +
          ∫ x in Ioi P, scaleReciprocalDecayEnvelope K a x := by
    exact MeasureTheory.integral_add houtP hinP
  unfold nearJReciprocalSquareEnvelope
  rw [MeasureTheory.integral_const_mul]
  rw [hsplit]
  rw [integral_scaleReciprocalDecayEnvelope_Ioi_tail K (ε / 2) P hK
      (by positivity) hP0,
    integral_scaleReciprocalDecayEnvelope_Ioi_tail K a P hK ha hP0]
  have houtDen : 0 < P ^ 2 + K * (ε / 2) := by positivity
  have hinDen : 0 < P ^ 2 + K * a := by positivity
  have houtBound : K * (ε / 2) / (P ^ 2 + K * (ε / 2)) ≤
      K * (ε / 2) / P ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [mul_pos hK (by positivity : 0 < ε / 2)]
  have hinBound : K * a / (P ^ 2 + K * a) ≤ K * a / P ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [mul_pos hK ha]
  calc
    16 * Real.pi * nearProfileDecayConstant *
        (K * (ε / 2) / (P ^ 2 + K * (ε / 2)) +
          K * a / (P ^ 2 + K * a)) ≤
      16 * Real.pi * nearProfileDecayConstant *
        (K * (ε / 2) / P ^ 2 + K * a / P ^ 2) := by
      exact mul_le_mul_of_nonneg_left (add_le_add houtBound hinBound)
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
          nearProfileDecayConstant_nonneg)
    _ = 16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) *
        K / P ^ 2 := by ring

/-- Discrete variation on an interval above `P` inherits the quadratic
tail of the continuous envelope. -/
theorem sum_norm_nearJDyadicMultiplierVector_sub_succ_le_highRange
    (a ε : ℝ) (K P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hP : 0 < P) (hPU : P ≤ U) :
    ∑ p ∈ Finset.Ico P U,
        ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
          nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
      16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) *
        (K : ℝ) / (P : ℝ) ^ 2 := by
  have hPReal : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hUR : (P : ℝ) ≤ (U : ℝ) := by exact_mod_cast hPU
  have hsub : Set.uIoc (P : ℝ) (U : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIoc_of_le hUR]
    intro x hx
    exact hPReal.trans hx.1
  have hmaxInt : IntervalIntegrable
      (nearJReciprocalSquareDyadicMax a ε K) volume (P : ℝ) (U : ℝ) := by
    rw [intervalIntegrable_iff]
    exact (nearJReciprocalSquareDyadicMax_integrableOn_Ioi
      a ε K ha hε haε hK).mono_set hsub
  have henvInt : IntervalIntegrable
      (nearJReciprocalSquareEnvelope a ε (K : ℝ)) volume
        (P : ℝ) (U : ℝ) := by
    rw [intervalIntegrable_iff]
    exact (nearJReciprocalSquareEnvelope_integrableOn_Ioi
      a ε (K : ℝ) ha hε (by exact_mod_cast hK)).mono_set hsub
  calc
    ∑ p ∈ Finset.Ico P U,
        ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
          nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
      ∫ x : ℝ in (P : ℝ)..(U : ℝ),
        nearJReciprocalSquareDyadicMax a ε K x :=
      sum_norm_nearJDyadicMultiplierVector_sub_succ_le_intervalIntegral
        a ε K P U ha hε haε hK hP hPU
    _ ≤ ∫ x : ℝ in (P : ℝ)..(U : ℝ),
        nearJReciprocalSquareEnvelope a ε (K : ℝ) x := by
      apply intervalIntegral.integral_mono_on hUR
        hmaxInt henvInt
      intro x hx
      exact nearJReciprocalSquareDyadicMax_le_envelope
        a ε K ha hε haε hK (hPReal.trans_le hx.1)
    _ ≤ ∫ x in Ioi (P : ℝ),
        nearJReciprocalSquareEnvelope a ε (K : ℝ) x := by
      rw [intervalIntegral.integral_of_le hUR]
      apply MeasureTheory.integral_mono_measure
        (Measure.restrict_mono_set volume (fun _x hx => hx.1))
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact nearJReciprocalSquareEnvelope_nonneg a ε (K : ℝ) x
            ha.le hε.le (by exact_mod_cast hK.le) (hPReal.trans hx).le)
        ((nearJReciprocalSquareEnvelope_integrableOn_Ioi
          a ε (K : ℝ) ha hε (by exact_mod_cast hK)).mono_set
            (fun x hx => hPReal.trans hx))
    _ ≤ 16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) *
        (K : ℝ) / (P : ℝ) ^ 2 :=
      integral_nearJReciprocalSquareEnvelope_Ioi_tail_le
        a ε (K : ℝ) (P : ℝ) ha hε (by exact_mod_cast hK) hPReal

/-! ## One high shell and its geometric iteration -/

/-- Above `sqrt K`, every truncated reciprocal-square Ramanujan shell has
an absolute `ℓ²` bound.  This is exactly where the elementary `X^4`
endpoint term becomes harmless rather than needing cancellation. -/
theorem norm_euclideanIntervalPartialSum_nearRamanujan_dyadic_le_highRange
    (K P R : ℕ) (hP : 0 < P) (hKP : K ≤ P ^ 2)
    (hR : R ∈ Finset.Icc (P + 1) (2 * P)) :
    ‖euclideanIntervalPartialSum (nearRamanujanVectorTerm K) (P + 1) R‖ ≤
      Real.sqrt 42 := by
  have hsubset : Finset.Icc (P + 1) R ⊆ Finset.Ioc P (2 * P) := by
    intro p hp
    have hpBounds := Finset.mem_Icc.mp hp
    have hRBounds := Finset.mem_Icc.mp hR
    exact Finset.mem_Ioc.mpr ⟨by omega, hpBounds.2.trans hRBounds.2⟩
  have hraw := norm_sum_nearRamanujanVectorTerm_dyadic_le
    (Finset.Icc (P + 1) R) K P hP hsubset
  have hP_le_sq : P ≤ P ^ 2 := by nlinarith
  have hOne_le_sq : 1 ≤ P ^ 2 := by nlinarith
  have hnumNat : 2 * K + 1 + 2 * P ≤ 5 * P ^ 2 := by omega
  have hden : (0 : ℝ) < (P : ℝ) ^ 2 := by positivity
  have hinside :
      2 * ((2 * K + 1 + 2 * P : ℕ) : ℝ) / (P : ℝ) ^ 2 + 32 ≤
        42 := by
    have hnumReal :
        ((2 * K + 1 + 2 * P : ℕ) : ℝ) ≤ 5 * (P : ℝ) ^ 2 := by
      exact_mod_cast hnumNat
    have hfrac :
        2 * ((2 * K + 1 + 2 * P : ℕ) : ℝ) / (P : ℝ) ^ 2 ≤ 10 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    linarith
  rw [euclideanIntervalPartialSum]
  exact hraw.trans (Real.sqrt_le_sqrt hinside)

/-- The finite multiplier sum on `P < p <= U` written over the natural
half-open denominator interval. -/
theorem finiteNearRamanujanMultiplierVector_eq_sum_Ioc
    (a ε : ℝ) (K P U : ℕ) :
    finiteNearRamanujanMultiplierVector a ε K (P + 1) U =
      ∑ p ∈ Finset.Ioc P U,
        euclideanCoordinateMul (nearRamanujanVectorTerm K p)
          (nearJDyadicMultiplierVector a ε K (p : ℝ)) := by
  unfold finiteNearRamanujanMultiplierVector
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · intro p _hp
    rfl

/-- On one denominator shell above `sqrt K`, the small-frequency zero of
`J_a` supplies the factor `K / P^2`. -/
theorem norm_finiteNearRamanujanMultiplierVector_dyadic_le_highRange
    (a ε : ℝ) (K P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hP : 0 < P) (hKP : K ≤ P ^ 2)
    (hPU : P < U) (hU2P : U ≤ 2 * P) :
    ‖finiteNearRamanujanMultiplierVector a ε K (P + 1) U‖ ≤
      (32 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
        (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := by
  have hStartEnd : P + 1 ≤ U := by omega
  have hscale : 0 ≤ ε / 2 + a := by positivity
  have hM : 0 ≤ Real.sqrt 42 := Real.sqrt_nonneg _
  have hRam : ∀ R ∈ Finset.Icc (P + 1) U,
      ‖euclideanIntervalPartialSum (nearRamanujanVectorTerm K) (P + 1) R‖ ≤
        Real.sqrt 42 := by
    intro R hR
    apply norm_euclideanIntervalPartialSum_nearRamanujan_dyadic_le_highRange
      K P R hP hKP
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hR).1, (Finset.mem_Icc.mp hR).2.trans hU2P⟩
  have habel := norm_euclidean_vector_sum_coordinateMul_le
    (nearRamanujanVectorTerm K)
    (fun p => nearJDyadicMultiplierVector a ε K (p : ℝ))
    hStartEnd (Real.sqrt 42) hRam
  have hterminal := norm_nearJDyadicMultiplierVector_le_highRange
    a ε K U ha hε haε (hP.trans hPU)
  have hvariation :=
    sum_norm_nearJDyadicMultiplierVector_sub_succ_le_highRange
      a ε K (P + 1) U ha hε haε hK (by omega) hStartEnd
  have hfactor : 0 ≤
      16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) * (K : ℝ) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
          nearProfileDecayConstant_nonneg) hscale)
      (Nat.cast_nonneg K)
  have hterminal' :
      ‖nearJDyadicMultiplierVector a ε K (U : ℝ)‖ ≤
        16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) *
          (K : ℝ) / (P : ℝ) ^ 2 := by
    refine hterminal.trans ?_
    exact div_le_div_of_nonneg_left hfactor (by positivity)
      (by exact_mod_cast Nat.pow_le_pow_left hPU.le 2)
  have hvariation' :
      ∑ p ∈ Finset.Ico (P + 1) U,
          ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
            nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
        16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) *
          (K : ℝ) / (P : ℝ) ^ 2 := by
    refine hvariation.trans ?_
    exact div_le_div_of_nonneg_left hfactor (by positivity)
      (by exact_mod_cast Nat.pow_le_pow_left (Nat.le_add_right P 1) 2)
  change ‖∑ p ∈ Finset.Icc (P + 1) U,
      euclideanCoordinateMul (nearRamanujanVectorTerm K p)
        (nearJDyadicMultiplierVector a ε K (p : ℝ))‖ ≤ _
  calc
    ‖∑ p ∈ Finset.Icc (P + 1) U,
        euclideanCoordinateMul (nearRamanujanVectorTerm K p)
          (nearJDyadicMultiplierVector a ε K (p : ℝ))‖ ≤
      Real.sqrt 42 *
        (‖nearJDyadicMultiplierVector a ε K (U : ℝ)‖ +
          ∑ p ∈ Finset.Ico (P + 1) U,
            ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
              nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖) :=
      habel
    _ ≤ Real.sqrt 42 *
        (2 * (16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) *
          (K : ℝ) / (P : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      nlinarith
    _ = (32 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
        (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := by ring

/-- All denominator shells above `sqrt K` are geometrically summable.
This is the unconditional replacement for applying Chan--Kumchev in that
range. -/
theorem norm_finiteNearRamanujanMultiplierVector_tail_le_highRange
    (a ε : ℝ) (K P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hP : 0 < P) (hKP : K ≤ P ^ 2) (hPU : P < U) :
    ‖finiteNearRamanujanMultiplierVector a ε K (P + 1) U‖ ≤
      (64 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
        (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := by
  by_cases hUle : U ≤ 2 * P
  · have hone := norm_finiteNearRamanujanMultiplierVector_dyadic_le_highRange
      a ε K P U ha hε haε hK hP hKP hPU hUle
    have hscale : 0 ≤ ε / 2 + a := by positivity
    have hnonneg : 0 ≤
        (32 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
          (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := by
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity : 0 ≤ 32 * Real.sqrt 42)
                Real.pi_nonneg)
              nearProfileDecayConstant_nonneg) hscale)
          (Nat.cast_nonneg K))
        (sq_nonneg _)
    calc
      ‖finiteNearRamanujanMultiplierVector a ε K (P + 1) U‖ ≤
          (32 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
            (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := hone
      _ ≤ 2 * ((32 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
            (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2) := by nlinarith
      _ = (64 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
            (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := by ring
  · have h2PU : 2 * P < U := lt_of_not_ge hUle
    have h2Ppos : 0 < 2 * P := by positivity
    have hK2P : K ≤ (2 * P) ^ 2 := by nlinarith
    have hleft := norm_finiteNearRamanujanMultiplierVector_dyadic_le_highRange
      a ε K P (2 * P) ha hε haε hK hP hKP (by omega) le_rfl
    have hright := norm_finiteNearRamanujanMultiplierVector_tail_le_highRange
      a ε K (2 * P) U ha hε haε hK h2Ppos hK2P h2PU
    have hdisjoint : Disjoint (Finset.Ioc P (2 * P))
        (Finset.Ioc (2 * P) U) := by
      rw [Finset.disjoint_left]
      intro p hpLeft hpRight
      have hl := Finset.mem_Ioc.mp hpLeft
      have hr := Finset.mem_Ioc.mp hpRight
      omega
    have hsplit :
        finiteNearRamanujanMultiplierVector a ε K (P + 1) U =
          finiteNearRamanujanMultiplierVector a ε K (P + 1) (2 * P) +
            finiteNearRamanujanMultiplierVector a ε K (2 * P + 1) U := by
      rw [finiteNearRamanujanMultiplierVector_eq_sum_Ioc,
        finiteNearRamanujanMultiplierVector_eq_sum_Ioc,
        finiteNearRamanujanMultiplierVector_eq_sum_Ioc]
      rw [← Finset.sum_union hdisjoint]
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) h2PU.le]
    rw [hsplit]
    calc
      ‖finiteNearRamanujanMultiplierVector a ε K (P + 1) (2 * P) +
          finiteNearRamanujanMultiplierVector a ε K (2 * P + 1) U‖ ≤
        ‖finiteNearRamanujanMultiplierVector a ε K (P + 1) (2 * P)‖ +
          ‖finiteNearRamanujanMultiplierVector a ε K (2 * P + 1) U‖ :=
        norm_add_le _ _
      _ ≤ (32 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
            (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 +
          (64 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
            (ε / 2 + a)) * (K : ℝ) / ((2 * P : ℕ) : ℝ) ^ 2 :=
        add_le_add hleft hright
      _ ≤ (64 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
            (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := by
        push_cast
        have hscale : 0 ≤ ε / 2 + a := by positivity
        have hbase : 0 ≤
            Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
              (ε / 2 + a) * (K : ℝ) / (P : ℝ) ^ 2 := by
          exact div_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (Real.sqrt_nonneg 42) Real.pi_nonneg)
                  nearProfileDecayConstant_nonneg) hscale)
              (Nat.cast_nonneg K))
            (sq_nonneg _)
        calc
          (32 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
                (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 +
              (64 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
                (ε / 2 + a)) * (K : ℝ) / (2 * (P : ℝ)) ^ 2 =
            32 * (Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
                (ε / 2 + a) * (K : ℝ) / (P : ℝ) ^ 2) +
              16 * (Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
                (ε / 2 + a) * (K : ℝ) / (P : ℝ) ^ 2) := by ring
          _ ≤ 64 * (Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
                (ε / 2 + a) * (K : ℝ) / (P : ℝ) ^ 2) := by nlinarith
          _ = (64 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
                (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := by ring
termination_by U - P
decreasing_by omega

/-! ## Crossing the square-root boundary -/

/-- The one denominator at a chosen ceiling of `sqrt K` has the same
small-frequency bound as the high tail. -/
theorem norm_finiteNearRamanujanMultiplierVector_singleton_le_highRange
    (a ε : ℝ) (K P : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hP : 2 ≤ P) (hKP : K ≤ P ^ 2) :
    ‖finiteNearRamanujanMultiplierVector a ε K P P‖ ≤
      (16 * Real.sqrt 54 * Real.pi * nearProfileDecayConstant *
        (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := by
  let Q := P - 1
  have hQ : 0 < Q := by dsimp [Q]; omega
  have hPmem : P ∈ Finset.Ioc Q (2 * Q) := by
    dsimp [Q]
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hsubset : ({P} : Finset ℕ) ⊆ Finset.Ioc Q (2 * Q) := by
    intro p hp
    have hpEq : p = P := Finset.mem_singleton.mp hp
    simpa only [hpEq] using! hPmem
  have hraw := norm_sum_nearRamanujanVectorTerm_dyadic_le
    ({P} : Finset ℕ) K Q hQ hsubset
  have hKQ : K ≤ 4 * Q ^ 2 := by
    dsimp [Q]
    have hP2 : P ≤ 2 * (P - 1) := by omega
    have hsquare : P ^ 2 ≤ (2 * (P - 1)) ^ 2 := Nat.pow_le_pow_left hP2 2
    nlinarith
  have hQsq : 1 ≤ Q ^ 2 := by nlinarith
  have hQleSq : Q ≤ Q ^ 2 := by nlinarith
  have hnumNat : 2 * K + 1 + 2 * Q ≤ 11 * Q ^ 2 := by omega
  have hden : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
  have hinside :
      2 * ((2 * K + 1 + 2 * Q : ℕ) : ℝ) / (Q : ℝ) ^ 2 + 32 ≤ 54 := by
    have hnumReal :
        ((2 * K + 1 + 2 * Q : ℕ) : ℝ) ≤ 11 * (Q : ℝ) ^ 2 := by
      exact_mod_cast hnumNat
    have hfrac :
        2 * ((2 * K + 1 + 2 * Q : ℕ) : ℝ) / (Q : ℝ) ^ 2 ≤ 22 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    linarith
  have hraw54 : ‖nearRamanujanVectorTerm K P‖ ≤ Real.sqrt 54 := by
    have hone :
        (∑ p ∈ ({P} : Finset ℕ), nearRamanujanVectorTerm K p) =
          nearRamanujanVectorTerm K P := by simp
    rw [hone] at hraw
    exact hraw.trans (Real.sqrt_le_sqrt hinside)
  have hw := norm_nearJDyadicMultiplierVector_le_highRange
    a ε K P ha hε haε (by omega)
  have hcoord := norm_euclideanCoordinateMul_le
    (nearRamanujanVectorTerm K P)
    (nearJDyadicMultiplierVector a ε K (P : ℝ))
  have hone : finiteNearRamanujanMultiplierVector a ε K P P =
      euclideanCoordinateMul (nearRamanujanVectorTerm K P)
        (nearJDyadicMultiplierVector a ε K (P : ℝ)) := by
    unfold finiteNearRamanujanMultiplierVector
    simp
  rw [hone]
  calc
    ‖euclideanCoordinateMul (nearRamanujanVectorTerm K P)
        (nearJDyadicMultiplierVector a ε K (P : ℝ))‖ ≤
      ‖nearRamanujanVectorTerm K P‖ *
        ‖nearJDyadicMultiplierVector a ε K (P : ℝ)‖ := hcoord
    _ ≤ Real.sqrt 54 *
        (16 * Real.pi * nearProfileDecayConstant * (ε / 2 + a) *
          (K : ℝ) / (P : ℝ) ^ 2) :=
      mul_le_mul hraw54 hw (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = (16 * Real.sqrt 54 * Real.pi * nearProfileDecayConstant *
          (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := by ring

/-- Fully elementary tail across the square-root boundary.  Here `P` is
any integer ceiling of `sqrt K`, expressed without introducing a square
root by `(P-1)^2 <= K <= P^2`.  The first term is the already-formalized
low-range tail, and the remaining two terms are an absolute boundary/high
tail contribution. -/
theorem norm_finiteNearRamanujanMultiplierVector_tail_le_unconditional
    (a ε : ℝ) (K Q P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hQ : 0 < Q) (hP : 2 ≤ P)
    (hQP : Q < P - 1) (hPm1K : (P - 1) ^ 2 ≤ K)
    (hKP : K ≤ P ^ 2) (hPU : P < U) :
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ ≤
      (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
          (64 * Real.pi * nearProfileDecayConstant) +
        (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
          nearProfileDecayConstant * (ε / 2 + a) *
          (K : ℝ) / (P : ℝ) ^ 2 := by
  have hQlow : Q < P - 1 := hQP
  have hlow := norm_finiteNearRamanujanMultiplierVector_tail_le_lowRange
    a ε K Q (P - 1) ha hε haε hK hQ hQlow hPm1K
  have hsingle :=
    norm_finiteNearRamanujanMultiplierVector_singleton_le_highRange
      a ε K P ha hε haε hP hKP
  have hhigh := norm_finiteNearRamanujanMultiplierVector_tail_le_highRange
    a ε K P U ha hε haε hK (by omega) hKP hPU
  have hPm1succ : P - 1 + 1 = P := by omega
  have hdisjoint₁ : Disjoint (Finset.Ioc Q (P - 1))
      (Finset.Ioc (P - 1) P) := by
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    exact (not_lt_of_ge (Finset.mem_Ioc.mp hp₁).2)
      (Finset.mem_Ioc.mp hp₂).1
  have hdisjoint₂ : Disjoint
      (Finset.Ioc Q (P - 1) ∪ Finset.Ioc (P - 1) P)
      (Finset.Ioc P U) := by
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [Finset.mem_union, Finset.mem_Ioc] at hp₁ hp₂
    rcases hp₁ with hp₁ | hp₁
    · exact (not_lt_of_ge (hp₁.2.trans (by omega : P - 1 ≤ P))) hp₂.1
    · exact (not_lt_of_ge hp₁.2) hp₂.1
  have hunion₁ :
      Finset.Ioc Q (P - 1) ∪ Finset.Ioc (P - 1) P =
        Finset.Ioc Q P := by
    ext p
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  have hunion₂ :
      (Finset.Ioc Q (P - 1) ∪ Finset.Ioc (P - 1) P) ∪
          Finset.Ioc P U = Finset.Ioc Q U := by
    rw [hunion₁]
    ext p
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  have hsplit :
      finiteNearRamanujanMultiplierVector a ε K (Q + 1) U =
        finiteNearRamanujanMultiplierVector a ε K (Q + 1) (P - 1) +
          finiteNearRamanujanMultiplierVector a ε K P P +
          finiteNearRamanujanMultiplierVector a ε K (P + 1) U := by
    rw [finiteNearRamanujanMultiplierVector_eq_sum_Ioc]
    rw [show finiteNearRamanujanMultiplierVector a ε K (Q + 1) (P - 1) =
        ∑ p ∈ Finset.Ioc Q (P - 1),
          euclideanCoordinateMul (nearRamanujanVectorTerm K p)
            (nearJDyadicMultiplierVector a ε K (p : ℝ)) from
      finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K Q (P - 1)]
    rw [show finiteNearRamanujanMultiplierVector a ε K P P =
        ∑ p ∈ Finset.Ioc (P - 1) P,
          euclideanCoordinateMul (nearRamanujanVectorTerm K p)
            (nearJDyadicMultiplierVector a ε K (p : ℝ)) by
      simpa only [hPm1succ] using!
        finiteNearRamanujanMultiplierVector_eq_sum_Ioc
          a ε K (P - 1) P]
    rw [finiteNearRamanujanMultiplierVector_eq_sum_Ioc]
    rw [← Finset.sum_union hdisjoint₁, ← Finset.sum_union hdisjoint₂,
      hunion₂]
  rw [hsplit]
  calc
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) (P - 1) +
        finiteNearRamanujanMultiplierVector a ε K P P +
        finiteNearRamanujanMultiplierVector a ε K (P + 1) U‖ ≤
      ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) (P - 1)‖ +
        ‖finiteNearRamanujanMultiplierVector a ε K P P‖ +
        ‖finiteNearRamanujanMultiplierVector a ε K (P + 1) U‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
          (64 * Real.pi * nearProfileDecayConstant) +
        (16 * Real.sqrt 54 * Real.pi * nearProfileDecayConstant *
          (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 +
        (64 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
          (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 :=
      add_le_add (add_le_add hlow hsingle) hhigh
    _ = (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
          (64 * Real.pi * nearProfileDecayConstant) +
        (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
          nearProfileDecayConstant * (ε / 2 + a) *
          (K : ℝ) / (P : ℝ) ^ 2 := by ring

end

end Erdos1002
