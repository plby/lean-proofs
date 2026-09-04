/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareHybridCorrelation
import ErdosProblems.Erdos378.CentralAsymptotic

/-!
# Asymptotics for the hybrid inverse-square estimate

Moderate frequencies are estimated with the empty differencing list.  At
frequencies of cubic size the capped thirty-two-step estimate is uniformly
small.  These are the two estimates used for separated columns of the
inverse-square Vaughan term.
-/

open Filter
open scoped Topology BigOperators ComplexConjugate

namespace Erdos378
namespace InverseSquareHybridAsymptotic

open HigherDerivative
open AdaptiveShifts
open InverseSquareCorrelation
open InverseSquareBilinear
open InverseSquareAdaptiveShifts
open InverseSquareCentralCorrelation
open CentralAsymptotic

noncomputable section

/-- With no preliminary differencing, the inverse-square third derivative
estimate has the particularly useful form `2 + 12 M³ / Q`. -/
theorem norm_inverseSquareProductIntervalSum_le_moderate
    {Q : ℝ} (hQ : 0 < Q) {M a b : ℕ}
    (hM : 1 ≤ M) (hab : a < b) (hMa : M ≤ a) (hbM : b ≤ 2 * M)
    (hlength : 2 ≤ b - a) (hQupper : 4 * Q ≤ (M : ℝ) ^ 3) :
    ‖inverseSquareProductIntervalSum Q 1 a b‖ ≤
      2 + 12 * (M : ℝ) ^ 3 / Q := by
  let N := b - a
  have hN : 0 < N := by dsimp only [N]; omega
  have ha : 0 < a := Nat.zero_lt_of_lt (hM.trans hMa)
  have hsmall :
      Q * ((([] : List ℕ).length + 2).factorial : ℝ) *
          (([] : List ℕ).prod : ℝ) /
            (a : ℝ) ^ (([] : List ℕ).length + 3) ≤ 1 / 2 := by
    simp only [List.length_nil, zero_add, Nat.factorial_two, Nat.cast_ofNat,
      List.prod_nil, Nat.cast_one, mul_one]
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
    have haR : (M : ℝ) ≤ a := by exact_mod_cast hMa
    have hpow : (M : ℝ) ^ 3 ≤ (a : ℝ) ^ 3 := by gcongr
    rw [div_le_iff₀ (pow_pos (by positivity : (0 : ℝ) < a) 3)]
    calc
      Q * 2 ≤ (M : ℝ) ^ 3 / 2 := by linarith
      _ ≤ (a : ℝ) ^ 3 / 2 := by gcongr
      _ = 1 / 2 * (a : ℝ) ^ 3 := by ring
  have hraw := norm_inverseSquareProductIntervalSum_le_highDerivative
    Q hQ ha hab ([] : List ℕ) (by simp) (by simpa only [List.sum_nil, zero_add, N]) hsmall
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hbR : ((a + N : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
    exact_mod_cast (show a + N ≤ 2 * M by dsimp only [N]; omega)
  have hcube : (((a + N : ℕ) : ℝ)) ^ 3 ≤ 8 * (M : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * (M : ℝ)) ^ 3 := by gcongr
      _ = 8 * (M : ℝ) ^ 3 := by ring
  unfold inverseSquareHighDerivativeBound inverseSquareMomentMajorant at hraw
  norm_num [vdcMomentConstant, differencingError,
    reciprocalShiftFactor] at hraw
  calc
    ‖inverseSquareProductIntervalSum Q 1 a b‖ ≤
        8 * (N : ℝ) *
          (2 * (1 / (8 * (N : ℝ)) +
            3 * ((a + N : ℕ) : ℝ) ^ 3 /
              (32 * (N : ℝ) * Q))) := by
      convert hraw using 1 <;>
        simp only [N, Nat.cast_add, div_eq_mul_inv] <;> ring
    _ = 2 + (3 / 2) * ((a + N : ℕ) : ℝ) ^ 3 / Q := by
      field_simp [ne_of_gt hNR, ne_of_gt hQ]
      ring
    _ ≤ 2 + (3 / 2) * (8 * (M : ℝ) ^ 3) / Q := by
      gcongr
    _ = 2 + 12 * (M : ℝ) ^ 3 / Q := by ring

/-- A common upper bound for either branch of the capped terminal term at
cubic frequency. -/
def largeFrequencyTerminalBound (M C : ℕ) : ℝ :=
  inverseSquareTerminalConstant * logarithmicSafety M ^ 64 /
      (32 * (baseShift M : ℝ)) +
    (12 * 2 ^ 35 * (2 * (C : ℝ)) ^ 33) *
      (logarithmicSafety M ^ 32 / (M : ℝ))

def largeFrequencyMomentBound (M C : ℕ) : ℝ :=
  vdcMomentConstant 32 *
    (32 / (baseShift M : ℝ) + 1 / (256 * (baseShift M : ℝ)) +
      largeFrequencyTerminalBound M C)

lemma baseShift_sq_le (M : ℕ) : baseShift M ^ 2 ≤ M := by
  unfold baseShift
  have h₁ := Nat.sqrt_le (Nat.sqrt (Nat.sqrt (Nat.sqrt M)))
  have hs₁ : Nat.sqrt (Nat.sqrt (Nat.sqrt M)) ≤ M := by
    exact (Nat.sqrt_le_self _).trans
      ((Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _))
  simpa only [pow_two] using h₁.trans hs₁

theorem eventually_baseShift_le_div (C : ℕ) (hC : 0 < C) :
    ∀ᶠ M : ℕ in atTop, baseShift M ≤ M / C := by
  filter_upwards [eventually_ge_atTop (C ^ 2)] with M hM
  apply (Nat.le_div_iff_mul_le hC).2
  have hq := baseShift_sq_le M
  have hCsqrt : C ≤ Nat.sqrt M := Nat.le_sqrt.mpr (by
    simpa only [pow_two] using hM)
  have hqsqrt : baseShift M ≤ Nat.sqrt M := Nat.le_sqrt.mpr (by
    simpa only [pow_two] using hq)
  calc
    baseShift M * C ≤ Nat.sqrt M * Nat.sqrt M :=
      Nat.mul_le_mul hqsqrt hCsqrt
    _ ≤ M := Nat.sqrt_le M

theorem eventually_const_mul_logarithmicSafety_pow_le_sq (A : ℝ) :
    ∀ᶠ M : ℕ in atTop,
      A * logarithmicSafety M ^ 32 ≤ (M : ℝ) ^ 2 := by
  have hratio : Tendsto (fun M : ℕ ↦
      logarithmicSafety M ^ 32 / (M : ℝ)) atTop (nhds 0) := by
    have hmajor := tendsto_safety_pow_forty_div_baseShift
    have hnonneg : ∀ᶠ M : ℕ in atTop,
        0 ≤ logarithmicSafety M ^ 32 / (M : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with M hM
      positivity
    have hle : ∀ᶠ M : ℕ in atTop,
        logarithmicSafety M ^ 32 / (M : ℝ) ≤
          logarithmicSafety M ^ 64 / (baseShift M : ℝ) := by
      filter_upwards [eventually_ge_atTop 1,
        tendsto_baseShift_atTop.eventually (eventually_ge_atTop 1)] with M hM hq
      have hS : 1 ≤ logarithmicSafety M :=
        (one_lt_logarithmicSafety hM).le
      have hpow : logarithmicSafety M ^ 32 ≤
          logarithmicSafety M ^ 64 := pow_le_pow_right₀ hS (by omega)
      have hqM : baseShift M ≤ M := baseShift_le M
      exact div_le_div₀ (by positivity) hpow (by positivity)
        (by exact_mod_cast hqM)
    exact squeeze_zero' hnonneg hle hmajor
  have hscaled : Tendsto (fun M : ℕ ↦
      A * (logarithmicSafety M ^ 32 / (M : ℝ))) atTop (nhds 0) := by
    simpa using hratio.const_mul A
  have hle : ∀ᶠ M : ℕ in atTop,
      A * (logarithmicSafety M ^ 32 / (M : ℝ)) ≤ 1 :=
    hscaled.eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [hle, eventually_ge_atTop 1] with M hle hM
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hdiv : (A * logarithmicSafety M ^ 32) / (M : ℝ) ≤ 1 := by
    calc
      (A * logarithmicSafety M ^ 32) / (M : ℝ) =
          A * (logarithmicSafety M ^ 32 / (M : ℝ)) := by ring
      _ ≤ 1 := hle
  have hmul : A * logarithmicSafety M ^ 32 ≤ (M : ℝ) := by
    simpa using (div_le_iff₀ hMR).mp hdiv
  exact hmul.trans (by
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith)

theorem eventually_inverseSquareCorrelationSizeCondition :
    ∀ᶠ M : ℕ in atTop, inverseSquareCorrelationSizeCondition M := by
  simpa only [inverseSquareCorrelationSizeCondition] using
    eventually_const_mul_logarithmicSafety_pow_le_sq
      (2 * inverseSquareFrequencyConstant * ((34).factorial : ℝ))

theorem tendsto_largeFrequencyMomentBound_zero (C : ℕ) :
    Tendsto (fun M : ℕ ↦ largeFrequencyMomentBound M C)
      atTop (nhds 0) := by
  have hqTop : Tendsto (fun M : ℕ ↦ (baseShift M : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_baseShift_atTop
  have hqInv : Tendsto (fun M : ℕ ↦ ((baseShift M : ℝ))⁻¹)
      atTop (nhds 0) := hqTop.inv_tendsto_atTop
  have hfirst : Tendsto (fun M : ℕ ↦ 32 / (baseShift M : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hqInv.const_mul 32
  have hsecond : Tendsto (fun M : ℕ ↦ 1 / (256 * (baseShift M : ℝ)))
      atTop (nhds 0) := by
    convert hqInv.const_mul (1 / 256 : ℝ) using 1
    · funext M
      ring
    · ring_nf
  have hinactive : Tendsto (fun M : ℕ ↦
      inverseSquareTerminalConstant * logarithmicSafety M ^ 64 /
        (32 * (baseShift M : ℝ))) atTop (nhds 0) := by
    convert tendsto_safety_pow_forty_div_baseShift.const_mul
      (inverseSquareTerminalConstant / 32) using 1
    · funext M
      ring
    · ring_nf
  have hratio : Tendsto (fun M : ℕ ↦
      logarithmicSafety M ^ 32 / (M : ℝ)) atTop (nhds 0) := by
    have hmajor := tendsto_safety_pow_forty_div_baseShift
    have hnonneg : ∀ᶠ M : ℕ in atTop,
        0 ≤ logarithmicSafety M ^ 32 / (M : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with M hM
      positivity
    have hle : ∀ᶠ M : ℕ in atTop,
        logarithmicSafety M ^ 32 / (M : ℝ) ≤
          logarithmicSafety M ^ 64 / (baseShift M : ℝ) := by
      filter_upwards [eventually_ge_atTop 1,
        tendsto_baseShift_atTop.eventually (eventually_ge_atTop 1)] with M hM hq
      have hS : 1 ≤ logarithmicSafety M :=
        (one_lt_logarithmicSafety hM).le
      exact div_le_div₀ (by positivity)
        (pow_le_pow_right₀ hS (by omega)) (by positivity)
        (by exact_mod_cast baseShift_le M)
    exact squeeze_zero' hnonneg hle hmajor
  have hactive : Tendsto (fun M : ℕ ↦
      (12 * 2 ^ 35 * (2 * (C : ℝ)) ^ 33) *
        (logarithmicSafety M ^ 32 / (M : ℝ))) atTop (nhds 0) := by
    simpa using hratio.const_mul (12 * 2 ^ 35 * (2 * (C : ℝ)) ^ 33)
  unfold largeFrequencyMomentBound largeFrequencyTerminalBound
  simpa only [zero_add, mul_zero] using
    (hfirst.add hsecond |>.add (hinactive.add hactive)).const_mul
      (vdcMomentConstant 32)

lemma largeFrequencyTerminalBound_nonneg {M C : ℕ} (hM : 1 ≤ M) :
    0 ≤ largeFrequencyTerminalBound M C := by
  unfold largeFrequencyTerminalBound
  have hq : 0 < baseShift M := baseShift_pos (Nat.zero_lt_of_lt hM)
  have hS := logarithmicSafety_pos hM
  apply add_nonneg
  · exact div_nonneg (mul_nonneg inverseSquareTerminalConstant_pos.le
      (pow_nonneg hS.le 64)) (by positivity)
  · exact mul_nonneg (by positivity)
      (div_nonneg (pow_nonneg hS.le 32) (by positivity))

lemma largeFrequencyMomentBound_nonneg {M C : ℕ} (hM : 1 ≤ M) :
    0 ≤ largeFrequencyMomentBound M C := by
  unfold largeFrequencyMomentBound
  have hq : 0 < baseShift M := baseShift_pos (Nat.zero_lt_of_lt hM)
  exact mul_nonneg (vdcMomentConstant_pos 32).le <| add_nonneg
    (add_nonneg (by positivity) (by positivity))
    (largeFrequencyTerminalBound_nonneg hM)

/-- At cubic frequency, either the adaptive maximum occurs before the cap,
or the cap is active and the elementary lower bound `q ≥ M/(2C)` makes the
terminal derivative contribution tend to zero. -/
theorem cappedTerminalMajorant_le_largeFrequencyTerminalBound
    {Q : ℝ} (hQ : 0 < Q) {M C : ℕ}
    (hM : 1 ≤ M) (hC : 2 ≤ C)
    (hbase : inverseSquareShiftPredicate Q M (baseShift M))
    (hbaseCap : baseShift M ≤ M / C)
    (hlarge : (M : ℝ) ^ 3 ≤ 4 * Q) :
    cappedTerminalMajorant Q M C ≤ largeFrequencyTerminalBound M C := by
  let q := cappedInverseSquareShift Q M C
  have hq : baseShift M ≤ q :=
    baseShift_le_cappedInverseSquareShift hbase hbaseCap
  have hqNat : 1 ≤ q :=
    (baseShift_pos (Nat.zero_lt_of_lt hM)).trans_le hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqNat
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hCR : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hS : 0 ≤ logarithmicSafety M := (logarithmicSafety_pos hM).le
  by_cases hinactive : inverseSquareShift Q M ≤ M / C
  · unfold cappedTerminalMajorant largeFrequencyTerminalBound
    rw [if_pos hinactive]
    calc
      inverseSquareTerminalConstant * logarithmicSafety M ^ 64 /
          (32 * (cappedInverseSquareShift Q M C : ℝ)) ≤
        inverseSquareTerminalConstant * logarithmicSafety M ^ 64 /
          (32 * (baseShift M : ℝ)) := by
        apply div_le_div_of_nonneg_left
          (mul_nonneg inverseSquareTerminalConstant_pos.le
            (pow_nonneg hS 64)) (by
              have hb : 0 < baseShift M :=
                baseShift_pos (Nat.zero_lt_of_lt hM)
              positivity)
        exact_mod_cast Nat.mul_le_mul_left 32 hq
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hqeq : q = M / C := by
      dsimp only [q, cappedInverseSquareShift]
      exact min_eq_right (Nat.le_of_lt (lt_of_not_ge hinactive))
    have hdivPos : 1 ≤ M / C := hqeq ▸ hqNat
    have hMtwoCq : (M : ℝ) ≤ 2 * (C : ℝ) * q := by
      have hlt : M < C * (M / C + 1) := Nat.lt_mul_div_succ M (by omega)
      have hsucc : M / C + 1 ≤ 2 * (M / C) := by omega
      have hnat : M ≤ 2 * C * q := by
        rw [hqeq]
        calc
          M ≤ C * (M / C + 1) := hlt.le
          _ ≤ C * (2 * (M / C)) := Nat.mul_le_mul_left C hsucc
          _ = 2 * C * (M / C) := by ring
      exact_mod_cast hnat
    have hratio :
        (M : ℝ) ^ 32 / (q : ℝ) ^ 33 ≤
          (2 * (C : ℝ)) ^ 33 / (M : ℝ) := by
      rw [div_le_div_iff₀ (pow_pos hqR 33) hMpos]
      calc
        (M : ℝ) ^ 32 * (M : ℝ) = (M : ℝ) ^ 33 := by ring
        _ ≤ (2 * (C : ℝ) * q) ^ 33 := by gcongr
        _ = (2 * (C : ℝ)) ^ 33 * (q : ℝ) ^ 33 := by ring
    unfold cappedTerminalMajorant largeFrequencyTerminalBound
    rw [if_neg hinactive]
    calc
      (3 * (2 * (M : ℝ)) ^ 35 /
          (16 * (32 * (q : ℝ)) * Q * ((34).factorial : ℝ))) *
          (logarithmicSafety M ^ 32 / (q : ℝ) ^ 32) ≤
        (3 * (2 * (M : ℝ)) ^ 35 / ((q : ℝ) * Q)) *
          (logarithmicSafety M ^ 32 / (q : ℝ) ^ 32) := by
        apply mul_le_mul_of_nonneg_right _ (div_nonneg (pow_nonneg hS 32)
          (pow_nonneg hqR.le 32))
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos hqR hQ)
        have hfac : (1 : ℝ) ≤ 16 * 32 * ((34).factorial : ℝ) := by
          norm_num [Nat.factorial]
        calc
          (q : ℝ) * Q ≤ (16 * 32 * ((34).factorial : ℝ)) * ((q : ℝ) * Q) :=
            le_mul_of_one_le_left (mul_nonneg hqR.le hQ.le) hfac
          _ = 16 * (32 * (q : ℝ)) * Q * ((34).factorial : ℝ) := by ring
        all_goals rfl
      _ = 3 * (2 * (M : ℝ)) ^ 35 * logarithmicSafety M ^ 32 /
          ((q : ℝ) ^ 33 * Q) := by
        field_simp [ne_of_gt hqR, ne_of_gt hQ]
      _ ≤ 12 * (2 * (M : ℝ)) ^ 35 * logarithmicSafety M ^ 32 /
          ((q : ℝ) ^ 33 * (M : ℝ) ^ 3) := by
        rw [div_le_div_iff₀ (mul_pos (pow_pos hqR 33) hQ)
          (mul_pos (pow_pos hqR 33) (pow_pos hMpos 3))]
        have hnonneg : 0 ≤
            3 * (2 * (M : ℝ)) ^ 35 * logarithmicSafety M ^ 32 := by
          positivity
        have hmul := mul_le_mul_of_nonneg_left hlarge
          (mul_nonneg (pow_nonneg hqR.le 33) hnonneg)
        nlinarith [hmul]
      _ = (12 * 2 ^ 35) *
          ((M : ℝ) ^ 32 / (q : ℝ) ^ 33) * logarithmicSafety M ^ 32 := by
        field_simp [ne_of_gt hqR, ne_of_gt hMpos]
      _ ≤ (12 * 2 ^ 35) *
          ((2 * (C : ℝ)) ^ 33 / (M : ℝ)) *
            logarithmicSafety M ^ 32 := by gcongr
      _ = (12 * 2 ^ 35 * (2 * (C : ℝ)) ^ 33) *
          (logarithmicSafety M ^ 32 / (M : ℝ)) := by ring
      _ ≤ inverseSquareTerminalConstant * logarithmicSafety M ^ 64 /
          (32 * (baseShift M : ℝ)) +
          (12 * 2 ^ 35 * (2 * (C : ℝ)) ^ 33) *
            (logarithmicSafety M ^ 32 / (M : ℝ)) :=
        le_add_of_nonneg_left (div_nonneg
          (mul_nonneg inverseSquareTerminalConstant_pos.le (pow_nonneg hS 64))
          (mul_nonneg (by norm_num) (by positivity)))

theorem cappedInverseSquareMomentEnvelope_le_largeFrequencyMomentBound
    {Q : ℝ} (hQ : 0 < Q) {M C : ℕ}
    (hM : 1 ≤ M) (hC : 2 ≤ C)
    (hbase : inverseSquareShiftPredicate Q M (baseShift M))
    (hbaseCap : baseShift M ≤ M / C)
    (hlarge : (M : ℝ) ^ 3 ≤ 4 * Q) :
    cappedInverseSquareMomentEnvelope Q M C ≤
      largeFrequencyMomentBound M C := by
  have hq := baseShift_le_cappedInverseSquareShift hbase hbaseCap
  unfold cappedInverseSquareMomentEnvelope largeFrequencyMomentBound
  apply mul_le_mul_of_nonneg_left _ (vdcMomentConstant_pos 32).le
  apply add_le_add
  · apply add_le_add
    · exact div_le_div_of_nonneg_left (by norm_num) (by
        exact_mod_cast baseShift_pos (Nat.zero_lt_of_lt hM))
          (by exact_mod_cast hq)
    · apply div_le_div_of_nonneg_left (by norm_num) (by
          have hb : 0 < baseShift M := baseShift_pos (Nat.zero_lt_of_lt hM)
          positivity)
      exact_mod_cast Nat.mul_le_mul_left 256 hq
  · exact cappedTerminalMajorant_le_largeFrequencyTerminalBound
      hQ hM hC hbase hbaseCap hlarge

/-- The part of the normalized large-frequency correlation envelope which
still depends on the dyadic length. -/
def largeFrequencyCorrelationTail (M C : ℕ) : ℝ :=
  34 / (M : ℝ) +
    8 * (largeFrequencyMomentBound M C) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹

theorem tendsto_largeFrequencyCorrelationTail_zero (C : ℕ) :
    Tendsto (fun M : ℕ ↦ largeFrequencyCorrelationTail M C)
      atTop (nhds 0) := by
  have hMTop : Tendsto (fun M : ℕ ↦ (M : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun M : ℕ ↦ ((M : ℝ))⁻¹) atTop (nhds 0) :=
    hMTop.inv_tendsto_atTop
  have hfirst : Tendsto (fun M : ℕ ↦ 34 / (M : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul 34
  have hrpow : Tendsto (fun M : ℕ ↦
      (largeFrequencyMomentBound M C) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) :=
    (tendsto_largeFrequencyMomentBound_zero C).rpow_const_nhds_zero
      (by positivity)
  have hsecond : Tendsto (fun M : ℕ ↦
      8 * (largeFrequencyMomentBound M C) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) := by
    simpa using hrpow.const_mul 8
  unfold largeFrequencyCorrelationTail
  simpa only [zero_add] using hfirst.add hsecond

/-- Uniform smallness of every capped correlation envelope whose frequency
is at least cubic and lies in the range covered by the thirty-two-step
estimate.  The cap is chosen once from `delta`, independently of the
frequency and the dyadic length. -/
theorem exists_cap_eventually_largeFrequencyCorrelationEnvelope_le_mul
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ᶠ M : ℕ in atTop,
      ∀ Q : ℝ, 0 < Q → (M : ℝ) ^ 3 ≤ 4 * Q →
        Q ≤ inverseSquareFrequencyConstant * (M : ℝ) ^ 31 →
        cappedInverseSquareCorrelationEnvelope Q M C ≤ delta * M := by
  obtain ⟨C₀, hC₀⟩ := exists_nat_gt (68 / delta)
  let C := max 2 C₀
  have hC : 2 ≤ C := le_max_left _ _
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hCbig : 68 / delta < (C : ℝ) :=
    hC₀.trans_le (by exact_mod_cast (le_max_right 2 C₀))
  have hbasePart : 34 / (C : ℝ) < delta / 2 := by
    rw [div_lt_iff₀ hCpos]
    have hmul : (68 : ℝ) < (C : ℝ) * delta :=
      (div_lt_iff₀ hdelta).mp hCbig
    nlinarith
  have htail : ∀ᶠ M : ℕ in atTop,
      largeFrequencyCorrelationTail M C < delta / 2 :=
    (tendsto_largeFrequencyCorrelationTail_zero C).eventually
      (Iio_mem_nhds (by linarith))
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop 1,
    eventually_baseShift_le_div C (by omega),
    eventually_inverseSquareCorrelationSizeCondition, htail] with
      M hM hbaseCap hsize htailM
  intro Q hQ hlarge hQupper
  have hbase := baseShift_inverseSquarePredicate_of_frequency_upper
    hQ.le hM hQupper hsize
  have hmoment := cappedInverseSquareMomentEnvelope_le_largeFrequencyMomentBound
    hQ hM hC hbase hbaseCap hlarge
  have hq : 1 ≤ cappedInverseSquareShift Q M C :=
    (baseShift_pos (Nat.zero_lt_of_lt hM)).trans_le
      (baseShift_le_cappedInverseSquareShift hbase hbaseCap)
  have hmomentNonneg := cappedInverseSquareMomentEnvelope_nonneg hQ hq
  have hrpow :
      (cappedInverseSquareMomentEnvelope Q M C) ^
          ((2 ^ 32 : ℕ) : ℝ)⁻¹ ≤
        (largeFrequencyMomentBound M C) ^
          ((2 ^ 32 : ℕ) : ℝ)⁻¹ :=
    Real.rpow_le_rpow hmomentNonneg hmoment (by positivity)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  apply (div_le_iff₀ hMpos).mp
  apply le_of_lt
  calc
    cappedInverseSquareCorrelationEnvelope Q M C / (M : ℝ) =
        34 * ((M / C : ℕ) : ℝ) / (M : ℝ) +
          34 / (M : ℝ) +
          8 * (cappedInverseSquareMomentEnvelope Q M C) ^
            ((2 ^ 32 : ℕ) : ℝ)⁻¹ := by
      unfold cappedInverseSquareCorrelationEnvelope
      field_simp [ne_of_gt hMpos]
    _ = 34 * ((M / C : ℕ) : ℝ) / (M : ℝ) +
          (34 / (M : ℝ) +
            8 * (cappedInverseSquareMomentEnvelope Q M C) ^
              ((2 ^ 32 : ℕ) : ℝ)⁻¹) := by ring
    _ ≤ 34 * ((M / C : ℕ) : ℝ) / (M : ℝ) +
          (34 / (M : ℝ) +
            8 * (largeFrequencyMomentBound M C) ^
              ((2 ^ 32 : ℕ) : ℝ)⁻¹) := by
      gcongr
    _ = 34 * ((M / C : ℕ) : ℝ) / (M : ℝ) +
          largeFrequencyCorrelationTail M C := by
      unfold largeFrequencyCorrelationTail
      rfl
    _ ≤ 34 / (C : ℝ) + largeFrequencyCorrelationTail M C := by
      have hfirst : 34 * ((M / C : ℕ) : ℝ) / (M : ℝ) ≤
          34 / (C : ℝ) := by
        calc
          34 * ((M / C : ℕ) : ℝ) / (M : ℝ) ≤
              34 * ((M : ℝ) / (C : ℝ)) / (M : ℝ) := by
            gcongr
            exact Nat.cast_div_le
          _ = 34 / (C : ℝ) := by
            field_simp [ne_of_gt hMpos, ne_of_gt hCpos]
      exact add_le_add hfirst le_rfl
    _ < delta / 2 + delta / 2 := add_lt_add hbasePart htailM
    _ = delta := by ring

/-- A nonempty product correlation remembers the full size of the original
inverse-square phase.  This lower bound is the quantitative reason that
columns separated by `d` have correlation `O(M K /(R d))` when
`X ≥ R y²`. -/
theorem inverseSquareCentralCorrelationFrequency_lower_of_nonempty
    {X R : ℝ} {x y M K r s : ℕ}
    (hR : 0 < R) (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hXratio : R * (y : ℝ) ^ 2 ≤ X)
    (hNpos : 0 < inverseSquareCentralCorrelationLength x y M r s) :
    R * (M : ℝ) ^ 2 * ((s - r : ℕ) : ℝ) ≤
      8 * inverseSquareCentralCorrelationFrequency X r s * (K : ℝ) := by
  let a := inverseSquareCentralCorrelationLower x M r s
  let b := inverseSquareCentralCorrelationUpper y M r s
  let d := s - r
  have hrBounds := Finset.mem_Ioc.mp hr
  have hsBounds := Finset.mem_Ioc.mp hs
  have hrPos : 0 < r := hK.trans hrBounds.1
  have hsPos : 0 < s := hK.trans hsBounds.1
  have hdPos : 0 < d := by dsimp only [d]; omega
  have hab : a < b := by
    dsimp only [a, b, inverseSquareCentralCorrelationLength] at hNpos ⊢
    omega
  have hmMem : a + 1 ∈ commonProductInterval x y M (2 * M) r s := by
    rw [commonProductInterval, Finset.mem_Ioc]
    simpa only [a, b, inverseSquareCentralCorrelationLower,
      inverseSquareCentralCorrelationUpper] using
      (show a < a + 1 ∧ a + 1 ≤ b by omega)
  rcases (mem_commonProductInterval_iff hrPos hsPos).mp hmMem with
    ⟨hmIoc, hmr, _hms⟩
  have hyLower : M * K < y := by
    have hMr : M * K < (a + 1) * r := by
      calc
        M * K < M * r := Nat.mul_lt_mul_of_pos_left hrBounds.1 (by omega)
        _ ≤ (a + 1) * r := Nat.mul_le_mul_right r (by
          exact (Finset.mem_Ioc.mp hmIoc).1.le)
    exact hMr.trans_le hmr.2
  have hscale : R * (M : ℝ) ^ 2 * (K : ℝ) ^ 2 ≤ X := by
    calc
      R * (M : ℝ) ^ 2 * (K : ℝ) ^ 2 =
          R * (((M * K : ℕ) : ℝ) ^ 2) := by push_cast; ring
      _ ≤ R * (y : ℝ) ^ 2 := by
        gcongr
      _ ≤ X := hXratio
  have hdiff : (2 : ℝ) * (K : ℝ) * (d : ℝ) ≤
      ((s ^ 2 - r ^ 2 : ℕ) : ℝ) := by
    have hrsSq : r ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hrs.le 2
    rw [Nat.cast_sub hrsSq, Nat.cast_pow, Nat.cast_pow]
    have hdCast : ((d : ℕ) : ℝ) = (s : ℝ) - (r : ℝ) := by
      dsimp only [d]
      rw [Nat.cast_sub hrs.le]
    rw [hdCast]
    have hsum : (2 : ℝ) * K ≤ (s : ℝ) + r := by exact_mod_cast (by omega)
    nlinarith
  have hnum :
      (R * (M : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          ((2 : ℝ) * K * d) ≤
        X * (((s ^ 2 - r ^ 2 : ℕ) : ℝ)) :=
    mul_le_mul hscale hdiff (by positivity)
      ((by positivity : 0 ≤ R * (M : ℝ) ^ 2 * (K : ℝ) ^ 2).trans hscale)
  have hdenPos : (0 : ℝ) < (((r * s : ℕ) : ℝ) ^ 2) := by positivity
  have hden : (((r * s : ℕ) : ℝ) ^ 2) ≤
      16 * (K : ℝ) ^ 4 := by
    have hrsUpper : (r : ℝ) * s ≤ 4 * (K : ℝ) ^ 2 := by
      calc
        (r : ℝ) * s ≤ (2 * (K : ℝ)) * (2 * (K : ℝ)) := by
          gcongr
          · exact_mod_cast hrBounds.2
          · exact_mod_cast hsBounds.2
        _ = 4 * (K : ℝ) ^ 2 := by ring
    calc
      (((r * s : ℕ) : ℝ) ^ 2) = ((r : ℝ) * s) ^ 2 := by push_cast; rfl
      _ ≤ (4 * (K : ℝ) ^ 2) ^ 2 := (sq_le_sq₀ (by positivity) (by positivity)).2 hrsUpper
      _ = 16 * (K : ℝ) ^ 4 := by ring
  apply le_of_mul_le_mul_right _ hdenPos
  calc
    (R * (M : ℝ) ^ 2 * ((s - r : ℕ) : ℝ)) *
        (((r * s : ℕ) : ℝ) ^ 2) ≤
      (R * (M : ℝ) ^ 2 * (d : ℝ)) * (16 * (K : ℝ) ^ 4) := by
        apply mul_le_mul_of_nonneg_left hden
        positivity
    _ = 8 * (K : ℝ) *
        ((R * (M : ℝ) ^ 2 * (K : ℝ) ^ 2) *
          ((2 : ℝ) * K * d)) := by dsimp only [d]; ring
    _ ≤ 8 * (K : ℝ) *
        (X * (((s ^ 2 - r ^ 2 : ℕ) : ℝ))) := by gcongr
    _ = (8 * inverseSquareCentralCorrelationFrequency X r s * (K : ℝ)) *
        (((r * s : ℕ) : ℝ) ^ 2) := by
      unfold inverseSquareCentralCorrelationFrequency
      field_simp [ne_of_gt hdenPos]

/-- The two frequency regimes combined for one separated pair of dyadic
columns.  Below cubic frequency the third-derivative estimate gives the
explicit `1/(s-r)` saving; above cubic frequency the capped estimate gives
the prescribed relative error. -/
theorem norm_inverseSquareCentral_cutoff_correlation_le_separated
    {X R delta : ℝ} {x y M K r s C D : ℕ}
    (hX : 0 < X) (hR : 0 < R) (hdelta : 0 ≤ delta)
    (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hfar : D < s - r)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hXratio : R * (y : ℝ) ^ 2 ≤ X)
    (hsize : inverseSquareCentralCorrelationSizeCondition M)
    (hC : 2 ≤ C) (hbaseCap : baseShift M ≤ M / C)
    (hlargeEnvelope : ∀ Q : ℝ, 0 < Q →
      (M : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * (M : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q M C ≤ delta * M) :
    ‖∑ m ∈ Finset.Ioc M (2 * M),
      inverseSquareCutoffWeight X x y m s *
        conj (inverseSquareCutoffWeight X x y m r)‖ ≤
      2 + 96 * (M : ℝ) * (K : ℝ) /
          (R * ((D + 1 : ℕ) : ℝ)) + delta * (M : ℝ) := by
  let a := inverseSquareCentralCorrelationLower x M r s
  let b := inverseSquareCentralCorrelationUpper y M r s
  let N := inverseSquareCentralCorrelationLength x y M r s
  let Q := inverseSquareCentralCorrelationFrequency X r s
  have hrPos : 0 < r := hK.trans (Finset.mem_Ioc.mp hr).1
  have hsPos : 0 < s := hK.trans (Finset.mem_Ioc.mp hs).1
  have hRnonneg : 0 ≤ R := hR.le
  have hrightNonneg : 0 ≤
      2 + 96 * (M : ℝ) * (K : ℝ) /
          (R * ((D + 1 : ℕ) : ℝ)) + delta * (M : ℝ) := by
    positivity
  by_cases hNzero : N = 0
  · have htriv := norm_sum_inverseSquareCutoffWeight_correlation_le_commonLength
      X hsPos hrPos (x := x) (y := y)
        (m₀ := M) (m₁ := 2 * M) (k₁ := s) (k₂ := r)
    have hzero :
        min (2 * M) (min (y / s) (y / r)) -
            max M (max (x / s) (x / r)) = 0 := by
      dsimp only [N, inverseSquareCentralCorrelationLength,
        inverseSquareCentralCorrelationUpper,
        inverseSquareCentralCorrelationLower] at hNzero
      simpa only [min_comm (y / s), max_comm (x / s)] using hNzero
    rw [hzero] at htriv
    norm_num at htriv
    rw [htriv]
    simpa using hrightNonneg
  have hNpos : 0 < N := Nat.pos_of_ne_zero hNzero
  have hscale := inverseSquareCentralCorrelation_scale_bounds
    hM hK hKM hr hs hrs hXlo hXhi hyx hNpos
  rcases hscale with ⟨hab, hMa, hbM, hQpos, _hQlo, hQupper⟩
  by_cases hlength : 2 ≤ N
  · by_cases hmoderate : 4 * Q ≤ (M : ℝ) ^ 3
    · rw [norm_sum_inverseSquareCutoffWeight_correlation_comm
        X x y M (2 * M) s r]
      rw [sum_inverseSquareCutoffWeight_correlation_eq_phase X hrPos hsPos hrs.le]
      change ‖inverseSquareProductIntervalSum Q 1 a b‖ ≤ _
      have hraw := norm_inverseSquareProductIntervalSum_le_moderate
        hQpos hM hab hMa hbM hlength hmoderate
      have hfreq := inverseSquareCentralCorrelationFrequency_lower_of_nonempty
        hR hM hK hKM hr hs hrs hXratio hNpos
      have hD : ((D + 1 : ℕ) : ℝ) ≤ ((s - r : ℕ) : ℝ) := by
        exact_mod_cast hfar
      have hden : 0 < R * ((D + 1 : ℕ) : ℝ) := by positivity
      have hratio : 12 * (M : ℝ) ^ 3 / Q ≤
          96 * (M : ℝ) * (K : ℝ) /
            (R * ((D + 1 : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ hQpos hden]
        have hfreqD : R * (M : ℝ) ^ 2 * ((D + 1 : ℕ) : ℝ) ≤
            8 * Q * (K : ℝ) := by
          exact (mul_le_mul_of_nonneg_left hD (by positivity)).trans hfreq
        nlinarith [mul_le_mul_of_nonneg_left hfreqD
          (show (0 : ℝ) ≤ 12 * M by positivity)]
      exact hraw.trans <| by
        have hdeltaNonneg : 0 ≤ delta * (M : ℝ) := by
          positivity
        linarith
    · have hlarge : (M : ℝ) ^ 3 ≤ 4 * Q := (lt_of_not_ge hmoderate).le
      have hoff := norm_inverseSquareCentral_cutoff_correlation_le
        hX hM hK hKM hr hs hrs hXlo hXhi hyx hsize hC hbaseCap
      have henv := hlargeEnvelope Q hQpos hlarge hQupper
      have hsmall :
          ‖∑ m ∈ Finset.Ioc M (2 * M),
            inverseSquareCutoffWeight X x y m s *
              conj (inverseSquareCutoffWeight X x y m r)‖ ≤
            delta * (M : ℝ) := hoff.trans (by simpa only [Q] using henv)
      calc
        _ ≤ delta * (M : ℝ) := hsmall
        _ ≤ _ := by
          have hfrac : 0 ≤ 96 * (M : ℝ) * (K : ℝ) /
              (R * ((D + 1 : ℕ) : ℝ)) := by positivity
          linarith
  · have hNone : N = 1 := by omega
    have htriv := norm_sum_inverseSquareCutoffWeight_correlation_le_commonLength
      X hsPos hrPos (x := x) (y := y)
        (m₀ := M) (m₁ := 2 * M) (k₁ := s) (k₂ := r)
    have hone :
        min (2 * M) (min (y / s) (y / r)) -
            max M (max (x / s) (x / r)) = 1 := by
      dsimp only [N, inverseSquareCentralCorrelationLength,
        inverseSquareCentralCorrelationUpper,
        inverseSquareCentralCorrelationLower] at hNone
      simpa only [min_comm (y / s), max_comm (x / s)] using hNone
    rw [hone] at htriv
    norm_num at htriv
    exact htriv.trans (by
      have hrest : 0 ≤ 96 * (M : ℝ) * (K : ℝ) /
          (R * ((D + 1 : ℕ) : ℝ)) + delta * (M : ℝ) := by
        positivity
      linarith)

end

end InverseSquareHybridAsymptotic
end Erdos378
