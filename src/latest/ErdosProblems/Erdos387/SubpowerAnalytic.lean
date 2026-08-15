/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.SubpowerScale
import ErdosProblems.Erdos387.SwitchedClassSieve

/-!
# Analytic estimates on the subpower scale

This file records the elementary logarithmic identities and polynomial
envelopes needed to specialize the finite Section 6 estimates.  Separating
these facts from the combinatorial counting statements keeps all rounding
and coercion issues local to the powers-of-two parameterization.
-/

namespace Erdos387

open Filter
open scoped Topology

namespace SubpowerScale

theorem roughPower_pos {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    0 < roughPower N k := by
  unfold roughPower BPZScale.xExp
  positivity

theorem two_le_roughPower {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    2 ≤ roughPower N k := by
  unfold roughPower BPZScale.xExp
  calc
    2 ≤ 600 := by norm_num
    _ ≤ 600 * (3 ^ k * k ^ 100 * N ^ (2 * k + 3)) :=
      Nat.le_mul_of_pos_right 600 (by positivity)
    _ = 600 * 3 ^ k * k ^ 100 * N ^ (2 * k + 3) := by ring

theorem X_pos (N k : ℕ) : 0 < X N k := by
  rw [X_eq_pow_two]
  positivity

theorem z_pos (N k : ℕ) : 0 < z N k := by
  unfold z
  positivity

theorem log_z_eq (N k : ℕ) :
    Real.log (z N k : ℝ) = (roughPower N k : ℝ) * Real.log 2 := by
  simp [z, Real.log_pow]

theorem log_X_eq (N k : ℕ) :
    Real.log (X N k : ℝ) =
      (BPZScale.xExp k * N ^ (2 * k + 5) : ℕ) * Real.log 2 := by
  rw [X_eq_pow_two]
  simp [Real.log_pow]

/-- The exact logarithmic separation built into the subpower scale. -/
theorem log_X_div_log_z_eq_square {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    Real.log (X N k : ℝ) / Real.log (z N k : ℝ) = (N : ℝ) ^ 2 := by
  rw [log_X_eq, log_z_eq]
  have hx : (0 : ℝ) < BPZScale.xExp k := by
    unfold BPZScale.xExp
    positivity
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hrough : (0 : ℝ) < roughPower N k := by
    exact_mod_cast roughPower_pos hN hk
  have hpow : N ^ (2 * k + 5) = N ^ (2 * k + 3) * N ^ 2 := by
    rw [← pow_add]
  rw [hpow]
  unfold roughPower
  push_cast
  field_simp

theorem two_le_z {N k : ℕ} (hN : 0 < N) (hk : 0 < k) : 2 ≤ z N k := by
  unfold z
  have hE : 1 ≤ roughPower N k := roughPower_pos hN hk
  simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hE

/-- Every fixed natural is eventually below the roughness threshold. -/
theorem eventually_const_le_z {k : ℕ} (hk : 0 < k) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, A ≤ z N k := by
  have hzTop : Tendsto (fun N : ℕ => z N k) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    unfold z roughPower
    apply Nat.pow_le_pow_right (by omega)
    have hx : 0 < BPZScale.xExp k := by
      unfold BPZScale.xExp
      positivity
    have hpow : N ≤ N ^ (2 * k + 3) := by
      simpa using Nat.pow_le_pow_right hN (by omega : 1 ≤ 2 * k + 3)
    exact hpow.trans (by simpa [mul_comm] using
      Nat.le_mul_of_pos_left (N ^ (2 * k + 3)) hx)
  exact hzTop.eventually_ge_atTop A

theorem z_le_X {N k : ℕ} (hN : 0 < N) : z N k ≤ X N k := by
  rw [X_eq_pow_two]
  unfold z roughPower
  apply Nat.pow_le_pow_right (by omega)
  gcongr
  omega

theorem eventually_const_le_X {k : ℕ} (hk : 0 < k) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, A ≤ X N k := by
  filter_upwards [eventually_const_le_z hk A,
    eventually_ge_atTop (1 : ℕ)] with N hz hN
  exact hz.trans (z_le_X (by omega))

/-- The inner switching endpoint is bounded by the square of the ambient
endpoint as soon as the latter absorbs the fixed coefficient. -/
theorem innerSwitchEndpoint_le_X_sq
    {B X large : ℕ} (hX : 2 * B + 1 ≤ X) :
    2 * B * (X / (large + 1)) + 1 ≤ X ^ 2 := by
  have hdiv : X / (large + 1) ≤ X := Nat.div_le_self X _
  calc
    2 * B * (X / (large + 1)) + 1 ≤ 2 * B * X + 1 := by gcongr
    _ ≤ X ^ 2 := by nlinarith

/-- The outer switching endpoint is a fixed power of `X`. -/
theorem outerSwitchEndpoint_le_X_pow
    {B X large k : ℕ} (hX : 2 * B + 1 ≤ X) :
    2 * B * (2 * B * (X / (large + 1)) + 1) ^ k + 1 ≤
      X ^ (2 * k + 1) := by
  let T := 2 * B * (X / (large + 1)) + 1
  have hT : T ≤ X ^ 2 := innerSwitchEndpoint_le_X_sq hX
  have hTone : 1 ≤ T ^ k := by
    exact one_le_pow₀ (by dsimp [T]; omega)
  calc
    2 * B * T ^ k + 1 ≤ (2 * B + 1) * T ^ k := by
      nlinarith
    _ ≤ X * (X ^ 2) ^ k := Nat.mul_le_mul hX (Nat.pow_le_pow_left hT k)
    _ = X ^ (2 * k + 1) := by
      rw [← pow_mul]
      calc
        X * X ^ (2 * k) = X ^ 1 * X ^ (2 * k) := by simp
        _ = X ^ (1 + 2 * k) := (pow_add X 1 (2 * k)).symm
        _ = X ^ (2 * k + 1) := by congr 1 <;> omega

/-- A natural upper bound by a power of `X` becomes the corresponding
logarithmic upper bound. -/
theorem log_le_nat_mul_log_X {T X D : ℕ}
    (hTpos : 0 < T) (hXpos : 0 < X) (hT : T ≤ X ^ D) :
    Real.log (T : ℝ) ≤ (D : ℝ) * Real.log (X : ℝ) := by
  have hlog := Real.strictMonoOn_log.monotoneOn
    (by positivity : (0 : ℝ) < T)
    (by positivity : (0 : ℝ) < X ^ D)
    (by exact_mod_cast hT)
  simpa [Real.log_pow] using hlog

theorem innerSwitch_log_div_log_z_le
    {B N k large : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hX : 2 * B + 1 ≤ X N k) :
    Real.log ((2 * B * (X N k / (large + 1)) + 1 : ℕ) : ℝ) /
        Real.log (z N k : ℝ) ≤ 2 * (N : ℝ) ^ 2 := by
  have hzlog : 0 < Real.log (z N k : ℝ) :=
    Real.log_pos (by exact_mod_cast two_le_z hN hk)
  rw [div_le_iff₀ hzlog]
  calc
    Real.log (2 * B * (X N k / (large + 1)) + 1 : ℕ) ≤
        (2 : ℝ) * Real.log (X N k : ℝ) :=
      log_le_nat_mul_log_X (by omega) (X_pos _ _)
        (innerSwitchEndpoint_le_X_sq hX)
    _ = (2 * (N : ℝ) ^ 2) * Real.log (z N k : ℝ) := by
      rw [show Real.log (X N k : ℝ) =
          (N : ℝ) ^ 2 * Real.log (z N k : ℝ) by
        have := log_X_div_log_z_eq_square hN hk
        rw [div_eq_iff (ne_of_gt hzlog)] at this
        exact this]
      ring

theorem outerSwitch_log_div_log_z_le
    {B N k large : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hX : 2 * B + 1 ≤ X N k) :
    Real.log ((2 * B * (2 * B * (X N k / (large + 1)) + 1) ^ k + 1 : ℕ) : ℝ) /
        Real.log (z N k : ℝ) ≤ (2 * k + 1 : ℕ) * (N : ℝ) ^ 2 := by
  have hzlog : 0 < Real.log (z N k : ℝ) :=
    Real.log_pos (by exact_mod_cast two_le_z hN hk)
  rw [div_le_iff₀ hzlog]
  calc
    Real.log (2 * B * (2 * B * (X N k / (large + 1)) + 1) ^ k + 1 : ℕ) ≤
        (2 * k + 1 : ℕ) * Real.log (X N k : ℝ) :=
      log_le_nat_mul_log_X (by omega) (X_pos _ _)
        (outerSwitchEndpoint_le_X_pow hX)
    _ = ((2 * k + 1 : ℕ) * (N : ℝ) ^ 2) *
          Real.log (z N k : ℝ) := by
      rw [show Real.log (X N k : ℝ) =
          (N : ℝ) ^ 2 * Real.log (z N k : ℝ) by
        have := log_X_div_log_z_eq_square hN hk
        rw [div_eq_iff (ne_of_gt hzlog)] at this
        exact this]
      ring

/-- The fixed part of the all-endpoint rough harmonic envelope. -/
noncomputable def roughEnvelopeOffset (K : ℝ) : ℝ :=
  10 * (1 + |K +
      BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2|) +
    2 * (Real.exp 16 +
      4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant)

theorem roughEnvelopeOffset_nonneg (K : ℝ) :
    0 ≤ roughEnvelopeOffset K := by
  unfold roughEnvelopeOffset
  have hcorr : 0 ≤
      BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant := by
    unfold BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant
    positivity
  positivity

theorem one_le_log_z {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    1 ≤ Real.log (z N k : ℝ) := by
  rw [log_z_eq]
  have hrough : (2 : ℝ) ≤ roughPower N k := by
    exact_mod_cast two_le_roughPower hN hk
  have hlog := Real.log_two_gt_d9
  nlinarith

/-- If the variable endpoint contributes at most `D log X`, the explicit
Wirsing envelope is bounded by a fixed multiple of `N²`. -/
theorem roughLogRatioEnvelope_le_mul_square
    {K : ℝ} {N k D T : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hT : Real.log (T : ℝ) / Real.log (z N k : ℝ) ≤
      (D : ℝ) * (N : ℝ) ^ 2) :
    RoughHarmonic.roughLogRatioEnvelope K (z N k) T ≤
      ((D : ℝ) + roughEnvelopeOffset K) * (N : ℝ) ^ 2 := by
  let Q := K + BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2
  let lz := Real.log (z N k : ℝ)
  have hlzOne : 1 ≤ lz := one_le_log_z hN hk
  have hlzPos : 0 < lz := lt_of_lt_of_le zero_lt_one hlzOne
  have hzTwo := two_le_z hN hk
  have hzm1Pos : (0 : ℝ) < (z N k - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < z N k - 1)
  have hzPos : (0 : ℝ) < z N k := by positivity
  have hzm1Le : ((z N k - 1 : ℕ) : ℝ) ≤ z N k := by
    exact_mod_cast Nat.sub_le (z N k) 1
  have hlogSub : Real.log (z N k - 1 : ℕ) ≤ lz := by
    exact Real.strictMonoOn_log.monotoneOn hzm1Pos hzPos hzm1Le
  have hQabs : Q ≤ |Q| := le_abs_self Q
  have habsMul : |Q| ≤ |Q| * lz := by
    simpa using mul_le_mul_of_nonneg_left hlzOne (abs_nonneg Q)
  have hnum :
      K + Real.log (z N k - 1 : ℕ) +
          BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2 ≤
        (1 + |Q|) * lz := by
    dsimp [Q]
    linarith
  have hratio :
      (K + Real.log (z N k - 1 : ℕ) +
          BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) / lz ≤
        1 + |Q| := by
    rw [div_le_iff₀ hlzPos]
    exact hnum
  have hNtwo : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hoff := roughEnvelopeOffset_nonneg K
  unfold RoughHarmonic.roughLogRatioEnvelope roughEnvelopeOffset
  dsimp [lz] at hT hratio ⊢
  have hfixed :
      10 * (1 + |Q|) +
          2 * (Real.exp 16 +
            4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant) ≤
        (10 * (1 + |Q|) +
          2 * (Real.exp 16 +
            4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant)) *
          (N : ℝ) ^ 2 := by
    let F := 10 * (1 + |Q|) +
      2 * (Real.exp 16 +
        4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant)
    have hF : 0 ≤ F := by
      dsimp [F]
      have hcorr : 0 ≤
          BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant := by
        unfold BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant
        positivity
      positivity
    change F ≤ F * (N : ℝ) ^ 2
    calc
      F = F * 1 := by ring
      _ ≤ F * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hNtwo hF
  dsimp [Q] at hratio hfixed ⊢
  nlinarith

/-- Both rough masses occurring in the localized switching estimate have a
uniform quadratic envelope in the scale parameter. -/
theorem exists_switchingRoughMass_quadratic_bound
    {B k : ℕ} (hk : 0 < k) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧
      ∀ᶠ N : ℕ in atTop,
        roughReciprocalMass (z N k)
              (2 * B * (X N k / (large N k + 1)) + 1) ≤
            A * (N : ℝ) ^ 2 ∧
          roughReciprocalMass (z N k)
              (2 * B *
                (2 * B * (X N k / (large N k + 1)) + 1) ^ k + 1) ≤
            A * (N : ℝ) ^ 2 := by
  obtain ⟨K, hK, hmass⟩ :=
    RoughHarmonic.exists_uniform_roughReciprocalMass_le_envelope
  let A := (2 * k + 1 : ℕ) + roughEnvelopeOffset K + 1
  have hA : 0 < A := by
    dsimp [A]
    have := roughEnvelopeOffset_nonneg K
    positivity
  refine ⟨K, A, hK, hA, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (2 * B + 1))] with N hN
  have hNpos : 0 < N := by omega
  have hXbig : 2 * B + 1 ≤ X N k := by
    have hpow : N ≤ X N k := by
      rw [X_eq_pow_two]
      have hNtwo : N ≤ 2 ^ N := Nat.le_of_lt N.lt_two_pow_self
      exact hNtwo.trans (Nat.pow_le_pow_right (by omega) (by
        have hNpow : N ≤ N ^ (2 * k + 5) := by
          simpa using Nat.pow_le_pow_right (by omega : 1 ≤ N)
            (by omega : 1 ≤ 2 * k + 5)
        exact hNpow.trans (Nat.le_mul_of_pos_left _ (by
          unfold BPZScale.xExp
          positivity))))
    exact (le_max_right 1 (2 * B + 1) |>.trans hN).trans hpow
  have hzTwo := two_le_z hNpos hk
  have hsmallBase := hmass (z N k)
    (2 * B * (X N k / (large N k + 1)) + 1) hzTwo
  have hlargeBase := hmass (z N k)
    (2 * B * (2 * B * (X N k / (large N k + 1)) + 1) ^ k + 1) hzTwo
  have hsmallEnv := roughLogRatioEnvelope_le_mul_square (K := K) hNpos hk
    (innerSwitch_log_div_log_z_le (large := large N k) hNpos hk hXbig)
  have hlargeEnv := roughLogRatioEnvelope_le_mul_square (K := K) hNpos hk
    (outerSwitch_log_div_log_z_le (large := large N k) hNpos hk hXbig)
  have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsmallCoeff : (2 : ℝ) + roughEnvelopeOffset K ≤ A := by
    dsimp [A]
    push_cast
    linarith
  have hlargeCoeff :
      ((2 * k + 1 : ℕ) : ℝ) + roughEnvelopeOffset K ≤ A := by
    dsimp [A]
    linarith
  constructor
  · exact hsmallBase.trans (hsmallEnv.trans (by
      exact mul_le_mul_of_nonneg_right hsmallCoeff (sq_nonneg _)))
  · exact hlargeBase.trans (hlargeEnv.trans (by
      exact mul_le_mul_of_nonneg_right hlargeCoeff (sq_nonneg _)))

/-- On the subpower scale the localized reciprocal-certificate main term is
`O(1/N)`.  This is the quantitative saving in Proposition 6.2. -/
theorem exists_localizedSwitchedReciprocalEnvelope_le_div
    {C : ℝ} (hC : 0 < C) {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hB : 0 < B) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop,
      CoverBPZ.localizedSwitchedReciprocalEnvelope S C
          (X N S.k) (z N S.k) (large N S.k) ≤ D / N := by
  obtain ⟨_Krough, A, _hKrough, hA, hmass⟩ :=
    exists_switchingRoughMass_quadratic_bound (B := B)
      (k := S.k) (by have := S.hk3; omega)
  let D : ℝ :=
    (S.k : ℝ) * ((12 * B : ℝ) * C) * A ^ (S.k + 1) /
      ((BPZScale.xExp S.k : ℝ) * Real.log 2)
  have hx : (0 : ℝ) < BPZScale.xExp S.k := by
    unfold BPZScale.xExp
    have := S.hk3
    positivity
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by
    dsimp [D]
    have hk : (0 : ℝ) < S.k := by exact_mod_cast (by have := S.hk3; omega)
    positivity
  refine ⟨D, hD, ?_⟩
  filter_upwards [hmass, eventually_ge_atTop (1 : ℕ)] with N hmassN hN
  have hNpos : 0 < N := by omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hzlog : 0 < Real.log (z N S.k : ℝ) :=
    Real.log_pos (by exact_mod_cast two_le_z hNpos (by have := S.hk3; omega))
  have hsmallNonneg :
      0 ≤ roughReciprocalMass (z N S.k)
        (2 * B * (X N S.k / (large N S.k + 1)) + 1) := by
    unfold roughReciprocalMass
    positivity
  have hbigNonneg :
      0 ≤ roughReciprocalMass (z N S.k)
        (2 * B *
          (2 * B * (X N S.k / (large N S.k + 1)) + 1) ^ S.k + 1) := by
    unfold roughReciprocalMass
    positivity
  have hpowMass :
      (roughReciprocalMass (z N S.k)
          (2 * B * (X N S.k / (large N S.k + 1)) + 1)) ^ S.k ≤
        (A * (N : ℝ) ^ 2) ^ S.k :=
    pow_le_pow_left₀ hsmallNonneg hmassN.1 S.k
  have henv :
      CoverBPZ.localizedSwitchedReciprocalEnvelope S C
          (X N S.k) (z N S.k) (large N S.k) ≤
        (S.k : ℝ) *
          (((12 * B : ℝ) * C / Real.log (z N S.k : ℝ)) *
            (A * (N : ℝ) ^ 2) *
            (A * (N : ℝ) ^ 2) ^ S.k) := by
    unfold CoverBPZ.localizedSwitchedReciprocalEnvelope
    gcongr
    exact hmassN.2
  have hpowN :
      ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2) ^ S.k) * N =
        (N : ℝ) ^ (2 * S.k + 3) := by
    calc
      ((N : ℝ) ^ 2 * ((N : ℝ) ^ 2) ^ S.k) * N =
          ((N : ℝ) ^ 2 * (N : ℝ) ^ (2 * S.k)) * (N : ℝ) ^ 1 := by
        rw [← pow_mul]
        simp
      _ = (N : ℝ) ^ (2 + 2 * S.k) * (N : ℝ) ^ 1 := by rw [pow_add]
      _ = (N : ℝ) ^ (2 + 2 * S.k + 1) := (pow_add _ _ _).symm
      _ = (N : ℝ) ^ (2 * S.k + 3) := by congr 1 <;> omega
  have hpowNthree :
      (N : ℝ) ^ 3 * ((N : ℝ) ^ 2) ^ S.k =
        (N : ℝ) ^ (2 * S.k + 3) := by
    calc
      (N : ℝ) ^ 3 * ((N : ℝ) ^ 2) ^ S.k =
          (N : ℝ) ^ 3 * (N : ℝ) ^ (2 * S.k) := by rw [← pow_mul]
      _ = (N : ℝ) ^ (3 + 2 * S.k) := (pow_add _ _ _).symm
      _ = (N : ℝ) ^ (2 * S.k + 3) := by congr 1 <;> omega
  have hpowA : A * A ^ S.k = A ^ (S.k + 1) := by
    rw [pow_succ']
  have heq :
      (S.k : ℝ) *
          (((12 * B : ℝ) * C / Real.log (z N S.k : ℝ)) *
            (A * (N : ℝ) ^ 2) *
            (A * (N : ℝ) ^ 2) ^ S.k) = D / N := by
    rw [log_z_eq]
    unfold roughPower
    push_cast
    dsimp [D]
    rw [mul_pow]
    field_simp
    calc
      (S.k : ℝ) * A * (N : ℝ) ^ 3 * A ^ S.k *
          ((N : ℝ) ^ 2) ^ S.k =
          (S.k : ℝ) * ((N : ℝ) ^ 3 * ((N : ℝ) ^ 2) ^ S.k) *
            (A * A ^ S.k) := by ring
      _ = (S.k : ℝ) * (N : ℝ) ^ (2 * S.k + 3) * A ^ (S.k + 1) := by
        rw [hpowNthree, hpowA]
  exact henv.trans_eq heq

theorem tendsto_localizedSwitchedReciprocalEnvelope_zero
    {C : ℝ} (hC : 0 < C) {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hB : 0 < B) :
    Tendsto (fun N : ℕ =>
      CoverBPZ.localizedSwitchedReciprocalEnvelope S C
        (X N S.k) (z N S.k) (large N S.k)) atTop (𝓝 0) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_localizedSwitchedReciprocalEnvelope_le_div hC S hB
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < N := by omega
    have hzlog : 0 < Real.log (z N S.k : ℝ) :=
      Real.log_pos (by
        exact_mod_cast two_le_z hNpos (by have := S.hk3; omega))
    have hmassSmall : 0 ≤ roughReciprocalMass (z N S.k)
        (2 * B * (X N S.k / (large N S.k + 1)) + 1) := by
      unfold roughReciprocalMass
      positivity
    have hmassBig : 0 ≤ roughReciprocalMass (z N S.k)
        (2 * B *
          (2 * B * (X N S.k / (large N S.k + 1)) + 1) ^ S.k + 1) := by
      unfold roughReciprocalMass
      positivity
    unfold CoverBPZ.localizedSwitchedReciprocalEnvelope
    positivity
  · exact hbound
  · simpa using tendsto_const_div_atTop_nhds_zero_nat D

/-- The exponent left after taking two divisor-switching complements. -/
def switchGapExp (k : ℕ) : ℕ := 6 * 3 ^ k * k ^ 100

theorem two_switch_add_gap (k : ℕ) :
    2 * BPZScale.switchExp k + switchGapExp k = BPZScale.xExp k := by
  simp [BPZScale.switchExp, switchGapExp, BPZScale.xExp]
  ring

theorem X_eq_switchSquare_mul_gap (N k : ℕ) :
    X N k =
      (base N k ^ BPZScale.switchExp k) ^ 2 *
        base N k ^ switchGapExp k := by
  unfold X BPZScale.X
  rw [← pow_mul, ← pow_add]
  congr 1
  rw [mul_comm]
  exact (two_switch_add_gap k).symm

theorem two_pow_N_le_base_gap {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    2 ^ N ≤ base N k ^ switchGapExp k := by
  unfold base scalePower
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by omega)
  have hpow : N ≤ N ^ (2 * k + 5) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ N)
      (by omega : 1 ≤ 2 * k + 5)
  have hgap : 0 < switchGapExp k := by
    unfold switchGapExp
    positivity
  exact hpow.trans (Nat.le_mul_of_pos_right _ hgap)

theorem two_pow_scalePower_le_base_gap {N k : ℕ} (hk : 0 < k) :
    2 ^ scalePower N k ≤ base N k ^ switchGapExp k := by
  unfold base
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by omega)
  have hgap : 1 ≤ switchGapExp k := by
    have : 0 < switchGapExp k := by
      unfold switchGapExp
      positivity
    omega
  exact Nat.le_mul_of_pos_right _ (by omega)

/-- Explicit exponentially decaying majorant for the normalized switched
certificate count. -/
theorem exists_switchedCertificateCountEnvelope_ratio_bound
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) (hB : 0 < B) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      CoverBPZ.switchedCertificateCountEnvelope S
          (X N S.k) (z N S.k) (large N S.k) / X N S.k ≤
        (A * (N : ℝ) ^ 2) ^ S.k /
          (2 : ℝ) ^ scalePower N S.k := by
  obtain ⟨_Krough, A, _hKrough, hA, hmass⟩ :=
    exists_switchingRoughMass_quadratic_bound (B := B)
      (k := S.k) (by have := S.hk3; omega)
  refine ⟨A, hA, ?_⟩
  filter_upwards [hmass, eventually_ge_atTop (1 : ℕ)] with N hmassN hN
  have hNpos : 0 < N := by omega
  have hk : 0 < S.k := by have := S.hk3; omega
  let Y := X N S.k / (large N S.k + 1)
  let G := base N S.k ^ switchGapExp S.k
  let W := base N S.k ^ BPZScale.switchExp S.k
  let P : ℝ := (A * (N : ℝ) ^ 2) ^ S.k
  have hY : Y ≤ W := by
    dsimp [Y, W, X, large]
    exact BPZScale.X_div_large_succ_le_switchPow (base N S.k) S.k
  have hYsq : (Y : ℝ) ^ 2 ≤ (W : ℝ) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left hY 2
  have hmassY : roughReciprocalMass (z N S.k) Y ≤ A * (N : ℝ) ^ 2 := by
    apply (RoughHarmonic.roughReciprocalMass_mono (z := z N S.k)
      (show Y ≤ 2 * B * Y + 1 by nlinarith)).trans
    simpa [Y] using hmassN.1
  have hmassYNonneg : 0 ≤ roughReciprocalMass (z N S.k) Y := by
    unfold roughReciprocalMass
    positivity
  have hmassPow :
      (roughReciprocalMass (z N S.k) Y) ^ S.k ≤ P := by
    dsimp [P]
    exact pow_le_pow_left₀ hmassYNonneg hmassY S.k
  have hdenPos : (0 : ℝ) < (2 : ℝ) ^ scalePower N S.k := by positivity
  have hgap : (2 : ℝ) ^ scalePower N S.k ≤ G := by
    exact_mod_cast two_pow_scalePower_le_base_gap (N := N) hk
  have hratioOne :
      (1 : ℝ) ≤ (G : ℝ) / (2 : ℝ) ^ scalePower N S.k := by
    rw [le_div_iff₀ hdenPos]
    simpa using hgap
  have hPnonneg : 0 ≤ P := by dsimp [P]; positivity
  have hPG :
      P ≤ (G : ℝ) * (P / (2 : ℝ) ^ scalePower N S.k) := by
    calc
      P = P * 1 := by ring
      _ ≤ P * ((G : ℝ) / (2 : ℝ) ^ scalePower N S.k) :=
        mul_le_mul_of_nonneg_left hratioOne hPnonneg
      _ = (G : ℝ) * (P / (2 : ℝ) ^ scalePower N S.k) := by ring
  have hXfactor : X N S.k = W ^ 2 * G := by
    simpa [W, G] using X_eq_switchSquare_mul_gap N S.k
  have hXrealPos : (0 : ℝ) < X N S.k := by exact_mod_cast X_pos N S.k
  rw [div_le_iff₀ hXrealPos]
  unfold CoverBPZ.switchedCertificateCountEnvelope
  push_cast
  change (Y : ℝ) ^ 2 *
      (roughReciprocalMass (z N S.k) Y) ^ S.k ≤
    P / (2 : ℝ) ^ scalePower N S.k * (X N S.k : ℝ)
  calc
    (Y : ℝ) ^ 2 * (roughReciprocalMass (z N S.k) Y) ^ S.k ≤
        (W : ℝ) ^ 2 * P :=
      mul_le_mul hYsq hmassPow (by positivity) (by positivity)
    _ ≤ (W : ℝ) ^ 2 *
        ((G : ℝ) * (P / (2 : ℝ) ^ scalePower N S.k)) :=
      mul_le_mul_of_nonneg_left hPG (by positivity)
    _ = P / (2 : ℝ) ^ scalePower N S.k * (X N S.k : ℝ) := by
      rw [hXfactor]
      push_cast
      ring

/-- The product-sensitive certificate count is exponentially negligible
relative to `X`; this is the second saving in the finite large-error bound. -/
theorem tendsto_switchedCertificateCountEnvelope_div_X_zero
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N : ℕ =>
      CoverBPZ.switchedCertificateCountEnvelope S
          (X N S.k) (z N S.k) (large N S.k) /
        X N S.k) atTop (𝓝 0) := by
  obtain ⟨_Krough, A, _hKrough, hA, hmass⟩ :=
    exists_switchingRoughMass_quadratic_bound (B := B)
      (k := S.k) (by have := S.hk3; omega)
  let P : ℕ → ℝ := fun N => (A * (N : ℝ) ^ 2) ^ S.k
  have hmajorant : Tendsto (fun N : ℕ => P N / (2 : ℝ) ^ N)
      atTop (𝓝 0) := by
    have hbase := tendsto_pow_const_div_const_pow_of_one_lt
      (2 * S.k) (by norm_num : (1 : ℝ) < 2)
    have hmul : Tendsto (fun N : ℕ =>
        A ^ S.k * ((N : ℝ) ^ (2 * S.k) / (2 : ℝ) ^ N))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hbase :
        Tendsto (fun N : ℕ =>
          A ^ S.k * ((N : ℝ) ^ (2 * S.k) / (2 : ℝ) ^ N))
          atTop (𝓝 (A ^ S.k * 0)))
    convert hmul using 1
    funext N
    dsimp [P]
    rw [mul_pow, ← pow_mul]
    ring
  apply squeeze_zero' (g := fun N : ℕ => P N / (2 : ℝ) ^ N)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hXpos : (0 : ℝ) < X N S.k := by exact_mod_cast X_pos N S.k
    have hcountNonneg : 0 ≤ CoverBPZ.switchedCertificateCountEnvelope S
        (X N S.k) (z N S.k) (large N S.k) := by
      unfold CoverBPZ.switchedCertificateCountEnvelope roughReciprocalMass
      positivity
    exact div_nonneg hcountNonneg hXpos.le
  · filter_upwards [hmass, eventually_ge_atTop (1 : ℕ)] with N hmassN hN
    have hNpos : 0 < N := by omega
    have hk : 0 < S.k := by have := S.hk3; omega
    let Y := X N S.k / (large N S.k + 1)
    let G := base N S.k ^ switchGapExp S.k
    let W := base N S.k ^ BPZScale.switchExp S.k
    have hY : Y ≤ W := by
      dsimp [Y, W, X, large]
      exact BPZScale.X_div_large_succ_le_switchPow (base N S.k) S.k
    have hYsq : (Y : ℝ) ^ 2 ≤ (W : ℝ) ^ 2 := by
      exact_mod_cast Nat.pow_le_pow_left hY 2
    have hmassY : roughReciprocalMass (z N S.k) Y ≤ A * (N : ℝ) ^ 2 := by
      apply (RoughHarmonic.roughReciprocalMass_mono (z := z N S.k)
        (show Y ≤ 2 * B * Y + 1 by nlinarith)).trans
      simpa [Y] using hmassN.1
    have hmassYNonneg : 0 ≤ roughReciprocalMass (z N S.k) Y := by
      unfold roughReciprocalMass
      positivity
    have hmassPow :
        (roughReciprocalMass (z N S.k) Y) ^ S.k ≤ P N := by
      dsimp [P]
      exact pow_le_pow_left₀ hmassYNonneg hmassY S.k
    have hdenPos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have hgap : (2 : ℝ) ^ N ≤ G := by
      exact_mod_cast two_pow_N_le_base_gap hNpos hk
    have hratioOne : (1 : ℝ) ≤ (G : ℝ) / (2 : ℝ) ^ N := by
      rw [le_div_iff₀ hdenPos]
      simpa using hgap
    have hPnonneg : 0 ≤ P N := by dsimp [P]; positivity
    have hPG : P N ≤ (G : ℝ) * (P N / (2 : ℝ) ^ N) := by
      calc
        P N = P N * 1 := by ring
        _ ≤ P N * ((G : ℝ) / (2 : ℝ) ^ N) :=
          mul_le_mul_of_nonneg_left hratioOne hPnonneg
        _ = (G : ℝ) * (P N / (2 : ℝ) ^ N) := by ring
    have hXfactor : X N S.k = W ^ 2 * G := by
      simpa [W, G] using X_eq_switchSquare_mul_gap N S.k
    have hXrealPos : (0 : ℝ) < X N S.k := by exact_mod_cast X_pos N S.k
    rw [div_le_iff₀ hXrealPos]
    unfold CoverBPZ.switchedCertificateCountEnvelope
    push_cast
    change (Y : ℝ) ^ 2 *
        (roughReciprocalMass (z N S.k) Y) ^ S.k ≤
      P N / (2 : ℝ) ^ N * (X N S.k : ℝ)
    calc
      (Y : ℝ) ^ 2 * (roughReciprocalMass (z N S.k) Y) ^ S.k ≤
          (W : ℝ) ^ 2 * P N :=
        mul_le_mul hYsq hmassPow (by positivity) (by positivity)
      _ ≤ (W : ℝ) ^ 2 *
          ((G : ℝ) * (P N / (2 : ℝ) ^ N)) :=
        mul_le_mul_of_nonneg_left hPG (by positivity)
      _ = P N / (2 : ℝ) ^ N * (X N S.k : ℝ) := by
        rw [hXfactor]
        push_cast
        ring
  · exact hmajorant

/-- Binary exponent used to dominate the fixed factor `2k`. -/
def brunFixedBaseExponent (k : ℕ) : ℕ := Nat.log 2 (2 * k) + 1

/-- One exponent dominating the upper-Brun endpoint factor
`8 * z^L * (2k)^L`. -/
def brunEndpointExponent (a b N k : ℕ) : ℕ :=
  (roughPower N k + brunFixedBaseExponent k) *
      CoverBPZ.refinedEvenBrunDepth a b (z N k) + 3

theorem two_mul_brunEndpointExponent_le_scalePower
    {a b N k : ℕ} (hk : 0 < k)
    (hN : 2 * ((BPZScale.xExp k + brunFixedBaseExponent k) *
          (2 * depthSlope a b k + 1)) + 6 ≤ N) :
    2 * brunEndpointExponent a b N k ≤ scalePower N k := by
  let q := brunFixedBaseExponent k
  let C := 2 * depthSlope a b k + 1
  let L := CoverBPZ.refinedEvenBrunDepth a b (z N k)
  have hNpos : 0 < N := by omega
  have hNone : 1 ≤ N := by omega
  have hLbase := logarithmicBrunDepth_le_slope
    (a := a) (b := b) (k := k) hNone
  have hL : L ≤ C * N := by
    dsimp [L, C, CoverBPZ.refinedEvenBrunDepth]
    nlinarith
  have hpowOne : 1 ≤ N ^ (2 * k + 3) := one_le_pow₀ hNpos
  have hroughQ :
      roughPower N k + q ≤
        (BPZScale.xExp k + q) * N ^ (2 * k + 3) := by
    unfold roughPower
    nlinarith
  have hprod :
      (roughPower N k + q) * L ≤
        ((BPZScale.xExp k + q) * C) * N ^ (2 * k + 4) := by
    calc
      (roughPower N k + q) * L ≤
          ((BPZScale.xExp k + q) * N ^ (2 * k + 3)) * (C * N) :=
        Nat.mul_le_mul hroughQ hL
      _ = ((BPZScale.xExp k + q) * C) * N ^ (2 * k + 4) := by
        rw [show N ^ (2 * k + 4) = N ^ (2 * k + 3) * N by
          simpa using pow_succ N (2 * k + 3)]
        ring
  have hbigPowOne : 1 ≤ N ^ (2 * k + 4) := one_le_pow₀ hNpos
  have hscale :
      scalePower N k = N ^ (2 * k + 4) * N := by
    unfold scalePower
    simpa using pow_succ N (2 * k + 4)
  dsimp [brunEndpointExponent, q, L] at hprod ⊢
  rw [hscale]
  let D := (BPZScale.xExp k + brunFixedBaseExponent k) * C
  have hmul := Nat.mul_le_mul_right (N ^ (2 * k + 4)) hN
  calc
    2 * ((roughPower N k + brunFixedBaseExponent k) *
          CoverBPZ.refinedEvenBrunDepth a b (z N k) + 3) ≤
        2 * (D * N ^ (2 * k + 4) + 3) := by
      gcongr
    _ = 2 * D * N ^ (2 * k + 4) + 6 := by ring
    _ ≤ (2 * D + 6) * N ^ (2 * k + 4) := by
      nlinarith
    _ ≤ N * N ^ (2 * k + 4) := by
      simpa [D] using hmul
    _ = N ^ (2 * k + 4) * N := by ring

theorem eventually_two_mul_brunEndpointExponent_le_scalePower
    (a b k : ℕ) (hk : 0 < k) :
    ∀ᶠ N : ℕ in atTop,
      2 * brunEndpointExponent a b N k ≤ scalePower N k := by
  filter_upwards [eventually_ge_atTop
    (2 * ((BPZScale.xExp k + brunFixedBaseExponent k) *
      (2 * depthSlope a b k + 1)) + 6)] with N hN
  exact two_mul_brunEndpointExponent_le_scalePower hk hN

theorem upperBrunEndpoint_mul_eulerReciprocal_le_pow
    {a b N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    (4 : ℝ) *
        (z N k ^ CoverBPZ.refinedEvenBrunDepth a b (z N k) + 1 : ℕ) *
        (k : ℝ) ^ CoverBPZ.refinedEvenBrunDepth a b (z N k) *
        (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k) ≤
      (2 : ℝ) ^ brunEndpointExponent a b N k := by
  let L := CoverBPZ.refinedEvenBrunDepth a b (z N k)
  let q := brunFixedBaseExponent k
  have hzTwo := two_le_z hN hk
  have hzPowOne : 1 ≤ z N k ^ L := one_le_pow₀ (z_pos N k)
  have hsum : z N k ^ L + 1 ≤ 2 * z N k ^ L := by omega
  have hkbase : 2 * k ≤ 2 ^ q := by
    dsimp [q, brunFixedBaseExponent]
    exact (Nat.lt_pow_succ_log_self (by norm_num) (2 * k)).le
  have hkpow : ((2 * k : ℕ) : ℝ) ^ L ≤ (2 : ℝ) ^ (q * L) := by
    have hp := Nat.pow_le_pow_left hkbase L
    simpa [pow_mul] using (show (((2 * k) ^ L : ℕ) : ℝ) ≤
      (((2 ^ q) ^ L : ℕ) : ℝ) by exact_mod_cast hp)
  have hoddEven :
      PrimeReciprocal.logarithmicBrunDepth a b (z N k) + 1 = L := by
    rfl
  have hcombine :
      (k : ℝ) ^ L *
          (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k) ≤
        ((2 * k : ℕ) : ℝ) ^ L := by
    have htwo :
        (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k) ≤
          (2 : ℝ) ^ L := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc
      (k : ℝ) ^ L *
          (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k) ≤
          (k : ℝ) ^ L * (2 : ℝ) ^ L :=
        mul_le_mul_of_nonneg_left htwo (by positivity)
      _ = ((2 * k : ℕ) : ℝ) ^ L := by
        push_cast
        rw [mul_pow]
        ring
  have hzPow : ((z N k ^ L : ℕ) : ℝ) =
      (2 : ℝ) ^ (roughPower N k * L) := by
    unfold z
    rw [← pow_mul]
    push_cast
    rfl
  calc
    (4 : ℝ) * (z N k ^ L + 1 : ℕ) * (k : ℝ) ^ L *
          (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k) ≤
        8 * (z N k ^ L : ℕ) *
          ((k : ℝ) ^ L *
            (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k)) := by
      have hsumR : ((z N k ^ L + 1 : ℕ) : ℝ) ≤
          2 * ((z N k ^ L : ℕ) : ℝ) := by exact_mod_cast hsum
      push_cast at hsumR ⊢
      calc
        (4 : ℝ) * (↑(z N k) ^ L + 1) * ↑k ^ L *
              (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k) ≤
            (4 : ℝ) * ((2 : ℝ) * ↑(z N k) ^ L) * ↑k ^ L *
              (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k) := by
          gcongr
        _ = (8 : ℝ) * ↑(z N k) ^ L *
            (↑k ^ L *
              (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k)) := by ring
    _ ≤ 8 * (z N k ^ L : ℕ) * ((2 * k : ℕ) : ℝ) ^ L := by
      gcongr
    _ ≤ 8 * (z N k ^ L : ℕ) * (2 : ℝ) ^ (q * L) := by
      gcongr
    _ = (2 : ℝ) ^ brunEndpointExponent a b N k := by
      rw [hzPow]
      dsimp [brunEndpointExponent, q, L]
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
      congr 1
      ring

theorem self_le_roughPower {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    N ≤ roughPower N k := by
  unfold roughPower
  have hpow : N ≤ N ^ (2 * k + 3) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ N)
      (by omega : 1 ≤ 2 * k + 3)
  exact hpow.trans (Nat.le_mul_of_pos_left _ (by
    unfold BPZScale.xExp
    positivity))

/-- After inserting the reciprocal Euler-product bound, the entire
certificate-count times even-Brun endpoint remainder is negligible relative
to `X`. -/
theorem tendsto_certificateBrunEndpoint_normalized_zero
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) (hB : 0 < B)
    (a b : ℕ) :
    Tendsto (fun N : ℕ =>
      (CoverBPZ.switchedCertificateCountEnvelope S
          (X N S.k) (z N S.k) (large N S.k) / X N S.k) *
        ((4 : ℝ) *
          (z N S.k ^ CoverBPZ.refinedEvenBrunDepth a b (z N S.k) + 1 : ℕ) *
          (S.k : ℝ) ^ CoverBPZ.refinedEvenBrunDepth a b (z N S.k) *
          (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k)))
      atTop (𝓝 0) := by
  obtain ⟨A, hA, hcount⟩ :=
    exists_switchedCertificateCountEnvelope_ratio_bound S hB
  let P : ℕ → ℝ := fun N => (A * (N : ℝ) ^ 2) ^ S.k
  let e : ℕ → ℕ := fun N => brunEndpointExponent a b N S.k
  have hmajorant : Tendsto (fun N : ℕ => P N / (2 : ℝ) ^ N)
      atTop (𝓝 0) := by
    have hbase := tendsto_pow_const_div_const_pow_of_one_lt
      (2 * S.k) (by norm_num : (1 : ℝ) < 2)
    have hmul : Tendsto (fun N : ℕ =>
        A ^ S.k * ((N : ℝ) ^ (2 * S.k) / (2 : ℝ) ^ N))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hbase :
        Tendsto (fun N : ℕ =>
          A ^ S.k * ((N : ℝ) ^ (2 * S.k) / (2 : ℝ) ^ N))
          atTop (𝓝 (A ^ S.k * 0)))
    convert hmul using 1
    funext N
    dsimp [P]
    rw [mul_pow, ← pow_mul]
    ring
  have hexp := eventually_two_mul_brunEndpointExponent_le_scalePower
    a b S.k (by have := S.hk3; omega)
  apply squeeze_zero' (g := fun N : ℕ => P N / (2 : ℝ) ^ N)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hXpos : (0 : ℝ) < X N S.k := by exact_mod_cast X_pos N S.k
    have hcountNonneg : 0 ≤ CoverBPZ.switchedCertificateCountEnvelope S
        (X N S.k) (z N S.k) (large N S.k) := by
      unfold CoverBPZ.switchedCertificateCountEnvelope roughReciprocalMass
      positivity
    have hendpointNonneg : 0 ≤
        (4 : ℝ) *
          (z N S.k ^ CoverBPZ.refinedEvenBrunDepth a b (z N S.k) + 1 : ℕ) *
          (S.k : ℝ) ^ CoverBPZ.refinedEvenBrunDepth a b (z N S.k) *
          (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) := by
      positivity
    exact mul_nonneg (div_nonneg hcountNonneg hXpos.le) hendpointNonneg
  · filter_upwards [hcount, hexp, eventually_ge_atTop (1 : ℕ)] with
      N hcountN hexpN hN
    have hNpos : 0 < N := by omega
    have hk : 0 < S.k := by have := S.hk3; omega
    have hendpoint := upperBrunEndpoint_mul_eulerReciprocal_le_pow
      (a := a) (b := b) hNpos hk
    have hcountNonneg : 0 ≤
        CoverBPZ.switchedCertificateCountEnvelope S
          (X N S.k) (z N S.k) (large N S.k) / X N S.k := by
      apply div_nonneg
      · unfold CoverBPZ.switchedCertificateCountEnvelope roughReciprocalMass
        positivity
      · positivity
    have hPNnonneg : 0 ≤ P N / (2 : ℝ) ^ scalePower N S.k := by
      dsimp [P]
      positivity
    have hfirst :
        (CoverBPZ.switchedCertificateCountEnvelope S
            (X N S.k) (z N S.k) (large N S.k) / X N S.k) *
          ((4 : ℝ) *
            (z N S.k ^ CoverBPZ.refinedEvenBrunDepth a b (z N S.k) + 1 : ℕ) *
            (S.k : ℝ) ^ CoverBPZ.refinedEvenBrunDepth a b (z N S.k) *
            (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k)) ≤
          (P N / (2 : ℝ) ^ scalePower N S.k) * (2 : ℝ) ^ e N := by
      exact mul_le_mul hcountN (by simpa [e] using hendpoint)
        (by positivity) hPNnonneg
    have hNe : N ≤ e N := by
      have hrough := self_le_roughPower hNpos hk
      have hLOne : 1 ≤ CoverBPZ.refinedEvenBrunDepth a b (z N S.k) := by
        unfold CoverBPZ.refinedEvenBrunDepth
        omega
      dsimp [e, brunEndpointExponent]
      calc
        N ≤ roughPower N S.k := hrough
        _ ≤ (roughPower N S.k + brunFixedBaseExponent S.k) *
              CoverBPZ.refinedEvenBrunDepth a b (z N S.k) := by
          exact le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ hLOne)
        _ ≤ (roughPower N S.k + brunFixedBaseExponent S.k) *
              CoverBPZ.refinedEvenBrunDepth a b (z N S.k) + 3 := by omega
    have hexpN' : 2 * e N ≤ scalePower N S.k := by
      simpa [e] using hexpN
    have hsumExp : e N + N ≤ scalePower N S.k := by omega
    have hpowExp :
        (2 : ℝ) ^ e N * (2 : ℝ) ^ N ≤
          (2 : ℝ) ^ scalePower N S.k := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num) hsumExp
    have hfrac :
        (P N / (2 : ℝ) ^ scalePower N S.k) * (2 : ℝ) ^ e N ≤
          P N / (2 : ℝ) ^ N := by
      rw [show P N / (2 : ℝ) ^ scalePower N S.k * (2 : ℝ) ^ e N =
          (P N * (2 : ℝ) ^ e N) /
            (2 : ℝ) ^ scalePower N S.k by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hPnonneg : 0 ≤ P N := by dsimp [P]; positivity
      calc
        P N * (2 : ℝ) ^ e N * (2 : ℝ) ^ N =
            P N * ((2 : ℝ) ^ e N * (2 : ℝ) ^ N) := by ring
        _ ≤ P N * (2 : ℝ) ^ scalePower N S.k :=
          mul_le_mul_of_nonneg_left hpowExp hPnonneg
    exact hfirst.trans hfrac
  · exact hmajorant

theorem two_pow_scalePower_le_X {N k : ℕ} (hk : 0 < k) :
    2 ^ scalePower N k ≤ X N k := by
  rw [X_eq_pow_two]
  apply Nat.pow_le_pow_right (by omega)
  have hx : 1 ≤ BPZScale.xExp k := by
    have : 0 < BPZScale.xExp k := by
      unfold BPZScale.xExp
      positivity
    omega
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- The lower-sieve CRT remainder, after multiplying by the reciprocal Euler
envelope, is negligible relative to `X`. -/
theorem tendsto_lowerBrunError_eulerNormalized_zero
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) (a b : ℕ) :
    Tendsto (fun N : ℕ =>
      ((4 : ℝ) *
          (z N S.k ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) + 1 : ℕ) *
          (S.k : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) *
          (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k)) /
        X N S.k) atTop (𝓝 0) := by
  let e : ℕ → ℕ := fun N => brunEndpointExponent a b N S.k
  have hexp := eventually_two_mul_brunEndpointExponent_le_scalePower
    a b S.k (by have := S.hk3; omega)
  have hmajorant : Tendsto (fun N : ℕ => (1 : ℝ) / (2 : ℝ) ^ N)
      atTop (𝓝 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
  apply squeeze_zero' (g := fun N : ℕ => (1 : ℝ) / (2 : ℝ) ^ N)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    positivity
  · filter_upwards [hexp, eventually_ge_atTop (1 : ℕ)] with N hexpN hN
    have hNpos : 0 < N := by omega
    have hk : 0 < S.k := by have := S.hk3; omega
    let Lm := PrimeReciprocal.logarithmicBrunDepth a b (z N S.k)
    let Lp := CoverBPZ.refinedEvenBrunDepth a b (z N S.k)
    have hL : Lm ≤ Lp := by dsimp [Lm, Lp, CoverBPZ.refinedEvenBrunDepth]; omega
    have hzOne : 1 ≤ z N S.k := by have := two_le_z hNpos hk; omega
    have hkOne : 1 ≤ S.k := by omega
    have hzPow : z N S.k ^ Lm ≤ z N S.k ^ Lp :=
      Nat.pow_le_pow_right hzOne hL
    have hkPow : S.k ^ Lm ≤ S.k ^ Lp := Nat.pow_le_pow_right hkOne hL
    have hzSumR : ((z N S.k ^ Lm + 1 : ℕ) : ℝ) ≤
        ((z N S.k ^ Lp + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hzPow 1
    have hkPowR : (S.k : ℝ) ^ Lm ≤ (S.k : ℝ) ^ Lp := by
      exact_mod_cast hkPow
    have hsmallLarge :
        (4 : ℝ) * (z N S.k ^ Lm + 1 : ℕ) * (S.k : ℝ) ^ Lm *
            (2 : ℝ) ^ Lm ≤
          (4 : ℝ) * (z N S.k ^ Lp + 1 : ℕ) * (S.k : ℝ) ^ Lp *
            (2 : ℝ) ^ Lm := by
      calc
        (4 : ℝ) * (z N S.k ^ Lm + 1 : ℕ) * (S.k : ℝ) ^ Lm *
              (2 : ℝ) ^ Lm ≤
            (4 : ℝ) * (z N S.k ^ Lp + 1 : ℕ) * (S.k : ℝ) ^ Lm *
              (2 : ℝ) ^ Lm := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hzSumR (by norm_num))
              (by positivity)) (by positivity)
        _ ≤ (4 : ℝ) * (z N S.k ^ Lp + 1 : ℕ) * (S.k : ℝ) ^ Lp *
              (2 : ℝ) ^ Lm := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hkPowR (by positivity)) (by positivity)
    have hendpoint := upperBrunEndpoint_mul_eulerReciprocal_le_pow
      (a := a) (b := b) hNpos hk
    have hfactor :
        (4 : ℝ) * (z N S.k ^ Lm + 1 : ℕ) * (S.k : ℝ) ^ Lm *
            (2 : ℝ) ^ Lm ≤ (2 : ℝ) ^ e N := by
      exact hsmallLarge.trans (by simpa [Lm, Lp, e] using hendpoint)
    have hNe : N ≤ e N := by
      have hrough := self_le_roughPower hNpos hk
      have hLOne : 1 ≤ CoverBPZ.refinedEvenBrunDepth a b (z N S.k) := by
        unfold CoverBPZ.refinedEvenBrunDepth
        omega
      dsimp [e, brunEndpointExponent]
      calc
        N ≤ roughPower N S.k := hrough
        _ ≤ (roughPower N S.k + brunFixedBaseExponent S.k) *
              CoverBPZ.refinedEvenBrunDepth a b (z N S.k) := by
          exact le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ hLOne)
        _ ≤ (roughPower N S.k + brunFixedBaseExponent S.k) *
              CoverBPZ.refinedEvenBrunDepth a b (z N S.k) + 3 := by omega
    have hexpN' : 2 * e N ≤ scalePower N S.k := by simpa [e] using hexpN
    have hsum : e N + N ≤ scalePower N S.k := by omega
    have hpowScale :
        (2 : ℝ) ^ e N * (2 : ℝ) ^ N ≤
          (2 : ℝ) ^ scalePower N S.k := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num) hsum
    have hscaleX : (2 : ℝ) ^ scalePower N S.k ≤ X N S.k := by
      exact_mod_cast two_pow_scalePower_le_X (N := N) hk
    have hpowX :
        (2 : ℝ) ^ e N * (2 : ℝ) ^ N ≤ X N S.k :=
      hpowScale.trans hscaleX
    have hXpos : (0 : ℝ) < X N S.k := by exact_mod_cast X_pos N S.k
    have hdenPos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    rw [div_le_div_iff₀ hXpos hdenPos]
    calc
      ((4 : ℝ) * (z N S.k ^ Lm + 1 : ℕ) * (S.k : ℝ) ^ Lm *
          (2 : ℝ) ^ Lm) * (2 : ℝ) ^ N ≤
        (2 : ℝ) ^ e N * (2 : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ ≤ X N S.k := hpowX
      _ = 1 * (X N S.k : ℝ) := by ring
  · exact hmajorant

/-! Small sign lemmas used when the three asymptotic estimates are assembled.
Keeping their finite-sum unfolding out of that assembly avoids expensive
repeated normalization. -/

theorem roughReciprocalMass_nonneg (z T : ℕ) :
    0 ≤ roughReciprocalMass z T := by
  unfold roughReciprocalMass
  exact Finset.sum_nonneg fun m _ => by positivity

theorem localizedSwitchedReciprocalEnvelope_nonneg
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    {C : ℝ} (hC : 0 ≤ C) {X z large : ℕ}
    (hlog : 0 ≤ Real.log (z : ℝ)) :
    0 ≤ CoverBPZ.localizedSwitchedReciprocalEnvelope S C X z large := by
  unfold CoverBPZ.localizedSwitchedReciprocalEnvelope
  refine mul_nonneg (by positivity) ?_
  refine mul_nonneg (mul_nonneg ?_ (roughReciprocalMass_nonneg _ _))
    (pow_nonneg (roughReciprocalMass_nonneg _ _) _)
  exact div_nonneg (mul_nonneg (by positivity) hC) hlog

theorem switchedCertificateCountEnvelope_nonneg
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (X z large : ℕ) :
    0 ≤ CoverBPZ.switchedCertificateCountEnvelope S X z large := by
  unfold CoverBPZ.switchedCertificateCountEnvelope
  exact mul_nonneg (by positivity)
    (pow_nonneg (roughReciprocalMass_nonneg _ _) _)

theorem brunEndpointTerm_nonneg (z k L : ℕ) :
    0 ≤ (4 : ℝ) * (z ^ L + 1 : ℕ) * (k : ℝ) ^ L := by
  exact mul_nonneg (mul_nonneg (by norm_num) (by positivity))
    (pow_nonneg (by positivity) _)

theorem refinedEvenEndpoint_nonneg (a b z k : ℕ) :
    0 ≤ (4 : ℝ) *
      (z ^ CoverBPZ.refinedEvenBrunDepth a b z + 1 : ℕ) *
      (k : ℝ) ^ CoverBPZ.refinedEvenBrunDepth a b z :=
  brunEndpointTerm_nonneg z k _

end SubpowerScale

end Erdos387
