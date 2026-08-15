/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ComparablePrimeEstimate
import ErdosProblems.Erdos387.SubpowerLargeError

/-!
# The comparable-prime estimate on the subpower scale

This file specializes the abstract binary-shell estimate to the exact
power-of-two thresholds used in `SubpowerScale`.
-/

namespace Erdos387

open Filter
open scoped Topology

namespace SubpowerScale

def comparableLowerLog (N k : ℕ) : ℕ :=
  scalePower N k * BPZScale.secondExp k

def comparableGapLog (N k : ℕ) : ℕ :=
  scalePower N k * BPZScale.gapExp k

def comparableUpperLog (N k : ℕ) : ℕ :=
  scalePower N k * BPZScale.mediumExp k

theorem secondMin_eq_pow_two (N k : ℕ) :
    secondMin N k = 2 ^ comparableLowerLog N k := by
  simp [secondMin, BPZScale.secondMin, base, comparableLowerLog,
    scalePower, pow_mul]

theorem gap_eq_pow_two (N k : ℕ) :
    gap N k = 2 ^ comparableGapLog N k := by
  simp [gap, BPZScale.gap, base, comparableGapLog, scalePower, pow_mul]

theorem medium_eq_pow_two (N k : ℕ) :
    medium N k = 2 ^ comparableUpperLog N k := by
  simp [medium, BPZScale.medium, base, comparableUpperLog,
    scalePower, pow_mul]

theorem comparableLowerLog_pos {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    0 < comparableLowerLog N k := by
  unfold comparableLowerLog scalePower BPZScale.secondExp
  positivity

theorem comparableGap_small
    {N k : ℕ} (hN : 0 < N) (hk : 3 ≤ k) :
    2 * (comparableGapLog N k + 1) ≤ comparableLowerLog N k := by
  have hk96 : 1 ≤ k ^ 96 := one_le_pow₀ (by omega)
  have hkCube : 5 ≤ k ^ 3 := by
    calc
      5 ≤ 3 ^ 3 := by norm_num
      _ ≤ k ^ 3 := Nat.pow_le_pow_left hk 3
  have hkPowers : 4 * k ^ 96 + 1 ≤ k ^ 99 := by
    calc
      4 * k ^ 96 + 1 ≤ 5 * k ^ 96 := by nlinarith
      _ ≤ k ^ 3 * k ^ 96 := Nat.mul_le_mul_right (k ^ 96) hkCube
      _ = k ^ 99 := by
        rw [show 99 = 3 + 96 by norm_num, pow_add]
  let A := 3 ^ k
  let T := scalePower N k
  have hcoeff : 2 ≤ 300 * A := by
    dsimp [A]
    have : 0 < 300 * 3 ^ k := by positivity
    omega
  have hcore :
      2 * BPZScale.gapExp k + 2 ≤ BPZScale.secondExp k := by
    unfold BPZScale.gapExp BPZScale.secondExp
    dsimp [A] at hcoeff
    calc
      2 * (600 * 3 ^ k * k ^ 96) + 2 ≤
          300 * 3 ^ k * (4 * k ^ 96 + 1) := by nlinarith
      _ ≤ 300 * 3 ^ k * k ^ 99 := by gcongr
  have hT : 1 ≤ T := by
    dsimp [T, scalePower]
    have : 0 < N ^ (2 * k + 5) := pow_pos hN _
    omega
  unfold comparableGapLog comparableLowerLog
  dsimp [T] at hT
  calc
    2 * (scalePower N k * BPZScale.gapExp k + 1) ≤
        scalePower N k * (2 * BPZScale.gapExp k + 2) := by
      nlinarith
    _ ≤ scalePower N k * BPZScale.secondExp k := by gcongr

theorem comparableGap_ratio_le
    {N k : ℕ} (hN : 0 < N) (hk : 3 ≤ k) :
    ((comparableGapLog N k + 2 : ℕ) : ℝ) /
        comparableLowerLog N k ≤
      3 / ((k : ℝ) ^ 3) := by
  let A := 3 ^ k
  let T := scalePower N k
  have hT : 1 ≤ T := by
    dsimp [T, scalePower]
    have : 0 < N ^ (2 * k + 5) := pow_pos hN _
    omega
  have hA : 1 ≤ A := by
    dsimp [A]
    exact one_le_pow₀ (by norm_num)
  have hk96 : 1 ≤ k ^ 96 := one_le_pow₀ (by omega)
  have hk3 : 0 < k ^ 3 := pow_pos (by omega) _
  have hcoeff : 2 ≤ T * (300 * A * k ^ 96) := by
    have hsmall : 2 ≤ 300 * A * k ^ 96 := by
      have : 0 < A * k ^ 96 := Nat.mul_pos (by omega) (by positivity)
      nlinarith
    apply hsmall.trans
    calc
      300 * A * k ^ 96 = 1 * (300 * A * k ^ 96) := by ring
      _ ≤ T * (300 * A * k ^ 96) := Nat.mul_le_mul_right _ hT
  have hnat :
      (comparableGapLog N k + 2) * k ^ 3 ≤
        3 * comparableLowerLog N k := by
    unfold comparableGapLog comparableLowerLog BPZScale.gapExp
      BPZScale.secondExp
    dsimp [T, A] at hcoeff ⊢
    rw [show k ^ 99 = k ^ 96 * k ^ 3 by
      simpa using pow_add k 96 3]
    nlinarith
  have hRpos : (0 : ℝ) < comparableLowerLog N k := by
    exact_mod_cast comparableLowerLog_pos hN (by omega)
  have hkpos : (0 : ℝ) < (k : ℝ) ^ 3 := by positivity
  apply (div_le_div_iff₀ hRpos hkpos).2
  exact_mod_cast hnat

theorem comparablePrimePairReciprocalSum_le_inv_cube
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {N k : ℕ} (hN : 0 < N) (hk : 3 ≤ k) :
    CoverBPZ.comparablePrimePairReciprocalSum
        (secondMin N k) (gap N k) (medium N k) ≤
      12 * (2 * C / Real.log 2) ^ 2 / ((k : ℝ) ^ 3) := by
  have hshell := CoverBPZ.comparablePrimePairReciprocalSum_le_shellRatio
    hC hcheb
    (secondMin := secondMin N k) (gap := gap N k)
    (medium := medium N k) (R := comparableLowerLog N k)
    (G := comparableGapLog N k) (Q := comparableUpperLog N k)
    (show 1 ≤ comparableLowerLog N k by
      exact comparableLowerLog_pos hN (by omega))
    (comparableGap_small hN hk)
    (by rw [secondMin_eq_pow_two])
    (by rw [gap_eq_pow_two])
    (by rw [medium_eq_pow_two])
  calc
    CoverBPZ.comparablePrimePairReciprocalSum
        (secondMin N k) (gap N k) (medium N k) ≤
        4 * (2 * C / Real.log 2) ^ 2 *
          (comparableGapLog N k + 2 : ℕ) /
            comparableLowerLog N k := hshell
    _ ≤ 4 * (2 * C / Real.log 2) ^ 2 *
          (3 / ((k : ℝ) ^ 3)) := by
      have hcoef : 0 ≤ 4 * (2 * C / Real.log 2) ^ 2 := by positivity
      rw [show 4 * (2 * C / Real.log 2) ^ 2 *
          (comparableGapLog N k + 2 : ℕ) /
            comparableLowerLog N k =
          (4 * (2 * C / Real.log 2) ^ 2) *
            (((comparableGapLog N k + 2 : ℕ) : ℝ) /
              comparableLowerLog N k) by ring]
      exact mul_le_mul_of_nonneg_left (comparableGap_ratio_le hN hk) hcoef
    _ = 12 * (2 * C / Real.log 2) ^ 2 / ((k : ℝ) ^ 3) := by ring

def mediumResidualExp (k : ℕ) : ℕ :=
  196 * 3 ^ k * k ^ 100

theorem two_medium_add_residual (k : ℕ) :
    2 * BPZScale.mediumExp k + mediumResidualExp k =
      BPZScale.xExp k := by
  unfold BPZScale.mediumExp mediumResidualExp BPZScale.xExp
  ring

theorem mediumResidualExp_pos {k : ℕ} (hk : 0 < k) :
    0 < mediumResidualExp k := by
  unfold mediumResidualExp
  positivity

theorem X_eq_medium_sq_mul_residual (N k : ℕ) :
    X N k = medium N k ^ 2 * base N k ^ mediumResidualExp k := by
  unfold X medium BPZScale.X BPZScale.medium
  rw [← pow_mul, ← pow_add]
  congr 1
  rw [mul_comm, two_medium_add_residual]

theorem medium_sq_le_X_half {N k : ℕ} (hN : 0 < N) (hk : 3 ≤ k) :
    medium N k ^ 2 ≤ X N k / 2 := by
  have hbaseTwo : 2 ≤ base N k := by
    unfold base scalePower
    have hpowPos : 0 < N ^ (2 * k + 5) := pow_pos hN _
    exact Nat.one_lt_pow hpowPos.ne' (by norm_num)
  have hExp : 2 * BPZScale.mediumExp k + 1 ≤ BPZScale.xExp k := by
    have hpos : 1 ≤ 3 ^ k * k ^ 100 := by
      have : 0 < 3 ^ k * k ^ 100 := by positivity
      omega
    unfold BPZScale.mediumExp BPZScale.xExp
    nlinarith
  unfold medium X BPZScale.medium BPZScale.X
  rw [← pow_mul]
  simpa [mul_comm] using BPZScale.coeff_mul_pow_le_half
    (t := base N k) (B := 1) (e := 2 * BPZScale.mediumExp k)
      (by omega) (by simpa using hbaseTwo) hExp

theorem z_le_secondMin {N k : ℕ} (hN : 0 < N) (hk : 3 ≤ k)
    (hNk : 2 * k ≤ N ^ 2) :
    z N k ≤ secondMin N k := by
  rw [secondMin_eq_pow_two]
  unfold z
  apply Nat.pow_le_pow_right (by omega)
  unfold comparableLowerLog scalePower roughPower BPZScale.secondExp
    BPZScale.xExp
  have hpow : N ^ (2 * k + 5) = N ^ (2 * k + 3) * N ^ 2 := by
    simpa using pow_add N (2 * k + 3) 2
  rw [hpow]
  calc
    600 * 3 ^ k * k ^ 100 * N ^ (2 * k + 3) =
        (300 * 3 ^ k * k ^ 99 * N ^ (2 * k + 3)) * (2 * k) := by
      rw [show k ^ 100 = k ^ 99 * k by
        simpa using pow_succ k 99]
      ring
    _ ≤ (300 * 3 ^ k * k ^ 99 * N ^ (2 * k + 3)) * N ^ 2 :=
      Nat.mul_le_mul_left _ hNk
    _ = N ^ (2 * k + 3) * N ^ 2 * (300 * 3 ^ k * k ^ 99) := by ring

def comparableSourceCountEnvelope (N k : ℕ) : ℕ :=
  k ^ 2 * (medium N k + 1) ^ 2

theorem card_comparablePrimeSource_le_envelope (N k : ℕ) :
    Fintype.card (CoverBPZ.ComparablePrimeSource k
      (secondMin N k) (gap N k) (medium N k)) ≤
      comparableSourceCountEnvelope N k := by
  exact CoverBPZ.card_comparablePrimeSource_le _ _ _ _

theorem medium_add_one_sq_le {N k : ℕ} :
    (medium N k + 1) ^ 2 ≤ 4 * medium N k ^ 2 := by
  have hm : 1 ≤ medium N k := by
    unfold medium BPZScale.medium base scalePower
    exact one_le_pow₀ (by
      have : 0 < 2 ^ N ^ (2 * k + 5) := by positivity
      omega)
  nlinarith

theorem residual_ge_two_pow_scalePower
    {N k : ℕ} (hk : 0 < k) :
    2 ^ scalePower N k ≤ base N k ^ mediumResidualExp k := by
  unfold base
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by omega)
  exact Nat.le_mul_of_pos_right _ (mediumResidualExp_pos hk)

theorem tendsto_comparableSourceCountEnvelope_div_X_zero {k : ℕ}
    (hk : 3 ≤ k) :
    Tendsto (fun N : ℕ =>
      (comparableSourceCountEnvelope N k : ℝ) / X N k)
      atTop (𝓝 0) := by
  let D : ℝ := 4 * (k : ℝ) ^ 2
  have hmajor : Tendsto (fun N : ℕ => D * ((1 / 2 : ℝ) ^ N))
      atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)
    simpa using (tendsto_const_nhds.mul hp :
      Tendsto (fun N : ℕ => D * ((1 / 2 : ℝ) ^ N)) atTop (𝓝 (D * 0)))
  apply squeeze_zero' (g := fun N : ℕ => D * ((1 / 2 : ℝ) ^ N))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < N := by omega
    let G := base N k ^ mediumResidualExp k
    have hmNat : 0 < medium N k := by
      unfold medium BPZScale.medium base scalePower
      positivity
    have hmPosNat : 0 < medium N k ^ 2 := pow_pos hmNat _
    have hmPos : (0 : ℝ) < (medium N k : ℝ) ^ 2 := by exact_mod_cast hmPosNat
    have hGPosNat : 0 < G := by
      dsimp [G]
      apply pow_pos
      unfold base
      positivity
    have hGPos : (0 : ℝ) < G := by exact_mod_cast hGPosNat
    have hXeq : (X N k : ℝ) = (medium N k : ℝ) ^ 2 * G := by
      exact_mod_cast X_eq_medium_sq_mul_residual N k
    have hcount : (comparableSourceCountEnvelope N k : ℝ) ≤
        D * (medium N k : ℝ) ^ 2 := by
      dsimp [comparableSourceCountEnvelope, D]
      push_cast
      have hs : ((medium N k : ℝ) + 1) ^ 2 ≤
          4 * (medium N k : ℝ) ^ 2 := by
        exact_mod_cast medium_add_one_sq_le (N := N) (k := k)
      calc
        (k : ℝ) ^ 2 * ((medium N k : ℝ) + 1) ^ 2 ≤
            (k : ℝ) ^ 2 * (4 * (medium N k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 4 * (k : ℝ) ^ 2 * (medium N k : ℝ) ^ 2 := by ring
    have hscale : (2 : ℝ) ^ scalePower N k ≤ G := by
      exact_mod_cast residual_ge_two_pow_scalePower
        (N := N) (k := k) (by omega)
    have hNscale : N ≤ scalePower N k := by
      unfold scalePower
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ N)
        (by omega : 1 ≤ 2 * k + 5)
    have hpow : (2 : ℝ) ^ N ≤ G :=
      (pow_le_pow_right₀ (by norm_num) hNscale).trans hscale
    rw [show (1 / 2 : ℝ) ^ N = 1 / (2 : ℝ) ^ N by
      simp [one_div]]
    rw [hXeq]
    rw [show D * (1 / (2 : ℝ) ^ N) = D / (2 : ℝ) ^ N by ring]
    apply (div_le_div_iff₀ (mul_pos hmPos hGPos)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)).2
    calc
      (comparableSourceCountEnvelope N k : ℝ) * (2 : ℝ) ^ N ≤
          (D * (medium N k : ℝ) ^ 2) * (2 : ℝ) ^ N := by gcongr
      _ ≤ (D * (medium N k : ℝ) ^ 2) * G := by gcongr
      _ = D * ((medium N k : ℝ) ^ 2 * G) := by ring
  · exact hmajor

/-- After multiplication by the reciprocal Euler-product envelope, the
even-Brun endpoint attached to all comparable-prime certificate classes is
still negligible relative to `X`. -/
theorem tendsto_comparableSourceEndpoint_normalized_zero
    {k : ℕ} (hk : 3 ≤ k) (a b : ℕ) :
    Tendsto (fun N : ℕ =>
      ((comparableSourceCountEnvelope N k : ℝ) / X N k) *
        ((4 : ℝ) *
          (z N k ^ CoverBPZ.refinedEvenBrunDepth a b (z N k) + 1 : ℕ) *
          (k : ℝ) ^ CoverBPZ.refinedEvenBrunDepth a b (z N k) *
          (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k)))
      atTop (𝓝 0) := by
  let D : ℝ := 4 * (k : ℝ) ^ 2
  let e : ℕ → ℕ := fun N => brunEndpointExponent a b N k
  have hmajor : Tendsto (fun N : ℕ => D * ((1 / 2 : ℝ) ^ N))
      atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)
    simpa using (tendsto_const_nhds.mul hp :
      Tendsto (fun N : ℕ => D * ((1 / 2 : ℝ) ^ N)) atTop (𝓝 (D * 0)))
  have hexp := eventually_two_mul_brunEndpointExponent_le_scalePower
    a b k (by omega)
  apply squeeze_zero' (g := fun N : ℕ => D * ((1 / 2 : ℝ) ^ N))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    positivity
  · filter_upwards [hexp, eventually_ge_atTop (1 : ℕ)] with N hexpN hN
    have hNpos : 0 < N := by omega
    let G := base N k ^ mediumResidualExp k
    have hmNat : 0 < medium N k := by
      unfold medium BPZScale.medium base scalePower
      positivity
    have hmPosNat : 0 < medium N k ^ 2 := pow_pos hmNat _
    have hmPos : (0 : ℝ) < (medium N k : ℝ) ^ 2 := by
      exact_mod_cast hmPosNat
    have hGPosNat : 0 < G := by
      dsimp [G]
      apply pow_pos
      unfold base
      positivity
    have hGPos : (0 : ℝ) < G := by exact_mod_cast hGPosNat
    have hXeq : (X N k : ℝ) = (medium N k : ℝ) ^ 2 * G := by
      exact_mod_cast X_eq_medium_sq_mul_residual N k
    have hcount : (comparableSourceCountEnvelope N k : ℝ) ≤
        D * (medium N k : ℝ) ^ 2 := by
      dsimp [comparableSourceCountEnvelope, D]
      push_cast
      have hs : ((medium N k : ℝ) + 1) ^ 2 ≤
          4 * (medium N k : ℝ) ^ 2 := by
        exact_mod_cast medium_add_one_sq_le (N := N) (k := k)
      calc
        (k : ℝ) ^ 2 * ((medium N k : ℝ) + 1) ^ 2 ≤
            (k : ℝ) ^ 2 * (4 * (medium N k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 4 * (k : ℝ) ^ 2 * (medium N k : ℝ) ^ 2 := by ring
    have hratio : (comparableSourceCountEnvelope N k : ℝ) / X N k ≤
        D / G := by
      rw [hXeq]
      apply (div_le_div_iff₀ (mul_pos hmPos hGPos) hGPos).2
      calc
        (comparableSourceCountEnvelope N k : ℝ) * G ≤
            (D * (medium N k : ℝ) ^ 2) * G := by gcongr
        _ = D * ((medium N k : ℝ) ^ 2 * G) := by ring
    have hendpoint := upperBrunEndpoint_mul_eulerReciprocal_le_pow
      (a := a) (b := b) hNpos (by omega : 0 < k)
    have hNe : N ≤ e N := by
      have hrough := self_le_roughPower hNpos (by omega : 0 < k)
      have hLOne : 1 ≤ CoverBPZ.refinedEvenBrunDepth a b (z N k) := by
        unfold CoverBPZ.refinedEvenBrunDepth
        omega
      dsimp [e, brunEndpointExponent]
      calc
        N ≤ roughPower N k := hrough
        _ ≤ (roughPower N k + brunFixedBaseExponent k) *
              CoverBPZ.refinedEvenBrunDepth a b (z N k) := by
          exact le_trans (Nat.le_add_right _ _)
            (Nat.le_mul_of_pos_right _ hLOne)
        _ ≤ (roughPower N k + brunFixedBaseExponent k) *
              CoverBPZ.refinedEvenBrunDepth a b (z N k) + 3 := by omega
    have hsum : e N + N ≤ scalePower N k := by
      have hexpN' : 2 * e N ≤ scalePower N k := by simpa [e] using hexpN
      omega
    have hpowScale :
        (2 : ℝ) ^ e N * (2 : ℝ) ^ N ≤
          (2 : ℝ) ^ scalePower N k := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num) hsum
    have hscaleG : (2 : ℝ) ^ scalePower N k ≤ G := by
      exact_mod_cast residual_ge_two_pow_scalePower
        (N := N) (k := k) (by omega)
    have hpowG : (2 : ℝ) ^ e N * (2 : ℝ) ^ N ≤ G :=
      hpowScale.trans hscaleG
    have hfirst :
        ((comparableSourceCountEnvelope N k : ℝ) / X N k) *
            ((4 : ℝ) *
              (z N k ^ CoverBPZ.refinedEvenBrunDepth a b (z N k) + 1 : ℕ) *
              (k : ℝ) ^ CoverBPZ.refinedEvenBrunDepth a b (z N k) *
              (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k)) ≤
          (D / G) * (2 : ℝ) ^ e N := by
      exact mul_le_mul hratio (by simpa [e] using hendpoint)
        (by positivity) (by positivity)
    rw [show (1 / 2 : ℝ) ^ N = 1 / (2 : ℝ) ^ N by simp [one_div]]
    rw [show D * (1 / (2 : ℝ) ^ N) = D / (2 : ℝ) ^ N by ring]
    apply hfirst.trans
    rw [show D / G * (2 : ℝ) ^ e N =
        (D * (2 : ℝ) ^ e N) / G by ring]
    apply (div_le_div_iff₀ hGPos (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)).2
    calc
      D * (2 : ℝ) ^ e N * (2 : ℝ) ^ N =
          D * ((2 : ℝ) ^ e N * (2 : ℝ) ^ N) := by ring
      _ ≤ D * G := mul_le_mul_of_nonneg_left hpowG (by dsimp [D]; positivity)
  · exact hmajor

theorem comparable_normalization_identity
    (x k v c A E P : ℝ) (hx : x ≠ 0) (hk : k ≠ 0) :
    (x * (12 * A ^ 2 / k) + 2 * c) * (3 * v / 2) +
        c * E * (P * v) =
      (18 * A ^ 2 / k + (3 * (c / x) + (c / x) * E * P)) * (x * v) := by
  field_simp [hx, hk] <;> ring

theorem comparable_normalization_identity_with_modulus
    (x k m v c A E P : ℝ) (hx : x ≠ 0) (hk : k ≠ 0)
    (hm : m ≠ 0) :
    ((x / m) * (12 * A ^ 2 / k) + 2 * c) * (3 * v / 2) +
        c * E * (P * v) =
      (18 * A ^ 2 / (m * k) +
        (3 * (c / x) + (c / x) * E * P)) * (x * v) := by
  field_simp [hx, hk, hm] <;> ring

/-- The comparable-prime exceptional set has normalized upper density
`O(1/(M k))`, where `M` is the fixed refined progression modulus, uniformly
along the subpower scale. -/
theorem eventually_refinedComparablePrimeErrors_normalized_lt
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (Cπ : ℝ) (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((CoverBPZ.RefinedComparablePrimeErrors S (X N S.k) (z N S.k)
          (secondMin N S.k) (gap N S.k) (medium N S.k)).card : ℝ) /
          ((X N S.k : ℝ) *
            finiteEulerProduct
              (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
              (fun p => binomialSieveNu S.k p)) <
        18 * (2 * Cπ / Real.log 2) ^ 2 /
          ((CoverBPZ.refinementModulus S : ℝ) * S.k) + ε := by
  obtain ⟨a, b, hdepth⟩ :=
    CoverBPZ.exists_refined_tail_and_euler_reciprocal_depth hCπ hcheb S
  let V : ℕ → ℝ := fun N =>
    finiteEulerProduct
      (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
      (fun p => binomialSieveNu S.k p)
  let Csrc : ℕ → ℝ := fun N => comparableSourceCountEnvelope N S.k
  let Eeven : ℕ → ℝ := fun N =>
    (4 : ℝ) *
      (z N S.k ^ CoverBPZ.refinedEvenBrunDepth a b (z N S.k) + 1 : ℕ) *
      (S.k : ℝ) ^ CoverBPZ.refinedEvenBrunDepth a b (z N S.k)
  let A : ℝ := 2 * Cπ / Real.log 2
  let Q : ℕ → ℝ := fun N =>
    3 * (Csrc N / X N S.k) +
      (Csrc N / X N S.k) * Eeven N *
        (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k)
  have hC0 : Tendsto (fun N => Csrc N / X N S.k) atTop (𝓝 0) := by
    simpa [Csrc] using
      tendsto_comparableSourceCountEnvelope_div_X_zero S.hk3
  have hendpoint0 : Tendsto (fun N =>
      (Csrc N / X N S.k) * Eeven N *
        (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k))
      atTop (𝓝 0) := by
    simpa [Csrc, Eeven, mul_assoc] using
      tendsto_comparableSourceEndpoint_normalized_zero S.hk3 a b
  have hQ0 : Tendsto Q atTop (𝓝 0) := by
    dsimp [Q]
    convert (tendsto_const_nhds.mul hC0).add hendpoint0 using 1 <;>
      norm_num
  have hQsmall : ∀ᶠ N : ℕ in atTop, Q N < ε :=
    (tendsto_order.1 hQ0).2 ε hε
  have hzEv : ∀ᶠ N : ℕ in atTop, 2 * S.k ≤ z N S.k :=
    eventually_const_le_z (k := S.k) (by have := S.hk3; omega) (2 * S.k)
  have hXEv : ∀ᶠ N : ℕ in atTop, 2 * S.k ≤ X N S.k :=
    eventually_const_le_X (k := S.k) (by have := S.hk3; omega) (2 * S.k)
  filter_upwards [hQsmall, hzEv, hXEv,
      eventually_ge_atTop (2 * S.k + 1)] with N hQsmallN hz2k hX2k hN
  have hNpos : 0 < N := by omega
  have hk : 0 < S.k := by have := S.hk3; omega
  have hNk : 2 * S.k ≤ N ^ 2 := by nlinarith
  have hzSecond : z N S.k ≤ secondMin N S.k :=
    z_le_secondMin hNpos S.hk3 hNk
  have hsecond : 2 * S.k ≤ secondMin N S.k := hz2k.trans hzSecond
  have hmediumHalf : medium N S.k ^ 2 ≤ X N S.k / 2 :=
    medium_sq_le_X_half hNpos S.hk3
  have hXhalf : S.k ≤ X N S.k / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    simpa [mul_comm] using hX2k
  have hzOne : 1 ≤ z N S.k := by
    have := two_le_z hNpos hk
    omega
  have htailEven := (hdepth (z N S.k)).2.1
  have hwindow := boundingSieve_brunMainSums_half_threeHalves
    (refinedBinomialBoundingSieve S (X N S.k) (z N S.k))
    (CoverBPZ.refinedEvenBrunDepth a b (z N S.k)) htailEven
  have hVpos : 0 < V N := by
    have hv := boundingSieve_finiteEulerProduct_pos
      (refinedBinomialBoundingSieve S (X N S.k) (z N S.k))
    simpa [V, refinedBinomialBoundingSieve] using hv
  have hmainNonneg : 0 ≤
      (refinedBinomialBoundingSieve S (X N S.k) (z N S.k)).mainSum
        (brunUpperWeight
          (CoverBPZ.refinedEvenBrunDepth a b (z N S.k))) := by
    change 0 ≤
      (refinedBinomialBoundingSieve S (X N S.k) (z N S.k)).mainSum
        (brunLowerWeight
          (CoverBPZ.refinedEvenBrunDepth a b (z N S.k)))
    have hlower := hwindow.1
    change V N / 2 ≤ _ at hlower
    linarith [hlower, hVpos]
  have hmainUpper :
      (refinedBinomialBoundingSieve S (X N S.k) (z N S.k)).mainSum
          (brunUpperWeight
            (CoverBPZ.refinedEvenBrunDepth a b (z N S.k))) ≤
        3 * V N / 2 := by
    simpa [V, refinedBinomialBoundingSieve] using hwindow.2
  let Src := CoverBPZ.ComparablePrimeSource S.k
    (secondMin N S.k) (gap N S.k) (medium N S.k)
  have hsrcCard : (Fintype.card Src : ℝ) ≤ Csrc N := by
    change (Fintype.card (CoverBPZ.ComparablePrimeSource S.k
      (secondMin N S.k) (gap N S.k) (medium N S.k)) : ℝ) ≤
        (comparableSourceCountEnvelope N S.k : ℝ)
    have hc := card_comparablePrimeSource_le_envelope N S.k
    exact_mod_cast hc
  have hpair :
      (∑ s : Src, (1 : ℝ) / (s.q.val * s.r.val : ℕ)) ≤
        12 * A ^ 2 / (S.k : ℝ) := by
    calc
      (∑ s : Src, (1 : ℝ) / (s.q.val * s.r.val : ℕ)) ≤
          (S.k : ℝ) ^ 2 *
            CoverBPZ.comparablePrimePairReciprocalSum
              (secondMin N S.k) (gap N S.k) (medium N S.k) :=
        CoverBPZ.sum_comparablePrimeSource_reciprocal_le
      _ ≤ (S.k : ℝ) ^ 2 *
            (12 * A ^ 2 / (S.k : ℝ) ^ 3) := by
        gcongr
        simpa [A] using
          comparablePrimePairReciprocalSum_le_inv_cube hCπ hcheb hNpos S.hk3
      _ = 12 * A ^ 2 / (S.k : ℝ) := by
        field_simp
  have hEulerRecip := (hdepth (z N S.k)).2.2
  change 1 ≤ (2 : ℝ) ^
    PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) * V N at hEulerRecip
  have hfinite :=
    CoverBPZ.refinedComparablePrimeErrors_card_le_brun_envelope_with_modulus
    (X := X N S.k) (z := z N S.k) (secondMin := secondMin N S.k)
    (gap := gap N S.k) (medium := medium N S.k) S
      hsecond (by simpa [pow_two] using hmediumHalf) hzSecond hXhalf hk hzOne
      (CoverBPZ.refinedEvenBrunDepth_even a b _) hmainNonneg
  have hXrealPos : (0 : ℝ) < X N S.k := by exact_mod_cast X_pos N S.k
  have hkRealNe : (S.k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hMRealNe : (CoverBPZ.refinementModulus S : ℝ) ≠ 0 := by
    exact_mod_cast (CoverBPZ.refinementModulus_pos S).ne'
  have hMRealPos : (0 : ℝ) < CoverBPZ.refinementModulus S := by
    exact_mod_cast CoverBPZ.refinementModulus_pos S
  have hdenPos : 0 < (X N S.k : ℝ) * V N := mul_pos hXrealPos hVpos
  rw [div_lt_iff₀ hdenPos]
  have hmainFactorNonneg : 0 ≤ 3 * V N / 2 := by positivity
  have hsumNonneg : 0 ≤
      ∑ s : Src, (1 : ℝ) / (s.q.val * s.r.val : ℕ) := by positivity
  have hcoefNonneg : 0 ≤
      ((X N S.k : ℝ) / CoverBPZ.refinementModulus S) *
          (∑ s : Src, (1 : ℝ) / (s.q.val * s.r.val : ℕ)) +
        2 * Fintype.card Src := by
    exact add_nonneg
      (mul_nonneg (div_nonneg hXrealPos.le hMRealPos.le) hsumNonneg)
      (by positivity)
  have hEevenNonneg : 0 ≤ Eeven N := by
    exact refinedEvenEndpoint_nonneg a b (z N S.k) S.k
  have hCsrcNonneg : 0 ≤ Csrc N := by
    dsimp only [Csrc]
    positivity
  calc
    ((CoverBPZ.RefinedComparablePrimeErrors S (X N S.k) (z N S.k)
        (secondMin N S.k) (gap N S.k) (medium N S.k)).card : ℝ) ≤
        ((((X N S.k : ℝ) / CoverBPZ.refinementModulus S) *
              (∑ s : Src, (1 : ℝ) / (s.q.val * s.r.val : ℕ)) +
            2 * Fintype.card Src) *
          (refinedBinomialBoundingSieve S (X N S.k) (z N S.k)).mainSum
            (brunUpperWeight
              (CoverBPZ.refinedEvenBrunDepth a b (z N S.k))) +
          Fintype.card Src * Eeven N) := by
      simpa [Src, Eeven] using hfinite
    _ ≤ ((((X N S.k : ℝ) / CoverBPZ.refinementModulus S) *
              (∑ s : Src, (1 : ℝ) / (s.q.val * s.r.val : ℕ)) +
            2 * Fintype.card Src) * (3 * V N / 2) +
          Fintype.card Src * Eeven N) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmainUpper hcoefNonneg) le_rfl
    _ ≤ ((((X N S.k : ℝ) / CoverBPZ.refinementModulus S) *
              (12 * A ^ 2 / (S.k : ℝ)) +
              2 * Csrc N) * (3 * V N / 2) +
          Csrc N * Eeven N) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ hmainFactorNonneg
        exact add_le_add
          (mul_le_mul_of_nonneg_left hpair
            (div_nonneg hXrealPos.le hMRealPos.le))
          (mul_le_mul_of_nonneg_left hsrcCard (by norm_num))
      · exact mul_le_mul_of_nonneg_right hsrcCard hEevenNonneg
    _ ≤ ((((X N S.k : ℝ) / CoverBPZ.refinementModulus S) *
              (12 * A ^ 2 / (S.k : ℝ)) +
              2 * Csrc N) * (3 * V N / 2) +
          Csrc N * Eeven N *
            ((2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) *
              V N)) := by
      apply add_le_add le_rfl
      calc
          Csrc N * Eeven N = Csrc N * Eeven N * 1 := by ring
          _ ≤ Csrc N * Eeven N *
              ((2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) *
                V N) := by
            exact mul_le_mul_of_nonneg_left hEulerRecip
              (mul_nonneg hCsrcNonneg hEevenNonneg)
    _ = (18 * A ^ 2 /
          ((CoverBPZ.refinementModulus S : ℝ) * S.k) + Q N) *
          ((X N S.k : ℝ) * V N) := by
      simpa only [Q] using comparable_normalization_identity_with_modulus
        (X N S.k : ℝ) (S.k : ℝ)
          (CoverBPZ.refinementModulus S : ℝ)
          (V N) (Csrc N) A (Eeven N)
          ((2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k))
          hXrealPos.ne' hkRealNe hMRealNe
    _ < (18 * A ^ 2 /
          ((CoverBPZ.refinementModulus S : ℝ) * S.k) + ε) *
          ((X N S.k : ℝ) * V N) := by
      apply mul_lt_mul_of_pos_right _ hdenPos
      linarith
    _ = (18 * (2 * Cπ / Real.log 2) ^ 2 /
          ((CoverBPZ.refinementModulus S : ℝ) * S.k) + ε) *
          ((X N S.k : ℝ) *
            finiteEulerProduct
              (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
              (fun p => binomialSieveNu S.k p)) := by
      rfl

/-- Once the fixed `k` makes the explicit comparable-prime main constant
smaller than half of its allotted budget, the whole exceptional set is
eventually smaller than `X * V / (32 * M)`.  This is the form consumed by
the final five-error union bound. -/
theorem eventually_refinedComparablePrimeErrors_card_lt_scale
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (Cπ : ℝ) (hCπ : 0 < Cπ)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t)
    (hconstant :
      18 * (2 * Cπ / Real.log 2) ^ 2 /
          ((CoverBPZ.refinementModulus S : ℝ) * S.k) <
        1 / (64 * CoverBPZ.refinementModulus S : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      ((CoverBPZ.RefinedComparablePrimeErrors S (X N S.k) (z N S.k)
          (secondMin N S.k) (gap N S.k) (medium N S.k)).card : ℝ) <
        ((X N S.k : ℝ) *
          finiteEulerProduct
            (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
            (fun p => binomialSieveNu S.k p)) /
          (32 * CoverBPZ.refinementModulus S : ℝ) := by
  let V : ℕ → ℝ := fun N =>
    finiteEulerProduct
      (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
      (fun p => binomialSieveNu S.k p)
  have hMpos : (0 : ℝ) < CoverBPZ.refinementModulus S := by
    exact_mod_cast CoverBPZ.refinementModulus_pos S
  have hnormalized :=
    eventually_refinedComparablePrimeErrors_normalized_lt S Cπ hCπ hcheb
      (1 / (64 * CoverBPZ.refinementModulus S : ℝ)) (by positivity)
  filter_upwards [hnormalized] with N hN
  have hVpos : 0 < V N := by
    have hv := boundingSieve_finiteEulerProduct_pos
      (refinedBinomialBoundingSieve S (X N S.k) (z N S.k))
    simpa [V, refinedBinomialBoundingSieve] using hv
  have hXpos : (0 : ℝ) < X N S.k := by
    exact_mod_cast X_pos N S.k
  have hscalePos : 0 < (X N S.k : ℝ) * V N := mul_pos hXpos hVpos
  have hbudget :
      18 * (2 * Cπ / Real.log 2) ^ 2 /
            ((CoverBPZ.refinementModulus S : ℝ) * S.k) +
          1 / (64 * CoverBPZ.refinementModulus S : ℝ) <
        1 / (32 * CoverBPZ.refinementModulus S : ℝ) := by
    calc
      18 * (2 * Cπ / Real.log 2) ^ 2 /
            ((CoverBPZ.refinementModulus S : ℝ) * S.k) +
          1 / (64 * CoverBPZ.refinementModulus S : ℝ) <
          1 / (64 * CoverBPZ.refinementModulus S : ℝ) +
            1 / (64 * CoverBPZ.refinementModulus S : ℝ) :=
        by simpa [add_comm] using
          add_lt_add_left hconstant
            (1 / (64 * CoverBPZ.refinementModulus S : ℝ))
      _ = 1 / (32 * CoverBPZ.refinementModulus S : ℝ) := by ring
  rw [div_lt_iff₀ hscalePos] at hN
  calc
    ((CoverBPZ.RefinedComparablePrimeErrors S (X N S.k) (z N S.k)
        (secondMin N S.k) (gap N S.k) (medium N S.k)).card : ℝ) <
        (18 * (2 * Cπ / Real.log 2) ^ 2 /
            ((CoverBPZ.refinementModulus S : ℝ) * S.k) +
          1 / (64 * CoverBPZ.refinementModulus S : ℝ)) *
            ((X N S.k : ℝ) * V N) := hN
    _ < (1 / (32 * CoverBPZ.refinementModulus S : ℝ)) *
            ((X N S.k : ℝ) * V N) :=
      mul_lt_mul_of_pos_right hbudget hscalePos
    _ = ((X N S.k : ℝ) * V N) /
          (32 * CoverBPZ.refinementModulus S : ℝ) := by ring

/-- A modulus-free numerical condition on `k` implies the explicit
comparable-prime budget hypothesis.  The factor `M` cancels because it occurs
in both the exceptional-set main term and the sifted density. -/
theorem comparable_constant_lt_budget_of_k
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (Cπ : ℝ)
    (hk : 1152 * (2 * Cπ / Real.log 2) ^ 2 < (S.k : ℝ)) :
    18 * (2 * Cπ / Real.log 2) ^ 2 /
          ((CoverBPZ.refinementModulus S : ℝ) * S.k) <
        1 / (64 * CoverBPZ.refinementModulus S : ℝ) := by
  have hM : (0 : ℝ) < CoverBPZ.refinementModulus S := by
    exact_mod_cast CoverBPZ.refinementModulus_pos S
  have hkpos : (0 : ℝ) < S.k := by
    exact_mod_cast (by have := S.hk3; omega : 0 < S.k)
  apply (div_lt_div_iff₀ (mul_pos hM hkpos) (mul_pos (by norm_num) hM)).2
  calc
    18 * (2 * Cπ / Real.log 2) ^ 2 *
          (64 * CoverBPZ.refinementModulus S) =
        (1152 * (2 * Cπ / Real.log 2) ^ 2) *
          CoverBPZ.refinementModulus S := by ring
    _ < (S.k : ℝ) * CoverBPZ.refinementModulus S :=
      mul_lt_mul_of_pos_right hk hM
    _ = 1 * ((CoverBPZ.refinementModulus S : ℝ) * S.k) := by ring

end SubpowerScale

end Erdos387
