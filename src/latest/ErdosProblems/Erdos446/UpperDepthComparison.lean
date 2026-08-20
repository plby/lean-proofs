/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.PrimeBlocks
import ErdosProblems.Erdos446.ScaleAsymptotics

/-!
# Erdős Problem 446: comparison of the upper and lower block depths

The upper argument cuts the doubly-exponential prime blocks at `2 * y`.
This file gives that cutoff an exact integer definition and compares it to
the depth selected in the lower construction.  Since

`fordConstructionScale M K = blockEndpoint (M + K + 7)`,

the two depths differ by one of two fixed shifts.  Thus no unrecorded
`O(1)` error is lost when the upper block sum is expressed using
`fordCombinatorialWeight`.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

/-- The last doubly-exponential prime-block endpoint not exceeding `2*y`.
This is the exact integer version of
`floor (log (log (2*y)) / log 2)`. -/
def upperPrimeBlockDepth (y : ℕ) : ℕ :=
  Nat.log 2 (Nat.log 2 (2 * y))

/-- The unnormalized real floor which usually appears in statements of the
upper argument. -/
noncomputable def upperLogLogDepth (y : ℕ) : ℕ :=
  ⌊Real.log (Real.log (2 * y : ℝ)) / Real.log 2⌋₊

theorem fordConstructionScale_eq_blockEndpoint (M K : ℕ) :
    fordConstructionScale M K = blockEndpoint (M + K + 7) := by
  simp only [fordConstructionScale, blockEndpoint]
  congr 1
  rw [pow_add]
  ring

/-- The endpoint indexed by `upperPrimeBlockDepth` really lies below the
upper cutoff. -/
theorem blockEndpoint_upperPrimeBlockDepth_le {y : ℕ} (hy : 2 ≤ y) :
    blockEndpoint (upperPrimeBlockDepth y) ≤ 2 * y := by
  have hN : 2 * y ≠ 0 := by omega
  have hlog : Nat.log 2 (2 * y) ≠ 0 := by
    exact (Nat.log_pos (by omega) (by omega)).ne'
  dsimp [upperPrimeBlockDepth, blockEndpoint]
  exact (Nat.pow_le_pow_right (by omega)
    (Nat.pow_log_le_self 2 hlog)).trans
      (Nat.pow_log_le_self 2 hN)

/-- The next block endpoint is strictly beyond the upper cutoff. -/
theorem lt_blockEndpoint_upperPrimeBlockDepth_succ {y : ℕ} (hy : 2 ≤ y) :
    2 * y < blockEndpoint (upperPrimeBlockDepth y + 1) := by
  let N := 2 * y
  let L := Nat.log 2 N
  let J := Nat.log 2 L
  have hN : N ≠ 0 := by dsimp [N]; omega
  have hL : L ≠ 0 := by
    dsimp [L, N]
    exact (Nat.log_pos (by omega) (by omega)).ne'
  have hNL : N < 2 ^ (L + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) N
  have hLJ : L < 2 ^ (J + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) L
  have hpow : 2 ^ (L + 1) ≤ 2 ^ (2 ^ (J + 1)) := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  exact hNL.trans_le (by
    simpa [blockEndpoint, upperPrimeBlockDepth, N, L, J] using hpow)

/-- Exact cutoff characterization, suitable for rewriting the terminal block
in the upper block partition. -/
theorem blockEndpoint_le_two_mul_iff_le_upperPrimeBlockDepth
    {y j : ℕ} (hy : 2 ≤ y) :
    blockEndpoint j ≤ 2 * y ↔ j ≤ upperPrimeBlockDepth y := by
  constructor
  · intro hj
    by_contra hnot
    have hsucc : upperPrimeBlockDepth y + 1 ≤ j := by omega
    have := blockEndpoint_mono hsucc
    have hlt := lt_blockEndpoint_upperPrimeBlockDepth_succ hy
    omega
  · intro hj
    exact (blockEndpoint_mono hj).trans
      (blockEndpoint_upperPrimeBlockDepth_le hy)

/-- Real-logarithmic form of the exact upper cutoff.  The subtractive
constant is the normalization forced by
`blockEndpoint j = 2^(2^j)`; dropping it gives the customary
`floor(log log (2y) / log 2) + O(1)` notation. -/
theorem upperPrimeBlockDepth_eq_floor_log_log {y : ℕ} (hy : 2 ≤ y) :
    upperPrimeBlockDepth y =
      ⌊(Real.log (Real.log (2 * y : ℝ)) - Real.log (Real.log 2)) /
          Real.log 2⌋₊ := by
  let J := upperPrimeBlockDepth y
  have hNnat : 1 < 2 * y := by omega
  have hNR : (1 : ℝ) < 2 * y := by exact_mod_cast hNnat
  have hlogN : 0 < Real.log (2 * y : ℝ) := Real.log_pos hNR
  have hendpointJPos : (0 : ℝ) < blockEndpoint J := by
    exact_mod_cast blockEndpoint_pos J
  have hendpointSuccPos : (0 : ℝ) < blockEndpoint (J + 1) := by
    exact_mod_cast blockEndpoint_pos (J + 1)
  have hlowNat := blockEndpoint_upperPrimeBlockDepth_le hy
  have huppNat := lt_blockEndpoint_upperPrimeBlockDepth_succ hy
  have hlowLog : Real.log (blockEndpoint J : ℝ) ≤
      Real.log (2 * y : ℝ) :=
    Real.log_le_log hendpointJPos (by exact_mod_cast hlowNat)
  have huppLog : Real.log (2 * y : ℝ) <
      Real.log (blockEndpoint (J + 1) : ℝ) :=
    Real.strictMonoOn_log (zero_lt_one.trans hNR) hendpointSuccPos
      (by exact_mod_cast huppNat)
  have hlogEndpointJ : 0 < Real.log (blockEndpoint J : ℝ) := by
    rw [log_blockEndpoint]
    positivity
  have hlogEndpointSucc : 0 <
      Real.log (blockEndpoint (J + 1) : ℝ) := by
    rw [log_blockEndpoint]
    positivity
  have hlowLogLog : Real.log (Real.log (blockEndpoint J : ℝ)) ≤
      Real.log (Real.log (2 * y : ℝ)) :=
    Real.log_le_log hlogEndpointJ hlowLog
  have huppLogLog : Real.log (Real.log (2 * y : ℝ)) <
      Real.log (Real.log (blockEndpoint (J + 1) : ℝ)) :=
    Real.strictMonoOn_log hlogN hlogEndpointSucc huppLog
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hleft : (J : ℝ) ≤
      (Real.log (Real.log (2 * y : ℝ)) - Real.log (Real.log 2)) /
        Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    rw [log_log_blockEndpoint] at hlowLogLog
    linarith
  have hright :
      (Real.log (Real.log (2 * y : ℝ)) - Real.log (Real.log 2)) /
          Real.log 2 < (J : ℝ) + 1 := by
    rw [div_lt_iff₀ hlog2]
    rw [log_log_blockEndpoint] at huppLogLog
    push_cast at huppLogLog
    linarith
  have hnonneg : 0 ≤
      (Real.log (Real.log (2 * y : ℝ)) - Real.log (Real.log 2)) /
        Real.log 2 := (Nat.cast_nonneg J).trans hleft
  symm
  exact (Nat.floor_eq_iff hnonneg).2 ⟨hleft, hright⟩

/-- The customary unnormalized floor differs from the actual terminal block
index by at most one. -/
theorem upperLogLogDepth_bounds_upperPrimeBlockDepth
    {y : ℕ} (hy : 2 ≤ y) :
    upperLogLogDepth y ≤ upperPrimeBlockDepth y ∧
      upperPrimeBlockDepth y ≤ upperLogLogDepth y + 1 := by
  let Q : ℝ := Real.log (Real.log (2 * y : ℝ)) / Real.log 2
  let c : ℝ := -Real.log (Real.log 2) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2lt : Real.log 2 < 1 := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos (neg_pos.mpr (Real.log_neg hlog2 hlog2lt)) hlog2
  have hhalf : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlogCompare : -Real.log 2 < Real.log (Real.log 2) := by
    rw [← hloghalf]
    exact Real.strictMonoOn_log (by norm_num) hlog2 hhalf
  have hclt : c < 1 := by
    dsimp [c]
    rw [div_lt_iff₀ hlog2]
    linarith
  have hN4 : (4 : ℕ) ≤ 2 * y := by omega
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogN : 1 ≤ Real.log (2 * y : ℝ) := by
    have hmono : Real.log (4 : ℝ) ≤ Real.log (2 * y : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN4)
    rw [hlog4] at hmono
    nlinarith [Real.log_two_gt_d9]
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    exact div_nonneg (Real.log_nonneg hlogN) hlog2.le
  have hQc :
      (Real.log (Real.log (2 * y : ℝ)) - Real.log (Real.log 2)) /
          Real.log 2 = Q + c := by
    dsimp [Q, c]
    ring
  have hfloorEq : upperPrimeBlockDepth y = ⌊Q + c⌋₊ := by
    rw [upperPrimeBlockDepth_eq_floor_log_log hy, hQc]
  have hQle : Q ≤ Q + c := by linarith
  have hfloorLe : ⌊Q⌋₊ ≤ ⌊Q + c⌋₊ := Nat.floor_mono hQle
  have hQcNonneg : 0 ≤ Q + c := hQnonneg.trans (by linarith)
  have hQcLt : Q + c < (⌊Q⌋₊ : ℝ) + 2 := by
    have hQlt := Nat.lt_floor_add_one Q
    linarith
  have hfloorLt : ⌊Q + c⌋₊ < ⌊Q⌋₊ + 2 := by
    rw [Nat.floor_lt hQcNonneg]
    exact_mod_cast hQcLt
  dsimp [upperLogLogDepth]
  change ⌊Q⌋₊ ≤ upperPrimeBlockDepth y ∧
    upperPrimeBlockDepth y ≤ ⌊Q⌋₊ + 1
  rw [hfloorEq]
  omega

/-- The lower-construction depth and the actual upper prime-block cutoff
differ by the explicit fixed shift `M+7`, with at most one further block. -/
theorem upperPrimeBlockDepth_bounds_fordScaleDepth
    {M y : ℕ} (hy : fordConstructionScale M 1 ≤ y) :
    M + fordScaleDepth M y + 7 ≤ upperPrimeBlockDepth y ∧
      upperPrimeBlockDepth y ≤ M + fordScaleDepth M y + 8 := by
  have hy2 : 2 ≤ y := by
    have := (depth_lt_fordConstructionScale M 1).trans_le hy
    omega
  let K := fordScaleDepth M y
  have hinterval := fordScaleDepth_interval hy
  have hlowEndpoint : blockEndpoint (M + K + 7) ≤ 2 * y := by
    rw [← fordConstructionScale_eq_blockEndpoint M K]
    exact hinterval.1.trans (by omega)
  have hlow :=
    (blockEndpoint_le_two_mul_iff_le_upperPrimeBlockDepth hy2).mp hlowEndpoint
  have hnext : y < blockEndpoint (M + K + 8) := by
    calc
      y < fordConstructionScale M (K + 1) := by
        simpa [K] using fordScaleDepth_lt_next_scale hy
      _ = blockEndpoint (M + (K + 1) + 7) :=
        fordConstructionScale_eq_blockEndpoint M (K + 1)
      _ = blockEndpoint (M + K + 8) := by congr 1
  have hendpointPos : 2 ≤ blockEndpoint (M + K + 8) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 ^ (M + K + 8)) :=
        Nat.pow_le_pow_right (by omega) (Nat.one_le_pow _ _ (by omega))
      _ = blockEndpoint (M + K + 8) := by rfl
  have htwoy : 2 * y < blockEndpoint (M + K + 9) := by
    have hmul : 2 * y < 2 * blockEndpoint (M + K + 8) := by omega
    have hsq : 2 * blockEndpoint (M + K + 8) ≤
        blockEndpoint (M + K + 8) ^ 2 := by
      nlinarith
    have hsucc : blockEndpoint (M + K + 9) =
        blockEndpoint (M + K + 8) ^ 2 := by
      unfold blockEndpoint
      rw [show M + K + 9 = (M + K + 8) + 1 by omega,
        pow_succ, pow_mul]
    rw [hsucc]
    exact hmul.trans_le hsq
  have hupp : upperPrimeBlockDepth y < M + K + 9 := by
    by_contra hnot
    have hge : M + K + 9 ≤ upperPrimeBlockDepth y := by omega
    have hep := (blockEndpoint_mono hge).trans
      (blockEndpoint_upperPrimeBlockDepth_le hy2)
    omega
  exact ⟨by simpa [K] using hlow, by simpa [K] using (show
    upperPrimeBlockDepth y ≤ M + K + 8 by omega)⟩

theorem upperPrimeBlockDepth_eq_shift_or_succ
    {M y : ℕ} (hy : fordConstructionScale M 1 ≤ y) :
    upperPrimeBlockDepth y = M + fordScaleDepth M y + 7 ∨
      upperPrimeBlockDepth y = M + fordScaleDepth M y + 8 := by
  have h := upperPrimeBlockDepth_bounds_fordScaleDepth hy
  omega

/-- Number of consecutive prime blocks retained after the fixed initial
index `M`, including the possibly partial terminal block.  This is the `K`
parameter to use in `blockPool M K` and in the upper block partition. -/
def upperPrimeBlockCount (M y : ℕ) : ℕ :=
  upperPrimeBlockDepth y + 1 - M

theorem add_upperPrimeBlockCount {M y : ℕ}
    (hy : fordConstructionScale M 1 ≤ y) :
    M + upperPrimeBlockCount M y = upperPrimeBlockDepth y + 1 := by
  have h := (upperPrimeBlockDepth_bounds_fordScaleDepth hy).1
  dsimp [upperPrimeBlockCount]
  omega

/-- In the relative coordinates used by `blockPool M K`, the upper block
count is exactly the lower selected depth plus eight or nine. -/
theorem upperPrimeBlockCount_eq_shift_or_succ {M y : ℕ}
    (hy : fordConstructionScale M 1 ≤ y) :
    upperPrimeBlockCount M y = fordScaleDepth M y + 8 ∨
      upperPrimeBlockCount M y = fordScaleDepth M y + 9 := by
  rcases upperPrimeBlockDepth_eq_shift_or_succ hy with h | h
  · left
    dsimp [upperPrimeBlockCount]
    omega
  · right
    dsimp [upperPrimeBlockCount]
    omega

theorem upperPrimeBlockCount_terminal_endpoint {M y : ℕ}
    (hy : fordConstructionScale M 1 ≤ y) :
    blockEndpoint (M + upperPrimeBlockCount M y) =
      blockEndpoint (upperPrimeBlockDepth y + 1) := by
  rw [add_upperPrimeBlockCount hy]

theorem fordCombinatorialWeight_succ_eq {K : ℕ} (hK : 0 < K) :
    fordCombinatorialWeight (K + 1) =
      (2 * Real.log 2) *
        (1 + ((K : ℝ)⁻¹)) ^ (K - 1) *
          fordCombinatorialWeight K := by
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hK1R : (K : ℝ) + 1 ≠ 0 := by positivity
  have hfac : (K.factorial : ℝ) ≠ 0 := by positivity
  have hpow : ((K : ℝ) + 1) ^ K =
      (((K : ℝ) + 1) ^ (K - 1)) * ((K : ℝ) + 1) := by
    calc
      ((K : ℝ) + 1) ^ K = ((K : ℝ) + 1) ^ ((K - 1) + 1) := by
        congr 1
        omega
      _ = (((K : ℝ) + 1) ^ (K - 1)) * ((K : ℝ) + 1) := by
        rw [pow_succ]
  have hratio : (1 + ((K : ℝ)⁻¹)) ^ (K - 1) =
      (((K : ℝ) + 1) ^ (K - 1)) / (K : ℝ) ^ (K - 1) := by
    rw [show 1 + ((K : ℝ)⁻¹) = ((K : ℝ) + 1) / K by
      field_simp]
    rw [div_pow]
  dsimp [fordCombinatorialWeight]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    hpow, hratio]
  field_simp
  ring

theorem fordCombinatorialWeight_le_succ {K : ℕ} (hK : 0 < K) :
    fordCombinatorialWeight K ≤ fordCombinatorialWeight (K + 1) := by
  rw [fordCombinatorialWeight_succ_eq hK]
  have hbase : (1 : ℝ) ≤ 2 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hratio : (1 : ℝ) ≤
      (1 + ((K : ℝ)⁻¹)) ^ (K - 1) := by
    apply one_le_pow₀
    have hinv : 0 ≤ ((K : ℝ)⁻¹) := by positivity
    linarith
  have hw : 0 ≤ fordCombinatorialWeight K := by
    dsimp [fordCombinatorialWeight]
    positivity
  calc
    fordCombinatorialWeight K = 1 * 1 * fordCombinatorialWeight K := by ring
    _ ≤ (2 * Real.log 2) *
        (1 + ((K : ℝ)⁻¹)) ^ (K - 1) *
          fordCombinatorialWeight K := by gcongr

theorem fordCombinatorialWeight_succ_le {K : ℕ} (hK : 0 < K) :
    fordCombinatorialWeight (K + 1) ≤
      (2 * Real.log 2 * Real.exp 1) * fordCombinatorialWeight K := by
  rw [fordCombinatorialWeight_succ_eq hK]
  have hpow : (1 + ((K : ℝ)⁻¹)) ^ (K - 1) ≤ Real.exp 1 := by
    calc
      (1 + ((K : ℝ)⁻¹)) ^ (K - 1) ≤
          (1 + ((K : ℝ)⁻¹)) ^ K := by
        apply pow_le_pow_right₀
        · have hinv : 0 ≤ ((K : ℝ)⁻¹) := by positivity
          linarith
        · omega
      _ ≤ Real.exp 1 := Real.one_add_inv_pow_le_exp
  have hbase : 0 ≤ 2 * Real.log 2 := by positivity
  have hw : 0 ≤ fordCombinatorialWeight K := by
    dsimp [fordCombinatorialWeight]
    positivity
  calc
    (2 * Real.log 2) * (1 + ((K : ℝ)⁻¹)) ^ (K - 1) *
        fordCombinatorialWeight K ≤
      (2 * Real.log 2) * Real.exp 1 * fordCombinatorialWeight K := by
        gcongr
    _ = (2 * Real.log 2 * Real.exp 1) *
        fordCombinatorialWeight K := by ring

/-- Increasing the depth by a fixed number of blocks cannot decrease the
Ford weight (once the depth is positive). -/
theorem fordCombinatorialWeight_le_add {K c : ℕ} (hK : 0 < K) :
    fordCombinatorialWeight K ≤ fordCombinatorialWeight (K + c) := by
  induction c with
  | zero => simp
  | succ c ih =>
      exact ih.trans (by
        simpa [Nat.add_assoc] using
          (fordCombinatorialWeight_le_succ (K := K + c) (by omega)))

/-- A fixed enlargement of the block depth changes the Ford weight by at
most a fixed multiplicative factor. -/
theorem fordCombinatorialWeight_add_le {K c : ℕ} (hK : 0 < K) :
    fordCombinatorialWeight (K + c) ≤
      (2 * Real.log 2 * Real.exp 1) ^ c *
        fordCombinatorialWeight K := by
  induction c with
  | zero => simp
  | succ c ih =>
      have hstep := fordCombinatorialWeight_succ_le (K := K + c) (by omega)
      rw [pow_succ]
      calc
        fordCombinatorialWeight (K + (c + 1)) =
            fordCombinatorialWeight ((K + c) + 1) := by congr 1
        _ ≤ (2 * Real.log 2 * Real.exp 1) *
            fordCombinatorialWeight (K + c) := hstep
        _ ≤ (2 * Real.log 2 * Real.exp 1) *
            ((2 * Real.log 2 * Real.exp 1) ^ c *
              fordCombinatorialWeight K) := by
                gcongr
        _ = (2 * Real.log 2 * Real.exp 1) ^ c *
            (2 * Real.log 2 * Real.exp 1) *
              fordCombinatorialWeight K := by ring

/-- Constant-shift stability of the Ford combinatorial coefficient. -/
theorem fordCombinatorialWeight_add_isTheta (c : ℕ) :
    (fun K : ℕ ↦ fordCombinatorialWeight (K + c)) =Θ[atTop]
      fordCombinatorialWeight := by
  constructor
  · apply Asymptotics.IsBigO.of_bound
      ((2 * Real.log 2 * Real.exp 1) ^ c)
    filter_upwards [eventually_gt_atTop 0] with K hK
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [fordCombinatorialWeight]
      positivity), Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [fordCombinatorialWeight]
      positivity)]
    exact fordCombinatorialWeight_add_le hK
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop 0] with K hK
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [fordCombinatorialWeight]
      positivity), Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [fordCombinatorialWeight]
      positivity), one_mul]
    exact fordCombinatorialWeight_le_add hK

/-- A depth which is eventually one of two fixed enlargements has the same
Ford weight up to absolute multiplicative constants. -/
theorem fordCombinatorialWeight_choice_isTheta
    (K J : ℕ → ℕ) (c₁ c₂ : ℕ)
    (hK : ∀ᶠ y in atTop, 0 < K y)
    (hJ : ∀ᶠ y in atTop, J y = K y + c₁ ∨ J y = K y + c₂) :
    (fun y ↦ fordCombinatorialWeight (J y)) =Θ[atTop]
      (fun y ↦ fordCombinatorialWeight (K y)) := by
  let A : ℝ := 2 * Real.log 2 * Real.exp 1
  let C : ℝ := A ^ c₁ + A ^ c₂
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hK, hJ] with y hKy hJy
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [fordCombinatorialWeight]
      positivity), Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [fordCombinatorialWeight]
      positivity)]
    rcases hJy with hJy | hJy
    · rw [hJy]
      have hb := fordCombinatorialWeight_add_le (K := K y) (c := c₁) hKy
      have hw : 0 ≤ fordCombinatorialWeight (K y) := by
        dsimp [fordCombinatorialWeight]
        positivity
      calc
        fordCombinatorialWeight (K y + c₁) ≤
            A ^ c₁ * fordCombinatorialWeight (K y) := by
              simpa [A] using hb
        _ ≤ C * fordCombinatorialWeight (K y) := by
          apply mul_le_mul_of_nonneg_right _ hw
          dsimp [C]
          linarith [show 0 ≤ A ^ c₂ by positivity]
    · rw [hJy]
      have hb := fordCombinatorialWeight_add_le (K := K y) (c := c₂) hKy
      have hw : 0 ≤ fordCombinatorialWeight (K y) := by
        dsimp [fordCombinatorialWeight]
        positivity
      calc
        fordCombinatorialWeight (K y + c₂) ≤
            A ^ c₂ * fordCombinatorialWeight (K y) := by
              simpa [A] using hb
        _ ≤ C * fordCombinatorialWeight (K y) := by
          apply mul_le_mul_of_nonneg_right _ hw
          dsimp [C]
          linarith [show 0 ≤ A ^ c₁ by positivity]
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hK, hJ] with y hKy hJy
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [fordCombinatorialWeight]
      positivity), Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [fordCombinatorialWeight]
      positivity), one_mul]
    rcases hJy with hJy | hJy
    · rw [hJy]
      exact fordCombinatorialWeight_le_add hKy
    · rw [hJy]
      exact fordCombinatorialWeight_le_add hKy

/-- The exact terminal block used by the upper argument gives, up to a
constant factor, precisely the same coefficient as the selected lower
depth. -/
theorem fordCombinatorialWeight_upperPrimeBlockDepth_isTheta (M : ℕ) :
    (fun y : ℕ ↦ fordCombinatorialWeight (upperPrimeBlockDepth y)) =Θ[atTop]
      (fun y : ℕ ↦ fordCombinatorialWeight (fordScaleDepth M y)) := by
  apply fordCombinatorialWeight_choice_isTheta
      (fordScaleDepth M) upperPrimeBlockDepth (M + 7) (M + 8)
  · filter_upwards [eventually_ge_atTop (fordConstructionScale M 1)]
      with y hy
    exact fordScaleDepth_pos hy
  · filter_upwards [eventually_ge_atTop (fordConstructionScale M 1)]
      with y hy
    rcases upperPrimeBlockDepth_eq_shift_or_succ hy with h | h
    · left
      omega
    · right
      omega

/-- Constant-shift stability in the relative coordinates used by
`blockPool M K` and `UpperBlockPartition`. -/
theorem fordCombinatorialWeight_upperPrimeBlockCount_isTheta (M : ℕ) :
    (fun y : ℕ ↦
      fordCombinatorialWeight (upperPrimeBlockCount M y)) =Θ[atTop]
      (fun y : ℕ ↦ fordCombinatorialWeight (fordScaleDepth M y)) := by
  apply fordCombinatorialWeight_choice_isTheta
      (fordScaleDepth M) (upperPrimeBlockCount M) 8 9
  · filter_upwards [eventually_ge_atTop (fordConstructionScale M 1)]
      with y hy
    exact fordScaleDepth_pos hy
  · filter_upwards [eventually_ge_atTop (fordConstructionScale M 1)]
      with y hy
    exact upperPrimeBlockCount_eq_shift_or_succ hy

end Erdos446
