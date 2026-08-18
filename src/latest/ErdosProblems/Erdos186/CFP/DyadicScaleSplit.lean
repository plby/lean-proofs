/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.HDimension
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingSource

/-!
# Dyadic levels below a source scale

The outer CFP construction needs two dyadic levels below `s`: a terminal
level a fixed factor below `s`, and a lower level a logarithmic factor below
`s`.  These lemmas package the exact natural-number rounding estimates.
-/

namespace Erdos186.CFP

noncomputable section

/-- A dyadic level obtained by dividing `s` by a variable natural factor on
the logarithmic scale. -/
def dyadicLevelBelow (s divisor : ℕ) : ℕ :=
  Nat.log 2 s - Nat.log 2 divisor

/-- The level `dyadicLevelBelow s divisor` is within a factor two of the
ordinary quotient scale `s/divisor`. -/
theorem dyadicLevelBelow_window
    {s divisor : ℕ} (hs : 0 < s) (hdivisor : 0 < divisor)
    (hlog : Nat.log 2 divisor ≤ Nat.log 2 s) :
    divisor * 2 ^ dyadicLevelBelow s divisor < 2 * s ∧
      s < 2 * divisor * 2 ^ dyadicLevelBelow s divisor := by
  have hsPowLow : 2 ^ Nat.log 2 s ≤ s :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hs)
  have hsPowHigh : s < 2 ^ (Nat.log 2 s + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two s
  have hdivPowLow : 2 ^ Nat.log 2 divisor ≤ divisor :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hdivisor)
  have hdivPowHigh : divisor < 2 ^ (Nat.log 2 divisor + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two divisor
  have hsplit : Nat.log 2 divisor + dyadicLevelBelow s divisor =
      Nat.log 2 s := by
    dsimp only [dyadicLevelBelow]
    exact Nat.add_sub_of_le hlog
  constructor
  · calc
      divisor * 2 ^ dyadicLevelBelow s divisor <
          2 ^ (Nat.log 2 divisor + 1) *
            2 ^ dyadicLevelBelow s divisor :=
        Nat.mul_lt_mul_of_pos_right hdivPowHigh (by positivity)
      _ = 2 * (2 ^ Nat.log 2 divisor *
          2 ^ dyadicLevelBelow s divisor) := by
        rw [pow_succ]
        ring
      _ = 2 * 2 ^ Nat.log 2 s := by rw [← pow_add, hsplit]
      _ ≤ 2 * s := Nat.mul_le_mul_left 2 hsPowLow
  · calc
      s < 2 ^ (Nat.log 2 s + 1) := hsPowHigh
      _ = 2 * 2 ^ Nat.log 2 s := by rw [pow_succ]; ring
      _ = 2 * (2 ^ Nat.log 2 divisor *
          2 ^ dyadicLevelBelow s divisor) := by rw [← pow_add, hsplit]
      _ ≤ 2 * (divisor * 2 ^ dyadicLevelBelow s divisor) := by
        exact Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_right _ hdivPowLow)
      _ = 2 * divisor * 2 ^ dyadicLevelBelow s divisor := by ring

/-- A terminal dyadic level using a ceiling logarithm has the sharper upper
bound `divisor * 2^level ≤ s` and loses at most a factor four below. -/
def dyadicTerminalBelow (s divisor : ℕ) : ℕ :=
  Nat.log 2 s - Nat.clog 2 divisor

theorem dyadicTerminalBelow_window
    {s divisor : ℕ} (hs : 0 < s) (hdivisor : 0 < divisor)
    (hlog : Nat.clog 2 divisor ≤ Nat.log 2 s) :
    divisor * 2 ^ dyadicTerminalBelow s divisor ≤ s ∧
      s < 4 * divisor * 2 ^ dyadicTerminalBelow s divisor := by
  have hsPowLow : 2 ^ Nat.log 2 s ≤ s :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hs)
  have hsPowHigh : s < 2 ^ (Nat.log 2 s + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two s
  have hdivPow := PreprocessingBilu.le_two_pow_clog_lt_two_mul hdivisor
  have hsplit : Nat.clog 2 divisor + dyadicTerminalBelow s divisor =
      Nat.log 2 s := by
    dsimp only [dyadicTerminalBelow]
    exact Nat.add_sub_of_le hlog
  constructor
  · calc
      divisor * 2 ^ dyadicTerminalBelow s divisor ≤
          2 ^ Nat.clog 2 divisor *
            2 ^ dyadicTerminalBelow s divisor :=
        Nat.mul_le_mul_right _ hdivPow.1
      _ = 2 ^ Nat.log 2 s := by rw [← pow_add, hsplit]
      _ ≤ s := hsPowLow
  · calc
      s < 2 ^ (Nat.log 2 s + 1) := hsPowHigh
      _ = 2 * 2 ^ Nat.log 2 s := by rw [pow_succ]; ring
      _ = 2 * (2 ^ Nat.clog 2 divisor *
          2 ^ dyadicTerminalBelow s divisor) := by rw [← pow_add, hsplit]
      _ < 2 * (2 * divisor *
          2 ^ dyadicTerminalBelow s divisor) := by
        exact Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_right hdivPow.2 (by positivity)) (by omega)
      _ = 4 * divisor * 2 ^ dyadicTerminalBelow s divisor := by ring

/-- The logarithmic factor in the low-prefix estimate is uniformly linear
in the source dyadic logarithm. -/
theorem dyadicLowPrefix_log_le
    {m n low H : ℕ} (hm : 0 < m)
    (hlow : 2 ^ low ≤ m)
    (hn : Nat.log 2 n + 1 ≤ H * (Nat.log 2 m + 1)) :
    Nat.log 2 (2 ^ low * n + 1) + 1 ≤
      (H + 3) * (Nat.log 2 m + 1) := by
  let ell := Nat.log 2 m + 1
  have hell : 0 < ell := by dsimp only [ell]; omega
  have hmPow : m ≤ 2 ^ ell :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two m).le
  have hnPow : n ≤ 2 ^ (H * ell) := by
    have hnlt : n < 2 ^ (Nat.log 2 n + 1) :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two n
    have hexp : Nat.log 2 n + 1 ≤ H * ell := by
      simpa only [ell] using hn
    exact hnlt.le.trans (Nat.pow_le_pow_right (by omega) hexp)
  have hproduct : 2 ^ low * n ≤ 2 ^ ((H + 1) * ell) := by
    calc
      2 ^ low * n ≤ m * n := Nat.mul_le_mul_right n hlow
      _ ≤ 2 ^ ell * 2 ^ (H * ell) := Nat.mul_le_mul hmPow hnPow
      _ = 2 ^ ((H + 1) * ell) := by
        rw [← pow_add]
        congr 1
        ring
  have hplus : 2 ^ low * n + 1 ≤ 2 ^ ((H + 1) * ell + 1) := by
    calc
      2 ^ low * n + 1 ≤
          2 ^ ((H + 1) * ell) + 2 ^ ((H + 1) * ell) := by
        exact Nat.add_le_add hproduct
          (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
      _ = 2 ^ ((H + 1) * ell + 1) := by rw [pow_succ]; ring
  have hlog : Nat.log 2 (2 ^ low * n + 1) ≤
      (H + 1) * ell + 1 := by
    calc
      Nat.log 2 (2 ^ low * n + 1) ≤
          Nat.log 2 (2 ^ ((H + 1) * ell + 1)) :=
        Nat.log_mono_right hplus
      _ = (H + 1) * ell + 1 := Nat.log_pow Nat.one_lt_two _
  dsimp only [ell] at hlog ⊢
  have hellOne : 1 ≤ Nat.log 2 m + 1 := by omega
  calc
    Nat.log 2 (2 ^ low * n + 1) + 1 ≤
        (H + 1) * (Nat.log 2 m + 1) + 2 := by omega
    _ ≤ (H + 1) * (Nat.log 2 m + 1) +
        2 * (Nat.log 2 m + 1) := by omega
    _ = (H + 3) * (Nat.log 2 m + 1) := by ring

/-- A fixed polynomial margin at the source scale turns an
`endpoint * s^(D-2)` ambient bound into the `(D-1)`-st power window used by
the preprocessing horizon. -/
theorem endpoint_mul_source_pow_le_horizon_pow
    {endpoint coefficient s horizon D : ℕ}
    (hD : 2 ≤ D) (hcoefficient : 0 < coefficient)
    (hsource : s ≤ coefficient * horizon)
    (hlarge : endpoint * coefficient ^ (D - 1) ≤ s) :
    endpoint * s ^ (D - 2) ≤ horizon ^ (D - 1) := by
  have hsub : D - 1 = (D - 2) + 1 := by omega
  have hcoefficientBound : endpoint * coefficient ^ (D - 2) ≤ horizon := by
    have hmul : coefficient * (endpoint * coefficient ^ (D - 2)) ≤
        coefficient * horizon := by
      calc
        coefficient * (endpoint * coefficient ^ (D - 2)) =
            endpoint * coefficient ^ (D - 1) := by
          rw [hsub, pow_succ]
          ring
        _ ≤ s := hlarge
        _ ≤ coefficient * horizon := hsource
    exact Nat.le_of_mul_le_mul_left hmul hcoefficient
  calc
    endpoint * s ^ (D - 2) ≤
        endpoint * (coefficient * horizon) ^ (D - 2) := by
      gcongr
    _ = (endpoint * coefficient ^ (D - 2)) *
        horizon ^ (D - 2) := by
      rw [mul_pow]
      ring
    _ ≤ horizon * horizon ^ (D - 2) :=
      Nat.mul_le_mul_right _ hcoefficientBound
    _ = horizon ^ (D - 1) := by
      rw [hsub, pow_succ]
      ring

/-- The logarithmically lowered dyadic level satisfies the full source
horizon power condition once a single explicit fixed-coefficient lower
bound on `s` is available. -/
theorem dyadicLevelBelow_horizon_power
    {N s divisor endpoint horizonFactor D : ℕ}
    (hs : 0 < s) (hdivisor : 0 < divisor)
    (hhorizonFactor : 0 < horizonFactor) (hD : 2 ≤ D)
    (hlog : Nat.log 2 divisor ≤ Nat.log 2 s)
    (hoffset : Nat.clog 2 horizonFactor ≤ dyadicLevelBelow s divisor)
    (hN : N ≤ endpoint * s ^ (D - 2))
    (hlarge : endpoint *
        (2 * divisor * 2 ^ Nat.clog 2 horizonFactor) ^ (D - 1) ≤ s) :
    N ≤ (horizonFactor *
      2 ^ (dyadicLevelBelow s divisor - Nat.clog 2 horizonFactor)) ^
        (D - 1) := by
  let low := dyadicLevelBelow s divisor
  let offset := Nat.clog 2 horizonFactor
  let coefficient := 2 * divisor * 2 ^ offset
  let horizon := horizonFactor * 2 ^ (low - offset)
  have hlevel := (dyadicLevelBelow_window hs hdivisor hlog).2.le
  have hsplit : offset + (low - offset) = low := Nat.add_sub_of_le hoffset
  have hpowSplit : 2 ^ low = 2 ^ offset * 2 ^ (low - offset) := by
    rw [← pow_add, hsplit]
  have hsource : s ≤ coefficient * horizon := by
    calc
      s ≤ 2 * divisor * 2 ^ low := by
        simpa only [low] using hlevel
      _ = coefficient * (1 * 2 ^ (low - offset)) := by
        dsimp only [coefficient]
        rw [hpowSplit]
        ring
      _ ≤ coefficient *
          (horizonFactor * 2 ^ (low - offset)) := by
        gcongr
        omega
      _ = coefficient * horizon := rfl
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    positivity
  have hpower := endpoint_mul_source_pow_le_horizon_pow hD hcoefficient
    hsource (by simpa only [coefficient, offset] using hlarge)
  exact hN.trans (by simpa only [horizon, low, offset] using hpower)

/-- A multiplicative lower bound on `s` gives an exact lower bound for the
logarithmically shifted dyadic level. -/
theorem le_dyadicLevelBelow_of_mul_pow_le
    {s divisor lower : ℕ} (hdivisor : 0 < divisor)
    (hlarge : divisor * 2 ^ lower ≤ s) :
    lower ≤ dyadicLevelBelow s divisor := by
  have hpow : 2 ^ (Nat.log 2 divisor + lower) ≤ s := by
    calc
      2 ^ (Nat.log 2 divisor + lower) =
          2 ^ Nat.log 2 divisor * 2 ^ lower := by rw [pow_add]
      _ ≤ divisor * 2 ^ lower := by
        gcongr
        exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hdivisor)
      _ ≤ s := hlarge
  have hlog : Nat.log 2 divisor + lower ≤ Nat.log 2 s := by
    calc
      Nat.log 2 divisor + lower =
          Nat.log 2 (2 ^ (Nat.log 2 divisor + lower)) := by
        rw [Nat.log_pow Nat.one_lt_two]
      _ ≤ Nat.log 2 s := Nat.log_mono_right hpow
  dsimp only [dyadicLevelBelow]
  omega

/-- If the terminal fixed divisor has smaller ceiling-logarithm than the
variable low-level divisor has floor-logarithm, then the selected low level
is strictly before the selected terminal level. -/
theorem dyadicLevelBelow_lt_dyadicTerminalBelow
    {s lowDivisor terminalDivisor : ℕ}
    (hlow : Nat.log 2 lowDivisor ≤ Nat.log 2 s)
    (hterminal : Nat.clog 2 terminalDivisor ≤ Nat.log 2 s)
    (hdivisors : Nat.clog 2 terminalDivisor < Nat.log 2 lowDivisor) :
    dyadicLevelBelow s lowDivisor <
      dyadicTerminalBelow s terminalDivisor := by
  dsimp only [dyadicLevelBelow, dyadicTerminalBelow]
  omega

end

end Erdos186.CFP

#print axioms Erdos186.CFP.dyadicLevelBelow_window
#print axioms Erdos186.CFP.dyadicTerminalBelow_window
#print axioms Erdos186.CFP.dyadicLowPrefix_log_le
#print axioms Erdos186.CFP.endpoint_mul_source_pow_le_horizon_pow
#print axioms Erdos186.CFP.dyadicLevelBelow_horizon_power
#print axioms Erdos186.CFP.le_dyadicLevelBelow_of_mul_pow_le
#print axioms Erdos186.CFP.dyadicLevelBelow_lt_dyadicTerminalBelow
