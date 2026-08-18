/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredPreprocessingSource

/-!
# A preprocessing window chosen from the reserve scale

The source proof chooses its approximation horizon at the scale `s`, while
the ambient interval endpoint is allowed to be as large as a fixed power of
`s`.  This is the numerical separation required by retained preprocessing.
-/

namespace Erdos186.CFP.PreprocessingBilu

noncomputable section

def scaleDyadicLast (s : ℕ) : ℕ := Nat.clog 2 (s + 1)

def scaleDyadicHorizon (horizonFactor s : ℕ) : ℕ :=
  horizonFactor * 2 ^ scaleDyadicLast s

def scaleDyadicFold (horizonFactor s : ℕ) : ℕ :=
  2 ^ (Nat.clog 2 horizonFactor + scaleDyadicLast s)

/-- The scale-chosen horizon and dyadic fold lie in the required Bilu
window and are bounded by a fixed multiple of `s+1`. -/
theorem scaleDyadic_window
    {horizonFactor s : ℕ} (hfactor : 0 < horizonFactor) :
    s < scaleDyadicHorizon horizonFactor s ∧
      scaleDyadicHorizon horizonFactor s ≤
        scaleDyadicFold horizonFactor s ∧
      scaleDyadicFold horizonFactor s <
        horizonFactor * 2 ^ (scaleDyadicLast s + 1) ∧
      scaleDyadicFold horizonFactor s <
        4 * horizonFactor * (s + 1) := by
  have hs1 : 0 < s + 1 := by omega
  have hsPow := le_two_pow_clog_lt_two_mul hs1
  have hfactorOne : 1 ≤ horizonFactor := hfactor
  have hsHorizon : s < scaleDyadicHorizon horizonFactor s := by
    have hsOne : s + 1 ≤ 2 ^ scaleDyadicLast s := by
      simpa only [scaleDyadicLast] using hsPow.1
    have hpowH : 2 ^ scaleDyadicLast s ≤
        horizonFactor * 2 ^ scaleDyadicLast s := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right (2 ^ scaleDyadicLast s) hfactorOne
    dsimp only [scaleDyadicHorizon]
    omega
  have hwindow := dyadicFold_window
    (last := scaleDyadicLast s) hfactor
  have hfoldBound : scaleDyadicFold horizonFactor s <
      4 * horizonFactor * (s + 1) := by
    calc
      scaleDyadicFold horizonFactor s <
          horizonFactor * 2 ^ (scaleDyadicLast s + 1) := by
        simpa only [scaleDyadicFold] using hwindow.2
      _ = 2 * horizonFactor * 2 ^ scaleDyadicLast s := by
        rw [pow_succ]
        ring
      _ < 2 * horizonFactor * (2 * (s + 1)) := by
        apply Nat.mul_lt_mul_of_pos_left
        · simpa only [scaleDyadicLast] using hsPow.2
        · positivity
      _ = 4 * horizonFactor * (s + 1) := by ring
  exact ⟨hsHorizon, hwindow.1, hwindow.2, hfoldBound⟩

/-- If the source endpoint is bounded by the appropriate power of `s`, the
ambient interval `max (n+1) fold` fits under the scale-chosen horizon power.
The extra rank in the exponent also absorbs the factor-two dyadic rounding
of the fold. -/
theorem scaleDyadic_ambient_le_horizon_pow
    {horizonFactor s n D : ℕ}
    (hfactor : 0 < horizonFactor) (hs : 0 < s) (hD : 3 ≤ D)
    (hn : n ≤ s ^ (D - 2)) :
    max (n + 1) (scaleDyadicFold horizonFactor s) ≤
      (scaleDyadicHorizon horizonFactor s) ^ (D - 1) := by
  let horizon := scaleDyadicHorizon horizonFactor s
  let fold := scaleDyadicFold horizonFactor s
  have hw := scaleDyadic_window (s := s) hfactor
  have hh : 1 < horizon := by dsimp only [horizon]; omega
  have hnH : n + 1 ≤ horizon ^ (D - 1) := by
    have hsH : s ≤ horizon := hw.1.le
    have hpLow : s ^ (D - 2) ≤ horizon ^ (D - 2) :=
      Nat.pow_le_pow_left hsH _
    have hpStrict : horizon ^ (D - 2) < horizon ^ (D - 1) :=
      Nat.pow_lt_pow_right hh (by omega)
    omega
  have hfoldTwo : fold < 2 * horizon := by
    dsimp only [fold, horizon, scaleDyadicFold, scaleDyadicHorizon]
    calc
      2 ^ (Nat.clog 2 horizonFactor + scaleDyadicLast s) <
          horizonFactor * 2 ^ (scaleDyadicLast s + 1) := hw.2.2.1
      _ = 2 * (horizonFactor * 2 ^ scaleDyadicLast s) := by
        rw [pow_succ]
        ring
  have htwoSquare : 2 * horizon ≤ horizon ^ 2 := by
    rw [pow_two]
    nlinarith
  have hsquarePower : horizon ^ 2 ≤ horizon ^ (D - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact max_le hnH (hfoldTwo.le.trans (htwoSquare.trans hsquarePower))

end

end Erdos186.CFP.PreprocessingBilu

#print axioms Erdos186.CFP.PreprocessingBilu.scaleDyadic_window
#print axioms
  Erdos186.CFP.PreprocessingBilu.scaleDyadic_ambient_le_horizon_pow
