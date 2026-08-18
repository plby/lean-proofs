/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.DyadicScaleSplit
import ErdosProblems.Erdos186.CFP.SharpColorCapacityNumerics
import ErdosProblems.Erdos186.CFP.LargeInputLogNumerics

/-!
# A uniform dyadic crossing window below the sharp colouring cap

The lower dyadic level is placed a logarithmic factor below `s`, while the
terminal level is placed a sufficiently large fixed factor below `s`.  A
single large-input cutoff then makes the low-prefix and terminal-ratio costs
strictly smaller than the population cap used by the sharp random colouring.
-/

namespace Erdos186.CFP

noncomputable section

set_option autoImplicit false

/-- If two nonnegative costs each consume at most one thirty-second of a
positive source scale, then their sum (with one unit of strict slack) fits
below the corresponding quotient cap. -/
private theorem add_one_lt_div_of_thirtyTwo_scaled
    {denominator firstCost secondCost source : ℕ}
    (hdenominator : 0 < denominator) (hfirstPos : 1 ≤ firstCost)
    (hfirst : 32 * denominator * firstCost < source)
    (hsecond : 32 * denominator * secondCost ≤ source) :
    firstCost + secondCost + 1 < source / denominator := by
  have hadd : 32 * denominator * (firstCost + secondCost) < 2 * source := by
    calc
      32 * denominator * (firstCost + secondCost) =
          32 * denominator * firstCost +
            32 * denominator * secondCost := by ring
      _ < source + source := Nat.add_lt_add_of_lt_of_le hfirst hsecond
      _ = 2 * source := by ring
  have hhalf : 16 * denominator * (firstCost + secondCost) < source := by
    apply Nat.lt_of_mul_lt_mul_left (a := 2)
    simpa only [show 2 * (16 * denominator * (firstCost + secondCost)) =
        32 * denominator * (firstCost + secondCost) by ring] using hadd
  have hsource : denominator * (firstCost + secondCost + 2) ≤ source := by
    calc
      denominator * (firstCost + secondCost + 2) ≤
          denominator * (16 * (firstCost + secondCost)) := by
        exact Nat.mul_le_mul_left denominator (by omega)
      _ = 16 * denominator * (firstCost + secondCost) := by ring
      _ ≤ source := hhalf.le
  have hdiv : firstCost + secondCost + 2 ≤ source / denominator := by
    rw [Nat.le_div_iff_mul_le hdenominator]
    simpa only [Nat.mul_comm] using hsource
  omega

/-- Fixed choices of the logarithmic and terminal divisors eventually give
the strict crossing inequality needed by the projected dyadic certificate. -/
theorem exists_cutoff_projectedDyadicCrossing
    (q C0 ratio H minimumLevel terminalBase : ℕ) (eta : ℝ)
    (hC0 : 0 < C0) (hterminalBase : 0 < terminalBase)
    (hterminalBaseLarge : 4096 * C0 * ratio ≤ terminalBase)
    (heta : 0 < eta) :
    ∃ lowCoefficient cutoff : ℕ,
      0 < lowCoefficient ∧ 2 ≤ cutoff ∧
      ∀ {m n s : ℕ}, cutoff ≤ m →
        Nat.log 2 n + 1 ≤ H * (Nat.log 2 m + 1) →
        Real.rpow (m : ℝ) eta ≤ (s : ℝ) → s ≤ m →
        let low := dyadicLevelBelow s
          (lowCoefficient * (Nat.log 2 m + 1))
        let terminal := dyadicTerminalBelow s ((q + 1) * terminalBase)
        minimumLevel ≤ low ∧ low < terminal ∧
          2 ^ (low + 1) * (Nat.log 2 (2 ^ low * n + 1) + 1) +
              16 * ratio * 2 ^ terminal + 1 <
            RandomPartition.colorCap s q C0 := by
  let capDenominator := 4 * C0 * (2 * q + 1)
  let terminalDivisor := (q + 1) * terminalBase
  let lowBase := 128 * capDenominator * (H + 3)
  let lowCoefficient :=
    max lowBase (2 ^ (Nat.clog 2 terminalDivisor + 1))
  have hcapDenominator : 0 < capDenominator := by
    dsimp only [capDenominator]
    positivity
  have hterminal : 0 < terminalDivisor := by
    dsimp only [terminalDivisor]
    positivity
  have hlowBase : 0 < lowBase := by
    dsimp only [lowBase]
    positivity
  have hlowCoefficient : 0 < lowCoefficient := by
    exact hlowBase.trans_le (le_max_left _ _)
  let absorptionCoefficient := lowCoefficient * 2 ^ minimumLevel
  obtain ⟨cutoff, hcutoff, habsorb⟩ :=
    exists_cutoff_logPolynomial_le_rpow eta heta absorptionCoefficient 1
  refine ⟨lowCoefficient, cutoff, hlowCoefficient, hcutoff, ?_⟩
  intro m n s hm hlogn hslow hsm
  let ell := Nat.log 2 m + 1
  let lowDivisor := lowCoefficient * ell
  let low := dyadicLevelBelow s lowDivisor
  let terminal := dyadicTerminalBelow s terminalDivisor
  have hmPos : 0 < m := by omega
  have hell : 0 < ell := by dsimp only [ell]; omega
  have hlowDivisor : 0 < lowDivisor :=
    Nat.mul_pos hlowCoefficient hell
  have habsorbReal := habsorb (m := m) hm
  have habsorbNat : absorptionCoefficient * ell ≤ s := by
    have hreal : ((absorptionCoefficient * ell : ℕ) : ℝ) ≤ (s : ℝ) := by
      calc
        ((absorptionCoefficient * ell : ℕ) : ℝ) =
            ((absorptionCoefficient * (Nat.log 2 m + 1) ^ 1 : ℕ) : ℝ) := by
          simp only [ell, pow_one]
        _ ≤ Real.rpow (m : ℝ) eta := habsorbReal
        _ ≤ (s : ℝ) := hslow
    exact_mod_cast hreal
  have hminimumLarge : lowDivisor * 2 ^ minimumLevel ≤ s := by
    simpa only [absorptionCoefficient, lowDivisor, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using
      habsorbNat
  have hsPos : 0 < s := by
    have : 0 < lowDivisor * 2 ^ minimumLevel := by positivity
    exact this.trans_le hminimumLarge
  have hlowDivisorLe : lowDivisor ≤ s := by
    calc
      lowDivisor = lowDivisor * 1 := by rw [Nat.mul_one]
      _ ≤ lowDivisor * 2 ^ minimumLevel := by
        exact Nat.mul_le_mul_left lowDivisor Nat.one_le_two_pow
      _ ≤ s := hminimumLarge
  have hlowLog : Nat.log 2 lowDivisor ≤ Nat.log 2 s :=
    Nat.log_mono_right hlowDivisorLe
  have hminimum : minimumLevel ≤ low := by
    simpa only [low] using
      (le_dyadicLevelBelow_of_mul_pow_le hlowDivisor hminimumLarge)
  have hterminalPowLe : 2 ^ Nat.clog 2 terminalDivisor ≤ s := by
    calc
      2 ^ Nat.clog 2 terminalDivisor ≤ lowCoefficient := by
        exact (Nat.pow_le_pow_right (n := 2) (by omega) (by omega)).trans
          (le_max_right lowBase (2 ^ (Nat.clog 2 terminalDivisor + 1)))
      _ ≤ lowCoefficient * ell := by
        simpa only [Nat.mul_one] using
          Nat.mul_le_mul_left lowCoefficient (show 1 ≤ ell by omega)
      _ = lowDivisor := rfl
      _ ≤ s := hlowDivisorLe
  have hterminalLog : Nat.clog 2 terminalDivisor ≤ Nat.log 2 s := by
    calc
      Nat.clog 2 terminalDivisor =
          Nat.log 2 (2 ^ Nat.clog 2 terminalDivisor) := by
        rw [Nat.log_pow Nat.one_lt_two]
      _ ≤ Nat.log 2 s := Nat.log_mono_right hterminalPowLe
  have hdivisorGap : Nat.clog 2 terminalDivisor <
      Nat.log 2 lowDivisor := by
    have hpowLe : 2 ^ (Nat.clog 2 terminalDivisor + 1) ≤ lowDivisor := by
      calc
        2 ^ (Nat.clog 2 terminalDivisor + 1) ≤ lowCoefficient :=
          le_max_right _ _
        _ ≤ lowCoefficient * ell := by
          simpa only [Nat.mul_one] using
            Nat.mul_le_mul_left lowCoefficient (show 1 ≤ ell by omega)
        _ = lowDivisor := rfl
    have hlogLe : Nat.clog 2 terminalDivisor + 1 ≤
        Nat.log 2 lowDivisor := by
      calc
        Nat.clog 2 terminalDivisor + 1 =
            Nat.log 2 (2 ^ (Nat.clog 2 terminalDivisor + 1)) := by
          rw [Nat.log_pow Nat.one_lt_two]
        _ ≤ Nat.log 2 lowDivisor := Nat.log_mono_right hpowLe
    omega
  have hlowTerminal : low < terminal := by
    exact dyadicLevelBelow_lt_dyadicTerminalBelow hlowLog hterminalLog
      hdivisorGap
  have hlowWindow := dyadicLevelBelow_window hsPos hlowDivisor hlowLog
  have hterminalWindow :=
    dyadicTerminalBelow_window hsPos hterminal hterminalLog
  have hlowCoefficientTwo : 2 ≤ lowCoefficient := by
    have : 2 ≤ 2 ^ (Nat.clog 2 terminalDivisor + 1) := by
      calc
        2 = 2 ^ 1 := by simp
        _ ≤ 2 ^ (Nat.clog 2 terminalDivisor + 1) :=
          Nat.pow_le_pow_right (n := 2) (by omega) (by omega)
    exact this.trans (le_max_right _ _)
  have hpowLowS : 2 ^ low < s := by
    have htwoPow : 2 * 2 ^ low ≤ lowDivisor * 2 ^ low := by
      have htwoDivisor : 2 ≤ lowDivisor := by
        exact hlowCoefficientTwo.trans
          (by simpa only [Nat.mul_one] using
            Nat.mul_le_mul_left lowCoefficient (show 1 ≤ ell by omega))
      exact Nat.mul_le_mul_right _ htwoDivisor
    have : 2 * 2 ^ low < 2 * s :=
      htwoPow.trans_lt (by simpa only [low] using hlowWindow.1)
    omega
  have hpowLowM : 2 ^ low ≤ m := hpowLowS.le.trans hsm
  have hprefixLog : Nat.log 2 (2 ^ low * n + 1) + 1 ≤
      (H + 3) * ell := by
    simpa only [ell] using dyadicLowPrefix_log_le hmPos hpowLowM hlogn
  let prefixCost : ℕ := 2 ^ (low + 1) *
    (Nat.log 2 (2 ^ low * n + 1) + 1)
  let terminalCost : ℕ := 16 * ratio * 2 ^ terminal
  have hprefixBound : prefixCost ≤ 2 * (H + 3) * ell * 2 ^ low := by
    dsimp only [prefixCost]
    rw [pow_succ]
    nlinarith
  have hlowBaseLe : 128 * capDenominator * (H + 3) ≤
      lowCoefficient := by
    simpa only [lowBase] using le_max_left lowBase
      (2 ^ (Nat.clog 2 terminalDivisor + 1))
  have hprefixScaled : 32 * capDenominator * prefixCost < s := by
    have hlargeScaled :
        128 * capDenominator * (H + 3) * ell * 2 ^ low < 2 * s := by
      calc
        128 * capDenominator * (H + 3) * ell * 2 ^ low ≤
            lowCoefficient * ell * 2 ^ low := by gcongr
        _ = lowDivisor * 2 ^ low := rfl
        _ < 2 * s := by simpa only [low] using hlowWindow.1
    have hp : 32 * capDenominator * prefixCost ≤
        64 * capDenominator * (H + 3) * ell * 2 ^ low := by
      calc
        32 * capDenominator * prefixCost ≤
            32 * capDenominator *
              (2 * (H + 3) * ell * 2 ^ low) := by gcongr
        _ = 64 * capDenominator * (H + 3) * ell * 2 ^ low := by ring
    have htwice : 2 * (32 * capDenominator * prefixCost) < 2 * s := by
      calc
        2 * (32 * capDenominator * prefixCost) ≤
            2 * (64 * capDenominator * (H + 3) * ell * 2 ^ low) :=
          Nat.mul_le_mul_left 2 hp
        _ = 128 * capDenominator * (H + 3) * ell * 2 ^ low := by ring
        _ < 2 * s := hlargeScaled
    exact Nat.lt_of_mul_lt_mul_left htwice
  have hterminalScaled : 32 * capDenominator * terminalCost ≤ s := by
    have hcoefficient :
        32 * capDenominator * (16 * ratio) ≤ terminalDivisor := by
      have hq : 2 * q + 1 ≤ 2 * (q + 1) := by omega
      calc
        32 * capDenominator * (16 * ratio) =
            2048 * C0 * ratio * (2 * q + 1) := by
          dsimp only [capDenominator]
          ring
        _ ≤ 2048 * C0 * ratio * (2 * (q + 1)) :=
          Nat.mul_le_mul_left _ hq
        _ = (q + 1) * (4096 * C0 * ratio) := by ring
        _ ≤ (q + 1) * terminalBase :=
          Nat.mul_le_mul_left _ hterminalBaseLarge
        _ = terminalDivisor := by rfl
    calc
      32 * capDenominator * terminalCost =
          (32 * capDenominator * (16 * ratio)) * 2 ^ terminal := by
        dsimp only [terminalCost]
        ring
      _ ≤ terminalDivisor * 2 ^ terminal := by gcongr
      _ ≤ s := by simpa only [terminal] using hterminalWindow.1
  have hprefixPos : 1 ≤ prefixCost := by
    dsimp only [prefixCost]
    have hpowPos : 0 < 2 ^ (low + 1) := pow_pos (by omega) _
    have hlogPos : 0 < Nat.log 2 (2 ^ low * n + 1) + 1 := by omega
    exact Nat.mul_pos hpowPos hlogPos
  have hcap : prefixCost + terminalCost + 1 <
      RandomPartition.colorCap s q C0 := by
    change prefixCost + terminalCost + 1 < s / capDenominator
    exact add_one_lt_div_of_thirtyTwo_scaled hcapDenominator hprefixPos
      hprefixScaled hterminalScaled
  dsimp only [low, terminal]
  refine ⟨hminimum, hlowTerminal, ?_⟩
  dsimp only [prefixCost, terminalCost] at hcap ⊢
  exact hcap

end

end Erdos186.CFP

#print axioms Erdos186.CFP.exists_cutoff_projectedDyadicCrossing
