/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalStepanovExtensionSum

/-!
# Complete sums for the positive-shift reciprocal phase

This file specializes the unconditional simple-pole rational Weil estimate
to the exact iterated phase produced by `FiniteWeylInequality`.  At a pole the
natural `ZMod` inverse convention assigns a unit-modulus character value,
whereas the rational Weil sum assigns zero.  The two sums therefore differ by
at most the number of poles.
-/

namespace Erdos387

open scoped BigOperators

namespace PositiveShiftCompleteSum

/-- The complete sum of an iterated positive-shift reciprocal phase, bounded
in terms of its actual surviving pole conductor. -/
theorem norm_sum_le_conductor
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ)
    (hshift : ∀ h ∈ hs, h + 1 < p)
    (hpow : 2 ^ hs.length < p) :
    let coeff := InverseRational.iteratedDifferenceCoefficient
      (InverseRational.singlePoleCoefficient c (-a))
      (InverseRational.positiveShiftPairs p hs)
    ‖∑ x : ZMod p,
        ZMod.stdAddChar
          (InverseRational.zmodIteratedInversePhase p c a hs x)‖ ≤
      ((2 * (InverseRational.poleSupport coeff).card - 1 : ℕ) : ℝ) *
          Real.sqrt (p : ℝ) +
        (InverseRational.poleSupport coeff).card := by
  classical
  let coeff := InverseRational.iteratedDifferenceCoefficient
    (InverseRational.singlePoleCoefficient c (-a))
    (InverseRational.positiveShiftPairs p hs)
  let support := InverseRational.poleSupport coeff
  have hne : support.Nonempty := by
    simpa only [support, coeff] using
      InverseRational.positiveShift_iteratedDifference_nonempty
        hc hs hshift hpow
  have hcard : support.card ≤ 2 ^ hs.length := by
    simpa only [support, coeff] using
      InverseRational.card_positiveShift_poleSupport_le hc hs
  have hcardp : support.card < p := hcard.trans_lt hpow
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hweil :
      ‖∑ x : ZMod p,
          if x ∈ support then 0
          else ZMod.stdAddChar
            (InverseRational.simplePolePhase coeff x)‖ ≤
        ((2 * support.card - 1 : ℕ) : ℝ) *
          Real.sqrt (p : ℝ) := by
    simpa only [support] using
      RationalStepanov.norm_zeroExtendedSimplePolePhase_sum_le
        hp coeff hne hcardp
  have hidentity :
      (∑ x : ZMod p,
          ZMod.stdAddChar
            (InverseRational.zmodIteratedInversePhase p c a hs x)) =
        (∑ x : ZMod p,
          if x ∈ support then 0
          else ZMod.stdAddChar
            (InverseRational.simplePolePhase coeff x)) +
        ∑ x ∈ support,
          ZMod.stdAddChar (InverseRational.simplePolePhase coeff x) := by
    calc
      (∑ x : ZMod p,
          ZMod.stdAddChar
            (InverseRational.zmodIteratedInversePhase p c a hs x)) =
          ∑ x : ZMod p,
            ((if x ∈ support then 0
              else ZMod.stdAddChar
                (InverseRational.simplePolePhase coeff x)) +
             if x ∈ support then
               ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)
             else 0) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [show InverseRational.simplePolePhase coeff x =
            InverseRational.zmodIteratedInversePhase p c a hs x by
          exact InverseRational.simplePolePhase_iteratedPositiveShiftCoefficient
            c a hs x]
        by_cases hx : x ∈ support <;> simp [hx]
      _ = (∑ x : ZMod p,
            if x ∈ support then 0
            else ZMod.stdAddChar
              (InverseRational.simplePolePhase coeff x)) +
          ∑ x : ZMod p,
            if x ∈ support then
              ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)
            else 0 := Finset.sum_add_distrib
      _ = (∑ x : ZMod p,
            if x ∈ support then 0
            else ZMod.stdAddChar
              (InverseRational.simplePolePhase coeff x)) +
          ∑ x ∈ support,
            ZMod.stdAddChar (InverseRational.simplePolePhase coeff x) := by
        congr 1
        simp
  have hpoles :
      ‖∑ x ∈ support,
          ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ ≤
        (support.card : ℝ) := by
    calc
      ‖∑ x ∈ support,
          ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ ≤
          ∑ x ∈ support,
            ‖ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ :=
        norm_sum_le _ _
      _ = ∑ _x ∈ support, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [AddChar.norm_apply]
      _ = support.card := by simp
  dsimp only
  rw [hidentity]
  exact (norm_add_le _ _).trans (add_le_add hweil hpoles)

/-- Conductor-free envelope depending only on the differencing depth. -/
theorem norm_sum_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ)
    (hshift : ∀ h ∈ hs, h + 1 < p)
    (hpow : 2 ^ hs.length < p) :
    ‖∑ x : ZMod p,
        ZMod.stdAddChar
          (InverseRational.zmodIteratedInversePhase p c a hs x)‖ ≤
      ((2 * 2 ^ hs.length - 1 : ℕ) : ℝ) * Real.sqrt (p : ℝ) +
        2 ^ hs.length := by
  let coeff := InverseRational.iteratedDifferenceCoefficient
    (InverseRational.singlePoleCoefficient c (-a))
    (InverseRational.positiveShiftPairs p hs)
  let s := (InverseRational.poleSupport coeff).card
  have hcore := norm_sum_le_conductor (a := a) hc hs hshift hpow
  dsimp only at hcore
  have hsCard : s ≤ 2 ^ hs.length := by
    simpa only [s, coeff] using
      InverseRational.card_positiveShift_poleSupport_le hc hs
  have hconductor : 2 * s - 1 ≤ 2 * 2 ^ hs.length - 1 := by omega
  calc
    ‖∑ x : ZMod p,
        ZMod.stdAddChar
          (InverseRational.zmodIteratedInversePhase p c a hs x)‖ ≤
        ((2 * s - 1 : ℕ) : ℝ) * Real.sqrt (p : ℝ) + s := hcore
    _ ≤ ((2 * 2 ^ hs.length - 1 : ℕ) : ℝ) * Real.sqrt (p : ℝ) +
        2 ^ hs.length := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hconductor)
          (Real.sqrt_nonneg _)
      · exact_mod_cast hsCard

end PositiveShiftCompleteSum

end Erdos387
