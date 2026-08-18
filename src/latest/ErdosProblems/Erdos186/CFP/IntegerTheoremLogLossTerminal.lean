/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.IntegerTheoremTerminal
import ErdosProblems.Erdos186.CFP.LargeInputLogNumerics

/-!
# Large-input integer CFP theorem with its source logarithmic loss

The deterministic preprocessing in the source proof uses a deletion budget
of order `s`; its loss is therefore a fixed multiple of
`s * (Nat.log 2 |A| + 1)`.  This is exactly the logarithmic loss allowed by
the public theorem.  This file supplies the bounded-input and cast adapter
for that source-shaped natural estimate.
-/

namespace Erdos186.CFP

noncomputable section

set_option autoImplicit false

/-- The source-shaped large-input endpoint.  Unlike the stronger
`LargeInputNonemptyIntegerTheorem15`, the natural finite loss retains the
single dyadic logarithm that is present in the preprocessing argument. -/
def LargeInputLogLossNonemptyIntegerTheorem15 : Prop :=
  ∀ β η : ℝ, 1 < β → 0 < η → η < 1 →
    ∃ scaleNum scaleDen D lossCoefficient cutoff : ℕ,
      0 < scaleNum ∧ 0 < scaleDen ∧ scaleNum ≤ scaleDen ∧
      0 < lossCoefficient ∧ 2 ≤ cutoff ∧
      ∀ (n : ℕ) (A : Finset ℤ) (s : ℕ),
        A.Nonempty → cutoff ≤ A.card →
        A ⊆ Finset.Icc 1 (n : ℤ) →
        (n : ℝ) ≤ Real.rpow (A.card : ℝ) β →
        Real.rpow (A.card : ℝ) η ≤ (s : ℝ) →
        (scaleDen : ℝ) * (s : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤
            (scaleNum : ℝ) * (A.card : ℝ) →
        ∃ k loss : ℕ,
          Nonempty
            (FixedScaleWitness (integerPoints A) s D k loss
              scaleNum scaleDen) ∧
          loss ≤ lossCoefficient * s * (Nat.log 2 A.card + 1)

/-- With the source deletion budget `s`, deterministic preprocessing costs
one dyadic logarithm.  This is the source-faithful counterpart of
`preprocessingCardinalityLoss_le_scale`, which deliberately chose the
smaller budget `s / log` in order to prove the stronger `O(s)` estimate. -/
theorem preprocessingCardinalityLoss_le_scale_mul_log
    {A : Finset ℤ} {n m s D horizonCoefficient : ℕ}
    (hzero : 0 ∈ A)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hlog : Nat.log 2 n + 1 ≤
      horizonCoefficient * (Nat.log 2 m + 1)) :
    preprocessingCardinalityLoss A s D ≤
      (6 * D * horizonCoefficient + 1) * s *
        (Nat.log 2 m + 1) := by
  let ell := Nat.log 2 m + 1
  have hell : 1 ≤ ell := by dsimp only [ell]; omega
  have hbox₀ := Preprocessing.boxPotential_le
    (A := A) (n := n) (maxRank := D) hzero hA
  have hbox : Preprocessing.boxPotential A D ≤
      3 * D * horizonCoefficient * ell := by
    calc
      Preprocessing.boxPotential A D ≤
          D * (3 * (Nat.log 2 n + 1)) := hbox₀
      _ ≤ D * (3 * (horizonCoefficient * ell)) := by
        gcongr
      _ = 3 * D * horizonCoefficient * ell := by ring
  change (2 * s) * Preprocessing.boxPotential A D + s ≤ _
  calc
    (2 * s) * Preprocessing.boxPotential A D + s ≤
        (2 * s) * (3 * D * horizonCoefficient * ell) + s := by gcongr
    _ = (6 * D * horizonCoefficient) * s * ell + s := by ring
    _ ≤ (6 * D * horizonCoefficient) * s * ell + s * ell := by
      exact Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left s hell) _
    _ = (6 * D * horizonCoefficient + 1) * s * ell := by ring

/-- Above two, the natural dyadic logarithm is at most four times the real
binary logarithm. -/
theorem natLog_two_add_one_le_four_mul_logb {m : ℕ} (hm : 2 ≤ m) :
    ((Nat.log 2 m + 1 : ℕ) : ℝ) ≤
      4 * Real.logb 2 (m : ℝ) := by
  have hlog := natLog_two_add_one_le_four_mul_log hm
  have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmOne
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogTwoLe : Real.log 2 ≤ 1 :=
    (le_of_lt Real.log_two_lt_d9).trans (by norm_num)
  have hlog_le_logb : Real.log (m : ℝ) ≤ Real.logb 2 (m : ℝ) := by
    rw [Real.logb]
    apply (le_div_iff₀ hlogTwoPos).2
    calc
      Real.log (m : ℝ) * Real.log 2 ≤ Real.log (m : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlogTwoLe hlogm
      _ = Real.log (m : ℝ) := by ring
  exact hlog.trans (mul_le_mul_of_nonneg_left hlog_le_logb (by norm_num))

/-- Bounded inputs and the elementary logarithm comparison turn the
source-shaped large-input theorem into the exact corrected integer CFP
statement. -/
theorem nonemptyIntegerTheorem15_of_largeInputLogLoss
    (hlarge : LargeInputLogLossNonemptyIntegerTheorem15) :
    NonemptyIntegerTheorem15 := by
  intro β η hβ hη hη1
  obtain ⟨scaleNum, scaleDen, D, lossCoefficient, cutoff,
      hnum, hden, hscale, hlossCoefficient, hcutoff, hout⟩ :=
    hlarge β η hβ hη hη1
  let lossConstant := max (4 * lossCoefficient) cutoff
  have hlossConstant : 0 < lossConstant := by
    exact (Nat.mul_pos (by omega) hlossCoefficient).trans_le
      (le_max_left _ _)
  refine ⟨scaleNum, scaleDen, D, lossConstant, hnum, hden,
    hlossConstant, ?_⟩
  intro n A s hA hAinterval hn hslow hscaleCard
  have hs : 0 < s := by
    apply scale_pos_of_nonempty (integerPoints_nonempty hA) hη.le
    simpa only [card_integerPoints] using hslow
  by_cases hsmall : A.card < cutoff
  · have hcardLoss : (integerPoints A).card ≤ lossConstant := by
      rw [card_integerPoints]
      exact hsmall.le.trans
        ((le_max_right (4 * lossCoefficient) cutoff))
    simpa only [lossConstant, card_integerPoints] using
      exists_fixedScaleWitness_of_card_le
        (integerPoints A) s D scaleNum scaleDen lossConstant
        (integerPoints_nonempty hA) hs hnum hden hscale hcardLoss
  · have hcutoffA : cutoff ≤ A.card := by omega
    obtain ⟨k, loss, hW, hloss⟩ :=
      hout n A s hA hcutoffA hAinterval hn hslow hscaleCard
    refine ⟨k, loss, hW, ?_⟩
    have hcardTwo : 2 ≤ A.card := hcutoff.trans hcutoffA
    have hlog := natLog_two_add_one_le_four_mul_logb hcardTwo
    have hcastLoss : (loss : ℝ) ≤
        (lossCoefficient : ℝ) * (s : ℝ) *
          ((Nat.log 2 A.card + 1 : ℕ) : ℝ) := by
      exact_mod_cast hloss
    have hscaledLog :
        (lossCoefficient : ℝ) * (s : ℝ) *
            ((Nat.log 2 A.card + 1 : ℕ) : ℝ) ≤
          ((4 * lossCoefficient : ℕ) : ℝ) * (s : ℝ) *
            Real.logb 2 (A.card : ℝ) := by
      have hcoeff : 0 ≤ (lossCoefficient : ℝ) := by positivity
      have hsnonneg : 0 ≤ (s : ℝ) := by positivity
      calc
        (lossCoefficient : ℝ) * (s : ℝ) *
              ((Nat.log 2 A.card + 1 : ℕ) : ℝ) ≤
            (lossCoefficient : ℝ) * (s : ℝ) *
              (4 * Real.logb 2 (A.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg hcoeff hsnonneg)
        _ = ((4 * lossCoefficient : ℕ) : ℝ) * (s : ℝ) *
              Real.logb 2 (A.card : ℝ) := by
          norm_num
          ring
    calc
      (loss : ℝ) ≤ ((4 * lossCoefficient : ℕ) : ℝ) *
          (s : ℝ) * Real.logb 2 (A.card : ℝ) :=
        hcastLoss.trans hscaledLog
      _ ≤ (lossConstant : ℝ) * (s : ℝ) *
          Real.logb 2 (A.card : ℝ) + 1 := by
        have hlogb : 0 ≤ Real.logb 2 (A.card : ℝ) := by
          rw [Real.logb]
          positivity
        have hconstant : (4 * lossCoefficient : ℕ) ≤ lossConstant :=
          le_max_left _ _
        have hconstantReal :
            ((4 * lossCoefficient : ℕ) : ℝ) ≤
              (lossConstant : ℝ) := by exact_mod_cast hconstant
        have hmul := mul_le_mul_of_nonneg_right hconstantReal
          (mul_nonneg (by positivity : (0 : ℝ) ≤ (s : ℝ)) hlogb)
        nlinarith

end

end Erdos186.CFP

#print axioms Erdos186.CFP.nonemptyIntegerTheorem15_of_largeInputLogLoss
