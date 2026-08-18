/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.IntegerTheoremAssembly
import ErdosProblems.Erdos186.CFP.TrivialEnhancedWitness

/-!
# Large-input terminal reduction for the integer CFP theorem

The random-partition/greedy/dense-box construction is asymptotic and its
finite bookkeeping naturally returns a loss bounded by a fixed natural
multiple of the reserve scale.  This module removes both presentational
issues from that construction: bounded inputs are handled by the existing
rank-zero witness, and the natural large-input loss is converted to the
source-facing binary-logarithmic estimate.
-/

namespace Erdos186.CFP

noncomputable section

/-- Exact large-input output required from the concrete CFP construction.
All constants precede the input set.  Unlike an approximation or coverage
certificate, this is already a fixed-scale witness statement; it merely
uses the natural loss form produced by finite bookkeeping and is restricted
to cardinality above a fixed cutoff. -/
def LargeInputNonemptyIntegerTheorem15 : Prop :=
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
          loss ≤ lossCoefficient * s

/-- With the stable deletion budget chosen as `s / (log₂ m + 1)`, the
deterministic preprocessing loss is a fixed multiple of `s`.  The multiplier
depends only on the rank cutoff and on the uniform comparison between the
preprocessing horizon and the source cardinality. -/
theorem preprocessingCardinalityLoss_le_scale
    {A : Finset ℤ} {n m s D horizonCoefficient : ℕ}
    (hzero : 0 ∈ A)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hlog : Nat.log 2 n + 1 ≤
      horizonCoefficient * (Nat.log 2 m + 1)) :
    preprocessingCardinalityLoss A (s / (Nat.log 2 m + 1)) D ≤
      (6 * D * horizonCoefficient + 1) * s := by
  let ell := Nat.log 2 m + 1
  let q := s / ell
  have hbox₀ := Preprocessing.boxPotential_le
    (A := A) (n := n) (maxRank := D) hzero hA
  have hbox : Preprocessing.boxPotential A D ≤
      3 * D * horizonCoefficient * ell := by
    calc
      Preprocessing.boxPotential A D ≤
          D * (3 * (Nat.log 2 n + 1)) := hbox₀
      _ ≤ D * (3 * (horizonCoefficient * ell)) := by gcongr
      _ = 3 * D * horizonCoefficient * ell := by ring
  have hqell : q * ell ≤ s := Nat.div_mul_le_self s ell
  have hq : q ≤ s := Nat.div_le_self _ _
  change (2 * q) * Preprocessing.boxPotential A D + q ≤ _
  calc
    (2 * q) * Preprocessing.boxPotential A D + q ≤
        (2 * q) * (3 * D * horizonCoefficient * ell) + q := by gcongr
    _ = (6 * D * horizonCoefficient) * (q * ell) + q := by ring
    _ ≤ (6 * D * horizonCoefficient) * s + s := by gcongr
    _ = (6 * D * horizonCoefficient + 1) * s := by ring

/-- A nonempty integer set remains nonempty after the canonical embedding
in the one-dimensional lattice. -/
theorem integerPoints_nonempty {A : Finset ℤ} (hA : A.Nonempty) :
    (integerPoints A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨integerPoint a, mem_integerPoints_iff.mpr ha⟩

/-- The bounded-input branch and the logarithm cast turn the concrete
large-input theorem into the exact source-facing corrected Theorem 1.5. -/
theorem nonemptyIntegerTheorem15_of_largeInput
    (hlarge : LargeInputNonemptyIntegerTheorem15) :
    NonemptyIntegerTheorem15 := by
  intro β η hβ hη hη1
  obtain ⟨scaleNum, scaleDen, D, lossCoefficient, cutoff,
      hnum, hden, hscale, hlossCoefficient, hcutoff, hout⟩ :=
    hlarge β η hβ hη hη1
  let lossConstant := max lossCoefficient cutoff
  have hlossConstant : 0 < lossConstant :=
    hlossCoefficient.trans_le (le_max_left _ _)
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
        (le_max_right lossCoefficient cutoff)
    simpa only [lossConstant, card_integerPoints] using
      exists_fixedScaleWitness_of_card_le
        (integerPoints A) s D scaleNum scaleDen lossConstant
        (integerPoints_nonempty hA) hs hnum hden hscale hcardLoss
  · have hcutoffA : cutoff ≤ A.card := by omega
    obtain ⟨k, loss, hW, hloss⟩ :=
      hout n A s hA hcutoffA hAinterval hn hslow hscaleCard
    refine ⟨k, loss, hW, ?_⟩
    have hlossNat : loss ≤ lossConstant * s := by
      exact hloss.trans
        (Nat.mul_le_mul_right s (le_max_left lossCoefficient cutoff))
    have hcardTwo : 2 ≤ A.card := hcutoff.trans hcutoffA
    calc
      (loss : ℝ) ≤ ((lossConstant * s : ℕ) : ℝ) := by exact_mod_cast hlossNat
      _ ≤ (lossConstant : ℝ) * (s : ℝ) *
          Real.logb 2 (A.card : ℝ) + 1 :=
        IntegerTheoremAssembly.natCoefficient_mul_scale_le_logb_loss
          lossConstant s A.card hcardTwo

end

end Erdos186.CFP

#print axioms Erdos186.CFP.nonemptyIntegerTheorem15_of_largeInput
