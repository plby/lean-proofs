/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRandomAugmentation

/-! # Polynomial index coefficient and positive-probability random augmentation -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceRandomFailureCoefficient_le_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) (hj : 4 ≤ j) :
    sourceRandomFailureCoefficient W j ≤ (j + 3) * (Fintype.card V + 1) ^ (3 * j + 6) := by
  let N := Fintype.card V
  let d := 3 * j + 6
  let b := (N + 1) ^ d
  have hbase : 1 ≤ N + 1 := by omega
  have hn : W.terminalSize ≤ N := card_le_univ _
  have hcube : W.terminalSize ^ 3 + 1 ≤ (N + 1) ^ 3 := by
    apply (Nat.add_le_add_right (Nat.pow_le_pow_left hn 3) 1).trans
    nlinarith
  have hroot : (sourceRandomRootIndex W j).card ≤ (j - 1) * b := by
    have h := card_subsetsUpToCard_le (triplesSupportedOn (W.U (Fin.last ell))) (j - 2)
    calc
      _ ≤ (j - 2 + 1) * ((triplesSupportedOn (W.U (Fin.last ell))).card + 1) ^ (j - 2) := h
      _ ≤ (j - 1) * (W.terminalSize ^ 3 + 1) ^ (j - 2) := by
        rw [show j - 2 + 1 = j - 1 by omega]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
          (Nat.add_le_add_right (card_triplesSupportedOn_le_cube _) 1) _)
      _ ≤ (j - 1) * ((N + 1) ^ 3) ^ (j - 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcube _)
      _ = (j - 1) * (N + 1) ^ (3 * (j - 2)) := by rw [pow_mul]
      _ ≤ (j - 1) * b := Nat.mul_le_mul_left _ (pow_le_pow_right₀ hbase (by dsimp only [d]; omega))
  have htriple : Fintype.card (TripleOn V) ≤ N ^ 3 := by
    rw [Fintype.card_finset_len]
    exact Nat.choose_le_pow _ _
  have hpair : Fintype.card (VortexPairOn V) ≤ N ^ 2 := by
    rw [Fintype.card_finset_len]
    exact Nat.choose_le_pow _ _
  have hpow (r : ℕ) (hr : r ≤ d) : N ^ r ≤ b :=
    (Nat.pow_le_pow_left (Nat.le_succ N) r).trans (pow_le_pow_right₀ hbase hr)
  have htwo : Fintype.card (TripleOn V × TripleOn V) ≤ b := by
    rw [Fintype.card_prod]
    calc
      _ ≤ N ^ 3 * N ^ 3 := Nat.mul_le_mul htriple htriple
      _ = N ^ 6 := by ring
      _ ≤ b := hpow 6 (by dsimp only [d]; omega)
  have hthree : Fintype.card (TripleOn V × VortexPairOn V) ≤ b := by
    rw [Fintype.card_prod]
    calc
      _ ≤ N ^ 3 * N ^ 2 := Nat.mul_le_mul htriple hpair
      _ = N ^ 5 := by ring
      _ ≤ b := hpow 5 (by dsimp only [d]; omega)
  calc
    _ ≤ (j - 1) * b + 3 * b + b := Nat.add_le_add (Nat.add_le_add hroot (Nat.mul_le_mul_left _ htwo)) hthree
    _ = (j + 3) * b := by
      have hj' : j = (j - 1) + 1 := by omega
      nth_rewrite 2 [hj']
      ring

namespace SourceRandomConfigurationParameters

variable {V : Type*} [Fintype V] [DecidableEq V] {ell j s : ℕ}
  {W : Vortex V ell} {delta a : ℝ≥0}

theorem augmentation_failure_probability_polynomial
    (P : SourceRandomConfigurationParameters W j delta a s)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    P.law.probability (fun ω ↦ ¬ SourceVortexWellSpread W j
      (F ∪ sampleTerminalConfigurations W j ω) (y + a) (z + 3 * a)) ≤
        (j + 3 : ℕ) * (Fintype.card V + 1 : ℕ) ^ (3 * j + 6) * ((2 : ℝ≥0) ^ s)⁻¹ := by
  apply (P.augmentation_failure_probability F y z hF hdeltaY).trans
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact_mod_cast sourceRandomFailureCoefficient_le_polynomial W j P.order

theorem exists_supported_augmentation
    (P : SourceRandomConfigurationParameters W j delta a s)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize)
    (hsmall : (sourceRandomFailureCoefficient W j : ℝ≥0) * ((2 : ℝ≥0) ^ s)⁻¹ < 1) :
    ∃ ω, 0 < P.law.mass ω ∧ SourceVortexWellSpread W j
      (F ∪ sampleTerminalConfigurations W j ω) (y + a) (z + 3 * a) := by
  have hbad := (P.augmentation_failure_probability F y z hF hdeltaY).trans_lt hsmall
  apply P.law.exists_supported_of_probability_pos
  by_contra hnot
  have hzero : P.law.probability (fun ω ↦ SourceVortexWellSpread W j
      (F ∪ sampleTerminalConfigurations W j ω) (y + a) (z + 3 * a)) = 0 :=
    le_antisymm (not_lt.mp hnot) zero_le
  rw [FiniteLaw.probability_not, hzero, tsub_zero] at hbad
  exact (lt_irrefl 1 hbad)

end SourceRandomConfigurationParameters

end

end Erdos207
