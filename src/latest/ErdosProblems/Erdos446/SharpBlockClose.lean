/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.BlockCloseBounds

/-!
# Erdős Problem 446: diagonal-sharp close-pair mass

For the union-density lower bound it is convenient to absorb the diagonal
close-pair contribution into `compositionPenalty`.  The isolated-divisor
argument cannot afford that loss.  This module keeps the diagonal term
separate and exports the sharper estimate already implicit in the slot
calculation.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Sharp version of `compositionBlockFamily_closeWeight_upper`: the
diagonal costs one copy of the ideal block mass, while only the off-diagonal
term is multiplied by `compositionPenalty`. -/
theorem compositionBlockFamily_closeWeight_upper_sharp
    {N M K : ℕ} {C E : ℝ}
    (hM : 1 ≤ M) (hK : 0 < K) (hC : 0 ≤ C)
    {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hhalf : ∀ i : Fin K,
      Real.log 2 / 2 ≤ primeBlockMass (M + i))
    (hE : 4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ E)
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin K, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ)) :
    compositionFactorial b *
        (∑ a ∈ compositionBlockFamily M b,
          (closePairCount a : ℝ) / a) ≤
      (2 * Real.log 2 : ℝ) ^ K * Real.exp E *
        (1 + (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) *
          compositionPenalty b) := by
  let Base : ℝ := (2 * Real.log 2 : ℝ) ^ K * Real.exp E
  let Q : ℝ := 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfull := slotMassProduct_upper hM hC hb hmass hE
  have haway := slotMassProductAway_upper hM hK hC hb hmass hhalf hE
  have hexact := blockFamily_closeWeight_upper_exact
    (N := N) (M := M) (k := K) (b := extendComposition b)
    hN hendpoint hprime
  rw [slotCount_extendComposition_of_mem hb] at hexact
  have hdiag :
      (2 : ℝ) ^ K *
          (∏ s : BlockSlot K (extendComposition b),
            primeBlockMass (M + s.1)) ≤ Base := by
    calc
      (2 : ℝ) ^ K *
          (∏ s : BlockSlot K (extendComposition b),
            primeBlockMass (M + s.1)) ≤
          (2 : ℝ) ^ K * (Real.log 2 ^ K * Real.exp E) :=
        mul_le_mul_of_nonneg_left hfull (by positivity)
      _ = Base := by
        dsimp [Base]
        rw [mul_pow]
        ring
  have hterm : ∀ s : BlockSlot K (extendComposition b),
      (2 : ℝ) ^
          (K +
            ((∑ i ∈ Finset.range s.1.val, extendComposition b i) +
              s.2.val) + 1) *
          ((∏ t : {t : BlockSlot K (extendComposition b) // t ≠ s},
              primeBlockMass (M + t.1.1)) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) ≤
        (Base * (14 / Real.log 2 ^ 2)) *
          ((2 : ℝ) ^
              ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) /
            (2 : ℝ) ^ (M + s.1.val)) := by
    intro s
    have hpref := sum_range_extendComposition_eq_sum_Iio b s.1
    have ha := haway s
    have hlogEndpoint := log_blockEndpoint (M + s.1.val)
    have hpowers :
        (2 : ℝ) ^
            (K +
              ((∑ i ∈ Finset.range s.1.val, extendComposition b i) +
                s.2.val) + 1) =
          (2 : ℝ) ^ K *
            (2 : ℝ) ^
              ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) := by
      rw [hpref]
      rw [show K + ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val) + 1 =
        K + ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) by omega,
        pow_add]
    rw [hpowers, hlogEndpoint]
    have hpow0 : 0 ≤ (2 : ℝ) ^ K *
        (2 : ℝ) ^ ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) := by
      positivity
    calc
      ((2 : ℝ) ^ K *
            (2 : ℝ) ^
              ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1)) *
          ((∏ t : {t : BlockSlot K (extendComposition b) // t ≠ s},
              primeBlockMass (M + t.1.1)) *
            (7 / ((2 : ℝ) ^ (M + s.1.val) * Real.log 2))) ≤
        ((2 : ℝ) ^ K *
            (2 : ℝ) ^
              ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1)) *
          ((2 * Real.log 2 ^ (K - 1) * Real.exp E) *
            (7 / ((2 : ℝ) ^ (M + s.1.val) * Real.log 2))) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_right ha
          positivity
        · exact hpow0
      _ = (Base * (14 / Real.log 2 ^ 2)) *
          ((2 : ℝ) ^
              ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) /
            (2 : ℝ) ^ (M + s.1.val)) := by
        dsimp [Base]
        have hpowK : Real.log 2 ^ K =
            Real.log 2 * Real.log 2 ^ (K - 1) := by
          calc
            Real.log 2 ^ K = Real.log 2 ^ ((K - 1) + 1) := by
              congr 1 <;> omega
            _ = Real.log 2 ^ (K - 1) * Real.log 2 := by rw [pow_succ]
            _ = _ := by ring
        rw [mul_pow, hpowK]
        field_simp [hlog.ne']
        ring
  have hnondiag :
      (∑ s : BlockSlot K (extendComposition b),
        (2 : ℝ) ^
          (K +
            ((∑ i ∈ Finset.range s.1.val, extendComposition b i) +
              s.2.val) + 1) *
          ((∏ t : {t : BlockSlot K (extendComposition b) // t ≠ s},
              primeBlockMass (M + t.1.1)) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ)))) ≤
        Base * Q * compositionPenalty b := by
    calc
      _ ≤ ∑ s : BlockSlot K (extendComposition b),
          (Base * (14 / Real.log 2 ^ 2)) *
            ((2 : ℝ) ^
                ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) /
              (2 : ℝ) ^ (M + s.1.val)) :=
        Finset.sum_le_sum fun s hs ↦ hterm s
      _ = (Base * (14 / Real.log 2 ^ 2)) *
          (∑ s : BlockSlot K (extendComposition b),
            (2 : ℝ) ^
                ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) /
              (2 : ℝ) ^ (M + s.1.val)) := by rw [Finset.mul_sum]
      _ ≤ (Base * (14 / Real.log 2 ^ 2)) *
          ((4 / (2 : ℝ) ^ M) * compositionPenalty b) := by
        apply mul_le_mul_of_nonneg_left (closeExponentSum_le_penalty b)
        positivity
      _ = Base * Q * compositionPenalty b := by
        dsimp [Q]
        field_simp [hlog.ne']
        ring
  change compositionFactorial b *
      (∑ a ∈ blockFamily M K (extendComposition b),
        (closePairCount a : ℝ) / a) ≤ _
  calc
    compositionFactorial b *
        (∑ a ∈ blockFamily M K (extendComposition b),
          (closePairCount a : ℝ) / a) ≤
      (2 : ℝ) ^ K *
          (∏ s : BlockSlot K (extendComposition b),
            primeBlockMass (M + s.1)) +
        ∑ s : BlockSlot K (extendComposition b),
          (2 : ℝ) ^
            (K +
              ((∑ i ∈ Finset.range s.1.val, extendComposition b i) +
                s.2.val) + 1) *
            ((∏ t : {t : BlockSlot K (extendComposition b) // t ≠ s},
                primeBlockMass (M + t.1.1)) *
              (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) := by
      simpa only [compositionFactorial, extendComposition_fin] using hexact
    _ ≤ Base + Base * Q * compositionPenalty b := add_le_add hdiag hnondiag
    _ = Base * (1 + Q * compositionPenalty b) := by ring
    _ = (2 * Real.log 2 : ℝ) ^ K * Real.exp E *
        (1 + (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)) *
          compositionPenalty b) := by rfl

end Erdos446
