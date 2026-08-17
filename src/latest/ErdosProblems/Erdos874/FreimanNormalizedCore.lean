/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.FreimanNormalization
import ErdosProblems.Erdos874.LevSmelianski

/-!
# The normalized arithmetic core of Freiman's `3k - 4` theorem

This file isolates the last, purely numerical step in the normalized form of
Freiman's theorem.  For a normalized set `B ⊆ [0,n]` containing both
endpoints and having content one, the Lev--Smelianski sumset estimate gives

`min (n + |B|) (3|B| - 3) ≤ |B + B|`.

Under the small-doubling hypothesis `|B + B| ≤ 3|B| - 4`, the second
alternative is impossible.  Consequently `n + |B| ≤ |B + B|`, which is
exactly the endpoint/length inequality needed in the `3k - 4` theorem.

The additive-combinatorial estimate itself is developed in
`LevSmelianski.lean`; keeping this numerical implication separate makes the
subtraction conventions on natural-number cardinalities explicit.
-/

open scoped Pointwise

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The Lev--Smelianski self-sum estimate -/

/-- Integer-coordinate form of `lev_smelianski_self_sum`.  The content
hypothesis is the gcd of the absolute offsets from zero; this is the form
naturally produced by affine normalization of an integer finset. -/
theorem lev_smelianski_self_sum_int
    {B : Finset ℤ} {q : ℕ}
    (hB0 : 0 ∈ B) (hqB : (q : ℤ) ∈ B)
    (hBbounds : ∀ z ∈ B, 0 ≤ z ∧ z ≤ (q : ℤ))
    (hcontent : differenceContentAt B 0 = 1)
    (hcard : 3 ≤ B.card) :
    min (q + B.card) (3 * B.card - 3) ≤ (B + B).card := by
  have hBnonneg : ∀ z ∈ B, 0 ≤ z := fun z hz ↦ (hBbounds z hz).1
  have hBupper : ∀ z ∈ B, z ≤ (q : ℤ) := fun z hz ↦ (hBbounds z hz).2
  have hnat := lev_smelianski_self_sum (natify B)
    (zero_mem_natify hBnonneg hB0)
    ((mem_natify_iff hBnonneg).2 hqB)
    (fun _ hn ↦ natify_le hBnonneg hBupper hn)
    (gcd_natify_eq_one hBnonneg hcontent)
    (by simpa only [card_natify hBnonneg] using hcard)
  simpa only [card_natify hBnonneg, card_add_natify hBnonneg] using hnat

/-- Adapter using the equivalent `Finset.gcd Int.natAbs = 1` formulation.
This is convenient for clients which have already simplified the base point
zero out of `differenceContentAt`. -/
theorem lev_smelianski_self_sum_int_gcd
    {B : Finset ℤ} {q : ℕ}
    (hB0 : 0 ∈ B) (hqB : (q : ℤ) ∈ B)
    (hBbounds : ∀ z ∈ B, 0 ≤ z ∧ z ≤ (q : ℤ))
    (hgcd : B.gcd Int.natAbs = 1)
    (hcard : 3 ≤ B.card) :
    min (q + B.card) (3 * B.card - 3) ≤ (B + B).card := by
  apply lev_smelianski_self_sum_int hB0 hqB hBbounds
  · simpa only [differenceContentAt, sub_zero] using hgcd
  · exact hcard

/-- The numerical heart of the normalized `3k - 4` argument.

The hypothesis `hlower` is the self-sum specialization of the
Lev--Smelianski inequality.  The explicit `3 ≤ |B|` assumption makes the
natural-number truncated subtractions agree with the customary integer
formulas. -/
theorem normalized_three_k_minus_four_of_self_sum_lower
    {B : Finset ℤ} {n : ℕ}
    (hcard : 3 ≤ B.card)
    (hlower : min (n + B.card) (3 * B.card - 3) ≤ (B + B).card)
    (hsmall : (B + B).card ≤ 3 * B.card - 4) :
    n + 1 ≤ (B + B).card - B.card + 1 := by
  rw [min_le_iff] at hlower
  rcases hlower with hdiam | hthree
  · omega
  · omega

/-- Equivalent subtraction-free form of the numerical core. -/
theorem normalized_three_k_minus_four_diameter_of_self_sum_lower
    {B : Finset ℤ} {n : ℕ}
    (hcard : 3 ≤ B.card)
    (hlower : min (n + B.card) (3 * B.card - 3) ≤ (B + B).card)
    (hsmall : (B + B).card ≤ 3 * B.card - 4) :
    n + B.card ≤ (B + B).card := by
  rw [min_le_iff] at hlower
  rcases hlower with hdiam | hthree
  · exact hdiam
  · omega

/-! ## The concrete normalized `3k - 4` bound -/

/-- Freiman's `3k - 4` diameter bound for a primitive integer set in
normalized position.  The hypotheses say exactly that `B` lies in `[0,n]`,
contains both endpoints, and has gcd/content one. -/
theorem normalized_three_k_minus_four
    {B : Finset ℤ} {n : ℕ}
    (hB0 : 0 ∈ B) (hnB : (n : ℤ) ∈ B)
    (hBsub : B ⊆ Finset.Icc 0 (n : ℤ))
    (hcontent : differenceContentAt B 0 = 1)
    (hcard : 3 ≤ B.card)
    (hsmall : (B + B).card ≤ 3 * B.card - 4) :
    n + 1 ≤ (B + B).card - B.card + 1 := by
  have hBbounds : ∀ z ∈ B, 0 ≤ z ∧ z ≤ (n : ℤ) := by
    intro z hz
    exact Finset.mem_Icc.mp (hBsub hz)
  have hlower := lev_smelianski_self_sum_int
    hB0 hnB hBbounds hcontent hcard
  exact normalized_three_k_minus_four_of_self_sum_lower hcard hlower hsmall

/-- Subtraction-free version of `normalized_three_k_minus_four`. -/
theorem normalized_three_k_minus_four_diameter
    {B : Finset ℤ} {n : ℕ}
    (hB0 : 0 ∈ B) (hnB : (n : ℤ) ∈ B)
    (hBsub : B ⊆ Finset.Icc 0 (n : ℤ))
    (hcontent : differenceContentAt B 0 = 1)
    (hcard : 3 ≤ B.card)
    (hsmall : (B + B).card ≤ 3 * B.card - 4) :
    n + B.card ≤ (B + B).card := by
  have hBbounds : ∀ z ∈ B, 0 ≤ z ∧ z ≤ (n : ℤ) := by
    intro z hz
    exact Finset.mem_Icc.mp (hBsub hz)
  have hlower := lev_smelianski_self_sum_int
    hB0 hnB hBbounds hcontent hcard
  exact normalized_three_k_minus_four_diameter_of_self_sum_lower
    hcard hlower hsmall

end

end Erdos874
