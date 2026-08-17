/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.RoughUpper

/-!
# Ordering the two central restricted-sum layers

This file supplies the finite ordering bridge between the
Deshouillers--Freiman structure theorem and the endpoint comparison used by
`central_span_finite`.

Write `B = A \ C` for the regular part, put `q` for the structural step, and
suppose that the first `2*k+q` elements of `B` exist.  The canonical
complementary chain from `RoughUpper` starts with

* the first `k+q` elements, and
* the following `k` elements.

If the first sum were not larger, the chain would cross zero.  Consecutive
quotients differ by fewer than twice the length of the short containing
progression.  A long `q`-progression in a restricted layer of `C` would then
translate two different positive restricted-sum layers of `A` to a common
integer, contradicting admissibility.  Thus the required endpoint comparison
is strict.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The finite layer-ordering consequence of the structural progression
data.  The left side is the sum of the last `k` entries among the first
`2*k+q` regular entries, while the right side is the sum of the first `k+q`
entries.  This is exactly the `hcompare` input of `central_span_finite`.

The theorem is stated using the fields of `LargeSetStructure` separately so
that it can also be reused by any later strengthening of that certificate. -/
theorem central_layer_ordering_of_long_progression
    {A C B : Finset ℤ} {start : ℤ} {t q L M k : ℕ}
    (hA : IsAdmissible A) (hCA : C ⊆ A) (hBsub : B ⊆ A \ C)
    (hBpos : ∀ x ∈ B, 0 < x)
    (ht : 0 < t) (hq : 0 < q) (hL : 0 < L)
    (hAP : ContainsAP (restrictedSumset t C) (q : ℤ) L)
    (hcontained : ContainedInAP B start q M)
    (hk : 0 < k) (hcard : 2 * k + q ≤ B.card)
    (hshortLong : 2 * M ≤ L) :
    ∑ i ∈ Finset.range k, roughEntry B (k + q + i) <
      ∑ i ∈ Finset.range (k + q), roughEntry B i := by
  let T : ℕ := 2 * k + q
  let U : ℕ := k + q
  have hT : T ≤ B.card := by
    simpa [T] using hcard
  have hU : U ≤ T := by
    dsimp [T, U]
    omega
  have hUT : U < T := by
    dsimp [T, U]
    omega
  have hTU : T + q = 2 * U := by
    dsimp [T, U]
    omega
  have hnot : ¬ roughQuotient B T U q hT hU 0 < L := by
    intro hstart
    exact no_df95_packing_window_of_endpoint
      (A := A) (C := C) (B := B) (start := start) (t := t) (q := q)
      (L := L) (M := M) (S := T) (U := U)
      hA hCA hBsub hBpos ht hq hL hAP hcontained hT hU hUT hTU
      hshortLong hstart
  have hquotient : 0 < roughQuotient B T U q hT hU 0 := by
    have hLle : (L : ℤ) ≤ roughQuotient B T U q hT hU 0 :=
      le_of_not_gt hnot
    have hLposZ : (0 : ℤ) < L := by exact_mod_cast hL
    exact hLposZ.trans_le hLle
  have hfactor := roughDelta_eq_step_mul_roughQuotient
    hT hU hq hTU hcontained (j := 0) (Nat.zero_le U)
  have hdelta : 0 < roughDelta B T U hT hU 0 := by
    have hqpos : (0 : ℤ) < q := by exact_mod_cast hq
    rw [hfactor]
    exact mul_pos hqpos hquotient
  rw [roughDelta_eq_chainValue B T U hT hU (j := 0) (Nat.zero_le U)] at hdelta
  have hsub : 2 * k + q - (k + q) = k := by omega
  simpa [chainValue, chainIndexSum, T, U, hsub] using hdelta

end

end Erdos874
