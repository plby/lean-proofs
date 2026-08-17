/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.FreimanDimension
import ErdosProblems.Erdos874.FreimanThreeKInductive

/-!
# Freiman's `3k - 4` theorem for integer finsets

This file contains the integer inverse theorem used in the
Deshouillers--Freiman restricted-sum progression argument.  The first lemmas
are the endpoint and affine-transport parts of the theorem.  They are stated
separately because the additive-combinatorial core naturally proves a bound
for the diameter of a normalized set.
-/

open scoped Pointwise

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Cardinality defects under a quotient map -/

/-- Restricting a function to a smaller finset cannot increase the
cardinality defect `|T| - |f(T)|`.  The subtraction-free formulation is the
one used after reducing an integer sumset modulo its diameter. -/
theorem card_image_add_card_le_card_add_card_image_of_subset
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (f : X → Y) {S T : Finset X} (hST : S ⊆ T) :
    (T.image f).card + S.card ≤ T.card + (S.image f).card := by
  have himage : T.image f ⊆ S.image f ∪ (T \ S).image f := by
    intro y hy
    obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hy
    by_cases hxS : x ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hxS, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hxT, hxS⟩, rfl⟩)
  have himageCard : (T.image f).card ≤
      (S.image f).card + (T \ S).card := by
    calc
      (T.image f).card ≤ (S.image f ∪ (T \ S).image f).card :=
        Finset.card_le_card himage
      _ ≤ (S.image f).card + ((T \ S).image f).card :=
        Finset.card_union_le _ _
      _ ≤ (S.image f).card + (T \ S).card :=
        Nat.add_le_add_left Finset.card_image_le _
  rw [Finset.card_sdiff_of_subset hST] at himageCard
  have hcardST := Finset.card_le_card hST
  omega

/-- An integer finset contained between two endpoints is contained in the
corresponding difference-one arithmetic progression. -/
theorem containedInAP_one_of_subset_Icc
    {A : Finset ℤ} {lo hi : ℤ} (hlohi : lo ≤ hi)
    (hA : A ⊆ Finset.Icc lo hi) :
    ContainedInAP A lo 1 (hi + 1 - lo).toNat := by
  refine ⟨by norm_num, ?_⟩
  intro x hx
  have hx' := Finset.mem_Icc.mp (hA hx)
  have hnonneg : 0 ≤ x - lo := by omega
  have htopnonneg : 0 ≤ hi + 1 - lo := by omega
  refine ⟨(x - lo).toNat, ?_, ?_⟩
  · have hlt : x - lo < hi + 1 - lo := by omega
    have hcast : ((x - lo).toNat : ℤ) = x - lo :=
      Int.toNat_of_nonneg hnonneg
    have htopcast : (((hi + 1 - lo).toNat : ℕ) : ℤ) = hi + 1 - lo :=
      Int.toNat_of_nonneg htopnonneg
    have hcastlt : ((x - lo).toNat : ℤ) <
        ((hi + 1 - lo).toNat : ℤ) := by
      simpa only [hcast, htopcast] using hlt
    exact_mod_cast hcastlt
  · rw [Int.toNat_of_nonneg hnonneg]
    norm_num

/-- Affine images by a positive integral dilation preserve concrete
arithmetic-progression containment. -/
theorem ContainedInAP.affineImage_nat
    {B : Finset ℤ} {start : ℤ} {step length g : ℕ}
    (hB : ContainedInAP B start step length) (hg : 0 < g) (c : ℤ) :
    ContainedInAP (B.image fun x ↦ c + (g : ℤ) * x)
      (c + (g : ℤ) * start) (g * step) length := by
  refine ⟨Nat.mul_pos hg hB.step_pos, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i, hi, hyrep⟩ := hB.exists_coordinate hy
  refine ⟨i, hi, ?_⟩
  rw [hyrep]
  push_cast
  ring

/-- Once the normalized additive argument has bounded the diameter, the
`3k - 4` progression conclusion is immediate. -/
theorem freiman_three_k_minus_four_of_interval_bound
    {A : Finset ℤ} {lo hi : ℤ} (hlohi : lo ≤ hi)
    (hA : A ⊆ Finset.Icc lo hi)
    (hdiam : (hi + 1 - lo).toNat ≤ (A + A).card - A.card + 1) :
    ContainedInAP A lo 1 ((A + A).card - A.card + 1) := by
  exact (containedInAP_one_of_subset_Icc hlohi hA).mono_length hdiam

/-! ## Freiman's inverse theorem -/

/-- **Freiman's `3k - 4` theorem over the integers.**

If an integer finset with `k ≥ 3` elements has ordinary doubling at most
`3k - 4`, it is contained in an arithmetic progression with exactly
`|A+A| - |A| + 1` displayed terms. -/
theorem freiman_three_k_minus_four
    {A : Finset ℤ} (hcard : 3 ≤ A.card)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    ∃ start : ℤ, ∃ step : ℕ,
      ContainedInAP A start step ((A + A).card - A.card + 1) :=
  freiman_three_k_minus_four_inductive hcard hsmall

/-- Canonical-start version of `freiman_three_k_minus_four`: the progression
starts at the least element and its step is the gcd of all differences from
that element. -/
theorem freiman_three_k_minus_four_explicit
    {A : Finset ℤ} (hA : A.Nonempty) (hcard : 3 ≤ A.card)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    ContainedInAP A (A.min' hA) (differenceContentAt A (A.min' hA))
      ((A + A).card - A.card + 1) :=
  freiman_three_k_minus_four_inductive_explicit hA hcard hsmall

/-! ## The numerical seam in the Deshouillers--Freiman application -/

/-- A pair-sum set occupying more than `1.96 L` values satisfies the
`3k - 4` threshold as soon as its double is bounded by `5.8 L`.

The deliberately explicit cutoff `50` absorbs the integral `-4` in the
conclusion.  This is the exact rational arithmetic needed when the popular
pair-sum set is extracted from a block of the original admissible set. -/
lemma card_add_self_le_three_mul_sub_four_of_popular
    {S : Finset ℤ} {L : ℕ} (hL : 50 ≤ L)
    (hpopular : 49 * L < 25 * S.card)
    (hsmall : 5 * (S + S).card ≤ 29 * L) :
    (S + S).card ≤ 3 * S.card - 4 := by
  omega

/-- Version of the numerical seam in which `S + S` is injected into a
fourth restricted layer. -/
lemma card_add_self_le_three_mul_sub_four_of_popular_of_subset_four
    {B S : Finset ℤ} {L : ℕ} (hL : 50 ≤ L)
    (hpopular : 49 * L < 25 * S.card)
    (hsubset : S + S ⊆ restrictedSumset 4 B)
    (hfour : 5 * (restrictedSumset 4 B).card ≤ 29 * L) :
    (S + S).card ≤ 3 * S.card - 4 := by
  apply card_add_self_le_three_mul_sub_four_of_popular hL hpopular
  have hcard := Finset.card_le_card hsubset
  omega

/-- The same two rational estimates also give the density needed after the
`3k - 4` theorem: its progression container has at most `1.97 |S|` terms.
This form deliberately keeps natural-number subtraction, matching the exact
container length in the inverse theorem. -/
lemma three_k_minus_four_length_le_of_popular
    {S : Finset ℤ} {L : ℕ} (hL : 50 ≤ L)
    (hpopular : 49 * L < 25 * S.card)
    (hsmall : 5 * (S + S).card ≤ 29 * L) :
    100 * ((S + S).card - S.card + 1) ≤ 197 * S.card := by
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨s, hs⟩ := hSne
  have hcard : S.card ≤ (S + S).card := by
    refine Finset.card_le_card_of_injOn (fun x : ℤ ↦ x + s) ?_ ?_
    · intro x hx
      exact Finset.mem_add.mpr ⟨x, hx, s, hs, rfl⟩
    · intro x _ y _ hxy
      exact add_right_cancel hxy
  omega

/-- Restricted-four-layer version of the `1.97 |S|` container estimate. -/
lemma three_k_minus_four_length_le_of_popular_of_subset_four
    {B S : Finset ℤ} {L : ℕ} (hL : 50 ≤ L)
    (hpopular : 49 * L < 25 * S.card)
    (hsubset : S + S ⊆ restrictedSumset 4 B)
    (hfour : 5 * (restrictedSumset 4 B).card ≤ 29 * L) :
    100 * ((S + S).card - S.card + 1) ≤ 197 * S.card := by
  apply three_k_minus_four_length_le_of_popular hL hpopular
  have hcard := Finset.card_le_card hsubset
  omega

/-- Fully assembled `3k - 4` output for the popular-pair-sum construction:
`S` lies in a positive-step progression of its exact Freiman length, and that
length is at most `1.97 |S|`. -/
theorem exists_dense_AP_container_of_popular_pair_sums
    {B S : Finset ℤ} {L : ℕ} (hL : 50 ≤ L)
    (hpopular : 49 * L < 25 * S.card)
    (hsubset : S + S ⊆ restrictedSumset 4 B)
    (hfour : 5 * (restrictedSumset 4 B).card ≤ 29 * L) :
    ∃ start : ℤ, ∃ step : ℕ,
      ContainedInAP S start step ((S + S).card - S.card + 1) ∧
        100 * ((S + S).card - S.card + 1) ≤ 197 * S.card := by
  have hScard : 3 ≤ S.card := by omega
  have hsmall : (S + S).card ≤ 3 * S.card - 4 :=
    card_add_self_le_three_mul_sub_four_of_popular_of_subset_four
      hL hpopular hsubset hfour
  obtain ⟨start, step, hAP⟩ := freiman_three_k_minus_four hScard hsmall
  exact ⟨start, step, hAP,
    three_k_minus_four_length_le_of_popular_of_subset_four
      hL hpopular hsubset hfour⟩


end

end Erdos874
