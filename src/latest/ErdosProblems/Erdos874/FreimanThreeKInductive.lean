/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.FreimanNormalization
import ErdosProblems.Erdos874.FreimanNormalizedCore
import ErdosProblems.Erdos13.Erdos13Additive

/-!
# An endpoint-normalized proof of Freiman's `3k - 4` theorem

This file packages the classical integer theorem in the concrete
`ContainedInAP` interface used by the Erdős 874 development.  The proof
normalizes at the least element, applies the sharp normalized self-sum bound,
and then reconstructs the original set.  Keeping the least element and the
content explicit gives a slightly stronger conclusion than a bare existential
arithmetic-progression cover.
-/

open scoped Pointwise

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A finset between two integer endpoints lies in the corresponding
difference-one progression.  This elementary endpoint lemma is kept local so
the proof below is independent of the other `3k - 4` packaging module. -/
private theorem containedInAP_one_of_subset_Icc_inductive
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

/-! ## The sharp normalized self-sum estimate

The repository already contains Ruzsa's two-set normalized diameter theorem,
proved from the modular fiber decomposition and Kneser's theorem.  The next
lemma is its self-sum specialization, transported from nonnegative integers to
naturals.  This gives an independent route to the exact input required below.
-/

/-- A primitive nonnegative integer set containing both endpoints satisfies
the sharp Freiman lower bound
`min (q + |B|) (3|B| - 3) ≤ |B+B|`. -/
theorem lev_smelianski_self_sum_inductive
    {B : Finset ℤ} {q : ℕ}
    (hzero : 0 ∈ B) (htop : (q : ℤ) ∈ B)
    (hbounds : ∀ z ∈ B, 0 ≤ z ∧ z ≤ (q : ℤ))
    (hgcd : B.gcd Int.natAbs = 1) (hcard : 3 ≤ B.card) :
    min (q + B.card) (3 * B.card - 3) ≤ (B + B).card := by
  let C := natify B
  have hBnonneg : ∀ z ∈ B, 0 ≤ z := fun z hz ↦ (hbounds z hz).1
  have hCcard : C.card = B.card := by
    simpa [C] using card_natify hBnonneg
  have hCsub : C ⊆ Finset.Icc 0 q := by
    intro n hn
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.zero_le n, ?_⟩
    exact natify_le hBnonneg (fun z hz ↦ (hbounds z hz).2) (by simpa [C] using hn)
  have hCzero : 0 ∈ C := by
    simpa [C] using zero_mem_natify hBnonneg hzero
  have hCtop : q ∈ C := by
    apply (mem_natify_iff hBnonneg).2
    simpa [C] using htop
  have hqpos : 0 < q := by
    by_contra hq
    have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq
    subst q
    have hle := Finset.card_le_card hCsub
    have : C.card ≤ 1 := by simpa using hle
    omega
  have hcontent : differenceContentAt B 0 = 1 := by
    simpa only [differenceContentAt, sub_zero] using hgcd
  have hCgcdNat : C.gcd id = 1 := by
    simpa [C] using gcd_natify_eq_one hBnonneg hcontent
  have hCgcdInt : C.gcd (fun n ↦ (n : ℤ)) = 1 := by
    rw [Erdos13Additive.nat_int_finset_gcd]
    exact_mod_cast hCgcdNat
  have hUnionGcd : (C ∪ C).gcd (fun n ↦ (n : ℤ)) = 1 := by
    simpa using hCgcdInt
  have hruzsa := Erdos13Additive.ruzsa_normalized_diameter_bound
    hCsub hCsub (le_refl q) hqpos hCzero hCtop hCzero hCtop hUnionGcd
  have hCsum : (C + C).card = (B + B).card := by
    simpa [C] using card_add_natify hBnonneg
  rw [hCcard, hCsum] at hruzsa
  simp only [min_self] at hruzsa
  convert hruzsa using 1 <;> omega

/-- The endpoint-normalized form of Freiman's `3k - 4` theorem.  The common
difference in the resulting progression is the gcd of the differences from
the least element of `A`. -/
theorem freiman_three_k_minus_four_inductive_explicit_of_self_sum_lower
    {A : Finset ℤ} (hA : A.Nonempty) (hcard : 3 ≤ A.card)
    (hsmall : (A + A).card ≤ 3 * A.card - 4)
    (hself : ∀ {B : Finset ℤ} {q : ℕ},
      0 ∈ B → (q : ℤ) ∈ B →
      (∀ z ∈ B, 0 ≤ z ∧ z ≤ (q : ℤ)) →
      B.gcd Int.natAbs = 1 → 3 ≤ B.card →
      min (q + B.card) (3 * B.card - 3) ≤ (B + B).card) :
    ContainedInAP A (A.min' hA) (differenceContentAt A (A.min' hA))
      ((A + A).card - A.card + 1) := by
  let B := freimanNormalize A hA
  have hcard2 : 2 ≤ A.card := by omega
  have hBcard : B.card = A.card := by
    simpa [B] using card_freimanNormalize hA hcard2
  have hBcard3 : 3 ≤ B.card := by omega
  have hBzero : 0 ∈ B := by
    simpa [B] using zero_mem_freimanNormalize hA
  have hBnonneg : ∀ z ∈ B, 0 ≤ z := by
    intro z hz
    exact freimanNormalize_nonneg hA (by simpa [B] using hz)
  have hBne : B.Nonempty := ⟨0, hBzero⟩
  let top : ℤ := B.max' hBne
  let q : ℕ := top.toNat
  have htop_mem : top ∈ B := by
    exact Finset.max'_mem B hBne
  have htop_nonneg : 0 ≤ top := hBnonneg top htop_mem
  have hqcast : (q : ℤ) = top := by
    simpa [q] using Int.toNat_of_nonneg htop_nonneg
  have hq_mem : (q : ℤ) ∈ B := by
    simpa only [hqcast] using htop_mem
  have hBbounds : ∀ z ∈ B, 0 ≤ z ∧ z ≤ (q : ℤ) := by
    intro z hz
    refine ⟨hBnonneg z hz, ?_⟩
    rw [hqcast]
    exact Finset.le_max' B z hz
  have hBgcd : B.gcd Int.natAbs = 1 := by
    have hcontent := differenceContentAt_freimanNormalize_eq_one hA hcard2
    simpa only [B, differenceContentAt, sub_zero] using hcontent
  have hlower :
      min (q + B.card) (3 * B.card - 3) ≤ (B + B).card :=
    hself hBzero hq_mem hBbounds hBgcd hBcard3
  have hBsum : (B + B).card = (A + A).card := by
    simpa [B] using card_add_freimanNormalize hA hcard2
  have hBsmall : (B + B).card ≤ 3 * B.card - 4 := by
    omega
  have hlen : q + 1 ≤ (B + B).card - B.card + 1 :=
    normalized_three_k_minus_four_of_self_sum_lower hBcard3 hlower hBsmall
  have hBsubset : B ⊆ Finset.Icc (0 : ℤ) (q : ℤ) := by
    intro z hz
    exact Finset.mem_Icc.mpr (hBbounds z hz)
  have hq_nonneg : (0 : ℤ) ≤ (q : ℤ) := by positivity
  have hbase : ContainedInAP B 0 1 q.succ := by
    have h := containedInAP_one_of_subset_Icc_inductive hq_nonneg hBsubset
    simpa [Nat.succ_eq_add_one] using h
  have hnormalized :
      ContainedInAP B 0 1 ((B + B).card - B.card + 1) :=
    hbase.mono_length (by simpa [Nat.succ_eq_add_one] using hlen)
  have hdenormalized :=
    hnormalized.denormalize_min hA hcard2
  simpa only [B, mul_zero, add_zero, Nat.mul_one, hBsum, hBcard] using
    hdenormalized

/-- Freiman's `3k - 4` theorem in the existential form: a finite integer set
with at least three elements and doubling at most `3|A|-4` is contained in an
arithmetic progression having exactly `|A+A|-|A|+1` displayed terms. -/
theorem freiman_three_k_minus_four_inductive_of_self_sum_lower
    {A : Finset ℤ} (hcard : 3 ≤ A.card)
    (hsmall : (A + A).card ≤ 3 * A.card - 4)
    (hself : ∀ {B : Finset ℤ} {q : ℕ},
      0 ∈ B → (q : ℤ) ∈ B →
      (∀ z ∈ B, 0 ≤ z ∧ z ≤ (q : ℤ)) →
      B.gcd Int.natAbs = 1 → 3 ≤ B.card →
      min (q + B.card) (3 * B.card - 3) ≤ (B + B).card) :
    ∃ start : ℤ, ∃ step : ℕ,
      ContainedInAP A start step ((A + A).card - A.card + 1) := by
  let hA : A.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨A.min' hA, differenceContentAt A (A.min' hA),
    freiman_three_k_minus_four_inductive_explicit_of_self_sum_lower
      hA hcard hsmall hself⟩

/-- Explicit endpoint-and-content form of Freiman's `3k - 4` theorem, with
no additional hypotheses beyond small doubling. -/
theorem freiman_three_k_minus_four_inductive_explicit
    {A : Finset ℤ} (hA : A.Nonempty) (hcard : 3 ≤ A.card)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    ContainedInAP A (A.min' hA) (differenceContentAt A (A.min' hA))
      ((A + A).card - A.card + 1) := by
  apply freiman_three_k_minus_four_inductive_explicit_of_self_sum_lower
    hA hcard hsmall
  intro B q hzero htop hbounds hgcd hBcard
  exact lev_smelianski_self_sum_inductive hzero htop hbounds hgcd hBcard

/-- Freiman's `3k - 4` theorem for finite integer finsets. -/
theorem freiman_three_k_minus_four_inductive
    {A : Finset ℤ} (hcard : 3 ≤ A.card)
    (hsmall : (A + A).card ≤ 3 * A.card - 4) :
    ∃ start : ℤ, ∃ step : ℕ,
      ContainedInAP A start step ((A + A).card - A.card + 1) := by
  let hA : A.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨A.min' hA, differenceContentAt A (A.min' hA),
    freiman_three_k_minus_four_inductive_explicit hA hcard hsmall⟩

end

end Erdos874
