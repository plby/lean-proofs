/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Convex translate interval kernel

This file isolates the finite interval accounting used after an arithmetic
progression has been straightened to an interval.  It deliberately has no
dependency on the Erdős 874 development, so that its statements can be
adapted there without creating an import cycle.
-/

open scoped BigOperators

namespace ConvexTranslate

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A discrete interval of length `L`, beginning at the integer `a`. -/
def block (a : ℤ) (L : ℕ) : Finset ℤ :=
  Finset.Ico a (a + L)

@[simp] theorem mem_block {a x : ℤ} {L : ℕ} :
    x ∈ block a L ↔ a ≤ x ∧ x < a + L := by
  simp [block]

@[simp] theorem card_block (a : ℤ) (L : ℕ) :
    (block a L).card = L := by
  simp [block, Int.card_Ico]

/-- The union of the length-`L` blocks whose left endpoints occur in `xs`. -/
def blockUnion (xs : List ℤ) (L : ℕ) : Finset ℤ :=
  xs.toFinset.biUnion fun a => block a L

@[simp] theorem blockUnion_nil (L : ℕ) : blockUnion [] L = ∅ := by
  simp [blockUnion]

@[simp] theorem blockUnion_cons (a : ℤ) (xs : List ℤ) (L : ℕ) :
    blockUnion (a :: xs) L = block a L ∪ blockUnion xs L := by
  simp [blockUnion]

/-- The sum of the consecutive gaps, each truncated at the block length. -/
def truncatedGapSum (L : ℕ) : List ℤ → ℕ
  | [] | [_] => 0
  | a :: b :: xs => min L (b - a).natAbs + truncatedGapSum L (b :: xs)

@[simp] theorem truncatedGapSum_nil (L : ℕ) : truncatedGapSum L [] = 0 := rfl

@[simp] theorem truncatedGapSum_singleton (L : ℕ) (a : ℤ) :
    truncatedGapSum L [a] = 0 := rfl

@[simp] theorem truncatedGapSum_cons_cons (L : ℕ) (a b : ℤ) (xs : List ℤ) :
    truncatedGapSum L (a :: b :: xs) =
      min L (b - a).natAbs + truncatedGapSum L (b :: xs) := rfl

private def leftFringe (a b : ℤ) (L : ℕ) : Finset ℤ :=
  Finset.Ico a (min (a + L) b)

private def rightFringe (a b : ℤ) (L : ℕ) : Finset ℤ :=
  Finset.Ico (max a (b + L)) (a + L)

private lemma card_leftFringe {a b : ℤ} {L : ℕ} (hab : a ≤ b) :
    (leftFringe a b L).card = min L (b - a).natAbs := by
  rw [leftFringe, Int.card_Ico]
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have habs : (b - a).natAbs = (b - a).toNat := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.natAbs_of_nonneg hba, Int.toNat_of_nonneg hba]
  rw [habs]
  by_cases h : b ≤ a + L
  · rw [min_eq_right h]
    have hgap : (b - a).toNat ≤ L := by omega
    rw [min_eq_right hgap]
  · rw [min_eq_left (le_of_not_ge h)]
    have hgap : L ≤ (b - a).toNat := by omega
    rw [min_eq_left hgap]
    simp

private lemma card_rightFringe {a b : ℤ} {L : ℕ} (hba : b ≤ a) :
    (rightFringe a b L).card = min L (b - a).natAbs := by
  rw [rightFringe, Int.card_Ico]
  have hab : 0 ≤ a - b := sub_nonneg.mpr hba
  rw [show (b - a).natAbs = (a - b).toNat by omega]
  omega

private lemma leftFringe_subset_block (a b : ℤ) (L : ℕ) :
    leftFringe a b L ⊆ block a L := by
  intro x hx
  simp only [leftFringe, Finset.mem_Ico] at hx
  simp only [mem_block]
  exact ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩

private lemma rightFringe_subset_block (a b : ℤ) (L : ℕ) :
    rightFringe a b L ⊆ block a L := by
  intro x hx
  simp only [rightFringe, Finset.mem_Ico] at hx
  exact mem_block.mpr ⟨(le_max_left _ _).trans hx.1, hx.2⟩

private lemma leftFringe_disjoint_blockUnion {a b : ℤ} {xs : List ℤ} {L : ℕ}
    (hall : ∀ c ∈ b :: xs, b ≤ c) :
    Disjoint (leftFringe a b L) (blockUnion (b :: xs) L) := by
  rw [Finset.disjoint_left]
  intro x hx hxu
  simp only [leftFringe, Finset.mem_Ico] at hx
  simp only [blockUnion, Finset.mem_biUnion] at hxu
  obtain ⟨c, hc, hxc⟩ := hxu
  have hcb : b ≤ c := hall c (by simpa using hc)
  have hcx : c ≤ x := (mem_block.mp hxc).1
  omega

private lemma rightFringe_disjoint_blockUnion {a b : ℤ} {xs : List ℤ} {L : ℕ}
    (hall : ∀ c ∈ b :: xs, c ≤ b) :
    Disjoint (rightFringe a b L) (blockUnion (b :: xs) L) := by
  rw [Finset.disjoint_left]
  intro x hx hxu
  simp only [rightFringe, Finset.mem_Ico] at hx
  simp only [blockUnion, Finset.mem_biUnion] at hxu
  obtain ⟨c, hc, hxc⟩ := hxu
  have hcb : c ≤ b := hall c (by simpa using hc)
  have hxc' : x < c + L := (mem_block.mp hxc).2
  have hlow : b + L ≤ x := (le_max_right _ _).trans hx.1
  omega

/-- For nondecreasing endpoints, the union contains the first block and a
fresh fringe of size `min L gap` at every subsequent endpoint. -/
theorem add_truncatedGapSum_le_card_blockUnion_of_pairwise_le
    (xs : List ℤ) (L : ℕ) (hmono : xs.Pairwise (· ≤ ·)) :
    (if xs = [] then 0 else L) + truncatedGapSum L xs ≤ (blockUnion xs L).card := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      cases xs with
      | nil => simp [blockUnion]
      | cons b xs =>
          have hab : a ≤ b := (List.pairwise_cons.mp hmono).1 b (by simp)
          have htail : (b :: xs).Pairwise (· ≤ ·) :=
            (List.pairwise_cons.mp hmono).2
          have hall : ∀ c ∈ b :: xs, b ≤ c := by
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact le_rfl
            · exact (List.pairwise_cons.mp htail).1 c hc
          have hdis := leftFringe_disjoint_blockUnion (a := a) (b := b)
            (xs := xs) (L := L) hall
          have hsub : leftFringe a b L ∪ blockUnion (b :: xs) L ⊆
              blockUnion (a :: b :: xs) L := by
            intro x hx
            rcases Finset.mem_union.mp hx with hx | hx
            · rw [blockUnion_cons]
              exact Finset.mem_union_left _ (leftFringe_subset_block a b L hx)
            · rw [blockUnion_cons]
              exact Finset.mem_union_right _ hx
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_union_of_disjoint hdis, card_leftFringe hab] at hcard
          have hi := ih htail
          simp only [reduceCtorEq, ↓reduceIte] at hi
          simp only [reduceCtorEq, ↓reduceIte, truncatedGapSum_cons_cons]
          omega

/-- The decreasing version of the preceding interval-union estimate. -/
theorem add_truncatedGapSum_le_card_blockUnion_of_pairwise_ge
    (xs : List ℤ) (L : ℕ) (hmono : xs.Pairwise (· ≥ ·)) :
    (if xs = [] then 0 else L) + truncatedGapSum L xs ≤ (blockUnion xs L).card := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      cases xs with
      | nil => simp [blockUnion]
      | cons b xs =>
          have hba : b ≤ a := (List.pairwise_cons.mp hmono).1 b (by simp)
          have htail : (b :: xs).Pairwise (· ≥ ·) :=
            (List.pairwise_cons.mp hmono).2
          have hall : ∀ c ∈ b :: xs, c ≤ b := by
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact le_rfl
            · exact (List.pairwise_cons.mp htail).1 c hc
          have hdis := rightFringe_disjoint_blockUnion (a := a) (b := b)
            (xs := xs) (L := L) hall
          have hsub : rightFringe a b L ∪ blockUnion (b :: xs) L ⊆
              blockUnion (a :: b :: xs) L := by
            intro x hx
            rcases Finset.mem_union.mp hx with hx | hx
            · rw [blockUnion_cons]
              exact Finset.mem_union_left _ (rightFringe_subset_block a b L hx)
            · rw [blockUnion_cons]
              exact Finset.mem_union_right _ hx
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_union_of_disjoint hdis, card_rightFringe hba] at hcard
          have hi := ih htail
          simp only [reduceCtorEq, ↓reduceIte] at hi
          simp only [reduceCtorEq, ↓reduceIte, truncatedGapSum_cons_cons]
          omega

/-- A monotone chain of translates contained in `U` spends at most
`U.card` on its baseline block and its truncated consecutive gaps. -/
theorem add_truncatedGapSum_le_card_of_pairwise_le
    {xs : List ℤ} {L : ℕ} {U : Finset ℤ}
    (hmono : xs.Pairwise (· ≤ ·)) (hsub : blockUnion xs L ⊆ U) :
    (if xs = [] then 0 else L) + truncatedGapSum L xs ≤ U.card :=
  (add_truncatedGapSum_le_card_blockUnion_of_pairwise_le xs L hmono).trans
    (Finset.card_le_card hsub)

theorem add_truncatedGapSum_le_card_of_pairwise_ge
    {xs : List ℤ} {L : ℕ} {U : Finset ℤ}
    (hmono : xs.Pairwise (· ≥ ·)) (hsub : blockUnion xs L ⊆ U) :
    (if xs = [] then 0 else L) + truncatedGapSum L xs ≤ U.card :=
  (add_truncatedGapSum_le_card_blockUnion_of_pairwise_ge xs L hmono).trans
    (Finset.card_le_card hsub)

/-- An affine image of a straight block.  For nonzero `q` this is an
arithmetic progression of length `L`, common difference `q`. -/
def affineBlock (c q z : ℤ) (L : ℕ) : Finset ℤ :=
  (block z L).image fun n => c + q * n

@[simp] theorem card_affineBlock {c q z : ℤ} {L : ℕ} (hq : q ≠ 0) :
    (affineBlock c q z L).card = L := by
  rw [affineBlock, Finset.card_image_iff.mpr]
  · exact card_block z L
  · intro x hx y hy hxy
    simp only at hxy
    have : q * x = q * y := by omega
    exact (mul_left_cancel₀ hq this)

/-- Taking the union commutes with the common injective affine map. -/
theorem biUnion_affineBlock_eq_image (c q : ℤ) (zs : List ℤ) (L : ℕ) :
    zs.toFinset.biUnion (fun z => affineBlock c q z L) =
      (blockUnion zs L).image (fun n => c + q * n) := by
  ext x
  simp only [affineBlock, blockUnion, Finset.mem_biUnion, Finset.mem_image,
    List.mem_toFinset]
  constructor
  · rintro ⟨z, hz, n, hn, rfl⟩
    exact ⟨n, ⟨z, hz, hn⟩, rfl⟩
  · rintro ⟨n, ⟨z, hz, hn⟩, rfl⟩
    exact ⟨z, hz, n, hn, rfl⟩

theorem card_biUnion_affineBlock {c q : ℤ} (zs : List ℤ) (L : ℕ)
    (hq : q ≠ 0) :
    (zs.toFinset.biUnion (fun z => affineBlock c q z L)).card =
      (blockUnion zs L).card := by
  rw [biUnion_affineBlock_eq_image]
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  simp only at hxy
  have : q * x = q * y := by omega
  exact mul_left_cancel₀ hq this

/-- The interval-union bound transported back to a genuine `q`-progression. -/
theorem add_truncatedGapSum_le_card_of_affineBlocks_pairwise_le
    {c q : ℤ} {xs : List ℤ} {L : ℕ} {U : Finset ℤ} (hq : q ≠ 0)
    (hmono : xs.Pairwise (· ≤ ·))
    (hsub : xs.toFinset.biUnion (fun z => affineBlock c q z L) ⊆ U) :
    (if xs = [] then 0 else L) + truncatedGapSum L xs ≤ U.card := by
  have h₁ := add_truncatedGapSum_le_card_blockUnion_of_pairwise_le xs L hmono
  have h₂ : (blockUnion xs L).card ≤ U.card := by
    rw [← card_biUnion_affineBlock xs L hq]
    exact Finset.card_le_card hsub
  exact h₁.trans h₂

theorem add_truncatedGapSum_le_card_of_affineBlocks_pairwise_ge
    {c q : ℤ} {xs : List ℤ} {L : ℕ} {U : Finset ℤ} (hq : q ≠ 0)
    (hmono : xs.Pairwise (· ≥ ·))
    (hsub : xs.toFinset.biUnion (fun z => affineBlock c q z L) ⊆ U) :
    (if xs = [] then 0 else L) + truncatedGapSum L xs ≤ U.card := by
  have h₁ := add_truncatedGapSum_le_card_blockUnion_of_pairwise_ge xs L hmono
  have h₂ : (blockUnion xs L).card ≤ U.card := by
    rw [← card_biUnion_affineBlock xs L hq]
    exact Finset.card_le_card hsub
  exact h₁.trans h₂

/-- Two aligned arithmetic-progression translates already force the sharp
truncated-gap cost. -/
theorem add_truncatedGap_pair_le_card
    {a b : ℤ} {L : ℕ} {U : Finset ℤ}
    (hsub : blockUnion [a, b] L ⊆ U) :
    L + min L (b - a).natAbs ≤ U.card := by
  by_cases hab : a ≤ b
  · have hmono : [a, b].Pairwise (· ≤ ·) := by simp [hab]
    simpa using add_truncatedGapSum_le_card_of_pairwise_le hmono hsub
  · have hmono : [a, b].Pairwise (· ≥ ·) := by simp; omega
    simpa using add_truncatedGapSum_le_card_of_pairwise_ge hmono hsub

/-- A valley, split at one of its minima, has at most twice the ambient
cardinality worth of truncated gaps.  The common minimum may be placed at
the end of `left` and the beginning of `right`; baselines are harmlessly
dropped in this estimate. -/
theorem valley_truncatedGapSum_le_two_mul_card
    {left right : List ℤ} {L : ℕ} {U : Finset ℤ}
    (hleft : left.Pairwise (· ≥ ·)) (hright : right.Pairwise (· ≤ ·))
    (hsubLeft : blockUnion left L ⊆ U)
    (hsubRight : blockUnion right L ⊆ U) :
    truncatedGapSum L left + truncatedGapSum L right ≤ 2 * U.card := by
  have hl := add_truncatedGapSum_le_card_of_pairwise_ge hleft hsubLeft
  have hr := add_truncatedGapSum_le_card_of_pairwise_le hright hsubRight
  omega

/-- The valley estimate directly on translates of one nonzero-step
arithmetic progression. -/
theorem valley_truncatedGapSum_le_two_mul_card_affine
    {c q : ℤ} {left right : List ℤ} {L : ℕ} {U : Finset ℤ} (hq : q ≠ 0)
    (hleft : left.Pairwise (· ≥ ·)) (hright : right.Pairwise (· ≤ ·))
    (hsubLeft : left.toFinset.biUnion (fun z => affineBlock c q z L) ⊆ U)
    (hsubRight : right.toFinset.biUnion (fun z => affineBlock c q z L) ⊆ U) :
    truncatedGapSum L left + truncatedGapSum L right ≤ 2 * U.card := by
  have hl := add_truncatedGapSum_le_card_of_affineBlocks_pairwise_ge
    hq hleft hsubLeft
  have hr := add_truncatedGapSum_le_card_of_affineBlocks_pairwise_le
    hq hright hsubRight
  omega

/-- Window differences of a discretely convex sequence are nondecreasing.
The sequence is total on `ℕ`; a finite caller only needs the hypotheses on
the indices it uses. -/
theorem windowDiff_mono_of_increment_mono (s : ℕ → ℤ)
    (hinc : ∀ i j : ℕ, i ≤ j → s (i + 1) - s i ≤ s (j + 1) - s j)
    (o i j : ℕ) (hij : i ≤ j) :
    s (i + o) - s i ≤ s (j + o) - s j := by
  induction o with
  | zero => simp
  | succ o ih =>
      have hprev := ih
      have hstep := hinc (i + o) (j + o) (Nat.add_le_add_right hij o)
      simp only [Nat.add_assoc] at hstep
      omega

/-- If all `o`-window differences are divided by the same positive integer,
their exact quotients inherit monotonicity. -/
theorem quotientWindow_mono_of_increment_mono
    (s : ℕ → ℤ) (z : ℕ → ℤ) (q : ℤ) (o : ℕ)
    (hinc : ∀ i j : ℕ, i ≤ j → s (i + 1) - s i ≤ s (j + 1) - s j)
    (hq : 0 < q) (hz : ∀ i, q * z i = s (i + o) - s i)
    {i j : ℕ} (hij : i ≤ j) : z i ≤ z j := by
  have hd := windowDiff_mono_of_increment_mono s hinc o i j hij
  rw [← hz i, ← hz j] at hd
  nlinarith

/-- Range-restricted version needed for finite paths. -/
theorem windowDiff_mono_of_increment_mono_on (s : ℕ → ℤ) (T : ℕ)
    (hinc : ∀ i j : ℕ, i ≤ j → j < T →
      s (i + 1) - s i ≤ s (j + 1) - s j)
    (o i j : ℕ) (hij : i ≤ j) (hbound : j + o ≤ T) :
    s (i + o) - s i ≤ s (j + o) - s j := by
  induction o with
  | zero => simp
  | succ o ih =>
      have hprev := ih (by omega)
      have hstep := hinc (i + o) (j + o) (Nat.add_le_add_right hij o) (by omega)
      simp only [Nat.add_assoc] at hstep
      omega

theorem quotientWindow_mono_of_increment_mono_on
    (s : ℕ → ℤ) (z : ℕ → ℤ) (T : ℕ) (q : ℤ) (o : ℕ)
    (hinc : ∀ i j : ℕ, i ≤ j → j < T →
      s (i + 1) - s i ≤ s (j + 1) - s j)
    (hq : 0 < q)
    (hz : ∀ i, i + o ≤ T → q * z i = s (i + o) - s i)
    {i j : ℕ} (hij : i ≤ j) (hbound : j + o ≤ T) : z i ≤ z j := by
  have hd := windowDiff_mono_of_increment_mono_on s T hinc o i j hij hbound
  rw [← hz i (by omega), ← hz j hbound] at hd
  nlinarith

/-- Abstract summation over disjoint residue supports.  This is the exact
step that removes a spurious factor equal to the number of residue chains. -/
theorem sum_chainCosts_le_two_mul_card
    {R : Type*} [DecidableEq R] (rs : Finset R) (cost : R → ℕ)
    (support : R → Finset ℤ) (U : Finset ℤ)
    (hcost : ∀ r ∈ rs, cost r ≤ 2 * (support r).card)
    (hdis : (↑rs : Set R).PairwiseDisjoint support)
    (hsub : rs.biUnion support ⊆ U) :
    ∑ r ∈ rs, cost r ≤ 2 * U.card := by
  calc
    ∑ r ∈ rs, cost r ≤ ∑ r ∈ rs, 2 * (support r).card :=
      Finset.sum_le_sum fun r hr => hcost r hr
    _ = 2 * ∑ r ∈ rs, (support r).card := by
      simp [Finset.mul_sum]
    _ = 2 * (rs.biUnion support).card := by rw [Finset.card_biUnion hdis]
    _ ≤ 2 * U.card := Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)

/-- Range-level assembly.  The caller partitions the convex quotient path
at its sign crossing in every residue chain, supplying `left r` and
`right r`; `haccount` says that every retained `o`-window is one of the
consecutive gaps in those lists.  Pairwise disjoint residue supports remove
the factor `o`. -/
theorem sum_window_truncatedDisplacement_le_two_mul_card
    {ι R : Type*} [DecidableEq ι] [DecidableEq R]
    (E : Finset ι) (D : ι → ℕ) (rs : Finset R)
    (c : R → ℤ) {q : ℤ} (left right : R → List ℤ)
    (L : ℕ) (support : R → Finset ℤ) (U : Finset ℤ) (hq : q ≠ 0)
    (hleft : ∀ r ∈ rs, (left r).Pairwise (· ≥ ·))
    (hright : ∀ r ∈ rs, (right r).Pairwise (· ≤ ·))
    (hsubLeft : ∀ r ∈ rs,
      (left r).toFinset.biUnion (fun z => affineBlock (c r) q z L) ⊆ support r)
    (hsubRight : ∀ r ∈ rs,
      (right r).toFinset.biUnion (fun z => affineBlock (c r) q z L) ⊆ support r)
    (haccount : ∑ i ∈ E, min (D i) L ≤
      ∑ r ∈ rs, (truncatedGapSum L (left r) + truncatedGapSum L (right r)))
    (hdis : (↑rs : Set R).PairwiseDisjoint support)
    (hsub : rs.biUnion support ⊆ U) :
    ∑ i ∈ E, min (D i) L ≤ 2 * U.card := by
  refine haccount.trans (sum_chainCosts_le_two_mul_card rs
    (fun r => truncatedGapSum L (left r) + truncatedGapSum L (right r))
    support U ?_ hdis hsub)
  intro r hr
  exact valley_truncatedGapSum_le_two_mul_card_affine hq
    (hleft r hr) (hright r hr) (hsubLeft r hr) (hsubRight r hr)

/-- Finite averaging in the multiplication form convenient over naturals. -/
theorem exists_card_mul_le_of_sum_le {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {g : ι → ℕ} {B : ℕ} (hE : E.Nonempty)
    (hsum : ∑ i ∈ E, g i ≤ B) :
    ∃ i ∈ E, E.card * g i ≤ B := by
  by_contra hn
  have h : ∀ i ∈ E, B < E.card * g i := by
    intro i hi
    exact Nat.lt_of_not_ge fun hle => hn ⟨i, hi, hle⟩
  have hpoint : ∀ i ∈ E, B + 1 ≤ E.card * g i := by
    intro i hi
    have hi' := h i hi
    omega
  have hsum' : ∑ i ∈ E, (B + 1) ≤ ∑ i ∈ E, E.card * g i :=
    Finset.sum_le_sum hpoint
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum'
  have hpos : 0 < E.card := Finset.card_pos.mpr hE
  have hupper : E.card * (∑ i ∈ E, g i) ≤ E.card * B :=
    Nat.mul_le_mul_left E.card hsum
  have hbad : E.card * (B + 1) ≤ E.card * B := hsum'.trans hupper
  have : B + 1 ≤ B := Nat.le_of_mul_le_mul_left hbad hpos
  omega

/-- Pigeonhole the truncated sum, and use the strict capacity margin to
show that the selected displacement was not truncated. -/
theorem exists_small_displacement_of_sum_min_le
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (D : ι → ℕ)
    {G L C : ℕ} (hG : G ≤ E.card) (hGpos : 0 < G)
    (hsum : ∑ i ∈ E, min (D i) L ≤ 2 * C)
    (hmargin : 2 * C < G * L) :
    ∃ i ∈ E, D i < L ∧ G * D i ≤ 2 * C := by
  have hE : E.Nonempty := Finset.card_pos.mp (hGpos.trans_le hG)
  let values := E.image D
  have hvalues : values.Nonempty := hE.image D
  let m := values.min' hvalues
  have hm_mem : m ∈ values := Finset.min'_mem values hvalues
  obtain ⟨i, hi, hDi⟩ := Finset.mem_image.mp hm_mem
  have hm_le : ∀ j ∈ E, m ≤ D j := by
    intro j hj
    exact Finset.min'_le values (D j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hlower : E.card * min m L ≤ ∑ j ∈ E, min (D j) L := by
    calc
      E.card * min m L = ∑ _j ∈ E, min m L := by simp
      _ ≤ ∑ j ∈ E, min (D j) L := by
        exact Finset.sum_le_sum fun j hj => min_le_min_right L (hm_le j hj)
  have hmL : m < L := by
    by_contra hn
    have hLm : L ≤ m := Nat.le_of_not_gt hn
    have hmin : min m L = L := min_eq_right hLm
    have : G * L ≤ 2 * C := by
      calc
        G * L ≤ E.card * L := Nat.mul_le_mul_right L hG
        _ = E.card * min m L := by rw [hmin]
        _ ≤ ∑ j ∈ E, min (D j) L := hlower
        _ ≤ 2 * C := hsum
    omega
  have hmin : min m L = m := min_eq_left hmL.le
  have hGm : G * m ≤ 2 * C := by
    calc
      G * m ≤ E.card * m := Nat.mul_le_mul_right m hG
      _ = E.card * min m L := by rw [hmin]
      _ ≤ ∑ j ∈ E, min (D j) L := hlower
      _ ≤ 2 * C := hsum
  refine ⟨i, hi, ?_, ?_⟩
  · simpa [hDi] using hmL
  · simpa [hDi] using hGm

/-- Complete range-level conclusion: a convex-chain accounting certificate
and the capacity margin select an untruncated good window. -/
theorem exists_small_window_of_disjoint_convex_chains
    {ι R : Type*} [DecidableEq ι] [DecidableEq R]
    (E : Finset ι) (D : ι → ℕ) (rs : Finset R)
    (c : R → ℤ) {q : ℤ} (left right : R → List ℤ)
    (L G : ℕ) (support : R → Finset ℤ) (U : Finset ℤ) (hq : q ≠ 0)
    (hG : G ≤ E.card) (hGpos : 0 < G) (hmargin : 2 * U.card < G * L)
    (hleft : ∀ r ∈ rs, (left r).Pairwise (· ≥ ·))
    (hright : ∀ r ∈ rs, (right r).Pairwise (· ≤ ·))
    (hsubLeft : ∀ r ∈ rs,
      (left r).toFinset.biUnion (fun z => affineBlock (c r) q z L) ⊆ support r)
    (hsubRight : ∀ r ∈ rs,
      (right r).toFinset.biUnion (fun z => affineBlock (c r) q z L) ⊆ support r)
    (haccount : ∑ i ∈ E, min (D i) L ≤
      ∑ r ∈ rs, (truncatedGapSum L (left r) + truncatedGapSum L (right r)))
    (hdis : (↑rs : Set R).PairwiseDisjoint support)
    (hsub : rs.biUnion support ⊆ U) :
    ∃ i ∈ E, D i < L ∧ G * D i ≤ 2 * U.card := by
  apply exists_small_displacement_of_sum_min_le E D hG hGpos _ hmargin
  exact sum_window_truncatedDisplacement_le_two_mul_card E D rs c left right L
    support U hq hleft hright hsubLeft hsubRight haccount hdis hsub

/-- The residue-chain accounting plus averaging conclusion. -/
theorem exists_window_card_mul_gap_le_two_mul_card
    {ι R : Type*} [DecidableEq ι] [DecidableEq R]
    (E : Finset ι) (gap : ι → ℕ) (rs : Finset R) (cost : R → ℕ)
    (support : R → Finset ℤ) (U : Finset ℤ)
    (hE : E.Nonempty) (hgap : ∑ i ∈ E, gap i ≤ ∑ r ∈ rs, cost r)
    (hcost : ∀ r ∈ rs, cost r ≤ 2 * (support r).card)
    (hdis : (↑rs : Set R).PairwiseDisjoint support)
    (hsub : rs.biUnion support ⊆ U) :
    ∃ i ∈ E, E.card * gap i ≤ 2 * U.card := by
  apply exists_card_mul_le_of_sum_le hE
  exact hgap.trans (sum_chainCosts_le_two_mul_card rs cost support U hcost hdis hsub)

/-- Denominator form: if the retained window set has at least `T - 2*o`
members, one retained window has normalized gap at most `2*C/(T-2*o)` in
the division-free formulation used in Lean. -/
theorem exists_window_sub_two_mul_mul_gap_le_two_mul_card
    {ι R : Type*} [DecidableEq ι] [DecidableEq R]
    (T o : ℕ) (E : Finset ι) (gap : ι → ℕ)
    (rs : Finset R) (cost : R → ℕ) (support : R → Finset ℤ) (U : Finset ℤ)
    (hE : E.Nonempty) (hcard : T - 2 * o ≤ E.card)
    (hgap : ∑ i ∈ E, gap i ≤ ∑ r ∈ rs, cost r)
    (hcost : ∀ r ∈ rs, cost r ≤ 2 * (support r).card)
    (hdis : (↑rs : Set R).PairwiseDisjoint support)
    (hsub : rs.biUnion support ⊆ U) :
    ∃ i ∈ E, (T - 2 * o) * gap i ≤ 2 * U.card := by
  obtain ⟨i, hi, hib⟩ := exists_window_card_mul_gap_le_two_mul_card
    E gap rs cost support U hE hgap hcost hdis hsub
  exact ⟨i, hi, (Nat.mul_le_mul_right (gap i) hcard).trans hib⟩

/-! ## Automatic removal of the sign-crossing windows -/

/-- The adjacent increment of an integer sequence. -/
def increment (s : ℕ → ℤ) (j : ℕ) : ℤ := s (j + 1) - s j

/-- Every adjacent increment in `[j,j+o)` has one common weak sign. -/
def HasUniformIncrementSign (s : ℕ → ℤ) (j o : ℕ) : Prop :=
  (∀ t < o, 0 ≤ increment s (j + t)) ∨
  (∀ t < o, increment s (j + t) ≤ 0)

/-- Candidate `o`-windows retained after deleting those which straddle the
unique sign crossing of a discretely convex sequence. -/
noncomputable def goodWindows (s : ℕ → ℤ) (T o : ℕ) : Finset ℕ :=
  (Finset.range (T - o + 1)).filter fun j => HasUniformIncrementSign s j o

@[simp] theorem mem_goodWindows {s : ℕ → ℤ} {T o j : ℕ} :
    j ∈ goodWindows s T o ↔ j < T - o + 1 ∧ HasUniformIncrementSign s j o := by
  simp only [goodWindows, Finset.mem_filter, Finset.mem_range]

private theorem endpoint_signs_of_not_uniform
    {s : ℕ → ℤ} {T j o : ℕ} (ho : 0 < o) (hbound : j + o ≤ T)
    (hinc : ∀ i k : ℕ, i ≤ k → k < T → increment s i ≤ increment s k)
    (hbad : ¬ HasUniformIncrementSign s j o) :
    increment s j < 0 ∧ 0 < increment s (j + (o - 1)) := by
  have hnneg : ¬ ∀ t < o, 0 ≤ increment s (j + t) := by
    intro h
    exact hbad (Or.inl h)
  have hnpos : ¬ ∀ t < o, increment s (j + t) ≤ 0 := by
    intro h
    exact hbad (Or.inr h)
  push Not at hnneg hnpos
  obtain ⟨t, ht, htneg⟩ := hnneg
  obtain ⟨u, hu, hupos⟩ := hnpos
  have hjt := hinc j (j + t) (Nat.le_add_right _ _) (by omega)
  have huu : u ≤ o - 1 := by omega
  have hju := hinc (j + u) (j + (o - 1)) (Nat.add_le_add_left huu j) (by omega)
  exact ⟨by omega, by omega⟩

/-- Any two sign-crossing windows start fewer than `o-1` places apart. -/
private theorem bad_window_start_lt
    {s : ℕ → ℤ} {T a b o : ℕ} (ho : 0 < o)
    (haT : a + o ≤ T) (hbT : b + o ≤ T)
    (hinc : ∀ i k : ℕ, i ≤ k → k < T → increment s i ≤ increment s k)
    (ha : ¬ HasUniformIncrementSign s a o)
    (hb : ¬ HasUniformIncrementSign s b o) (hab : a ≤ b) :
    b < a + (o - 1) := by
  obtain ⟨_haneg, hapos⟩ := endpoint_signs_of_not_uniform ho haT hinc ha
  obtain ⟨hbneg, _hbpos⟩ := endpoint_signs_of_not_uniform ho hbT hinc hb
  by_contra hn
  have hle : a + (o - 1) ≤ b := Nat.le_of_not_gt hn
  have := hinc (a + (o - 1)) b hle (by omega)
  omega

/-- A discretely convex sequence has at most `o-1` sign-crossing
`o`-windows, independently of the ambient endpoint `T`. -/
theorem card_badWindows_le
    (s : ℕ → ℤ) (T o : ℕ) (ho : 0 < o) (hoT : o ≤ T)
    (hinc : ∀ i k : ℕ, i ≤ k → k < T → increment s i ≤ increment s k) :
    ((Finset.range (T - o + 1)).filter
      (fun j => ¬ HasUniformIncrementSign s j o)).card ≤ o - 1 := by
  let bad := (Finset.range (T - o + 1)).filter
    (fun j => ¬ HasUniformIncrementSign s j o)
  by_cases hempty : bad = ∅
  · simp [bad, hempty]
  · have hbad : bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    let a := bad.min' hbad
    have ha : a ∈ bad := Finset.min'_mem bad hbad
    have hsub : bad ⊆ Finset.Ico a (a + (o - 1)) := by
      intro b hb
      have hab : a ≤ b := Finset.min'_le bad b hb
      have ha' : ¬ HasUniformIncrementSign s a o := by
        exact (Finset.mem_filter.mp ha).2
      have hb' : ¬ HasUniformIncrementSign s b o := by
        exact (Finset.mem_filter.mp hb).2
      have haT : a + o ≤ T := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        omega
      have hbT : b + o ≤ T := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        omega
      exact Finset.mem_Ico.mpr
        ⟨hab, bad_window_start_lt ho haT hbT hinc ha' hb' hab⟩
    calc
      bad.card ≤ (Finset.Ico a (a + (o - 1))).card := Finset.card_le_card hsub
      _ = o - 1 := by simp [Nat.card_Ico]

/-- After deleting the at most `o-1` crossing windows, at least
`T-2*o+2` windows remain. -/
theorem sub_two_mul_add_two_le_card_goodWindows
    (s : ℕ → ℤ) (T o : ℕ) (ho : 0 < o) (hroom : 2 * o ≤ T)
    (hinc : ∀ i k : ℕ, i ≤ k → k < T → increment s i ≤ increment s k) :
    T - 2 * o + 2 ≤ (goodWindows s T o).card := by
  let all := Finset.range (T - o + 1)
  let bad := all.filter (fun j => ¬ HasUniformIncrementSign s j o)
  have hbad : bad.card ≤ o - 1 := by
    simpa [all, bad] using card_badWindows_le s T o ho (by omega) hinc
  have hpartition : (goodWindows s T o).card + bad.card = all.card := by
    simpa [goodWindows, all, bad, Finset.filter_not] using
      Finset.card_filter_add_card_filter_not
        (s := Finset.range (T - o + 1)) (p := fun j => HasUniformIncrementSign s j o)
  have hall : all.card = T - o + 1 := by simp [all]
  omega

/-! ## Canonical finite quotient paths -/

/-- `n+1` consecutive values of `w`, beginning at `start`. -/
def valueSegment (w : ℕ → ℤ) (start : ℕ) : ℕ → List ℤ
  | 0 => [w start]
  | n + 1 => w start :: valueSegment w (start + 1) n

@[simp] theorem valueSegment_zero (w : ℕ → ℤ) (start : ℕ) :
    valueSegment w start 0 = [w start] := rfl

@[simp] theorem valueSegment_succ (w : ℕ → ℤ) (start n : ℕ) :
    valueSegment w start (n + 1) = w start :: valueSegment w (start + 1) n := rfl

@[simp] theorem length_valueSegment (w : ℕ → ℤ) (start n : ℕ) :
    (valueSegment w start n).length = n + 1 := by
  induction n generalizing start with
  | zero => simp
  | succ n ih => simp [ih]

theorem mem_valueSegment {w : ℕ → ℤ} {start n : ℕ} {x : ℤ} :
    x ∈ valueSegment w start n ↔ ∃ k ≤ n, x = w (start + k) := by
  induction n generalizing start with
  | zero => simp
  | succ n ih =>
      simp only [valueSegment_succ, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨k, hk, rfl⟩)
        · exact ⟨0, by omega, by simp⟩
        · exact ⟨k + 1, by omega, by congr 1 <;> omega⟩
      · rintro ⟨k, hk, rfl⟩
        by_cases hk0 : k = 0
        · left
          subst k
          simp
        · right
          obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
          exact ⟨l, by omega, by congr 1 <;> omega⟩

theorem truncatedGapSum_valueSegment (w : ℕ → ℤ) (start n L : ℕ) :
    truncatedGapSum L (valueSegment w start n) =
      ∑ i ∈ Finset.range n,
        min L (w (start + i + 1) - w (start + i)).natAbs := by
  induction n generalizing start with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simp [valueSegment]
      | succ n =>
          rw [valueSegment_succ]
          change min L (w (start + 1) - w start).natAbs +
              truncatedGapSum L (valueSegment w (start + 1) (n + 1)) = _
          rw [ih]
          let f : ℕ → ℕ := fun i =>
            min L (w (start + i + 1) - w (start + i)).natAbs
          have hzero : min L (w (start + 1) - w start).natAbs = f 0 := by
            simp [f]
          have hshift :
              (∑ i ∈ Finset.range (n + 1),
                min L (w (start + 1 + i + 1) - w (start + 1 + i)).natAbs) =
              ∑ i ∈ Finset.range (n + 1), f (i + 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [f]
            simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          rw [hzero, hshift, add_comm]
          exact (Finset.sum_range_succ' f (n + 1)).symm

private theorem pairwise_valueSegment_le
    {w : ℕ → ℤ} {start n : ℕ}
    (hmono : ∀ i j, i ≤ j → j ≤ n → w (start + i) ≤ w (start + j)) :
    (valueSegment w start n).Pairwise (· ≤ ·) := by
  induction n generalizing start with
  | zero => simp
  | succ n ih =>
      rw [valueSegment_succ, List.pairwise_cons]
      constructor
      · intro x hx
        obtain ⟨k, hk, rfl⟩ := mem_valueSegment.mp hx
        have := hmono 0 (k + 1) (by omega) (by omega)
        convert this using 1 <;> congr 1 <;> omega
      · apply ih
        intro i j hij hj
        have := hmono (i + 1) (j + 1) (by omega) (by omega)
        convert this using 1 <;> congr 1 <;> omega

private theorem pairwise_valueSegment_ge
    {w : ℕ → ℤ} {start n : ℕ}
    (hmono : ∀ i j, i ≤ j → j ≤ n → w (start + j) ≤ w (start + i)) :
    (valueSegment w start n).Pairwise (· ≥ ·) := by
  induction n generalizing start with
  | zero => simp
  | succ n ih =>
      rw [valueSegment_succ, List.pairwise_cons]
      constructor
      · intro x hx
        obtain ⟨k, hk, rfl⟩ := mem_valueSegment.mp hx
        have := hmono 0 (k + 1) (by omega) (by omega)
        convert this using 1 <;> congr 1 <;> omega
      · apply ih
        intro i j hij hj
        have := hmono (i + 1) (j + 1) (by omega) (by omega)
        convert this using 1 <;> congr 1 <;> omega

/-- A finite integer path which decreases to index `m` and then increases
spends at most twice the ambient capacity on its truncated consecutive
gaps.  The two block-containment assumptions are automatic when all path
blocks lie in `U`; they are separated here for convenient reuse. -/
theorem sum_truncatedGap_le_two_mul_card_of_valley
    {w : ℕ → ℤ} {n m L : ℕ} {U : Finset ℤ} (hm : m ≤ n)
    (hleft : ∀ i j, i ≤ j → j ≤ m → w j ≤ w i)
    (hright : ∀ i j, m ≤ i → i ≤ j → j ≤ n → w i ≤ w j)
    (hsubLeft : blockUnion (valueSegment w 0 m) L ⊆ U)
    (hsubRight : blockUnion (valueSegment w m (n - m)) L ⊆ U) :
    (∑ i ∈ Finset.range n, min L (w (i + 1) - w i).natAbs) ≤ 2 * U.card := by
  have hpLeft : (valueSegment w 0 m).Pairwise (· ≥ ·) := by
    apply pairwise_valueSegment_ge
    intro i j hij hj
    simpa using hleft i j hij hj
  have hpRight : (valueSegment w m (n - m)).Pairwise (· ≤ ·) := by
    apply pairwise_valueSegment_le
    intro i j hij hj
    have hmn : m + j ≤ n := by omega
    exact hright (m + i) (m + j) (by omega) (by omega) hmn
  have hbLeft := add_truncatedGapSum_le_card_of_pairwise_ge hpLeft hsubLeft
  have hbRight := add_truncatedGapSum_le_card_of_pairwise_le hpRight hsubRight
  have hsLeft :
      (∑ i ∈ Finset.range m, min L (w (i + 1) - w i).natAbs) ≤ U.card := by
    have hform := truncatedGapSum_valueSegment w 0 m L
    simp only [Nat.zero_add] at hform
    rw [← hform]
    have hne : valueSegment w 0 m ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
    simp only [hne, ↓reduceIte] at hbLeft
    omega
  have hsRight :
      (∑ i ∈ Finset.range (n - m),
        min L (w (m + i + 1) - w (m + i)).natAbs) ≤ U.card := by
    rw [← truncatedGapSum_valueSegment w m (n - m) L]
    have hne : valueSegment w m (n - m) ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
    simp only [hne, ↓reduceIte] at hbRight
    omega
  rw [← Finset.sum_range_add_sum_Ico
    (f := fun i => min L (w (i + 1) - w i).natAbs) hm]
  rw [Finset.sum_Ico_eq_sum_range]
  have hsRight' :
      (∑ i ∈ Finset.range (n - m),
        min L (w (m + i + 1) - w (m + i)).natAbs) =
      ∑ i ∈ Finset.range (n - m),
        min L (w (m + i + 1) - w (m + i)).natAbs := rfl
  omega

/-- A finite nondecreasing integer sequence has a sign-crossing index: all
terms before it are nonpositive and all terms from it on are nonnegative. -/
theorem exists_signCrossing (g : ℕ → ℤ) (n : ℕ)
    (hmono : ∀ i j, i ≤ j → j < n → g i ≤ g j) :
    ∃ m ≤ n, (∀ i < m, g i ≤ 0) ∧ (∀ i, m ≤ i → i < n → 0 ≤ g i) := by
  let nonneg := (Finset.range n).filter fun i => 0 ≤ g i
  by_cases hne : nonneg.Nonempty
  · let m := nonneg.min' hne
    have hm_mem : m ∈ nonneg := Finset.min'_mem nonneg hne
    have hm_lt : m < n := (Finset.mem_filter.mp hm_mem).1 |> Finset.mem_range.mp
    have hgm : 0 ≤ g m := (Finset.mem_filter.mp hm_mem).2
    refine ⟨m, hm_lt.le, ?_, ?_⟩
    · intro i hi
      by_contra hn
      have hgi : 0 ≤ g i := le_of_not_ge hn
      have hi_mem : i ∈ nonneg := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hi.trans hm_lt), hgi⟩
      have := Finset.min'_le nonneg i hi_mem
      omega
    · intro i hmi hin
      exact hgm.trans (hmono m i hmi hin)
  · refine ⟨n, le_rfl, ?_, ?_⟩
    · intro i hi
      by_contra hn
      have hgi : 0 ≤ g i := le_of_not_ge hn
      exact hne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hgi⟩⟩
    · intro i hni hin
      omega

/-- Canonical quotient coordinate obtained by cumulatively summing the
window quotients along one residue chain. -/
def cumulative (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, g i

@[simp] theorem cumulative_zero (g : ℕ → ℤ) : cumulative g 0 = 0 := by
  simp [cumulative]

theorem cumulative_succ (g : ℕ → ℤ) (n : ℕ) :
    cumulative g (n + 1) = cumulative g n + g n := by
  simp [cumulative, Finset.sum_range_succ]

theorem cumulative_sub (g : ℕ → ℤ) (n : ℕ) :
    cumulative g (n + 1) - cumulative g n = g n := by
  rw [cumulative_succ]
  omega

private theorem cumulative_mono_of_nonneg {g : ℕ → ℤ} {i j : ℕ} (hij : i ≤ j)
    (hg : ∀ k, i ≤ k → k < j → 0 ≤ g k) : cumulative g i ≤ cumulative g j := by
  have hsum : 0 ≤ ∑ k ∈ Finset.Ico i j, g k := by
    exact Finset.sum_nonneg fun k hk => hg k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2
  have hsplit := Finset.sum_range_add_sum_Ico g hij
  simp only [cumulative] at *
  omega

private theorem cumulative_antitone_of_nonpos {g : ℕ → ℤ} {i j : ℕ} (hij : i ≤ j)
    (hg : ∀ k, i ≤ k → k < j → g k ≤ 0) : cumulative g j ≤ cumulative g i := by
  have hsum : ∑ k ∈ Finset.Ico i j, g k ≤ 0 := by
    exact Finset.sum_nonpos fun k hk => hg k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2
  have hsplit := Finset.sum_range_add_sum_Ico g hij
  simp only [cumulative] at *
  omega

private theorem blockUnion_valueSegment_subset
    {w : ℕ → ℤ} {start len n L : ℕ} (hbound : start + len ≤ n) :
    blockUnion (valueSegment w start len) L ⊆ blockUnion (valueSegment w 0 n) L := by
  intro x hx
  simp only [blockUnion, Finset.mem_biUnion, List.mem_toFinset] at hx ⊢
  obtain ⟨v, hv, hxv⟩ := hx
  obtain ⟨k, hk, rfl⟩ := mem_valueSegment.mp hv
  refine ⟨w (start + k), ?_, hxv⟩
  apply mem_valueSegment.mpr
  exact ⟨start + k, by omega, by congr 1 <;> omega⟩

/-- Automatic convex-valley packing for one residue chain. -/
theorem sum_truncatedGap_cumulative_le_two_mul_card
    (g : ℕ → ℤ) (n L : ℕ) (U : Finset ℤ)
    (hmono : ∀ i j, i ≤ j → j < n → g i ≤ g j)
    (hsub : blockUnion (valueSegment (cumulative g) 0 n) L ⊆ U) :
    ∑ i ∈ Finset.range n, min L (g i).natAbs ≤ 2 * U.card := by
  obtain ⟨m, hm, hneg, hpos⟩ := exists_signCrossing g n hmono
  have hleft : ∀ i j, i ≤ j → j ≤ m → cumulative g j ≤ cumulative g i := by
    intro i j hij hjm
    apply cumulative_antitone_of_nonpos hij
    intro k hik hkj
    exact hneg k (hkj.trans_le hjm)
  have hright : ∀ i j, m ≤ i → i ≤ j → j ≤ n → cumulative g i ≤ cumulative g j := by
    intro i j hmi hij hjn
    apply cumulative_mono_of_nonneg hij
    intro k hik hkj
    exact hpos k (hmi.trans hik) (hkj.trans_le hjn)
  have hpack := sum_truncatedGap_le_two_mul_card_of_valley hm hleft hright
    ((blockUnion_valueSegment_subset (start := 0) (len := m) (n := n)
      (L := L) (by omega)).trans hsub)
    ((blockUnion_valueSegment_subset (start := m) (len := n - m) (n := n)
      (L := L) (by omega)).trans hsub)
  have heq :
      (∑ i ∈ Finset.range n,
        min L (cumulative g (i + 1) - cumulative g i).natAbs) =
      ∑ i ∈ Finset.range n, min L (g i).natAbs := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [cumulative_sub]
  rw [← heq]
  exact hpack

/-- The preceding one-chain estimate transported to a genuine arithmetic
progression and an arbitrary ambient support. -/
theorem sum_truncatedGap_cumulative_affine_le_two_mul_card
    (g : ℕ → ℤ) (n L : ℕ) (c q : ℤ) (U : Finset ℤ) (hq : q ≠ 0)
    (hmono : ∀ i j, i ≤ j → j < n → g i ≤ g j)
    (hsub : (valueSegment (cumulative g) 0 n).toFinset.biUnion
      (fun z => affineBlock c q z L) ⊆ U) :
    ∑ i ∈ Finset.range n, min L (g i).natAbs ≤ 2 * U.card := by
  have hnorm := sum_truncatedGap_cumulative_le_two_mul_card g n L
    (blockUnion (valueSegment (cumulative g) 0 n) L) hmono (by rfl)
  have hcard : (blockUnion (valueSegment (cumulative g) 0 n) L).card ≤ U.card := by
    rw [← card_biUnion_affineBlock (c := c) (q := q)
      (valueSegment (cumulative g) 0 n) L hq]
    exact Finset.card_le_card hsub
  exact hnorm.trans (Nat.mul_le_mul_left 2 hcard)

/-! ## Canonical residue-chain selector -/

/-- Number of `o`-steps beginning at the residue representative `r` and
remaining in `[0,T]`. -/
def chainEdgeCount (T o r : ℕ) : ℕ := (T - r) / o

/-- Quotients encountered along one residue chain. -/
def chainQuotient (z : ℕ → ℤ) (o r n : ℕ) : ℤ := z (r + n * o)

/-- The actual `q`-progression translate union belonging to one canonical
residue chain, expressed through its cumulative quotient coordinates. -/
def canonicalChainBlocks (s z : ℕ → ℤ) (T o L : ℕ) (a q : ℤ)
    (r : Fin o) : Finset ℤ :=
  (valueSegment (cumulative (chainQuotient z o r)) 0
      (chainEdgeCount T o r)).toFinset.biUnion
    (fun v => affineBlock (a + s r) q v L)

/-- The cumulative quotient coordinate really is the normalized displacement
from the first translate in its residue chain. -/
theorem mul_cumulative_chainQuotient_eq
    (s z : ℕ → ℤ) (T o : ℕ) (q : ℤ)
    (hz : ∀ j, j + o ≤ T → q * z j = s (j + o) - s j)
    (r n : ℕ) (hbound : r + n * o ≤ T) :
    q * cumulative (chainQuotient z o r) n = s (r + n * o) - s r := by
  induction n with
  | zero => simp [cumulative, chainQuotient]
  | succ n ih =>
      have hprev : r + n * o ≤ T := by
        apply le_trans _ hbound
        exact Nat.add_le_add_left (Nat.mul_le_mul_right o (Nat.le_succ n)) r
      have hwindow : r + n * o + o ≤ T := by
        simpa [Nat.succ_mul, Nat.add_assoc] using hbound
      have hz' := hz (r + n * o) hwindow
      rw [cumulative_succ, chainQuotient]
      have hind := ih hprev
      have hsidx : r + (n + 1) * o = r + n * o + o := by
        simp [Nat.succ_mul, Nat.add_assoc]
      rw [hsidx]
      nlinarith

/-- Pointwise AP containment implies containment of every canonical residue
chain support. -/
theorem canonicalChainBlocks_subset_of_pointwise
    (s z : ℕ → ℤ) (T o L : ℕ) (a q : ℤ) (U : Finset ℤ)
    (ho : 0 < o) (hoT : o ≤ T)
    (hz : ∀ j, j + o ≤ T → q * z j = s (j + o) - s j)
    (hU : ∀ j ≤ T, ∀ k < L, a + s j + q * (k : ℤ) ∈ U)
    (r : Fin o) : canonicalChainBlocks s z T o L a q r ⊆ U := by
  intro y hy
  simp only [canonicalChainBlocks, Finset.mem_biUnion, List.mem_toFinset] at hy
  obtain ⟨v, hv, hyv⟩ := hy
  obtain ⟨n, hn, rfl⟩ := mem_valueSegment.mp hv
  simp only [Nat.zero_add] at hyv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyv
  have hxmem := mem_block.mp hx
  let k : ℕ := (x - cumulative (chainQuotient z o (r : ℕ)) n).toNat
  have hk0 : 0 ≤ x - cumulative (chainQuotient z o (r : ℕ)) n := by omega
  have hkcast : (k : ℤ) = x - cumulative (chainQuotient z o (r : ℕ)) n := by
    exact Int.toNat_of_nonneg hk0
  have hkL : k < L := by
    have hkLint : (k : ℤ) < (L : ℤ) := by rw [hkcast]; omega
    exact_mod_cast hkLint
  have hrT : (r : ℕ) ≤ T := by omega
  have hnDiv : n ≤ (T - (r : ℕ)) / o := hn
  have hmul : n * o ≤ T - (r : ℕ) := (Nat.le_div_iff_mul_le ho).mp hnDiv
  have hjT : (r : ℕ) + n * o ≤ T := by omega
  have hcoord := mul_cumulative_chainQuotient_eq s z T o q hz (r : ℕ) n hjT
  have hmem := hU ((r : ℕ) + n * o) hjT k hkL
  rw [hkcast] at hmem
  convert hmem using 1 <;> nlinarith

/-- The Euclidean residue-chain partition of all `o`-window starts. -/
private theorem sum_windows_eq_sum_chains
    {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (T o : ℕ) (ho : 0 < o) (hoT : o ≤ T) :
    (∑ j ∈ Finset.range (T - o + 1), f j) =
      ∑ r : Fin o, ∑ n ∈ Finset.range (chainEdgeCount T o r),
        f ((r : ℕ) + n * o) := by
  have hresidue : ∀ r : Fin o,
      (∑ n ∈ Finset.range (chainEdgeCount T o r), f ((r : ℕ) + n * o)) =
        ∑ j ∈ (Finset.range (T - o + 1)).filter (fun j => j % o = (r : ℕ)), f j := by
    intro r
    apply Finset.sum_bij'
      (fun n _hn => (r : ℕ) + n * o)
      (fun j _hj => j / o)
    · intro n hn
      have hnlt : n < chainEdgeCount T o r := Finset.mem_range.mp hn
      have hn1 : n + 1 ≤ chainEdgeCount T o r := by omega
      have hrT : (r : ℕ) ≤ T := by omega
      have hmul : (n + 1) * o ≤ T - (r : ℕ) :=
        (Nat.le_div_iff_mul_le ho).mp hn1
      rw [Nat.add_mul] at hmul
      have hindex : (r : ℕ) + n * o < T - o + 1 := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hindex, ?_⟩
      simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]
    · intro j hj
      obtain ⟨hjrange, hjmod⟩ := Finset.mem_filter.mp hj
      have hjlt : j < T - o + 1 := Finset.mem_range.mp hjrange
      have hjbound : j + o ≤ T := by omega
      have hjrepr : (r : ℕ) + (j / o) * o = j := by
        rw [← hjmod]
        exact Nat.mod_add_div' j o
      have hmul : (j / o + 1) * o ≤ T - (r : ℕ) := by
        rw [Nat.add_mul]
        omega
      have hdiv : j / o + 1 ≤ chainEdgeCount T o r :=
        (Nat.le_div_iff_mul_le ho).mpr hmul
      exact Finset.mem_range.mpr (by omega)
    · intro n hn
      rw [show (r : ℕ) + n * o = (r : ℕ) + o * n by ac_rfl,
        Nat.add_mul_div_left _ _ ho, Nat.div_eq_of_lt r.isLt]
      simp
    · intro j hj
      have hjmod := (Finset.mem_filter.mp hj).2
      rw [← hjmod]
      exact Nat.mod_add_div' j o
    · intro n hn
      rfl
  let residue : ℕ → Fin o := fun j => ⟨j % o, Nat.mod_lt j ho⟩
  have hfiber := Finset.sum_fiberwise
    (Finset.range (T - o + 1)) residue f
  calc
    ∑ j ∈ Finset.range (T - o + 1), f j =
        ∑ r : Fin o, ∑ j ∈ Finset.range (T - o + 1) with residue j = r, f j :=
      hfiber.symm
    _ = ∑ r : Fin o,
        ∑ j ∈ (Finset.range (T - o + 1)).filter
          (fun j => j % o = (r : ℕ)), f j := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr
      · ext j
        simp [residue, Fin.ext_iff]
      · intro j hj
        rfl
    _ = ∑ r : Fin o, ∑ n ∈ Finset.range (chainEdgeCount T o r),
        f ((r : ℕ) + n * o) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hresidue r).symm

/-- Exact cost partition needed by the canonical selector. -/
theorem costPartition (z : ℕ → ℤ) (T o L : ℕ) (ho : 0 < o) (hoT : o ≤ T) :
    (∑ j ∈ Finset.range (T - o + 1), min L (z j).natAbs) =
      ∑ r : Fin o, ∑ n ∈ Finset.range (chainEdgeCount T o r),
        min L (chainQuotient z o r n).natAbs := by
  simpa [chainQuotient] using
    sum_windows_eq_sum_chains (fun j => min L (z j).natAbs) T o ho hoT

/-- Fully automatic selector once the elementary Euclidean partition of
window indices among the canonical residue chains is supplied.  There are no
caller-provided valley halves or edge-accounting lists: convexity performs
the sign split inside each chain. -/
theorem exists_small_uniform_window_of_chain_partition
    (s z : ℕ → ℤ) (T o L : ℕ) (a q : ℤ)
    (support : Fin o → Finset ℤ) (U : Finset ℤ)
    (ho : 0 < o) (hroom : 2 * o ≤ T) (hq : 0 < q)
    (hinc : ∀ i j : ℕ, i ≤ j → j < T → increment s i ≤ increment s j)
    (hz : ∀ j, j + o ≤ T → q * z j = s (j + o) - s j)
    (hblocks : ∀ r : Fin o,
      canonicalChainBlocks s z T o L a q r ⊆ support r)
    (hdis : (Set.univ : Set (Fin o)).PairwiseDisjoint support)
    (hsub : (Finset.univ : Finset (Fin o)).biUnion support ⊆ U)
    (hmargin : 2 * U.card < (T - 2 * o + 2) * L) :
    ∃ j ∈ goodWindows s T o,
      (z j).natAbs < L ∧ (T - 2 * o + 2) * (z j).natAbs ≤ 2 * U.card := by
  let cost : Fin o → ℕ := fun r =>
    ∑ n ∈ Finset.range (chainEdgeCount T o r),
      min L (chainQuotient z o r n).natAbs
  have hchain : ∀ r : Fin o, cost r ≤ 2 * (support r).card := by
    intro r
    let g : ℕ → ℤ := chainQuotient z o r
    have hrT : (r : ℕ) ≤ T := by omega
    have hmono : ∀ i j, i ≤ j → j < chainEdgeCount T o r → g i ≤ g j := by
      intro i j hij hj
      have hj1 : j + 1 ≤ chainEdgeCount T o r := by omega
      have hmul : (j + 1) * o ≤ T - (r : ℕ) :=
        (Nat.le_div_iff_mul_le ho).mp hj1
      rw [Nat.add_mul] at hmul
      have hbound : (r : ℕ) + j * o + o ≤ T := by omega
      have hindexij : (r : ℕ) + i * o ≤ (r : ℕ) + j * o :=
        Nat.add_le_add_left (Nat.mul_le_mul_right o hij) r
      exact quotientWindow_mono_of_increment_mono_on s z T q o hinc hq
        hz hindexij hbound
    have hc := sum_truncatedGap_cumulative_affine_le_two_mul_card
      g (chainEdgeCount T o r) L (a + s r) q (support r) hq.ne'
      hmono (hblocks r)
    simpa [cost, g, canonicalChainBlocks] using hc
  have hsumAll :
      (∑ j ∈ Finset.range (T - o + 1), min L (z j).natAbs) ≤ 2 * U.card := by
    refine (costPartition z T o L ho (by omega)).le.trans ?_
    simpa [cost] using sum_chainCosts_le_two_mul_card
      (Finset.univ : Finset (Fin o)) cost support U
      (fun r _hr => hchain r) (by simpa using hdis) hsub
  have hgoodSub : goodWindows s T o ⊆ Finset.range (T - o + 1) := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hsumGood :
      (∑ j ∈ goodWindows s T o, min ((z j).natAbs) L) ≤ 2 * U.card := by
    have hle : (∑ j ∈ goodWindows s T o, min L (z j).natAbs) ≤
        ∑ j ∈ Finset.range (T - o + 1), min L (z j).natAbs :=
      Finset.sum_le_sum_of_subset_of_nonneg hgoodSub (by intros; omega)
    have := hle.trans hsumAll
    simpa [min_comm] using this
  have hG := sub_two_mul_add_two_le_card_goodWindows s T o ho hroom hinc
  have hGpos : 0 < T - 2 * o + 2 := by omega
  obtain ⟨j, hj, hjL, hjbound⟩ := exists_small_displacement_of_sum_min_le
    (goodWindows s T o) (fun j => (z j).natAbs) hG hGpos hsumGood hmargin
  exact ⟨j, hj, hjL, hjbound⟩

/-- Final pointwise form of the convex translate selector.  The only
residue-separation input left to the caller is the mathematically essential
fact that distinct canonical residue-chain supports are disjoint. -/
theorem exists_small_uniform_window
    (s z : ℕ → ℤ) (T o L : ℕ) (a q : ℤ) (U : Finset ℤ)
    (ho : 0 < o) (hroom : 2 * o ≤ T) (hq : 0 < q)
    (hinc : ∀ i j : ℕ, i ≤ j → j < T → increment s i ≤ increment s j)
    (hz : ∀ j, j + o ≤ T → q * z j = s (j + o) - s j)
    (hU : ∀ j ≤ T, ∀ k < L, a + s j + q * (k : ℤ) ∈ U)
    (hdis : (Set.univ : Set (Fin o)).PairwiseDisjoint
      (canonicalChainBlocks s z T o L a q))
    (hmargin : 2 * U.card < (T - 2 * o + 2) * L) :
    ∃ j ∈ goodWindows s T o,
      (z j).natAbs < L ∧ (T - 2 * o + 2) * (z j).natAbs ≤ 2 * U.card := by
  apply exists_small_uniform_window_of_chain_partition s z T o L a q
    (canonicalChainBlocks s z T o L a q) U ho hroom hq hinc hz
  · intro r
    exact Finset.Subset.rfl
  · exact hdis
  · apply Finset.biUnion_subset.mpr
    intro r hr
    exact canonicalChainBlocks_subset_of_pointwise s z T o L a q U ho
      (by omega) hz hU r
  · exact hmargin

end

end ConvexTranslate
