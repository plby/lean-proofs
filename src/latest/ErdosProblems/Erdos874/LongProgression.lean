/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.ProgressionExtraction
import ErdosProblems.Erdos874.RestrictedGrowth
import ErdosProblems.Erdos874.FreimanDimension

/-!
# Long restricted-sum progressions from a dense one-dimensional model

This file proves the elementary dense-model half of the restricted-sum
progression argument used for Erdős Problem 874. A set which misses few
points of an integer interval has many disjoint representations of every sum
in a central interval. Repeatedly choosing disjoint representing pairs embeds
an ordinary many-fold interval sum in a restricted sumset, and hence produces
a progression having quadratically many terms.
-/

open scoped BigOperators Pointwise

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The nonnegative integer interval with `m` terms, viewed in `ℤ`. -/
def normalizedInterval (m : ℕ) : Finset ℤ :=
  Finset.Ico 0 (m : ℤ)

@[simp]
lemma mem_normalizedInterval {m : ℕ} {x : ℤ} :
    x ∈ normalizedInterval m ↔ 0 ≤ x ∧ x < m := by
  simp [normalizedInterval]

@[simp]
lemma card_normalizedInterval (m : ℕ) :
    (normalizedInterval m).card = m := by
  simp [normalizedInterval]

/-- The canonical unordered representation of `z` arising from a lower
summand `x`. -/
def canonicalPair (z x : ℕ) : Finset ℤ :=
  {(x : ℤ), ((z - x : ℕ) : ℤ)}

/-- Canonical non-diagonal pairs are genuine pair representations in the
full normalized interval. -/
lemma canonicalPair_mem_pairRepresentations {m z x : ℕ}
    (hz : z < m) (hx : x < (z + 1) / 2) :
    canonicalPair z x ∈ pairRepresentations (normalizedInterval m) z := by
  rw [mem_pairRepresentations]
  have hle : x ≤ z := by omega
  have hlt : x < z - x := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [canonicalPair, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, mem_normalizedInterval]
    constructor <;> constructor <;> omega
  · rw [canonicalPair, Finset.card_pair]
    exact_mod_cast hlt.ne
  · simp [canonicalPair, hlt.ne]
    omega

/-- Distinct lower summands give distinct canonical unordered pairs. -/
lemma canonicalPair_injective_on {z : ℕ} :
  Set.InjOn (canonicalPair z) (Finset.range ((z + 1) / 2)) := by
  intro x hx y hy hxy
  have hx' : x < (z + 1) / 2 := by simpa using hx
  have hy' : y < (z + 1) / 2 := by simpa using hy
  have hxlt : x < z - x := by omega
  have hylt : y < z - y := by omega
  have hxmem : (x : ℤ) ∈ canonicalPair z y := by
    rw [← hxy]
    simp [canonicalPair]
  simp only [canonicalPair, Finset.mem_insert, Finset.mem_singleton] at hxmem
  rcases hxmem with h | h
  · exact_mod_cast h
  · have h' : x = z - y := by exact_mod_cast h
    have : y < x := by omega
    have hymem : (y : ℤ) ∈ canonicalPair z x := by
      rw [hxy]
      simp [canonicalPair]
    simp only [canonicalPair, Finset.mem_insert, Finset.mem_singleton] at hymem
    rcases hymem with hyx | hyx
    · exact (this.ne (by exact_mod_cast hyx)).elim
    · have hyx' : y = z - x := by exact_mod_cast hyx
      omega

/-- The family of all canonical pairs for a sum `z`. -/
def canonicalPairs (z : ℕ) : Finset (Finset ℤ) :=
  (Finset.range ((z + 1) / 2)).image (canonicalPair z)

@[simp]
lemma card_canonicalPairs (z : ℕ) :
    (canonicalPairs z).card = (z + 1) / 2 := by
  rw [canonicalPairs, Finset.card_image_of_injOn canonicalPair_injective_on]
  simp

lemma canonicalPairs_subset_pairRepresentations {m z : ℕ} (hz : z < m) :
    canonicalPairs z ⊆ pairRepresentations (normalizedInterval m) z := by
  intro P hP
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
  exact canonicalPair_mem_pairRepresentations hz (Finset.mem_range.mp hx)

/-- Every canonical full-interval pair is either already a representation
using `B`, or meets the set of holes of `B` in the full interval. -/
lemma canonicalPairs_subset_pairRepresentations_union_intersecting
    (B : Finset ℤ) {m z : ℕ} (hz : z < m) :
    canonicalPairs z ⊆
      pairRepresentations B z ∪
        intersectingPairRepresentations (normalizedInterval m) z
          (normalizedInterval m \ B) := by
  intro P hP
  have hPfull := canonicalPairs_subset_pairRepresentations hz hP
  by_cases hPB : P ⊆ B
  · simp only [Finset.mem_union]
    left
    obtain ⟨hPI, hPcard, hPsum⟩ := mem_pairRepresentations.mp hPfull
    exact mem_pairRepresentations.mpr ⟨hPB, hPcard, hPsum⟩
  · simp only [Finset.mem_union]
    right
    obtain ⟨x, hxP, hxB⟩ := Finset.not_subset.mp hPB
    have hxI : x ∈ normalizedInterval m :=
      (mem_pairRepresentations.mp hPfull).1 hxP
    exact Finset.mem_biUnion.mpr
      ⟨x, Finset.mem_sdiff.mpr ⟨hxI, hxB⟩,
        Finset.mem_filter.mpr ⟨hPfull, hxP⟩⟩

/-- Deleting `H` points from a full interval destroys at most `H` of the
canonical pair representations of any fixed sum. -/
theorem card_canonicalPairs_le_add_card_pairRepresentations_add_holes
    (B : Finset ℤ) {m z : ℕ} (hz : z < m) :
    (z + 1) / 2 ≤
      (pairRepresentations B z).card +
        (normalizedInterval m \ B).card := by
  calc
    (z + 1) / 2 = (canonicalPairs z).card := (card_canonicalPairs z).symm
    _ ≤ (pairRepresentations B z ∪
        intersectingPairRepresentations (normalizedInterval m) z
          (normalizedInterval m \ B)).card :=
      Finset.card_le_card
        (canonicalPairs_subset_pairRepresentations_union_intersecting B hz)
    _ ≤ (pairRepresentations B z).card +
        (intersectingPairRepresentations (normalizedInterval m) z
          (normalizedInterval m \ B)).card :=
      Finset.card_union_le _ _
    _ ≤ (pairRepresentations B z).card +
        (normalizedInterval m \ B).card := by
      gcongr
      exact card_intersectingPairRepresentations_le _ _ _

/-- A convenient pointwise form of the pair-rich estimate. -/
theorem pair_rich_of_few_holes
    (B : Finset ℤ) {m H v z : ℕ}
    (hz : z < m) (hholes : (normalizedInterval m \ B).card ≤ H)
    (hmargin : H + v < (z + 1) / 2) :
    v < (pairRepresentations B z).card := by
  have hcount :=
    card_canonicalPairs_le_add_card_pairRepresentations_add_holes B hz
  omega

/-! A symmetric version around the middle of the full two-sum interval is
needed when the dense model has density only slightly above one half. -/

private lemma orientedPair_injective_on {s : Finset ℕ} {f g : ℕ → ℤ}
    (hf : Set.InjOn f s) (hlt : ∀ i ∈ s, f i < g i) :
    Set.InjOn (fun i ↦ ({f i, g i} : Finset ℤ)) s := by
  intro i hi j hj hij
  change ({f i, g i} : Finset ℤ) = {f j, g j} at hij
  have hfi : f i ∈ ({f j, g j} : Finset ℤ) := by
    rw [← hij]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfi
  rcases hfi with hff | hfg
  · exact hf hi hj hff
  · have hfj : f j ∈ ({f i, g i} : Finset ℤ) := by
      rw [hij]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfj
    rcases hfj with hff | hgf
    · exact hf hi hj hff.symm
    · have := hlt i hi
      have := hlt j hj
      omega

/-- The complete `m`-term interval has at least `q` unordered non-diagonal
representations of every sum at distance at least `2q-1` from both ends of
its two-sum range. -/
theorem q_le_card_pairRepresentations_normalizedInterval
    {m q : ℕ} {z : ℤ}
    (hl : 2 * (q : ℤ) - 1 ≤ z)
    (hu : z ≤ 2 * (m : ℤ) - 2 * (q : ℤ) - 1) :
    q ≤ (pairRepresentations (normalizedInterval m) z).card := by
  have hqm : q ≤ m := by omega
  by_cases hz : z ≤ (m : ℤ) - 1
  · let f : ℕ → ℤ := fun j ↦ (j : ℤ)
    let g : ℕ → ℤ := fun j ↦ z - (j : ℤ)
    let P : Finset (Finset ℤ) :=
      (Finset.range q).image fun j ↦ {f j, g j}
    have horient : ∀ j ∈ Finset.range q, f j < g j := by
      intro j hj
      simp only [Finset.mem_range] at hj
      dsimp [f, g]
      omega
    have hfinj : Set.InjOn f (Finset.range q) := by
      intro i hi j hj h
      dsimp [f] at h
      exact_mod_cast h
    have hcardP : P.card = q := by
      change ((Finset.range q).image
        (fun j ↦ ({f j, g j} : Finset ℤ))).card = q
      rw [Finset.card_image_of_injOn
        (orientedPair_injective_on hfinj horient)]
      simp
    have hPsub : P ⊆ pairRepresentations (normalizedInterval m) z := by
      intro R hR
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hR
      have hjq : j < q := Finset.mem_range.mp hj
      have hjm : j < m := hjq.trans_le hqm
      have hjlt := horient j hj
      apply mem_pairRepresentations.mpr
      refine ⟨?_, Finset.card_pair hjlt.ne, ?_⟩
      · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
          mem_normalizedInterval]
        dsimp [f, g] at hjlt ⊢
        constructor <;> constructor <;> omega
      · dsimp [f, g]
        rw [Finset.sum_pair hjlt.ne]
        ring
    rw [← hcardP]
    exact Finset.card_le_card hPsub
  · have hz' : (m : ℤ) - 1 ≤ z := by omega
    let f : ℕ → ℤ := fun j ↦ z - ((m : ℤ) - 1) + (j : ℤ)
    let g : ℕ → ℤ := fun j ↦ (m : ℤ) - 1 - (j : ℤ)
    let P : Finset (Finset ℤ) :=
      (Finset.range q).image fun j ↦ {f j, g j}
    have horient : ∀ j ∈ Finset.range q, f j < g j := by
      intro j hj
      simp only [Finset.mem_range] at hj
      dsimp [f, g]
      omega
    have hfinj : Set.InjOn f (Finset.range q) := by
      intro i hi j hj h
      dsimp [f] at h
      omega
    have hcardP : P.card = q := by
      change ((Finset.range q).image
        (fun j ↦ ({f j, g j} : Finset ℤ))).card = q
      rw [Finset.card_image_of_injOn
        (orientedPair_injective_on hfinj horient)]
      simp
    have hPsub : P ⊆ pairRepresentations (normalizedInterval m) z := by
      intro R hR
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hR
      have hjq : j < q := Finset.mem_range.mp hj
      have hjm : j < m := hjq.trans_le hqm
      have hjlt := horient j hj
      apply mem_pairRepresentations.mpr
      refine ⟨?_, Finset.card_pair hjlt.ne, ?_⟩
      · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
          mem_normalizedInterval]
        dsimp [f, g] at hjlt ⊢
        constructor <;> constructor <;> omega
      · dsimp [f, g]
        rw [Finset.sum_pair hjlt.ne]
        ring
    rw [← hcardP]
    exact Finset.card_le_card hPsub


/-- Every representation in the full interval either survives in `B` or
meets a hole. -/
lemma pairRepresentations_normalizedInterval_subset_union_intersecting
    (B : Finset ℤ) (m : ℕ) (z : ℤ) :
    pairRepresentations (normalizedInterval m) z ⊆
      pairRepresentations B z ∪
        intersectingPairRepresentations (normalizedInterval m) z
          (normalizedInterval m \ B) := by
  intro P hP
  simp only [Finset.mem_union]
  by_cases hPB : P ⊆ B
  · left
    obtain ⟨hPI, hPcard, hPsum⟩ := mem_pairRepresentations.mp hP
    exact mem_pairRepresentations.mpr ⟨hPB, hPcard, hPsum⟩
  · right
    obtain ⟨x, hxP, hxB⟩ := Finset.not_subset.mp hPB
    have hxI : x ∈ normalizedInterval m :=
      (mem_pairRepresentations.mp hP).1 hxP
    exact Finset.mem_biUnion.mpr
      ⟨x, Finset.mem_sdiff.mpr ⟨hxI, hxB⟩,
        Finset.mem_filter.mpr ⟨hP, hxP⟩⟩

/-- At most one fixed-sum pair representation is lost per missing point. -/
theorem card_pairRepresentations_normalizedInterval_le_add_holes
    (B : Finset ℤ) (m : ℕ) (z : ℤ) :
    (pairRepresentations (normalizedInterval m) z).card ≤
      (pairRepresentations B z).card +
        (normalizedInterval m \ B).card := by
  calc
    (pairRepresentations (normalizedInterval m) z).card ≤
        (pairRepresentations B z ∪
          intersectingPairRepresentations (normalizedInterval m) z
            (normalizedInterval m \ B)).card :=
      Finset.card_le_card
        (pairRepresentations_normalizedInterval_subset_union_intersecting B m z)
    _ ≤ (pairRepresentations B z).card +
        (intersectingPairRepresentations (normalizedInterval m) z
          (normalizedInterval m \ B)).card := Finset.card_union_le _ _
    _ ≤ (pairRepresentations B z).card +
        (normalizedInterval m \ B).card := by
      gcongr
      exact card_intersectingPairRepresentations_le _ _ _

/-- Symmetric pair-rich estimate, effective even when the normalized model
has density only slightly above one half. -/
theorem pair_rich_symmetric_of_few_holes
    (B : Finset ℤ) {m H v : ℕ} {z : ℤ}
    (hholes : (normalizedInterval m \ B).card ≤ H)
    (hl : 2 * ((H + v : ℕ) : ℤ) + 1 ≤ z)
    (hu : z ≤ 2 * (m : ℤ) - 2 * ((H + v : ℕ) : ℤ) - 3) :
    v < (pairRepresentations B z).card := by
  have hfull := q_le_card_pairRepresentations_normalizedInterval
    (q := H + v + 1) (m := m) (z := z) (by omega) (by omega)
  have hloss := card_pairRepresentations_normalizedInterval_le_add_holes B m z
  omega

/-- The central interval on which the preceding symmetric estimate is
uniform. Its length is exactly `2m - 4(H+v) - 3`. -/
def richPairSums (m H v : ℕ) : Finset ℤ :=
  arithmeticProgression (2 * ((H + v : ℕ) : ℤ) + 1) 1
    (2 * m - 4 * (H + v) - 3)

/-- Uniform pair-richness on `richPairSums`. -/
theorem richPairSums_pair_rich
    (B : Finset ℤ) {m H v : ℕ}
    (hholes : (normalizedInterval m \ B).card ≤ H)
    (hroom : 2 * (H + v) + 2 ≤ m) :
    ∀ z ∈ richPairSums m H v,
      v < (pairRepresentations B z).card := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := mem_arithmeticProgression.mp hz
  apply pair_rich_symmetric_of_few_holes B hholes
  · push_cast
    omega
  · push_cast
    omega

/-- The lower half of the full two-sum interval.  Every one of these sums
has linearly many canonical representations. -/
def centralPairSums (m : ℕ) : Finset ℤ :=
  Finset.Ico (m / 2 : ℕ) m

@[simp]
lemma mem_centralPairSums {m : ℕ} {z : ℤ} :
    z ∈ centralPairSums m ↔ (m / 2 : ℤ) ≤ z ∧ z < m := by
  simp [centralPairSums]

/-- A uniform pair-rich estimate on `centralPairSums`. -/
theorem centralPairSums_pair_rich
    (B : Finset ℤ) {m H v : ℕ}
    (hholes : (normalizedInterval m \ B).card ≤ H)
    (hmargin : H + v < (m / 2 + 1) / 2) :
    ∀ z ∈ centralPairSums m, v < (pairRepresentations B z).card := by
  intro z hz
  rw [mem_centralPairSums] at hz
  have hz0 : 0 ≤ z := by omega
  let zn := z.toNat
  have hcast : (zn : ℤ) = z := Int.toNat_of_nonneg hz0
  have hznlt : zn < m := by omega
  have hznlo : m / 2 ≤ zn := by omega
  rw [← hcast]
  apply pair_rich_of_few_holes B hznlt hholes
  have : (m / 2 + 1) / 2 ≤ (zn + 1) / 2 :=
    Nat.div_le_div_right (by omega)
  exact hmargin.trans_le this

/-! ## Ordinary sums of a complete interval -/

/-- The `n`-fold ordinary sum of a nonempty `L`-term interval contains the
full interval of all possible sums.  The explicit subset form is all that is
needed by the restricted-pair packing argument. -/
theorem arithmeticProgression_subset_nsmul_arithmeticProgression
    (a : ℤ) {L : ℕ} (hL : 0 < L) (n : ℕ) :
    arithmeticProgression ((n : ℤ) * a) 1 (n * (L - 1) + 1) ⊆
      n • arithmeticProgression a 1 L := by
  induction n with
  | zero =>
      intro x hx
      simp only [zero_smul]
      obtain ⟨i, hi, rfl⟩ := mem_arithmeticProgression.mp hx
      have : i = 0 := by omega
      subst i
      simp
  | succ n ih =>
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_arithmeticProgression.mp hx
      let j := min i (L - 1)
      let k := i - j
      have hjle : j ≤ L - 1 := min_le_right _ _
      have hj : j < L := by omega
      have hj_i : j ≤ i := min_le_left _ _
      have hik : i = k + j := by
        dsimp [k]
        omega
      have hk : k < n * (L - 1) + 1 := by
        have hmul : (n + 1) * (L - 1) = n * (L - 1) + (L - 1) := by
          rw [Nat.add_mul]
          simp
        dsimp [k, j]
        omega
      have hk_mem : (n : ℤ) * a + (k : ℤ) ∈
          n • arithmeticProgression a 1 L := by
        apply ih
        apply mem_arithmeticProgression.mpr
        exact ⟨k, hk, by simp⟩
      have hj_mem : a + (j : ℤ) ∈ arithmeticProgression a 1 L := by
        apply mem_arithmeticProgression.mpr
        exact ⟨j, hj, by simp⟩
      rw [succ_nsmul]
      apply Finset.mem_add.mpr
      refine ⟨(n : ℤ) * a + (k : ℤ), hk_mem,
        a + (j : ℤ), hj_mem, ?_⟩
      rw [hxi]
      push_cast [hik]
      ring

/-! ## Dense normalized models and restricted pair packing -/

/-- A restricted two-sum is, in particular, an ordinary two-fold sum. -/
lemma restrictedSumset_two_subset_two_nsmul (S : Finset ℤ) :
    restrictedSumset 2 S ⊆ 2 • S := by
  intro z hz
  obtain ⟨R, hRS, hRcard, hRsum⟩ := mem_restrictedSumset.mp hz
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hRcard
  have hx : x ∈ S := hRS (by simp)
  have hy : y ∈ S := hRS (by simp)
  rw [two_nsmul]
  apply Finset.mem_add.mpr
  refine ⟨x, hx, y, hy, ?_⟩
  simpa [hxy] using hRsum

/-- Pointwise `n`-fold addition is monotone in the underlying finset. -/
lemma nsmul_finset_mono {A B : Finset ℤ} (hAB : A ⊆ B) (n : ℕ) :
    n • A ⊆ n • B := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
      exact Finset.mem_add.mpr ⟨x, ih hx, y, hAB hy, rfl⟩

/-- The central rich-pair interval of a dense normalized set lies in its
ordinary two-fold sumset. -/
theorem richPairSums_subset_two_nsmul
    (S : Finset ℤ) {m H : ℕ}
    (hholes : (normalizedInterval m \ S).card ≤ H)
    (hroom : 2 * H + 2 ≤ m) :
    richPairSums m H 0 ⊆ 2 • S := by
  intro z hz
  have hpair : 0 < (pairRepresentations S z).card :=
    richPairSums_pair_rich S hholes (by simpa using hroom) z hz
  obtain ⟨P, hP⟩ := Finset.card_pos.mp hpair
  apply restrictedSumset_two_subset_two_nsmul S
  obtain ⟨hPS, hPcard, hPsum⟩ := mem_pairRepresentations.mp hP
  exact mem_restrictedSumset.mpr ⟨P, hPS, hPcard, hPsum⟩

/-- A dense subset of a normalized interval has a long progression in every
even many-fold ordinary sumset. -/
theorem exists_long_even_sum_progression_of_dense_normalized
    (S : Finset ℤ) {m t : ℕ}
    (hSsub : S ⊆ normalizedInterval m)
    (hScard : 1000 ≤ S.card)
    (hdense : 100 * m ≤ 197 * S.card) :
    ∃ L : ℕ, 2 * t * S.card ≤ 100 * L ∧
      ContainsAP ((2 * t) • S) 1 L := by
  let H := (normalizedInterval m \ S).card
  let Q := 2 * m - 4 * H - 3
  let L := t * (Q - 1) + 1
  have hH : H = m - S.card := by
    dsimp [H]
    rw [Finset.card_sdiff_of_subset hSsub, card_normalizedInterval]
  have hSm : S.card ≤ m := by
    simpa using Finset.card_le_card hSsub
  have hroom : 2 * H + 2 ≤ m := by
    rw [hH]
    omega
  have hQpos : 0 < Q := by
    dsimp [Q]
    omega
  have hQbound : 3 * S.card ≤ 100 * Q := by
    dsimp [Q]
    rw [hH]
    omega
  have hQsub : richPairSums m H 0 ⊆ 2 • S :=
    richPairSums_subset_two_nsmul S (by rfl) hroom
  have htQsub : t • richPairSums m H 0 ⊆ (2 * t) • S := by
    have hmono := nsmul_finset_mono hQsub t
    rw [← mul_nsmul] at hmono
    simpa [mul_comm] using hmono
  have hinterval :
      arithmeticProgression
          ((t : ℤ) * (2 * (H : ℤ) + 1)) 1 L ⊆
        t • richPairSums m H 0 := by
    apply arithmeticProgression_subset_nsmul_arithmeticProgression
      (a := 2 * (H : ℤ) + 1) hQpos t
  refine ⟨L, ?_, ?_⟩
  · dsimp [L]
    have hQminus : 2 * S.card ≤ 100 * (Q - 1) := by omega
    calc
      2 * t * S.card = t * (2 * S.card) := by ring
      _ ≤ t * (100 * (Q - 1)) := Nat.mul_le_mul_left t hQminus
      _ = 100 * (t * (Q - 1)) := by ring
      _ ≤ 100 * (t * (Q - 1) + 1) := by
        exact Nat.mul_le_mul_left 100 (by omega)
  · exact ⟨(t : ℤ) * (2 * (H : ℤ) + 1), hinterval.trans htQsub⟩

/-- Affine images commute with many-fold addition in the direction needed to
transport a contained progression. -/
lemma affineImage_nsmul_subset_nsmul_affineImage
    (S : Finset ℤ) (c q : ℤ) (n : ℕ) :
    affineImage ((n : ℤ) * c) q (n • S) ⊆
      n • affineImage c q S := by
  induction n with
  | zero => simp [affineImage]
  | succ n ih =>
      intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_affineImage.mp hz
      rw [succ_nsmul] at hw ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hw
      apply Finset.mem_add.mpr
      refine ⟨(n : ℤ) * c + q * x, ih (mem_affineImage.mpr ⟨x, hx, rfl⟩),
        c + q * y, mem_affineImage.mpr ⟨y, hy, rfl⟩, ?_⟩
      push_cast
      ring

/-- Affine form of the dense-model theorem, consuming the concrete
`ContainedInAP` output of a one-dimensional Freiman theorem. -/
theorem exists_long_even_sum_progression_of_dense_AP
    (S : Finset ℤ) {start : ℤ} {step m t : ℕ}
    (hmodel : ContainedInAP S start step m)
    (hScard : 1000 ≤ S.card)
    (hdense : 100 * m ≤ 197 * S.card) :
    ∃ L : ℕ, 2 * t * S.card ≤ 100 * L ∧
      ContainsAP ((2 * t) • S) (step : ℤ) L := by
  obtain ⟨coord, hcoord, hcoordInj⟩ := hmodel.exists_injective_coordinate
  let T : Finset ℤ := S.image fun x ↦ (coord x : ℤ)
  have hcastInj : Set.InjOn (fun x : ℤ ↦ (coord x : ℤ)) S := by
    intro x hx y hy hxy
    apply hcoordInj hx hy
    exact Int.ofNat_injective hxy
  have hTcard : T.card = S.card := by
    dsimp [T]
    rw [Finset.card_image_of_injOn hcastInj]
  have hTsub : T ⊆ normalizedInterval m := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    rw [mem_normalizedInterval]
    constructor
    · positivity
    · exact_mod_cast (hcoord x hx).1
  have hST : affineImage start (step : ℤ) T = S := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi, hzi⟩ := mem_affineImage.mp hz
      obtain ⟨x, hx, hix⟩ := Finset.mem_image.mp hi
      have hxrep := (hcoord x hx).2
      have hzx : z = x := by
        calc
          z = start + (step : ℤ) * i := hzi
          _ = start + (step : ℤ) * (coord x : ℤ) := by rw [hix]
          _ = start + (coord x : ℤ) * (step : ℤ) := by ring
          _ = x := hxrep.symm
      simpa [hzx] using hx
    · intro hz
      apply mem_affineImage.mpr
      refine ⟨(coord z : ℤ), Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
      calc
        z = start + (coord z : ℤ) * (step : ℤ) := (hcoord z hz).2
        _ = start + (step : ℤ) * (coord z : ℤ) := by ring
  obtain ⟨L, hLbound, hL⟩ :=
    exists_long_even_sum_progression_of_dense_normalized T hTsub
      (by simpa [hTcard] using hScard) (by simpa [hTcard] using hdense) (t := t)
  refine ⟨L, by simpa [hTcard] using hLbound, ?_⟩
  have hAff := hL.affineImage (((2 * t : ℕ) : ℤ) * start) (step : ℤ)
  have hAff' : ContainsAP
      (affineImage (((2 * t : ℕ) : ℤ) * start) (step : ℤ)
        ((2 * t) • T)) (step : ℤ) L := by
    simpa using hAff
  apply hAff'.mono
  have hIncl := affineImage_nsmul_subset_nsmul_affineImage
    T start (step : ℤ) (2 * t)
  rw [hST] at hIncl
  exact hIncl

/-- **Dense-model long progression theorem.**  Suppose `S` occupies more
than `100/197` of a normalized progression and every element of `S` has more
than `v` pair representations in `B`.  Then `4t` distinct elements of `B`
produce a proper progression whose length is quadratic in the scale whenever
`t` is linear in that scale.

The numerical conclusion `100*L ≥ 2t|S|` is the finite form used in the
Deshouillers--Freiman argument. -/
theorem exists_long_restricted_progression_of_dense_normalized_pair_rich
    (B S : Finset ℤ) {m v t : ℕ}
    (hSsub : S ⊆ normalizedInterval m)
    (hScard : 1000 ≤ S.card)
    (hdense : 100 * m ≤ 197 * S.card)
    (hrich : ∀ z ∈ S, v < (pairRepresentations B z).card)
    (htv : 4 * t ≤ v) :
    ∃ L : ℕ, 2 * t * S.card ≤ 100 * L ∧
      ContainsAP (restrictedSumset (4 * t) B) 1 L := by
  let H := (normalizedInterval m \ S).card
  let Q := 2 * m - 4 * H - 3
  let L := t * (Q - 1) + 1
  have hH : H = m - S.card := by
    dsimp [H]
    rw [Finset.card_sdiff_of_subset hSsub, card_normalizedInterval]
  have hSm : S.card ≤ m := by
    simpa using Finset.card_le_card hSsub
  have hroom : 2 * H + 2 ≤ m := by
    rw [hH]
    omega
  have hQpos : 0 < Q := by
    dsimp [Q]
    omega
  have hQbound : 3 * S.card ≤ 100 * Q := by
    dsimp [Q]
    rw [hH]
    omega
  have hQsub : richPairSums m H 0 ⊆ 2 • S :=
    richPairSums_subset_two_nsmul S (by rfl) hroom
  have htQsub : t • richPairSums m H 0 ⊆ (2 * t) • S := by
    have hmono := nsmul_finset_mono hQsub t
    rw [← mul_nsmul] at hmono
    simpa [mul_comm] using hmono
  have htransfer : (2 * t) • S ⊆ restrictedSumset (4 * t) B := by
    have := nsmul_subset_restrictedSumset_two_mul_of_pair_rich hrich (2 * t)
      (by omega : 2 * (2 * t) ≤ v)
    rw [show 4 * t = 2 * (2 * t) by omega]
    exact this
  have hinterval :
      arithmeticProgression
          ((t : ℤ) * (2 * (H : ℤ) + 1)) 1 L ⊆
        t • richPairSums m H 0 := by
    apply arithmeticProgression_subset_nsmul_arithmeticProgression
      (a := 2 * (H : ℤ) + 1) hQpos t
  refine ⟨L, ?_, ?_⟩
  · dsimp [L]
    have hQminus : 2 * S.card ≤ 100 * (Q - 1) := by omega
    calc
      2 * t * S.card = t * (2 * S.card) := by ring
      _ ≤ t * (100 * (Q - 1)) := Nat.mul_le_mul_left t hQminus
      _ = 100 * (t * (Q - 1)) := by ring
      _ ≤ 100 * (t * (Q - 1) + 1) := by
        exact Nat.mul_le_mul_left 100 (by omega)
  · exact ⟨(t : ℤ) * (2 * (H : ℤ) + 1),
      hinterval.trans (htQsub.trans htransfer)⟩

/-- Affine dense-model endpoint with the pair-rich transfer included. -/
theorem exists_long_restricted_progression_of_dense_AP_pair_rich
    (B S : Finset ℤ) {start : ℤ} {step m v t : ℕ}
    (hmodel : ContainedInAP S start step m)
    (hScard : 1000 ≤ S.card)
    (hdense : 100 * m ≤ 197 * S.card)
    (hrich : ∀ z ∈ S, v < (pairRepresentations B z).card)
    (htv : 4 * t ≤ v) :
    ∃ L : ℕ, 2 * t * S.card ≤ 100 * L ∧
      ContainsAP (restrictedSumset (4 * t) B) (step : ℤ) L := by
  obtain ⟨L, hLbound, hL⟩ :=
    exists_long_even_sum_progression_of_dense_AP S hmodel hScard hdense (t := t)
  refine ⟨L, hLbound, hL.mono ?_⟩
  have htransfer :=
    nsmul_subset_restrictedSumset_two_mul_of_pair_rich hrich (2 * t)
      (by omega : 2 * (2 * t) ≤ v)
  rw [show 4 * t = 2 * (2 * t) by omega]
  exact htransfer

end

end Erdos874
