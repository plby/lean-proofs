/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.Foundations
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

/-!
# Restricted-sumset growth for Erdős Problem 874

This file contains the elementary growth mechanism used at the beginning of
the Deshouillers--Freiman argument.  Its main estimate is their Proposition
3.3:

`|B + B| ≤ 3 |B| + |4^∧ B|`.

The proof is included in a form useful later in the formalization.  After
choosing two distinct elements `a,b ∈ B`, all pair sums lie in one of three
translates/diagonal images of `B`, or are restricted two-sums of
`B \ {a,b}`.  Translation by `a+b` injects the last set into `4^∧ B`.

The final theorems combine this estimate with Mathlib's Plünnecke--Ruzsa
inequality.  Thus a linear bound on `4^∧ B` gives explicit control of every
ordinary iterated sumset `n • B`.
-/

open scoped BigOperators Pointwise

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Combining restricted sums on disjoint supports -/

/-- Restricted sums on disjoint supports combine to a restricted sum on the
union.  This is the basic bookkeeping lemma behind all later block-packing
arguments. -/
lemma add_restrictedSumset_subset_restrictedSumset_union
    {A B : Finset ℤ} {r s : ℕ} (hAB : Disjoint A B) :
    restrictedSumset r A + restrictedSumset s B ⊆
      restrictedSumset (r + s) (A ∪ B) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨R, hRA, hRcard, hRsum⟩ := mem_restrictedSumset.mp hx
  obtain ⟨S, hSB, hScard, hSsum⟩ := mem_restrictedSumset.mp hy
  have hRS : Disjoint R S := hAB.mono hRA hSB
  apply mem_restrictedSumset.mpr
  refine ⟨R ∪ S, Finset.union_subset (hRA.trans Finset.subset_union_left)
    (hSB.trans Finset.subset_union_right), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hRS, hRcard, hScard]
  · rw [Finset.sum_union hRS, hRsum, hSsum]

/-- A pair of disjoint witnessing blocks realizes the sum of their values as
a restricted sum.  This witness-level form is convenient when the blocks
are produced greedily. -/
lemma sum_mem_restrictedSumset_of_disjoint_witnesses
    {A R S : Finset ℤ} {r s : ℕ}
    (hRA : R ⊆ A) (hSB : S ⊆ A) (hRS : Disjoint R S)
    (hRcard : R.card = r) (hScard : S.card = s) :
    (∑ x ∈ R, x) + ∑ x ∈ S, x ∈ restrictedSumset (r + s) A := by
  apply mem_restrictedSumset.mpr
  refine ⟨R ∪ S, Finset.union_subset hRA hSB, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hRS, hRcard, hScard]
  · rw [Finset.sum_union hRS]

/-! ## Greedy packing of pair representations -/

/-- The two-element subsets of `B` that represent `z`. -/
def pairRepresentations (B : Finset ℤ) (z : ℤ) : Finset (Finset ℤ) :=
  (B.powersetCard 2).filter fun P ↦ (∑ x ∈ P, x) = z

lemma mem_pairRepresentations {B P : Finset ℤ} {z : ℤ} :
    P ∈ pairRepresentations B z ↔
      P ⊆ B ∧ P.card = 2 ∧ (∑ x ∈ P, x) = z := by
  simp only [pairRepresentations, Finset.mem_filter, Finset.mem_powersetCard]
  tauto

/-- Two two-element integer sets that contain the same specified element
and have the same sum are equal. -/
lemma pair_eq_of_mem_of_sum_eq {P Q : Finset ℤ} {u : ℤ}
    (hPcard : P.card = 2) (hQcard : Q.card = 2)
    (huP : u ∈ P) (huQ : u ∈ Q)
    (hsum : (∑ x ∈ P, x) = ∑ x ∈ Q, x) : P = Q := by
  have hPe : (P.erase u).card = 1 := by
    rw [Finset.card_erase_of_mem huP, hPcard]
  have hQe : (Q.erase u).card = 1 := by
    rw [Finset.card_erase_of_mem huQ, hQcard]
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hPe
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hQe
  have hPform : P = {u, p} := by
    rw [← Finset.insert_erase huP, hp]
  have hQform : Q = {u, q} := by
    rw [← Finset.insert_erase huQ, hq]
  have hup : u ≠ p := by
    apply Finset.card_pair_eq_two_iff.mp
    simpa [← hPform] using hPcard
  have huq : u ≠ q := by
    apply Finset.card_pair_eq_two_iff.mp
    simpa [← hQform] using hQcard
  rw [hPform, hQform] at hsum
  have hpq : u + p = u + q := by simpa [hup, huq] using hsum
  have : p = q := add_left_cancel hpq
  simp [hPform, hQform, this]

/-- For a fixed vertex `u` and fixed target sum `z`, at most one pair
representation of `z` contains `u`. -/
lemma card_pairRepresentations_filter_mem_le_one
    (B : Finset ℤ) (z u : ℤ) :
    ((pairRepresentations B z).filter fun P ↦ u ∈ P).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro P hP Q hQ
  rw [Finset.mem_filter] at hP hQ
  exact pair_eq_of_mem_of_sum_eq
    (mem_pairRepresentations.mp hP.1).2.1
    (mem_pairRepresentations.mp hQ.1).2.1 hP.2 hQ.2
    ((mem_pairRepresentations.mp hP.1).2.2.trans
      (mem_pairRepresentations.mp hQ.1).2.2.symm)

/-- Pair representations meeting a prescribed used set. -/
def intersectingPairRepresentations (B : Finset ℤ) (z : ℤ)
    (U : Finset ℤ) : Finset (Finset ℤ) :=
  U.biUnion fun u ↦ (pairRepresentations B z).filter fun P ↦ u ∈ P

/-- At most `|U|` pair representations of one integer meet `U`: each used
integer belongs to at most one such pair. -/
lemma card_intersectingPairRepresentations_le
    (B : Finset ℤ) (z : ℤ) (U : Finset ℤ) :
    (intersectingPairRepresentations B z U).card ≤ U.card := by
  calc
    (intersectingPairRepresentations B z U).card
        ≤ ∑ u ∈ U, ((pairRepresentations B z).filter fun P ↦ u ∈ P).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ U, 1 := by
      exact Finset.sum_le_sum fun u _ ↦
        card_pairRepresentations_filter_mem_le_one B z u
    _ = U.card := by simp

/-- If `z` has more pair representations than there are already used
vertices, one representation is disjoint from the used set.  This is the
precise pigeonhole step in the greedy iteration. -/
lemma exists_pairRepresentation_disjoint
    {B U : Finset ℤ} {z : ℤ}
    (hcard : U.card < (pairRepresentations B z).card) :
    ∃ P ∈ pairRepresentations B z, Disjoint P U := by
  by_contra h
  push Not at h
  have hsub : pairRepresentations B z ⊆
      intersectingPairRepresentations B z U := by
    intro P hP
    obtain ⟨u, huP, huU⟩ := Finset.not_disjoint_iff.mp (h P hP)
    exact Finset.mem_biUnion.mpr
      ⟨u, huU, Finset.mem_filter.mpr ⟨hP, huP⟩⟩
  have := (Finset.card_le_card hsub).trans
    (card_intersectingPairRepresentations_le B z U)
  omega

/-- Greedy transfer from a pair-rich ordinary sumset to a restricted
sumset.  Repetitions are allowed in `n • S`.  At the `i`-th step the already
chosen pairs use `2i ≤ v` vertices, while the new summand has more than `v`
pair representations, so a disjoint representation remains.

This is the exact combinatorial iteration used in the proof of
Deshouillers--Freiman Proposition 4 (there `n = v / 2`). -/
theorem nsmul_subset_restrictedSumset_two_mul_of_pair_rich
    {B S : Finset ℤ} {v : ℕ}
    (hrich : ∀ z ∈ S, v < (pairRepresentations B z).card) :
    ∀ n : ℕ, 2 * n ≤ v → n • S ⊆ restrictedSumset (2 * n) B := by
  intro n hn
  induction n with
  | zero =>
      intro z hz
      simpa [restrictedSumset_zero] using hz
  | succ n ih =>
      intro z hz
      rw [succ_nsmul] at hz
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hz
      have hn' : 2 * n ≤ v := by omega
      have hx' := ih hn' hx
      obtain ⟨U, hUB, hUcard, hUsum⟩ := mem_restrictedSumset.mp hx'
      have hUcardLt : U.card < (pairRepresentations B y).card := by
        rw [hUcard]
        exact hn'.trans_lt (hrich y hy)
      obtain ⟨P, hPrep, hPU⟩ := exists_pairRepresentation_disjoint hUcardLt
      obtain ⟨hPB, hPcard, hPsum⟩ := mem_pairRepresentations.mp hPrep
      apply mem_restrictedSumset.mpr
      refine ⟨P ∪ U, Finset.union_subset hPB hUB, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hPU, hPcard, hUcard]
        omega
      · rw [Finset.sum_union hPU, hPsum, hUsum]
        omega

/-! ## The residual two-sum injection -/

/-- If `a` and `b` are distinct members of `B`, translation by `a+b` maps
every restricted two-sum avoiding `a,b` into a restricted four-sum of `B`.
This is the injective map at the heart of Deshouillers--Freiman Proposition
3.3. -/
lemma add_add_restrictedSumset_two_erase_mem_restrictedSumset_four
    {B : Finset ℤ} {a b z : ℤ} (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b)
    (hz : z ∈ restrictedSumset 2 ((B.erase a).erase b)) :
    a + b + z ∈ restrictedSumset 4 B := by
  obtain ⟨S, hSsub, hScard, hSsum⟩ := mem_restrictedSumset.mp hz
  have hsa : a ∉ S := by
    intro h
    have := hSsub h
    simp at this
  have hsb : b ∉ S := by
    intro h
    have := hSsub h
    simp at this
  apply mem_restrictedSumset.mpr
  refine ⟨insert a (insert b S), ?_, ?_, ?_⟩
  · simp only [Finset.insert_subset_iff, ha, hb, true_and]
    exact hSsub.trans ((Finset.erase_subset b (B.erase a)).trans
      (Finset.erase_subset a B))
  · simp [hsa, hsb, hab, hScard]
  · simp [hsa, hsb, hab, hSsum]
    ring

/-- Cardinal form of the residual injection. -/
lemma card_restrictedSumset_two_erase_le_four
    {B : Finset ℤ} {a b : ℤ} (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b) :
    (restrictedSumset 2 ((B.erase a).erase b)).card ≤
      (restrictedSumset 4 B).card := by
  refine Finset.card_le_card_of_injOn (fun z : ℤ ↦ a + b + z) ?_ ?_
  · intro z hz
    exact add_add_restrictedSumset_two_erase_mem_restrictedSumset_four ha hb hab hz
  · intro x _ y _ hxy
    exact add_left_cancel hxy

/-! ## Covering the ordinary two-fold sumset -/

/-- Every ordinary pair sum is either in a translate by one of two fixed
elements, is a diagonal sum, or is a restricted pair sum avoiding those two
elements. -/
lemma add_self_subset_three_images_union_restrictedSumset_two_erase
    {B : Finset ℤ} {a b : ℤ} :
    B + B ⊆
      (B.image (fun x ↦ a + x) ∪ B.image (fun x ↦ b + x)) ∪
        (B.image (fun x ↦ x + x) ∪
          restrictedSumset 2 ((B.erase a).erase b)) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  by_cases hxa : x = a
  · subst x
    simp [Finset.mem_image, hy]
  by_cases hya : y = a
  · subst y
    simp [Finset.mem_image, hx, add_comm]
  by_cases hxb : x = b
  · subst x
    simp [Finset.mem_image, hy]
  by_cases hyb : y = b
  · subst y
    simp [Finset.mem_image, hx, add_comm]
  by_cases hxy : x = y
  · subst y
    simp only [Finset.mem_union]
    exact Or.inr (Or.inl (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  simp only [Finset.mem_union, Finset.mem_image]
  right
  right
  apply mem_restrictedSumset.mpr
  refine ⟨{x, y}, ?_, Finset.card_pair hxy, ?_⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
      Finset.mem_erase]
    exact ⟨⟨hxb, hxa, hx⟩, ⟨hyb, hya, hy⟩⟩
  · simp [hxy]

/-- The cardinal cover corresponding to
`add_self_subset_three_images_union_restrictedSumset_two_erase`. -/
lemma card_add_self_le_three_mul_add_card_restrictedSumset_two_erase
    {B : Finset ℤ} {a b : ℤ} :
    (B + B).card ≤
      3 * B.card + (restrictedSumset 2 ((B.erase a).erase b)).card := by
  have hcover := Finset.card_le_card
    (add_self_subset_three_images_union_restrictedSumset_two_erase
      (B := B) (a := a) (b := b))
  have h₁ := Finset.card_union_le
    (B.image (fun x ↦ a + x) ∪ B.image (fun x ↦ b + x))
    (B.image (fun x ↦ x + x) ∪ restrictedSumset 2 ((B.erase a).erase b))
  have h₂ := Finset.card_union_le (B.image (fun x ↦ a + x))
    (B.image (fun x ↦ b + x))
  have h₃ := Finset.card_union_le (B.image (fun x ↦ x + x))
    (restrictedSumset 2 ((B.erase a).erase b))
  have haCard : (B.image (fun x ↦ a + x)).card ≤ B.card := Finset.card_image_le
  have hbCard : (B.image (fun x ↦ b + x)).card ≤ B.card := Finset.card_image_le
  have hdCard : (B.image (fun x ↦ x + x)).card ≤ B.card := Finset.card_image_le
  omega

/-- Deshouillers--Freiman Proposition 3.3.  The hypothesis `2 ≤ |B|` is
only used to select the two distinct elements needed by the covering proof. -/
theorem card_add_self_le_three_mul_add_card_restrictedSumset_four
    {B : Finset ℤ} (hB : 2 ≤ B.card) :
    (B + B).card ≤ 3 * B.card + (restrictedSumset 4 B).card := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hB
  exact (card_add_self_le_three_mul_add_card_restrictedSumset_two_erase
    (B := B) (a := a) (b := b)).trans
    (Nat.add_le_add_left (card_restrictedSumset_two_erase_le_four ha hb hab) _)

/-! ## Controlled iteration -/

/-- A rational linear bound for the restricted four-fold sumset controls all
ordinary manyfold sumsets.  This is the direct interface used by later
growth arguments: Proposition 3.3 supplies small doubling, and the
Plünnecke--Ruzsa inequality performs the iteration. -/
theorem card_nsmul_le_of_restrictedSumset_four_bound
    {B : Finset ℤ} (hBcard : 2 ≤ B.card) {K : ℚ≥0}
    (hfour : (3 * B.card + (restrictedSumset 4 B).card : ℚ≥0) ≤ K * B.card)
    (n : ℕ) :
    ((n • B).card : ℚ≥0) ≤ K ^ n * B.card := by
  have hB : B.Nonempty := Finset.card_pos.mp (by omega)
  have hdoublingNat :=
    card_add_self_le_three_mul_add_card_restrictedSumset_four hBcard
  have hdoubling : ((B + B).card : ℚ≥0) ≤ K * B.card := by
    calc
      ((B + B).card : ℚ≥0) ≤
          3 * (B.card : ℚ≥0) + ((restrictedSumset 4 B).card : ℚ≥0) := by
        exact_mod_cast hdoublingNat
      _ ≤ K * B.card := hfour
  calc
    ((n • B).card : ℚ≥0)
        ≤ (((B + B).card : ℚ≥0) / B.card) ^ n * B.card :=
      Finset.pluennecke_ruzsa_inequality_nsmul_add hB B n
    _ ≤ K ^ n * B.card := by
      gcongr
      exact (div_le_iff₀ (by exact_mod_cast Finset.card_pos.mpr hB)).mpr hdoubling

/-- Integer-multiplier specialization of the controlled iteration theorem.
If `|4^∧B| ≤ q|B|`, then `|nB| ≤ (q+3)^n |B|` (written in `ℚ≥0` to
avoid divisibility and rounding artifacts). -/
theorem card_nsmul_le_of_card_restrictedSumset_four_le_mul
    {B : Finset ℤ} (hBcard : 2 ≤ B.card) {q : ℕ}
    (hfour : (restrictedSumset 4 B).card ≤ q * B.card) (n : ℕ) :
    ((n • B).card : ℚ≥0) ≤ (q + 3 : ℚ≥0) ^ n * B.card := by
  apply card_nsmul_le_of_restrictedSumset_four_bound hBcard (K := q + 3) ?_ n
  exact_mod_cast (show 3 * B.card + (restrictedSumset 4 B).card ≤
    (q + 3) * B.card from (Nat.add_le_add_left hfour _).trans_eq (by ring))

end

end Erdos874
