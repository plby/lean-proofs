/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Definitions

/-!
# Kirchberger witnesses and strict separation in three dimensions

This file proves the finite form of Kirchberger's theorem used in the
Pohoata--Zakharov argument.  If the convex hulls of two finite point sets in
`ℝ³` meet, the intersection is already witnessed by subsets containing at
most five points in total.  The proof applies Carathéodory's theorem in the
four-dimensional homogenized space `Point 3 × ℝ`.

We also record convenient strict-separation forms for finite point sets and
their convex hulls.
-/

namespace Erdos651

open Set

noncomputable section

private def kirchbergerPos (a : Point 3) : Point 3 × ℝ := (a, 1)

private def kirchbergerNeg (b : Point 3) : Point 3 × ℝ := (-b, -1)

private lemma kirchbergerPos_injective : Function.Injective kirchbergerPos := by
  intro a b h
  exact congrArg Prod.fst h

private lemma kirchbergerNeg_injective : Function.Injective kirchbergerNeg := by
  intro a b h
  simpa [kirchbergerNeg] using congrArg (fun z : Point 3 × ℝ => -z.1) h

/-- **Finite Kirchberger theorem in `ℝ³`.**  An intersection of two finite
convex hulls has a witness using at most five points in total. -/
theorem finite_kirchberger_point3 (A B : Finset (Point 3))
    (hAB : (convexHull ℝ (A : Set (Point 3)) ∩
      convexHull ℝ (B : Set (Point 3))).Nonempty) :
    ∃ A' B' : Finset (Point 3), A' ⊆ A ∧ B' ⊆ B ∧
      A'.card + B'.card ≤ 5 ∧
      (convexHull ℝ (A' : Set (Point 3)) ∩
        convexHull ℝ (B' : Set (Point 3))).Nonempty := by
  classical
  obtain ⟨x, hxA, hxB⟩ := hAB
  rw [Finset.mem_convexHull'] at hxA hxB
  obtain ⟨wa, hwa_nonneg, hwa_sum, hwa_center⟩ := hxA
  obtain ⟨wb, hwb_nonneg, hwb_sum, hwb_center⟩ := hxB
  let S : Finset (Point 3 × ℝ) :=
    A.image kirchbergerPos ∪ B.image kirchbergerNeg
  have hdisj : Disjoint (A.image kirchbergerPos) (B.image kirchbergerNeg) := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzA
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hzB
    have := congrArg Prod.snd heq
    norm_num [kirchbergerPos, kirchbergerNeg] at this
  let w : Point 3 × ℝ → ℝ := fun z =>
    if z.2 = 1 then (2 : ℝ)⁻¹ * wa z.1 else (2 : ℝ)⁻¹ * wb (-z.1)
  have hw_nonneg : ∀ z ∈ S, 0 ≤ w z := by
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      simp [w, kirchbergerPos, hwa_nonneg a ha]
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      simp only [w, kirchbergerNeg, neg_neg]
      rw [if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
      exact mul_nonneg (by norm_num) (hwb_nonneg b hb)
  have hw_sum : ∑ z ∈ S, w z = 1 := by
    rw [show S = A.image kirchbergerPos ∪ B.image kirchbergerNeg by rfl,
      Finset.sum_union hdisj]
    rw [Finset.sum_image kirchbergerPos_injective.injOn,
      Finset.sum_image kirchbergerNeg_injective.injOn]
    simp only [w, kirchbergerPos, kirchbergerNeg, neg_neg,
      if_pos rfl, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    rw [← Finset.mul_sum, hwa_sum, ← Finset.mul_sum, hwb_sum]
    norm_num
  have hw_center : ∑ z ∈ S, w z • z = 0 := by
    rw [show S = A.image kirchbergerPos ∪ B.image kirchbergerNeg by rfl,
      Finset.sum_union hdisj]
    rw [Finset.sum_image kirchbergerPos_injective.injOn,
      Finset.sum_image kirchbergerNeg_injective.injOn]
    simp only [w, kirchbergerPos, kirchbergerNeg, neg_neg,
      if_pos rfl, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Prod.fst_zero]
      simp_rw [mul_smul, smul_neg]
      rw [← Finset.smul_sum, Finset.sum_neg_distrib, ← Finset.smul_sum,
        hwa_center, hwb_center]
      simp
    · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero,
        smul_eq_mul, mul_one, mul_neg, mul_one]
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hwa_sum, hwb_sum]
      norm_num
  have hzero : (0 : Point 3 × ℝ) ∈ convexHull ℝ (S : Set (Point 3 × ℝ)) := by
    rw [Finset.mem_convexHull']
    exact ⟨w, hw_nonneg, hw_sum, hw_center⟩
  rw [convexHull_eq_union] at hzero
  simp only [Set.mem_iUnion, exists_prop] at hzero
  obtain ⟨t, htS, ht_ind, ht_zero⟩ := hzero
  let A' : Finset (Point 3) := A.filter fun a => kirchbergerPos a ∈ t
  let B' : Finset (Point 3) := B.filter fun b => kirchbergerNeg b ∈ t
  have hA'_sub : A' ⊆ A := Finset.filter_subset _ _
  have hB'_sub : B' ⊆ B := Finset.filter_subset _ _
  have ht_eq : t = A'.image kirchbergerPos ∪ B'.image kirchbergerNeg := by
    ext z
    constructor
    · intro hz
      have hzS := htS hz
      change z ∈ A.image kirchbergerPos ∪ B.image kirchbergerNeg at hzS
      rw [Finset.mem_union] at hzS
      rcases hzS with hzA | hzB
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzA
        rw [Finset.mem_union]
        exact Or.inl (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hz⟩, rfl⟩)
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hzB
        rw [Finset.mem_union]
        exact Or.inr (Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hz⟩, rfl⟩)
    · intro hz
      rw [Finset.mem_union] at hz
      rcases hz with hz | hz
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        exact (Finset.mem_filter.mp ha).2
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
        exact (Finset.mem_filter.mp hb).2
  have hcard : A'.card + B'.card ≤ 5 := by
    have ht_card : t.card ≤ 5 := by
      calc
        t.card = Fintype.card t := by simp
        _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → Point 3 × ℝ))) + 1 :=
          ht_ind.card_le_finrank_succ
        _ ≤ Module.finrank ℝ (Point 3 × ℝ) + 1 :=
          Nat.add_le_add_right (Submodule.finrank_le _) 1
        _ = 5 := by simp [Point]
    rw [ht_eq, Finset.card_union_of_disjoint] at ht_card
    · simpa [Finset.card_image_iff.mpr kirchbergerPos_injective.injOn,
        Finset.card_image_iff.mpr kirchbergerNeg_injective.injOn] using ht_card
    · exact hdisj.mono (Finset.image_subset_image hA'_sub)
        (Finset.image_subset_image hB'_sub)
  rw [Finset.mem_convexHull'] at ht_zero
  obtain ⟨wt, hwt_nonneg, hwt_sum, hwt_center⟩ := ht_zero
  have ht_disj : Disjoint (A'.image kirchbergerPos) (B'.image kirchbergerNeg) :=
    hdisj.mono (Finset.image_subset_image hA'_sub) (Finset.image_subset_image hB'_sub)
  have hsum_split :
      (∑ a ∈ A', wt (kirchbergerPos a)) +
        ∑ b ∈ B', wt (kirchbergerNeg b) = 1 := by
    rw [ht_eq, Finset.sum_union ht_disj,
      Finset.sum_image kirchbergerPos_injective.injOn,
      Finset.sum_image kirchbergerNeg_injective.injOn] at hwt_sum
    exact hwt_sum
  have hheight :
      (∑ a ∈ A', wt (kirchbergerPos a)) -
        ∑ b ∈ B', wt (kirchbergerNeg b) = 0 := by
    have hsnd := congrArg Prod.snd hwt_center
    rw [ht_eq, Finset.sum_union ht_disj,
      Finset.sum_image kirchbergerPos_injective.injOn,
      Finset.sum_image kirchbergerNeg_injective.injOn] at hsnd
    simpa [kirchbergerPos, kirchbergerNeg, Prod.snd_sum,
      Finset.sum_sub_distrib, sub_eq_add_neg] using hsnd
  have hsumA : ∑ a ∈ A', (2 * wt (kirchbergerPos a)) = 1 := by
    rw [← Finset.mul_sum]
    linarith
  have hsumB : ∑ b ∈ B', (2 * wt (kirchbergerNeg b)) = 1 := by
    rw [← Finset.mul_sum]
    linarith
  let y : Point 3 := ∑ a ∈ A', (2 * wt (kirchbergerPos a)) • a
  have hyA : y ∈ convexHull ℝ (A' : Set (Point 3)) := by
    rw [Finset.mem_convexHull']
    refine ⟨fun a => 2 * wt (kirchbergerPos a), ?_, hsumA, rfl⟩
    intro a ha
    apply mul_nonneg (by norm_num)
    apply hwt_nonneg
    rw [ht_eq, Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hfirst :
      (∑ a ∈ A', wt (kirchbergerPos a) • a) =
        ∑ b ∈ B', wt (kirchbergerNeg b) • b := by
    have hfst := congrArg Prod.fst hwt_center
    rw [ht_eq, Finset.sum_union ht_disj,
      Finset.sum_image kirchbergerPos_injective.injOn,
      Finset.sum_image kirchbergerNeg_injective.injOn] at hfst
    apply sub_eq_zero.mp
    simpa [kirchbergerPos, kirchbergerNeg, Prod.fst_sum,
      Finset.sum_neg_distrib, sub_eq_add_neg] using hfst
  have hy_eq : y = ∑ b ∈ B', (2 * wt (kirchbergerNeg b)) • b := by
    dsimp [y]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, hfirst, Finset.smul_sum]
  have hyB : y ∈ convexHull ℝ (B' : Set (Point 3)) := by
    rw [Finset.mem_convexHull']
    refine ⟨fun b => 2 * wt (kirchbergerNeg b), ?_, hsumB, hy_eq.symm⟩
    intro b hb
    apply mul_nonneg (by norm_num)
    apply hwt_nonneg
    rw [ht_eq, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  exact ⟨A', B', hA'_sub, hB'_sub, hcard, y, hyA, hyB⟩

/-- Disjoint finite convex hulls in `ℝ³` have a strict affine separator. -/
theorem finite_convexHulls_strictly_separated_point3 (A B : Finset (Point 3))
    (hdisj : Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3)))) :
    ∃ (f : Point 3 →L[ℝ] ℝ) (c : ℝ),
      (∀ a ∈ convexHull ℝ (A : Set (Point 3)), f a < c) ∧
      ∀ b ∈ convexHull ℝ (B : Set (Point 3)), c < f b := by
  obtain ⟨f, u, v, hA, huv, hB⟩ :=
    geometric_hahn_banach_compact_closed
      (convex_convexHull ℝ (A : Set (Point 3)))
      (show IsCompact (convexHull ℝ (A : Set (Point 3))) from
        (Finset.finite_toSet A).isCompact_convexHull ℝ)
      (convex_convexHull ℝ (B : Set (Point 3)))
      (show IsClosed (convexHull ℝ (B : Set (Point 3))) from
        ((Finset.finite_toSet B).isCompact_convexHull ℝ).isClosed) hdisj
  exact ⟨f, u, hA, fun b hb => huv.trans (hB b hb)⟩

/-- Pointwise version of strict separation for finite sets in `ℝ³`. -/
theorem finite_sets_strictly_separated_point3 (A B : Finset (Point 3))
    (hdisj : Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3)))) :
    ∃ (f : Point 3 →L[ℝ] ℝ) (c : ℝ),
      (∀ a ∈ A, f a < c) ∧ ∀ b ∈ B, c < f b := by
  obtain ⟨f, c, hA, hB⟩ := finite_convexHulls_strictly_separated_point3 A B hdisj
  exact ⟨f, c,
    fun a ha => hA a (subset_convexHull ℝ _ (Finset.mem_coe.mpr ha)),
    fun b hb => hB b (subset_convexHull ℝ _ (Finset.mem_coe.mpr hb))⟩

end

end Erdos651
