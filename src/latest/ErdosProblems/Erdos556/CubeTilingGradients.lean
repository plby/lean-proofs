import ErdosProblems.Erdos556.CubeTilings

/-!
# Strict transfer derivatives at a cube tiling

A different higher-dimensional profile intersecting a positive face
has strictly larger gradient. This rules out equality in a nontrivial
compression step.
-/

namespace Erdos556

open Finset

theorem distinct_intersecting_faces_card_two : ∀ p q : CubeProfile,
    profileDimension p = 2 → profileDimension q = 2 → p ≠ q →
    ¬ Disjoint (profileVertices p) (profileVertices q) →
      (profileVertices p ∩ profileVertices q).card = 2 := by
  decide

theorem IsCubeTiling.gradient_at_positive {w : CubeProfile → ℝ}
    (ht : IsCubeTiling w) (hw : IsCubeWeight w) (p : CubeProfile) (hp : 0 < w p) :
    cubeGradient w p = 2 * w p - profileDimension p := by
  classical
  unfold cubeGradient
  rw [sum_eq_single p]
  · rw [cubeOverlap_self, one_mul]
  · intro q _ hqp
    by_cases hq : 0 < w q
    · simp only [cubeOverlap, if_pos (ht.disjoint p q hqp.symm hp hq), zero_mul]
    · rw [hw.eq_zero_of_not_pos q hq, mul_zero]
  · intro h
    exact (h (mem_univ p)).elim

theorem IsCubeTiling.gradient_other_face_ge_four {w : CubeProfile → ℝ}
    (ht : IsCubeTiling w) (hw : IsCubeWeight w) (p q : CubeProfile) (hp : 0 < w p)
    (hpdim : profileDimension p = 2) (hqdim : profileDimension q = 2) (hpq : p ≠ q)
    (hinter : ¬ Disjoint (profileVertices p) (profileVertices q)) : 4 ≤ cubeGradient w q := by
  classical
  have hwp : w p = 2 := by
    rcases ht.normalized p hp with ⟨hd, _⟩ | ⟨_, h⟩
    · omega
    · exact h
  have hintcard := distinct_intersecting_faces_card_two p q hpdim hqdim hpq hinter
  have hover : cubeOverlap q p = 1 := by
    have hnot : ¬ Disjoint (profileVertices q) (profileVertices p) := fun h => hinter h.symm
    simp only [cubeOverlap, if_neg hnot]
  have hcover : (∑ r ∈ positiveCubeProfiles w,
      ((profileVertices r ∩ profileVertices q).card : ℝ)) = 4 := by
    have h := ht.sum_intersection_cards hw (profileVertices q)
    rw [profileVertices_card, hqdim] at h
    exact_mod_cast h
  have hpoint (r : CubeProfile) (hr : r ∈ positiveCubeProfiles w) :
      ((profileVertices r ∩ profileVertices q).card : ℝ) + (if r = p then 2 else 0) ≤
        2 * (cubeOverlap q r * w r) := by
    by_cases hrp : r = p
    · subst r
      rw [hintcard, if_pos rfl, hover, hwp]
      norm_num
    rw [if_neg hrp, add_zero]
    by_cases hd : Disjoint (profileVertices q) (profileVertices r)
    · have hz : profileVertices r ∩ profileVertices q = ∅ := disjoint_iff_inter_eq_empty.mp hd.symm
      simp only [hz, card_empty, Nat.cast_zero, cubeOverlap, if_pos hd, zero_mul, mul_zero, le_refl]
    · have hle : ((profileVertices r ∩ profileVertices q).card : ℝ) ≤ (profileVertices r).card := by
        exact_mod_cast card_le_card (show profileVertices r ∩ profileVertices q ⊆ profileVertices r from inter_subset_left)
      rw [ht.card_eq_twice_weight r (mem_filter.mp hr).2] at hle
      simpa only [cubeOverlap, if_neg hd, one_mul] using hle
  have hsum := sum_le_sum hpoint
  have hpP : p ∈ positiveCubeProfiles w := mem_filter.mpr ⟨mem_univ p, hp⟩
  have hrow : (∑ r ∈ positiveCubeProfiles w, cubeOverlap q r * w r) =
      ∑ r, cubeOverlap q r * w r := by
    apply sum_subset (subset_univ _)
    intro r _ hr
    have hz : w r = 0 := hw.eq_zero_of_not_pos r (fun h => hr (mem_filter.mpr ⟨mem_univ r, h⟩))
    rw [hz, mul_zero]
  rw [sum_add_distrib, hcover] at hsum
  have hdelta : (∑ r ∈ positiveCubeProfiles w, if r = p then (2 : ℝ) else 0) = 2 := by simp [hpP]
  rw [hdelta, ← mul_sum, hrow] at hsum
  simp only [cubeGradient, hqdim, Nat.cast_ofNat]
  linarith only [hsum]

theorem IsCubeTiling.gradient_high_profile_gt {w : CubeProfile → ℝ}
    (ht : IsCubeTiling w) (hw : IsCubeWeight w) (p q : CubeProfile) (hp : 0 < w p)
    (hpdim : 2 ≤ profileDimension p) (hqdim : 2 ≤ profileDimension q) (hpq : p ≠ q)
    (hover : cubeOverlap p q = 1) : cubeGradient w p < cubeGradient w q := by
  have hpface : profileDimension p = 2 ∧ w p = 2 := by
    rcases ht.normalized p hp with ⟨hd, _⟩ | h
    · omega
    · exact h
  have hgp : cubeGradient w p = 2 := by
    rw [ht.gradient_at_positive hw p hp, hpface.1, hpface.2]
    norm_num
  rw [hgp]
  by_cases hq3 : profileDimension q = 3
  · have hq : q = wholeCube := (profileDimension_three_iff q).mp hq3
    rw [hq, cubeGradient_wholeCube, hw.sum_four]
    norm_num
  · have hqmax := profileDimension_le_three q
    have hq2 : profileDimension q = 2 := by omega
    have hnot : ¬ Disjoint (profileVertices p) (profileVertices q) := by
      intro h
      simp only [cubeOverlap, if_pos h] at hover
      norm_num at hover
    have hg := ht.gradient_other_face_ge_four hw p q hp hpface.1 hq2 hpq hnot
    linarith

#print axioms IsCubeTiling.gradient_high_profile_gt

end Erdos556
