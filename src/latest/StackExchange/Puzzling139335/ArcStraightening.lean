import Wikipedia.SchoenfliesTheorem.JordanSchoenflies

/-!
# Straightening a named Jordan subarc

Matching the parametrizations of two pairs of Jordan arcs gives a boundary
homeomorphism respecting the named arcs.  Jordan--Schoenflies extends it to the
plane.  In particular, either arc of a cut pair can be carried to two consecutive
sides of the model square, and hence made polygonal.
-/

open Set unitInterval Schoenflies

namespace Puzzling139335

private theorem image_concatenate_lowerHalf (f g : ℝ → Plane) :
    concatenate f g '' lowerHalf = f '' I := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨2 * t, double_mem_I ht, (concatenate_of_le ht.2).symm⟩
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨t / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [concatenate_of_le (by linarith [ht.2])]
    congr 1
    ring

private theorem image_concatenate_upperHalf {f g : ℝ → Plane}
    (hmid : f 1 = g 0) : concatenate f g '' upperHalf = g '' I := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨2 * t - 1, doubleBack_mem_I ht, (concatenate_upperHalf hmid ht).symm⟩
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [concatenate_upperHalf hmid ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    congr 1
    ring

/-- A plane homeomorphism can match two prescribed pairs of Jordan boundary arcs,
including their named endpoints. -/
theorem cutPair_exists_matching_homeomorph {C D A B A' B' : Set Plane}
    {p q p' q' : Plane} (h : IsCutPair C p q A B)
    (h' : IsCutPair D p' q' A' B') :
    ∃ H : Plane ≃ₜ Plane,
      H '' C = D ∧ H '' A = A' ∧ H '' B = B' ∧ H p = p' ∧ H q = q' := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := h.fst
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := h.snd.reverse
  obtain ⟨f', hf'c, hf'i, hf'im, hf'0, hf'1⟩ := h'.fst
  obtain ⟨g', hg'c, hg'i, hg'im, hg'0, hg'1⟩ := h'.snd.reverse
  have hmid : f 1 = g 0 := hf1.trans hg0.symm
  have hmid' : f' 1 = g' 0 := hf'1.trans hg'0.symm
  have hloop : IsLoop (concatenate f g) := by
    refine IsLoop.concatenate hfc hfi hgc hgi hmid (hg1.trans hf0.symm) ?_
    intro z hz hz'
    have hzAB : z ∈ A ∩ B := ⟨hfim ▸ hz, hgim ▸ hz'⟩
    rw [h.inter_eq] at hzAB
    simpa only [mem_insert_iff, mem_singleton_iff, hf0, hf1] using hzAB
  have hloop' : IsLoop (concatenate f' g') := by
    refine IsLoop.concatenate hf'c hf'i hg'c hg'i hmid' (hg'1.trans hf'0.symm) ?_
    intro z hz hz'
    have hzAB : z ∈ A' ∩ B' := ⟨hf'im ▸ hz, hg'im ▸ hz'⟩
    rw [h'.inter_eq] at hzAB
    simpa only [mem_insert_iff, mem_singleton_iff, hf'0, hf'1] using hzAB
  have hwhole : concatenate f g '' I = C := by
    rw [image_concatenate hmid, hfim, hgim, h.union_eq]
  have hwhole' : concatenate f' g' '' I = D := by
    rw [image_concatenate hmid', hf'im, hg'im, h'.union_eq]
  obtain ⟨e, he⟩ := hloop.exists_homeomorph hloop'
  obtain ⟨H, hH⟩ := jordan_schoenflies_of_homeomorph
    (show IsJordanCurve (concatenate f g '' I) from ⟨_, hloop, rfl⟩)
    (show IsJordanCurve (concatenate f' g' '' I) from ⟨_, hloop', rfl⟩) e
  have hparam : ∀ t ∈ I, H (concatenate f g t) = concatenate f' g' t := by
    intro t ht
    exact (hH ⟨concatenate f g t, mem_image_of_mem _ ht⟩).trans (he t ht)
  have himage (s : Set ℝ) (hs : s ⊆ I) :
      H '' (concatenate f g '' s) = concatenate f' g' '' s := by
    rw [image_image]
    apply image_congr
    intro t ht
    exact hparam t (hs ht)
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hwhole, ← hwhole']
    exact himage I Subset.rfl
  · rw [← hfim, ← hf'im, ← image_concatenate_lowerHalf f g,
      ← image_concatenate_lowerHalf f' g']
    exact himage lowerHalf lowerHalf_subset_I
  · rw [← hgim, ← hg'im, ← image_concatenate_upperHalf hmid,
      ← image_concatenate_upperHalf hmid']
    exact himage upperHalf upperHalf_subset_I
  · simpa only [concatenate_zero, hf0, hf'0] using hparam 0 zero_mem_I
  · have hhalf : (1 / 2 : ℝ) ∈ I := ⟨by norm_num, by norm_num⟩
    have hp := hparam (1 / 2) hhalf
    simpa only [concatenate_of_le le_rfl, mul_one_div, mul_one,
      div_self (by norm_num : (2 : ℝ) ≠ 0), hf1, hf'1] using hp

private theorem modelCutPair : IsCutPair modelCurve cornerNE cornerSW
    (sideTop ∪ sideLeft) (sideBottom ∪ sideRight) where
  fst := isArcBetween_upperSides
  snd := isArcBetween_lowerSides.reverse
  union_eq := modelCurve_eq_sides.symm
  inter_eq := by
    apply Subset.antisymm
    · intro z hz
      exact (mem_insert_iff.mpr <| (upperSides_meet_lowerSides z hz.1 hz.2).imp_right
        mem_singleton_iff.mpr)
    · intro z hz
      rcases mem_insert_iff.mp hz with rfl | hz
      · exact ⟨isArcBetween_upperSides.left_mem, isArcBetween_lowerSides.right_mem⟩
      · rw [mem_singleton_iff] at hz
        subst z
        exact ⟨isArcBetween_upperSides.right_mem, isArcBetween_lowerSides.left_mem⟩

/-- A named arc of a Jordan curve can be made polygonal by a homeomorphism of
the entire plane.  The whole curve is simultaneously mapped to the model square. -/
theorem cutPair_exists_polygonal_homeomorph {C A B : Set Plane} {p q : Plane}
    (h : IsCutPair C p q A B) :
    ∃ H : Plane ≃ₜ Plane,
      H '' C = modelCurve ∧ IsPolygonal (H '' A) ∧ H p ≠ H q := by
  obtain ⟨H, hC, hA, _, _, _⟩ := cutPair_exists_matching_homeomorph h modelCutPair
  refine ⟨H, hC, ?_, H.injective.ne h.fst.ne⟩
  rw [hA]
  exact (isPolygonal_segment cornerNE cornerNW).union
    (isPolygonal_segment cornerNW cornerSW)
    ⟨cornerNW, isArcBetween_sideTop.right_mem, isArcBetween_sideLeft.left_mem⟩

end Puzzling139335
