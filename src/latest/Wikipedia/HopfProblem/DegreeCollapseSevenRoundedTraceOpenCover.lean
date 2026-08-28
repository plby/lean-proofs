import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedCollarHomeomorph

/-!
# A genuine open cover of the compact rounded attachment

Remove the other compact pieces to obtain unchanged cylinder and handle
regions. Their only possible uncovered intersection is the original
attaching face, which lies in the proved open rounded collar. All added
points lie in that collar as well.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def cylinderOnlyPart : Opens (ambientSet A) where
  carrier := {y | y.val ∉ range (UnroundedTrace.handleMap A) ∪
    A.collarSheet '' addedParameters A}
  is_open' := ((UnroundedTrace.closedEmbedding_handle A).isClosed_range.union
    (isCompact_addedImage A).isClosed).isOpen_compl.preimage continuous_subtype_val

def handleOnlyPart : Opens (ambientSet A) where
  carrier := {y | y.val ∉ range (UnroundedTrace.cylinderMap A) ∪
    A.collarSheet '' addedParameters A}
  is_open' := ((UnroundedTrace.closedEmbedding_cylinder A).isClosed_range.union
    (isCompact_addedImage A).isClosed).isOpen_compl.preimage continuous_subtype_val

theorem cylinderOnlyPart_mem (p : cylinderOnlyPart A) :
    p.val.val ∈ range (UnroundedTrace.cylinderMap A) := by
  rcases p.val.property with (hc | hh) | ha
  · exact hc
  · exact (p.property (Or.inl hh)).elim
  · exact (p.property (Or.inr ha)).elim

theorem handleOnlyPart_mem (p : handleOnlyPart A) :
    p.val.val ∈ range (UnroundedTrace.handleMap A) := by
  rcases p.val.property with (hc | hh) | ha
  · exact (p.property (Or.inl hc)).elim
  · exact hh
  · exact (p.property (Or.inr ha)).elim

theorem intersection_mem_collarPart (y : ambientSet A)
    (hc : y.val ∈ range (UnroundedTrace.cylinderMap A))
    (hh : y.val ∈ range (UnroundedTrace.handleMap A)) : y ∈ collarPart A := by
  have hi : y.val ∈ range (UnroundedTrace.cylinderMap A) ∩
      range (UnroundedTrace.handleMap A) := ⟨hc, hh⟩
  rw [UnroundedTrace.map_intersection_eq] at hi
  obtain ⟨⟨s, v⟩, he⟩ := hi
  have hv : v.val ∈ ball (0 : Vector 4) A.radius :=
    (closedBall_subset_ball (UnroundedTrace.handleRadius_lt A)) v.property
  have ht : (0 : ℝ) ∈ Ioo (-collarHeight A) (collarHeight A) :=
    ⟨neg_lt_zero.mpr (collarHeight_pos A), collarHeight_pos A⟩
  have hL : 0 ≤ GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A)
      (v.val, 0) := GeneralRoundedHandleCorner.nonneg_of_corner (bump A)
        (UnroundedTrace.handleRadius_pos A).le (Or.inl le_rfl)
  change y ∈ (collarPart A : Set (ambientSet A))
  rw [← range_collarMap A]
  exact ⟨⟨((s, v.val), 0), hv, ht, hL⟩, Subtype.ext he⟩

theorem openPieces_cover (y : ambientSet A) :
    y ∈ cylinderOnlyPart A ∨ y ∈ handleOnlyPart A ∨ y ∈ collarPart A := by
  by_cases ha : y.val ∈ A.collarSheet '' addedParameters A
  · exact Or.inr (Or.inr (addedImage_mem_part A y ha))
  by_cases hc : y.val ∈ range (UnroundedTrace.cylinderMap A)
  · by_cases hh : y.val ∈ range (UnroundedTrace.handleMap A)
    · exact Or.inr (Or.inr (intersection_mem_collarPart A y hc hh))
    · exact Or.inl (fun h ↦ h.elim hh ha)
  · exact Or.inr (Or.inl (fun h ↦ h.elim hc ha))

inductive Piece where
  | cylinder
  | handle
  | collar

def pieceDomain : Piece → Opens (ambientSet A)
  | .cylinder => cylinderOnlyPart A
  | .handle => handleOnlyPart A
  | .collar => collarPart A

theorem pieceDomain_covers (y : ambientSet A) : ∃ i, y ∈ pieceDomain A i := by
  rcases openPieces_cover A y with hc | hh | hr
  · exact ⟨.cylinder, hc⟩
  · exact ⟨.handle, hh⟩
  · exact ⟨.collar, hr⟩

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
