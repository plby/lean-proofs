import Wikipedia.SmoothSixDPoincare.ZeroIndexBoundaryPair

/-! # Reverse the actual surgery pieces and identify a top-index sphere removal -/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

open PuncturedHandle

variable {E F R X Y : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y)

def reverse : SurgeryBoundaryPair F E R Y X where
  oldExterior := d.newExterior
  newExterior := d.oldExterior
  oldPiece := d.newPiece ∘ Prod.swap
  newPiece := d.oldPiece ∘ Prod.swap
  oldExterior_closed := d.newExterior_closed
  newExterior_closed := d.oldExterior_closed
  oldPiece_closed := d.newPiece_closed.comp
    (Homeomorph.prodComm (UnitSphere F) (UnitBall E)).isClosedEmbedding
  newPiece_closed := d.oldPiece_closed.comp
    (Homeomorph.prodComm (UnitBall F) (UnitSphere E)).isClosedEmbedding
  old_cover := by
    have hs : Surjective (Prod.swap : UnitSphere F × UnitBall E → UnitBall E × UnitSphere F) :=
      (Homeomorph.prodComm (UnitSphere F) (UnitBall E)).surjective
    rw [hs.range_comp]
    exact d.new_cover
  new_cover := by
    have hs : Surjective (Prod.swap : UnitBall F × UnitSphere E → UnitSphere E × UnitBall F) :=
      (Homeomorph.prodComm (UnitBall F) (UnitSphere E)).surjective
    rw [hs.range_comp]
    exact d.old_cover
  boundary := d.boundary ∘ Prod.swap
  old_overlap := by
    intro r p
    constructor
    · intro h
      obtain ⟨q, hr, hp⟩ := (d.new_overlap r p.swap).mp h
      exact ⟨q.swap, hr, congrArg Prod.swap hp⟩
    · rintro ⟨q, rfl, rfl⟩
      exact (d.new_overlap _ _).mpr ⟨q.swap, rfl, rfl⟩
  new_overlap := by
    intro r p
    constructor
    · intro h
      obtain ⟨q, hr, hp⟩ := (d.old_overlap r p.swap).mp h
      exact ⟨q.swap, hr, congrArg Prod.swap hp⟩
    · rintro ⟨q, rfl, rfl⟩
      exact (d.old_overlap _ _).mpr ⟨q.swap, rfl, rfl⟩

theorem reverse_attachingSphere (v : UnitSphere F) :
    d.reverse.attachingSphere v = d.beltSphere v := rfl

theorem reverse_beltSphere (u : UnitSphere E) :
    d.reverse.beltSphere u = d.attachingSphere u := rfl

variable [Subsingleton F]

def topIndexBoundaryHomeomorph : (Y ⊕ UnitSphere E) ≃ₜ X :=
  d.reverse.zeroIndexBoundaryHomeomorph

theorem topIndexBoundaryHomeomorph_exterior (r : R) :
    d.topIndexBoundaryHomeomorph (Sum.inl (d.newExterior r)) = d.oldExterior r :=
  d.reverse.zeroIndexBoundaryHomeomorph_old r

theorem topIndexBoundaryHomeomorph_attaching (u : UnitSphere E) :
    d.topIndexBoundaryHomeomorph (Sum.inr u) = d.attachingSphere u := rfl

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
