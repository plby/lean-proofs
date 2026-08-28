import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

/-!
# Closed embedded covers of the actual surgery complements

Removing the core or belt restricts the original closed embeddings to the
precise punctured parameter spaces. The common exterior avoids both deleted
spheres. These restricted pieces are exhaustive closed covers of the
noncompact complements, not merely local neighborhoods.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.ClosedCover

theorem isClosedEmbedding_codRestrict {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} (hf : IsClosedEmbedding f) {s : Set B} (hs : ∀ x, f x ∈ s) :
    IsClosedEmbedding (s.codRestrict f hs) :=
  ⟨hf.isEmbedding.codRestrict s hs, (hf.isClosedMap.codRestrict hs).isClosed_range⟩

end Wikipedia.SmoothSixDPoincare.ClosedCover

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

open PuncturedHandle

variable {E F R X Y : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y)

def oldExteriorMap : R → d.OldComplement :=
  d.OldComplement.codRestrict d.oldExterior d.oldExterior_avoids

def newExteriorMap : R → d.NewComplement :=
  d.NewComplement.codRestrict d.newExterior d.newExterior_avoids

def oldParameterComplement : (UnitSphere E × PuncturedBall F) ≃ₜ
    (d.oldPiece ⁻¹' d.OldComplement) :=
  (oldPuncturedDomain E F).trans (Homeomorph.setCongr (by
    ext p
    exact (not_congr (d.oldPiece_mem_core_iff p)).symm))

def newParameterComplement : (PuncturedBall E × UnitSphere F) ≃ₜ
    (d.newPiece ⁻¹' d.NewComplement) :=
  (newPuncturedDomain E F).trans (Homeomorph.setCongr (by
    ext p
    exact (not_congr (d.newPiece_mem_belt_iff p)).symm))

def oldPuncturedMap : UnitSphere E × PuncturedBall F → d.OldComplement :=
  d.OldComplement.restrictPreimage d.oldPiece ∘ d.oldParameterComplement

def newPuncturedMap : PuncturedBall E × UnitSphere F → d.NewComplement :=
  d.NewComplement.restrictPreimage d.newPiece ∘ d.newParameterComplement

theorem oldPuncturedMap_coe (p : UnitSphere E × PuncturedBall F) :
    (d.oldPuncturedMap p : X) = d.oldPiece (oldPunctured p) := rfl

theorem newPuncturedMap_coe (p : PuncturedBall E × UnitSphere F) :
    (d.newPuncturedMap p : Y) = d.newPiece (newPunctured p) := rfl

theorem isClosedEmbedding_oldExteriorMap : IsClosedEmbedding d.oldExteriorMap :=
  ClosedCover.isClosedEmbedding_codRestrict d.oldExterior_closed d.oldExterior_avoids

theorem isClosedEmbedding_newExteriorMap : IsClosedEmbedding d.newExteriorMap :=
  ClosedCover.isClosedEmbedding_codRestrict d.newExterior_closed d.newExterior_avoids

theorem isClosedEmbedding_oldPuncturedMap : IsClosedEmbedding d.oldPuncturedMap :=
  (d.oldPiece_closed.restrictPreimage d.OldComplement).comp
    d.oldParameterComplement.isClosedEmbedding

theorem isClosedEmbedding_newPuncturedMap : IsClosedEmbedding d.newPuncturedMap :=
  (d.newPiece_closed.restrictPreimage d.NewComplement).comp
    d.newParameterComplement.isClosedEmbedding

theorem oldComplement_cover : range d.oldExteriorMap ∪ range d.oldPuncturedMap = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  have hz : (z : X) ∈ range d.oldExterior ∪ range d.oldPiece := by
    rw [d.old_cover]
    trivial
  rcases hz with ⟨r, hr⟩ | ⟨p, hp⟩
  · exact Or.inl ⟨r, Subtype.ext hr⟩
  · have hpavoid : d.oldPiece p ∈ d.OldComplement := hp.symm ▸ z.property
    have hpne : (p.2 : F) ≠ 0 := fun h => hpavoid ((d.oldPiece_mem_core_iff p).mpr h)
    refine Or.inr ⟨(p.1, ⟨p.2, hpne, p.2.property⟩), Subtype.ext ?_⟩
    exact hp

theorem newComplement_cover : range d.newExteriorMap ∪ range d.newPuncturedMap = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro z
  have hz : (z : Y) ∈ range d.newExterior ∪ range d.newPiece := by
    rw [d.new_cover]
    trivial
  rcases hz with ⟨r, hr⟩ | ⟨p, hp⟩
  · exact Or.inl ⟨r, Subtype.ext hr⟩
  · have hpavoid : d.newPiece p ∈ d.NewComplement := hp.symm ▸ z.property
    have hpne : (p.1 : E) ≠ 0 := fun h => hpavoid ((d.newPiece_mem_belt_iff p).mpr h)
    refine Or.inr ⟨(⟨p.1, hpne, p.1.property⟩, p.2), Subtype.ext ?_⟩
    exact hp

/-- No extra overlap appears after deleting the attaching core. -/
theorem oldPunctured_overlap (r : R) (p : UnitSphere E × PuncturedBall F) :
    d.oldExteriorMap r = d.oldPuncturedMap p ↔
      ∃ q, r = d.boundary q ∧ p = (q.1, boundaryPoint q.2) := by
  rw [Subtype.ext_iff]
  change d.oldExterior r = d.oldPiece (oldPunctured p) ↔ _
  rw [d.old_overlap]
  constructor
  · rintro ⟨q, hr, hp⟩
    exact ⟨q, hr, oldPunctured_injective (hp.trans (oldPunctured_boundary q).symm)⟩
  · rintro ⟨q, hr, rfl⟩
    exact ⟨q, hr, oldPunctured_boundary q⟩

/-- The belt complement has exactly the same shared-face incidences. -/
theorem newPunctured_overlap (r : R) (p : PuncturedBall E × UnitSphere F) :
    d.newExteriorMap r = d.newPuncturedMap p ↔
      ∃ q, r = d.boundary q ∧ p = (boundaryPoint q.1, q.2) := by
  rw [Subtype.ext_iff]
  change d.newExterior r = d.newPiece (newPunctured p) ↔ _
  rw [d.new_overlap]
  constructor
  · rintro ⟨q, hr, hp⟩
    exact ⟨q, hr, newPunctured_injective (hp.trans (newPunctured_boundary q).symm)⟩
  · rintro ⟨q, hr, rfl⟩
    exact ⟨q, hr, newPunctured_boundary q⟩

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
