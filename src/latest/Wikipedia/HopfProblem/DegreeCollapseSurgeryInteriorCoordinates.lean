import Wikipedia.HopfProblem.DegreeCollapseSurgeryExteriorHomology

/-!
# The genuine open product piece and core-complement cover

The complement of the closed exterior is exactly the image of the open
normal ball. The original closed embedding restricts to an actual
homeomorphism onto this open piece. Together with the whole core complement
it covers the original endpoint, without an auxiliary atlas or quotient.
-/

noncomputable section

open Set Function Topology Metric

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryInteriorCoordinates

open Wikipedia.SmoothSixDPoincare PuncturedHandle

variable {E F R X Y : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y)

abbrev OpenBall (F : Type*) [NormedAddCommGroup F] := {v : F // ‖v‖ < 1}

def interiorSet : Set X := (range d.oldExterior)ᶜ

theorem isOpen_interiorSet : IsOpen (interiorSet d) :=
  d.oldExterior_closed.isClosed_range.isOpen_compl

theorem oldPiece_mem_exterior_iff (p : UnitSphere E × UnitBall F) :
    d.oldPiece p ∈ range d.oldExterior ↔ ‖p.2.val‖ = 1 := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨q, -, rfl⟩ := (d.old_overlap r p).mp hr
    exact mem_sphere_zero_iff_norm.mp q.2.property
  · intro hp
    let q : UnitSphere E × UnitSphere F := (p.1, ⟨p.2.val, mem_sphere_zero_iff_norm.mpr hp⟩)
    exact ⟨d.boundary q, (d.old_overlap _ _).mpr ⟨q, rfl, rfl⟩⟩

theorem oldPiece_mem_interior_iff (p : UnitSphere E × UnitBall F) :
    d.oldPiece p ∈ interiorSet d ↔ ‖p.2.val‖ < 1 := by
  change d.oldPiece p ∉ range d.oldExterior ↔ _
  rw [oldPiece_mem_exterior_iff]
  constructor
  · intro h
    by_contra hn
    exact h (le_antisymm p.2.property (le_of_not_gt hn))
  · exact fun h ↦ h.ne

theorem interior_subset_range : interiorSet d ⊆ range d.oldPiece := by
  intro x hx
  have hc : x ∈ range d.oldExterior ∪ range d.oldPiece := by rw [d.old_cover]; trivial
  exact hc.resolve_left hx

def parameterHomeomorph : (UnitSphere E × OpenBall F) ≃ₜ (d.oldPiece ⁻¹' interiorSet d) where
  toFun p := ⟨(p.1, ⟨p.2.val, p.2.property.le⟩),
    (oldPiece_mem_interior_iff d _).mpr p.2.property⟩
  invFun p := (p.val.1, ⟨p.val.2.val, (oldPiece_mem_interior_iff d _).mp p.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)

def interiorHomeomorph : (UnitSphere E × OpenBall F) ≃ₜ interiorSet d :=
  (parameterHomeomorph d).trans
    (d.oldPiece_closed.isEmbedding.homeomorphOfSubsetRange (interior_subset_range d))

theorem interiorHomeomorph_point (p : UnitSphere E × OpenBall F) :
    (interiorHomeomorph d p).val = d.oldPiece (p.1, ⟨p.2.val, p.2.property.le⟩) := rfl

theorem interiorHomeomorph_zero (u : UnitSphere E) :
    (interiorHomeomorph d (u, ⟨0, by simp⟩)).val = d.attachingSphere u := rfl

theorem isOpen_coreComplement [ProperSpace E] [T2Space X] : IsOpen d.OldComplement :=
  (isCompact_range d.attachingSphere.continuous).isClosed.isOpen_compl

theorem complement_interior_cover : d.OldComplement ∪ interiorSet d = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  by_cases hx : x ∈ range d.oldExterior
  · obtain ⟨r, rfl⟩ := hx
    exact Or.inl (d.oldExterior_avoids r)
  · exact Or.inr hx

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryInteriorCoordinates
