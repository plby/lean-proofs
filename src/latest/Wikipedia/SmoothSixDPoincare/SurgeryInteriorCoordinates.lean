import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

/-!
# The actual open disk-times-sphere neighborhood of the new belt sphere

The complement of the closed common exterior is exactly the open radial part
of the new surgery piece. These coordinates use only the proved closed covers
and precise face incidences, not smoothness of the boundary homeomorphism.
-/

noncomputable section

open Set Topology Metric

namespace Wikipedia.SmoothSixDPoincare

namespace PuncturedHandle

abbrev OpenUnitBall (N : Type*) [NormedAddCommGroup N] := {x : N // ‖x‖ < 1}

end PuncturedHandle

namespace SurgeryBoundaryPair

open PuncturedHandle

variable {N P R X Y : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair N P R X Y)

abbrev NewInterior : Set Y := (range d.newExterior)ᶜ

theorem isOpen_newInterior : IsOpen d.NewInterior :=
  d.newExterior_closed.isClosed_range.isOpen_compl

theorem newPiece_mem_exterior_iff (p : UnitBall N × UnitSphere P) :
    d.newPiece p ∈ range d.newExterior ↔ ‖(p.1 : N)‖ = 1 := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨q, -, rfl⟩ := (d.new_overlap r p).mp hr
    exact mem_sphere_zero_iff_norm.mp q.1.property
  · intro hp
    let q : UnitSphere N × UnitSphere P :=
      (⟨p.1, mem_sphere_zero_iff_norm.mpr hp⟩, p.2)
    exact ⟨d.boundary q, (d.new_overlap _ _).mpr ⟨q, rfl, rfl⟩⟩

theorem newPiece_mem_newInterior_iff (p : UnitBall N × UnitSphere P) :
    d.newPiece p ∈ d.NewInterior ↔ ‖(p.1 : N)‖ < 1 := by
  change ¬d.newPiece p ∈ range d.newExterior ↔ _
  rw [d.newPiece_mem_exterior_iff]
  constructor
  · intro hp
    rcases lt_or_eq_of_le p.1.property with h | h
    · exact h
    · exact (hp h).elim
  · exact fun h => h.ne

theorem newInterior_subset_range : d.NewInterior ⊆ range d.newPiece := by
  intro y hy
  have hc : y ∈ range d.newExterior ∪ range d.newPiece := by rw [d.new_cover]; trivial
  exact hc.resolve_left hy

def newInteriorParameter : (OpenUnitBall N × UnitSphere P) ≃ₜ (d.newPiece ⁻¹' d.NewInterior) where
  toFun p := ⟨(⟨p.1, p.1.property.le⟩, p.2), (d.newPiece_mem_newInterior_iff _).mpr p.1.property⟩
  invFun p := (⟨p.val.1, (d.newPiece_mem_newInterior_iff _).mp p.property⟩, p.val.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Genuine open normal coordinates on the whole neighborhood, including the belt zero section. -/
def newInteriorHomeomorph : (OpenUnitBall N × UnitSphere P) ≃ₜ d.NewInterior :=
  d.newInteriorParameter.trans
    (d.newPiece_closed.isEmbedding.homeomorphOfSubsetRange d.newInterior_subset_range)

theorem newInteriorHomeomorph_coe (p : OpenUnitBall N × UnitSphere P) :
    (d.newInteriorHomeomorph p : Y) = d.newPiece (⟨p.1, p.1.property.le⟩, p.2) := rfl

theorem beltSphere_mem_newInterior (v : UnitSphere P) :
    d.beltSphere v ∈ d.NewInterior := by
  apply (d.newPiece_mem_newInterior_iff (ballZero, v)).mpr
  simp [ballZero]

theorem newInteriorHomeomorph_zero (v : UnitSphere P) :
    d.newInteriorHomeomorph (⟨0, by simp⟩, v) =
      ⟨d.beltSphere v, d.beltSphere_mem_newInterior v⟩ := rfl

theorem newInteriorHomeomorph_mem_belt_iff (p : OpenUnitBall N × UnitSphere P) :
    (d.newInteriorHomeomorph p : Y) ∈ range d.beltSphere ↔ (p.1 : N) = 0 :=
  d.newPiece_mem_belt_iff (⟨p.1, p.1.property.le⟩, p.2)

end SurgeryBoundaryPair

end Wikipedia.SmoothSixDPoincare
