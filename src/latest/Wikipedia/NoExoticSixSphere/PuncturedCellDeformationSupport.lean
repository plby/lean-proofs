import Wikipedia.NoExoticSixSphere.PuncturedCellAttachment

/-!
# Support control for the actual punctured-cell deformation

The descended deformation keeps points represented in the characteristic
disk inside its image, while fixing the original base. Consequently it
cannot create a new hit of a point outside that disk image. This is the
control needed when correcting one face while avoiding the other cell's
chosen puncture.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Metric Topology
open scoped unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.PuncturedCellAttachment

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A P : TopCat.{u}} [T1Space P]
  {f : TopCat.of (sphere (0 : E) 1) ⟶ A}
  {i : A ⟶ P} {j : TopCat.of (Disk E) ⟶ P}
  (hP : IsPushout f boundary i j) (p : E) (hp : ‖p‖ < 1)

theorem deformation_cell (t : I) (d : j ⁻¹' (punctured (j := j) p hp : Set P)) :
    deformationRel hP p hp (t, cellInclusion (j := j) p hp d) =
      cellInclusion (j := j) p hp (cellDeformationRel hP p hp (t, d)) :=
  PushoutHomotopy.glue_inr (isPushout hP p hp)
    (PushoutHomotopy.baseDeformation (retraction hP p hp) (retraction_baseInclusion hP p hp))
    (PushoutHomotopy.cellDeformation (isPushout hP p hp) (retraction hP p hp)
      (cellRetraction hP p hp) (retraction_cellInclusion hP p hp) (cellDeformationRel hP p hp))
    (PushoutHomotopy.deformations_compatible (isPushout hP p hp) (retraction hP p hp)
      (cellRetraction hP p hp) (retraction_baseInclusion hP p hp)
      (retraction_cellInclusion hP p hp) (cellDeformationRel hP p hp)) t d

theorem deformation_cell_mem (t : I) (x : punctured (j := j) p hp)
    (hx : x.val ∈ Set.range j) : (deformationRel hP p hp (t, x)).val ∈ Set.range j := by
  obtain ⟨d, hd⟩ := hx
  have hdu : j d ∈ punctured (j := j) p hp := by rw [hd]; exact x.property
  let d' : j ⁻¹' (punctured (j := j) p hp : Set P) := ⟨d, hdu⟩
  have he : cellInclusion (j := j) p hp d' = x := Subtype.ext hd
  rw [← he, deformation_cell]
  exact Set.mem_range_self (cellDeformationRel hP p hp (t, d')).val

theorem deformation_fixed_of_mem_base (t : I) (x : punctured (j := j) p hp)
    (hx : x.val ∈ Set.range i) : deformationRel hP p hp (t, x) = x := by
  obtain ⟨a, ha⟩ := hx
  have he : baseInclusion hP p hp a = x := Subtype.ext ha
  rw [← he]
  exact deformation_fixed hP p hp t a

theorem deformation_avoids_of_not_mem_cell (q : P) (hq : q ∉ Set.range j)
    (t : I) (x : punctured (j := j) p hp) (hx : x.val ≠ q) :
    (deformationRel hP p hp (t, x)).val ≠ q := by
  obtain (⟨a, ha⟩ | ⟨d, hd⟩) := Types.eq_or_eq_of_isPushout (hP.map (forget TopCat)) x.val
  · rw [deformation_fixed_of_mem_base hP p hp t x ⟨a, ha⟩]
    exact hx
  · intro he
    have hm := deformation_cell_mem hP p hp t x ⟨d, hd⟩
    exact hq (he ▸ hm)

end NoExoticSixSphere.PuncturedCellAttachment
