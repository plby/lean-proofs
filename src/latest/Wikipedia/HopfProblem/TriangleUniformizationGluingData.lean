import Wikipedia.HopfProblem.TriangleUniformizationGluingProper

/-!
# Input data from an actual closed-half-plane homeomorphism

An actual homeomorphism from the closed half-Ford triangle to either
closed complex half-plane, carrying interior to interior, supplies every
topological input to the uniformization construction.  The ambient map
is extended by zero outside the closed triangle; only its restriction to
the open triangle is used for the later holomorphy input.
-/

noncomputable section

open Set UpperHalfPlane Complex
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

/-- Extend the literal values of a supplied closed-half-plane homeomorphism. -/
def closedHalfPlaneMap (ε : ℝ)
    (e : halfFordRegion ≃ₜ {w : ℂ // 0 ≤ ε * w.im}) (z : ℍ) : ℂ := by
  classical
  exact if hz : z ∈ halfFordRegion then (e ⟨z, hz⟩ : ℂ) else 0

theorem closedHalfPlaneMap_apply (ε : ℝ)
    (e : halfFordRegion ≃ₜ {w : ℂ // 0 ≤ ε * w.im})
    (z : ℍ) (hz : z ∈ halfFordRegion) :
    closedHalfPlaneMap ε e z = (e ⟨z, hz⟩ : ℂ) := by
  simp only [closedHalfPlaneMap, dif_pos hz]

namespace SignedHalfPlaneMap

variable (ε : ℝ) (hε : ε ^ 2 = 1)
    (e : halfFordRegion ≃ₜ {w : ℂ // 0 ≤ ε * w.im})
    (hinterior : ∀ z : halfFordRegion,
      (z : ℍ) ∈ halfFordInterior ↔ 0 < ε * (e z : ℂ).im)

/-- Supply the signed-half-plane map data from a real closed-domain
homeomorphism; no global quotient conclusion is included in the inputs. -/
def ofHomeomorph : SignedHalfPlaneMap where
  toFun := closedHalfPlaneMap ε e
  continuousOn := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc := continuous_subtype_val.comp e.continuous
    apply hc.congr
    intro z
    exact (closedHalfPlaneMap_apply ε e z z.property).symm
  boundary_real z hz hi := by
    rw [closedHalfPlaneMap_apply ε e z hz]
    have hn : ¬0 < ε * (e ⟨z, hz⟩ : ℂ).im := by
      intro hp
      exact hi ((hinterior ⟨z, hz⟩).mpr hp)
    have heq : ε * (e ⟨z, hz⟩ : ℂ).im = 0 :=
      le_antisymm (le_of_not_gt hn) (e ⟨z, hz⟩).property
    have hε0 : ε ≠ 0 := by intro hz; rw [hz] at hε; norm_num at hε
    exact (mul_eq_zero.mp heq).resolve_left hε0
  orientation := ε
  orientation_sq := hε
  injOn := by
    intro z hz w hw he
    rw [closedHalfPlaneMap_apply ε e z hz, closedHalfPlaneMap_apply ε e w hw] at he
    have hh : e ⟨z, hz⟩ = e ⟨w, hw⟩ := Subtype.ext he
    exact congrArg Subtype.val (e.injective hh)
  image_eq := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [closedHalfPlaneMap_apply ε e z hz]
      exact (e ⟨z, hz⟩).property
    · intro hw
      obtain ⟨z, hz⟩ := e.surjective ⟨w, hw⟩
      refine ⟨z, z.property, ?_⟩
      rw [closedHalfPlaneMap_apply ε e z z.property]
      exact congrArg Subtype.val hz
  interior_positive z hz := by
    have hclosed := halfFordInterior_subset_halfFordRegion hz
    rw [closedHalfPlaneMap_apply ε e z hclosed]
    exact (hinterior ⟨z, hclosed⟩).mp hz

@[simp] theorem ofHomeomorph_apply (z : ℍ) (hz : z ∈ halfFordRegion) :
    (ofHomeomorph ε hε e hinterior).toFun z = (e ⟨z, hz⟩ : ℂ) :=
  closedHalfPlaneMap_apply ε e z hz

/-- The local properness input is automatic for this actual homeomorphism. -/
theorem ofHomeomorph_local_isProperMap :
    IsProperMap (fun z : halfFordRegion => (ofHomeomorph ε hε e hinterior).toFun z) := by
  apply (ofHomeomorph ε hε e hinterior).local_isProperMap_of_homeomorph e
  intro z
  exact (ofHomeomorph_apply ε hε e hinterior z z.property).symm

end SignedHalfPlaneMap
end Wikipedia.HopfProblem.TriangleUniformizationGluing
