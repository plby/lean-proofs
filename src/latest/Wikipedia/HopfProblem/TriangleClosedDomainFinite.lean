import Wikipedia.HopfProblem.TriangleClosedDomainBoundary
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The actual finite part of the compactified closed triangle

The literal finite inclusion identifies the closed half-Ford region in
the upper half-plane with the complement of the ideal vertex in the
actual compact closure of the complex triangle.  Both topologies are
their original subspace topologies.  The interior and the two finite
marked vertices correspond exactly, with no closed-disc parametrization
or uniformization hypothesis.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open RiemannBoundary

/-- The finite part of the actual compact closed triangle. -/
abbrev TriangleClosedFinite := {x : TriangleClosedDomain // x ≠ triangleClosedInfinity}

/-- The concrete finite closed-triangle inequalities are precisely the
actual closed half-Ford region, with the original upper-half-plane point. -/
theorem coe_mem_triangleClosedSet_iff_halfFordRegion (z : ℍ) :
    ((z : ℂ) : OnePoint ℂ) ∈ triangleClosedSet ↔ z ∈ halfFordRegion := by
  rw [coe_mem_triangleClosedSet_iff_closure, closure_triangleInterior]
  exact coe_mem_triangleClosedRegion_iff_halfFordRegion z

/-- The literal finite inclusion into the actual compact closed source. -/
def halfFordToClosedDomain (z : halfFordRegion) : TriangleClosedDomain :=
  ⟨((z : ℍ) : ℂ), (coe_mem_triangleClosedSet_iff_halfFordRegion z).mpr z.property⟩

@[simp] theorem halfFordToClosedDomain_val (z : halfFordRegion) :
    (halfFordToClosedDomain z : OnePoint ℂ) = (((z : ℍ) : ℂ) : OnePoint ℂ) := rfl

theorem halfFordToClosedDomain_ne_infinity (z : halfFordRegion) :
    halfFordToClosedDomain z ≠ triangleClosedInfinity := by
  intro h
  exact OnePoint.coe_ne_infty ((z : ℍ) : ℂ) (congrArg Subtype.val h)

/-- The same literal inclusion, restricted to the actual finite target. -/
def halfFordToClosedFinite (z : halfFordRegion) : TriangleClosedFinite :=
  ⟨halfFordToClosedDomain z, halfFordToClosedDomain_ne_infinity z⟩

theorem halfFordToClosedFinite_isEmbedding : IsEmbedding halfFordToClosedFinite := by
  have htarget : IsEmbedding (fun x : TriangleClosedFinite => x.val.val) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  apply htarget.of_comp_iff.mp
  exact OnePoint.isOpenEmbedding_coe.isEmbedding.comp
    (UpperHalfPlane.isEmbedding_coe.comp Topology.IsEmbedding.subtypeVal)

theorem halfFordToClosedFinite_surjective : Function.Surjective halfFordToClosedFinite := by
  intro x
  have hx : x.val.val ≠ (∞ : OnePoint ℂ) := by
    intro h
    exact x.property (Subtype.ext h)
  obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hx
  have hmem : (z : OnePoint ℂ) ∈ triangleClosedSet := by
    rw [hz]
    exact x.val.property
  have him : 0 < z.im := ((coe_mem_triangleClosedSet_iff z).mp hmem).2.2.1
  let w : ℍ := ⟨z, him⟩
  have hw : w ∈ halfFordRegion :=
    (coe_mem_triangleClosedSet_iff_halfFordRegion w).mp hmem
  exact ⟨⟨w, hw⟩, Subtype.ext (Subtype.ext hz)⟩

/-- The actual finite closed source is homeomorphic to the explicit
closed half-Ford region.  This uses only their concrete finite membership
conditions and their existing subspace topologies. -/
def halfFordClosedHomeomorph : halfFordRegion ≃ₜ TriangleClosedFinite :=
  halfFordToClosedFinite_isEmbedding.toHomeomorphOfSurjective halfFordToClosedFinite_surjective

@[simp] theorem halfFordClosedHomeomorph_apply (z : halfFordRegion) :
    halfFordClosedHomeomorph z = halfFordToClosedFinite z := rfl

@[simp] theorem halfFordClosedHomeomorph_val (z : halfFordRegion) :
    (halfFordClosedHomeomorph z).val.val = (((z : ℍ) : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem halfFordClosedHomeomorph_symm_val (x : TriangleClosedFinite) :
    ((((halfFordClosedHomeomorph.symm x : halfFordRegion) : ℍ) : ℂ) : OnePoint ℂ) =
      x.val.val :=
  congrArg (fun y : TriangleClosedFinite => y.val.val)
    (halfFordClosedHomeomorph.apply_symm_apply x)

/-- The actual open half-Ford interior corresponds exactly to the
original open complex interior of the compact source. -/
theorem halfFordClosedHomeomorph_mem_interior_iff (z : halfFordRegion) :
    (halfFordClosedHomeomorph z).val ∈ triangleClosedInterior ↔
      (z : ℍ) ∈ halfFordInterior := by
  change (((z : ℍ) : ℂ) : OnePoint ℂ) ∈ onePointDomain triangleInterior ↔ _
  rw [coe_mem_onePointDomain, halfFordInterior_eq_preimage_triangleInterior]
  rfl

theorem halfFordClosedHomeomorph_symm_mem_interior_iff (x : TriangleClosedFinite) :
    (halfFordClosedHomeomorph.symm x : ℍ) ∈ halfFordInterior ↔
      x.val ∈ triangleClosedInterior := by
  have h := halfFordClosedHomeomorph_mem_interior_iff (halfFordClosedHomeomorph.symm x)
  rw [halfFordClosedHomeomorph.apply_symm_apply] at h
  exact h.symm

/-- On the actual open interior, the finite identification is exactly the
original inclusion used by the constructed Riemann map. -/
theorem halfFordClosedHomeomorph_of_interior (z : ℍ) (hz : z ∈ halfFordInterior) :
    (halfFordClosedHomeomorph ⟨z, halfFordInterior_subset_halfFordRegion hz⟩).val =
      triangleClosedInclusion (⟨(z : ℂ), by
        change (z : ℂ) ∈ triangleInterior
        simpa only [halfFordInterior_eq_preimage_triangleInterior, mem_preimage] using hz⟩ :
        RiemannMapping.triangleDomain) := rfl

theorem centerOne_mem_halfFordRegion : centerOne ∈ halfFordRegion :=
  (coe_mem_triangleClosedSet_iff_halfFordRegion centerOne).mp triangleClosedCenterOne.property

theorem centerTwo_mem_halfFordRegion : centerTwo ∈ halfFordRegion :=
  (coe_mem_triangleClosedSet_iff_halfFordRegion centerTwo).mp triangleClosedCenterTwo.property

/-- The first finite marked vertex is unchanged by the homeomorphism. -/
@[simp] theorem halfFordClosedHomeomorph_centerOne :
    halfFordClosedHomeomorph ⟨centerOne, centerOne_mem_halfFordRegion⟩ =
      (⟨triangleClosedCenterOne, triangleClosedCenterOne_ne_infty⟩ : TriangleClosedFinite) := rfl

/-- The second finite marked vertex is unchanged by the homeomorphism. -/
@[simp] theorem halfFordClosedHomeomorph_centerTwo :
    halfFordClosedHomeomorph ⟨centerTwo, centerTwo_mem_halfFordRegion⟩ =
      (⟨triangleClosedCenterTwo, triangleClosedCenterTwo_ne_infty⟩ : TriangleClosedFinite) := rfl

@[simp] theorem halfFordClosedHomeomorph_symm_centerOne :
    halfFordClosedHomeomorph.symm
      ⟨triangleClosedCenterOne, triangleClosedCenterOne_ne_infty⟩ =
      (⟨centerOne, centerOne_mem_halfFordRegion⟩ : halfFordRegion) := by
  rw [← halfFordClosedHomeomorph_centerOne, halfFordClosedHomeomorph.symm_apply_apply]

@[simp] theorem halfFordClosedHomeomorph_symm_centerTwo :
    halfFordClosedHomeomorph.symm
      ⟨triangleClosedCenterTwo, triangleClosedCenterTwo_ne_infty⟩ =
      (⟨centerTwo, centerTwo_mem_halfFordRegion⟩ : halfFordRegion) := by
  rw [← halfFordClosedHomeomorph_centerTwo, halfFordClosedHomeomorph.symm_apply_apply]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
