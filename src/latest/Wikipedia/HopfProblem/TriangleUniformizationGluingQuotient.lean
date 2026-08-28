import Wikipedia.HopfProblem.TriangleUniformizationGluingFordOrbits
import Wikipedia.HopfProblem.TriangleUniformizationGluingSignedHalfPlane

/-!
# Descent of the folded map to the actual triangle orbit space

The actual closed Ford orbit classification proves independence of the
chosen representative.  Local finiteness of the proved closed tiling
then supplies continuity.  A signed half-plane bijection gives an actual
continuous bijection from the full triangle orbit quotient to `ℂ`.

Analyticity and the cusp extension are separate subsequent assertions;
neither is assumed in this construction.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

theorem exists_fordRepresentative (q : TriangleOrbitSpace) :
    ∃ z : ℍ, z ∈ fordRegion ∧ triangleOrbitProjection z = q := by
  obtain ⟨u, rfl⟩ := triangleOrbitProjection_surjective q
  obtain ⟨g, hg⟩ := triangle_exists_fordRegion_representative u
  exact ⟨triangleGeometricRepresentation g u, hg, triangleOrbitProjection_smul g u⟩

/-- A representative in the proved closed fundamental polygon. -/
def fordRepresentative (q : TriangleOrbitSpace) : fordRegion :=
  ⟨Classical.choose (exists_fordRepresentative q),
    (Classical.choose_spec (exists_fordRepresentative q)).1⟩

@[simp] theorem fordRepresentative_projection (q : TriangleOrbitSpace) :
    triangleOrbitProjection (fordRepresentative q) = q :=
  (Classical.choose_spec (exists_fordRepresentative q)).2

namespace BoundaryMap

variable (D : BoundaryMap)

/-- The real boundary values identify exactly the needed side pairs;
the actual orbit classification proves agreement for every closed Ford
representative of the same orbit. -/
theorem foldedFordMap_eq_of_projection_eq {z w : ℍ}
    (hz : z ∈ fordRegion) (hw : w ∈ fordRegion)
    (he : triangleOrbitProjection z = triangleOrbitProjection w) :
    D.foldedFordMap z = D.foldedFordMap w := by
  rcases (orbitProjection_eq_iff_fordRegion hz hw).mp he with rfl | ⟨hr, hi⟩
  · rfl
  · rw [hr, D.foldedFordMap_rightReflection_boundary hz hi]

/-- The descended function on the existing actual quotient topology. -/
def quotientMap (q : TriangleOrbitSpace) : ℂ := D.foldedFordMap (fordRepresentative q)

/-- Evaluation is independent of the chosen closed Ford representative. -/
theorem quotientMap_projection (z : ℍ) (hz : z ∈ fordRegion) :
    D.quotientMap (triangleOrbitProjection z) = D.foldedFordMap z :=
  D.foldedFordMap_eq_of_projection_eq (fordRepresentative _).property hz
    (fordRepresentative_projection _)

/-- The invariant function on the original upper half-plane. -/
def upstairsMap (z : ℍ) : ℂ := D.quotientMap (triangleOrbitProjection z)

theorem upstairsMap_of_mem {z : ℍ} (hz : z ∈ fordRegion) :
    D.upstairsMap z = D.foldedFordMap z := D.quotientMap_projection z hz

@[simp] theorem upstairsMap_smul (g : TriangleGroup) (z : ℍ) :
    D.upstairsMap (triangleGeometricRepresentation g z) = D.upstairsMap z := by
  change D.quotientMap (triangleOrbitProjection (triangleGeometricRepresentation g z)) = _
  rw [triangleOrbitProjection_smul]
  rfl

theorem upstairsMap_eqOn_translate (g : TriangleGroup) :
    EqOn D.upstairsMap (fun z => D.foldedFordMap (triangleGeometricRepresentation g⁻¹ z))
      (triangleGeometricRepresentation g '' fordRegion) := by
  rintro z ⟨w, hw, rfl⟩
  change D.upstairsMap (triangleGeometricRepresentation g w) =
    D.foldedFordMap (triangleGeometricRepresentation g⁻¹ (triangleGeometricRepresentation g w))
  rw [D.upstairsMap_smul, map_inv]
  change D.upstairsMap w =
    D.foldedFordMap ((triangleGeometricRepresentation g).symm (triangleGeometricRepresentation g w))
  rw [(triangleGeometricRepresentation g).symm_apply_apply w, D.upstairsMap_of_mem hw]

theorem upstairsMap_continuousOn_translate (g : TriangleGroup) :
    ContinuousOn D.upstairsMap (triangleGeometricRepresentation g '' fordRegion) := by
  have hc : Continuous (triangleGeometricRepresentation g⁻¹ : ℍ → ℍ) :=
    (triangleGeometricRepresentation_holomorphic g⁻¹).continuous
  have hm : MapsTo (triangleGeometricRepresentation g⁻¹)
      (triangleGeometricRepresentation g '' fordRegion) fordRegion := by
    rintro z ⟨w, hw, rfl⟩
    rw [map_inv]
    change (triangleGeometricRepresentation g).symm (triangleGeometricRepresentation g w) ∈ _
    rw [(triangleGeometricRepresentation g).symm_apply_apply w]
    exact hw
  exact (D.foldedFordMap_continuousOn.comp hc.continuousOn hm).congr
    (D.upstairsMap_eqOn_translate g)

/-- Continuity follows from the actual locally finite closed Ford cover,
not from continuity of a chosen representative function. -/
theorem upstairsMap_continuous : Continuous D.upstairsMap := by
  apply fordRegion_translates_locallyFinite.continuous triangle_translates_fordRegion_cover
  · intro g
    have h := (triangleGeometricBiholomorph g).toHomeomorph.isClosedMap
      fordRegion fordRegion_closed
    have he : ((triangleGeometricBiholomorph g).toHomeomorph : ℍ → ℍ) =
        triangleGeometricRepresentation g := rfl
    rwa [he] at h
  · exact D.upstairsMap_continuousOn_translate

theorem quotientMap_continuous : Continuous D.quotientMap := by
  apply triangleOrbitProjection_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
  exact D.upstairsMap_continuous

end BoundaryMap

namespace SignedHalfPlaneMap

variable (D : SignedHalfPlaneMap)

abbrev quotientMap : TriangleOrbitSpace → ℂ := D.toBoundaryMap.quotientMap

abbrev upstairsMap : ℍ → ℂ := D.toBoundaryMap.upstairsMap

theorem quotientMap_continuous : Continuous D.quotientMap :=
  D.toBoundaryMap.quotientMap_continuous

theorem quotientMap_surjective : Function.Surjective D.quotientMap := by
  intro w
  obtain ⟨z, hz, he⟩ := D.foldedFordMap_surjOn (Set.mem_univ w)
  refine ⟨triangleOrbitProjection z, ?_⟩
  change D.toBoundaryMap.quotientMap (triangleOrbitProjection z) = w
  rw [D.toBoundaryMap.quotientMap_projection z hz]
  exact he

theorem quotientMap_injective : Function.Injective D.quotientMap := by
  intro q r he
  have hfold : D.foldedFordMap (fordRepresentative q) =
      D.foldedFordMap (fordRepresentative r) := he
  have hor := (orbitProjection_eq_iff_fordRegion (fordRepresentative q).property
      (fordRepresentative r).property).mpr
    ((D.foldedFordMap_eq_iff (fordRepresentative q).property
      (fordRepresentative r).property).mp hfold)
  simpa only [fordRepresentative_projection] using hor

theorem quotientMap_bijective : Function.Bijective D.quotientMap :=
  ⟨D.quotientMap_injective, D.quotientMap_surjective⟩

/-- A set-theoretic equivalence for the actual descended map.  The
topological and analytic inverse properties are proved separately. -/
def quotientEquiv : TriangleOrbitSpace ≃ ℂ :=
  Equiv.ofBijective D.quotientMap D.quotientMap_bijective

@[simp] theorem quotientEquiv_apply (q : TriangleOrbitSpace) :
    D.quotientEquiv q = D.quotientMap q := rfl

theorem quotientMap_construction :
    Continuous D.quotientMap ∧ Function.Bijective D.quotientMap ∧
      ∀ z : ℍ, z ∈ fordRegion →
        D.quotientMap (triangleOrbitProjection z) = D.foldedFordMap z :=
  ⟨D.quotientMap_continuous, D.quotientMap_bijective, D.toBoundaryMap.quotientMap_projection⟩

end SignedHalfPlaneMap
end Wikipedia.HopfProblem.TriangleUniformizationGluing
