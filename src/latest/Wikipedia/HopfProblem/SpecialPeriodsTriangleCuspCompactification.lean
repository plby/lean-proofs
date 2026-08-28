import Wikipedia.HopfProblem.SpecialPeriodsTriangleFundamentalDomain
import Wikipedia.HopfProblem.SpecialPeriodsTriangleHorodisc
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientBasic
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Compact cusp complements in the actual triangle quotient

Every orbit meets the explicit Ford polygon, whose height truncations
are compact.  Consequently the image of every high horodisc has compact
complement in the actual full orbit quotient.  These are genuine open
neighborhoods of the added point in its one-point compactification.

Only the topology of this compactification is constructed here.  A
complex chart at the added point is a further step; no identification
with the projective line is assumed.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The actual one-point compactification of the full triangle quotient. -/
abbrev TriangleCompactifiedOrbitSpace := OnePoint TriangleOrbitSpace

/-- The additional cusp point, distinct from every original orbit. -/
def triangleCuspPoint : TriangleCompactifiedOrbitSpace := ∞

def triangleOpenInclusion : TriangleOrbitSpace → TriangleCompactifiedOrbitSpace := OnePoint.some

theorem triangleOpenInclusion_isOpenEmbedding : IsOpenEmbedding triangleOpenInclusion :=
  OnePoint.isOpenEmbedding_coe

theorem triangleOpenInclusion_ne_cusp (q : TriangleOrbitSpace) :
    triangleOpenInclusion q ≠ triangleCuspPoint := OnePoint.coe_ne_infty q

theorem triangleCompactifiedOrbitSpace_compact : CompactSpace TriangleCompactifiedOrbitSpace :=
  inferInstance

theorem triangleCompactifiedOrbitSpace_t2 : T2Space TriangleCompactifiedOrbitSpace :=
  inferInstance

namespace Triangle

/-- The open image of the actual height-`Y` horodisc in the full quotient. -/
def cuspImage (Y : ℝ) : TopologicalSpace.Opens TriangleOrbitSpace :=
  ⟨triangleOrbitProjection '' (horodisc Y : Set ℍ),
    triangleOrbitProjection_isOpenMap _ (horodisc Y).isOpen⟩

@[simp] theorem mem_cuspImage (Y : ℝ) (q : TriangleOrbitSpace) :
    q ∈ cuspImage Y ↔ ∃ z : ℍ, Y < z.im ∧ triangleOrbitProjection z = q := Iff.rfl

theorem cuspImage_antitone : Antitone (fun Y : ℝ => (cuspImage Y : Set TriangleOrbitSpace)) := by
  intro Y Z hYZ q hq
  obtain ⟨z, hz, rfl⟩ := hq
  exact ⟨z, hYZ.trans_lt hz, rfl⟩

theorem cuspImage_compl_subset_truncated_image (Y : ℝ) :
    (cuspImage Y : Set TriangleOrbitSpace)ᶜ ⊆
      triangleOrbitProjection '' truncatedFordRegion Y := by
  intro q hq
  obtain ⟨z, rfl⟩ := triangleOrbitProjection_surjective q
  obtain ⟨g, hg⟩ := triangle_exists_fordRegion_representative z
  have he : triangleOrbitProjection (triangleGeometricRepresentation g z) =
      triangleOrbitProjection z := triangleOrbitProjection_smul g z
  refine ⟨triangleGeometricRepresentation g z, ⟨hg, ?_⟩, he⟩
  apply le_of_not_gt
  intro hi
  exact hq ⟨triangleGeometricRepresentation g z, hi, he⟩

/-- This is actual compactness of the omitted part of the full quotient,
obtained from the concrete truncated polygon. -/
theorem cuspImage_compl_compact (Y : ℝ) :
    IsCompact (cuspImage Y : Set TriangleOrbitSpace)ᶜ :=
  ((truncatedFordRegion_compact Y).image triangleOrbitProjection_continuous).of_isClosed_subset
    (cuspImage Y).isOpen.isClosed_compl (cuspImage_compl_subset_truncated_image Y)

/-- The actual cusp neighborhood in the one-point compactification. -/
def cuspNeighborhood (Y : ℝ) : TopologicalSpace.Opens TriangleCompactifiedOrbitSpace :=
  OnePoint.opensOfCompl (cuspImage Y : Set TriangleOrbitSpace)ᶜ
    (cuspImage Y).isOpen.isClosed_compl (cuspImage_compl_compact Y)

@[simp] theorem cuspPoint_mem_cuspNeighborhood (Y : ℝ) :
    triangleCuspPoint ∈ cuspNeighborhood Y :=
  OnePoint.infty_mem_opensOfCompl _ _

@[simp] theorem openInclusion_mem_cuspNeighborhood (Y : ℝ) (q : TriangleOrbitSpace) :
    triangleOpenInclusion q ∈ cuspNeighborhood Y ↔ q ∈ cuspImage Y := by
  change (q : OnePoint TriangleOrbitSpace) ∉
    ((↑) : TriangleOrbitSpace → OnePoint TriangleOrbitSpace) ''
      (cuspImage Y : Set TriangleOrbitSpace)ᶜ ↔ _
  simp only [OnePoint.coe_injective.mem_set_image, mem_compl_iff, not_not]
  rfl

theorem cuspNeighborhood_preimage (Y : ℝ) :
    triangleOpenInclusion ⁻¹' (cuspNeighborhood Y : Set TriangleCompactifiedOrbitSpace) =
      cuspImage Y := by
  ext q
  exact openInclusion_mem_cuspNeighborhood Y q

theorem cuspNeighborhood_mem_nhds (Y : ℝ) :
    (cuspNeighborhood Y : Set TriangleCompactifiedOrbitSpace) ∈ 𝓝 triangleCuspPoint :=
  (cuspNeighborhood Y).isOpen.mem_nhds (cuspPoint_mem_cuspNeighborhood Y)

end Triangle
end Wikipedia.HopfProblem.SpecialPeriods
