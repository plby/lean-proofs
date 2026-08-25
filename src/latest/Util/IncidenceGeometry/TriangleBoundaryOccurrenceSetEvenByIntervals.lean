import Util.IncidenceGeometry.CyclicPresentationTriangleGeneralPosition
import Util.IncidenceGeometry.CyclicToggleWeightSumEven
import Util.IncidenceGeometry.TriangleSegmentBoundaryParityToggle
import Util.IncidenceGeometry.TriangleBoundaryCyclicIntersectionOccurrenceSet
import Util.IncidenceGeometry.TriangleBoundaryMultiplicityEqualsOccurrenceNcard

open Classical
noncomputable section

lemma TriangleBoundaryOccurrenceSetEvenByIntervals
    {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K)
    (z a b : EuclideanSpace ℝ (Fin 2))
    (hza : z ≠ a) (hab : a ≠ b) (hbz : b ≠ z)
    (hncol : ¬ ∃ c : ℝ, b - a = c • (z - a))
    (hgp : CyclicPresentationTriangleGeneralPosition R z a b) :
    Even (Set.ncard (TriangleBoundaryCyclicIntersectionOccurrenceSet R z a b)) := by
  let V := {p : EuclideanSpace ℝ (Fin 2) // p ∈ R.vertices}
  let triangleInterior : Set (EuclideanSpace ℝ (Fin 2)) :=
    convexHull ℝ ({z, a, b} : Set (EuclideanSpace ℝ (Fin 2))) \
      (segment ℝ z a ∪ segment ℝ a b ∪ segment ℝ b z)
  let inside : V → Bool := fun p => decide (p.1 ∈ triangleInterior)
  let edgeBoundaryCount : V → ℕ := fun p =>
    Set.ncard (openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ z a) +
      Set.ncard (openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ a b) +
        Set.ncard (openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ b z)
  have hgp_parts := hgp
  rcases hgp_parts with ⟨hverticesOff, hzCarrier, haCarrier, hbCarrier,
    hNoOverlapZA, hNoOverlapAB, hNoOverlapBZ, hTransZA, hTransAB, hTransBZ,
    _hboundaryFinite⟩
  have hsegmentCarrier :
      ∀ p : V, segment ℝ p.1 (R.successor p).1 ⊆ J.carrier := by
    intro p x hx
    rw [R.cyclic_carrier_eq]
    exact Set.mem_iUnion.2 ⟨p, hx⟩
  have hlocal :
      ∀ p : V, Odd (edgeBoundaryCount p) ↔ inside p ≠ inside (R.successor p) := by
    intro p
    dsimp [edgeBoundaryCount, inside, triangleInterior]
    refine TriangleSegmentBoundaryParityToggle p.1 (R.successor p).1 z a b
      (R.successor_nondegenerate p) hza hab hbz hncol (hverticesOff p)
      (hverticesOff (R.successor p)) ?_ ?_ ?_ (hNoOverlapZA p) (hNoOverlapAB p)
      (hNoOverlapBZ p) (hTransZA p) (hTransAB p) (hTransBZ p)
    · intro hzSeg
      exact hzCarrier (hsegmentCarrier p hzSeg)
    · intro haSeg
      exact haCarrier (hsegmentCarrier p haSeg)
    · intro hbSeg
      exact hbCarrier (hsegmentCarrier p hbSeg)
  rw [← TriangleBoundaryMultiplicityEqualsOccurrenceNcard R z a b hgp]
  rw [TriangleBoundaryCyclicIntersectionMultiplicity]
  change Even (R.vertices.attach.sum fun p : V => edgeBoundaryCount p)
  rw [Finset.attach_eq_univ]
  exact CyclicToggleWeightSumEven R.successor inside edgeBoundaryCount hlocal
