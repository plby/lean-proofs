import Util.IncidenceGeometry.CyclicCurvePresentation
import Util.IncidenceGeometry.CyclicFanMiddleSumEven
import Util.IncidenceGeometry.CyclicPresentationTriangleGeneralPosition
import Util.IncidenceGeometry.TriangleBoundaryCyclicIntersectionMultiplicity
import Util.IncidenceGeometry.TriangleBoundaryEvenIntersections

open Classical
noncomputable section

lemma CyclicPresentationTriangleFanMiddleSumEven
    {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K)
    {α : Type*} [Fintype α]
    (σ : Equiv.Perm α)
    (z : EuclideanSpace ℝ (Fin 2)) (a : α → EuclideanSpace ℝ (Fin 2))
    (hza : ∀ i : α, z ≠ a i)
    (hside : ∀ i : α, a i ≠ a (σ i))
    (hbz : ∀ i : α, a (σ i) ≠ z)
    (hncol : ∀ i : α, ¬ ∃ c : ℝ, a (σ i) - a i = c • (z - a i))
    (hgp : ∀ i : α, CyclicPresentationTriangleGeneralPosition R z (a i) (a (σ i))) :
    Even (∑ i : α, R.vertices.attach.sum fun p =>
      Set.ncard (openSegment ℝ (a i) (a (σ i)) ∩
        openSegment ℝ p.1 (R.successor p).1)) := by
  let incoming : α → ℕ := fun i =>
    R.vertices.attach.sum fun p =>
      Set.ncard (openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ z (a i))
  let middle : α → ℕ := fun i =>
    R.vertices.attach.sum fun p =>
      Set.ncard (openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ (a i) (a (σ i)))
  let outgoing : α → ℕ := fun i =>
    R.vertices.attach.sum fun p =>
      Set.ncard (openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ (a (σ i)) z)
  have htriangle : ∀ i : α, Even (incoming i + middle i + outgoing i) := by
    intro i
    have htri :=
      TriangleBoundaryEvenIntersections R z (a i) (a (σ i))
        (hza i) (hside i) (hbz i) (hncol i) (hgp i)
    rw [TriangleBoundaryCyclicIntersectionMultiplicity] at htri
    convert htri using 1
    simp [incoming, middle, outgoing, Finset.sum_add_distrib]
  have hcancel : ∀ i : α, outgoing i = incoming (σ i) := by
    intro i
    simp [incoming, outgoing, openSegment_symm]
  have hmiddle : Even (∑ i : α, middle i) :=
    CyclicFanMiddleSumEven σ incoming middle outgoing htriangle hcancel
  convert hmiddle using 1
  simp [middle, Set.inter_comm]
