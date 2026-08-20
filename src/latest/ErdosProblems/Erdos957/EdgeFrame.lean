import ErdosProblems.Erdos957.GeometryCore

/-!
# Unit supporting-edge charts for Erdős 957, Cases 2 and 4

The two-extreme local cases use the coordinate system of a consecutive unit
hull edge, rather than the tangent-bisector chart used in the one-extreme
cases.  This file isolates that normalization.

For a directed unit supporting edge with vector `e`, the chart is

`q ↦ (e · (q - o), -cross e (q - o))`.

It sends the initial endpoint to `(0,0)`, the terminal endpoint to `(1,0)`,
preserves squared distance, reverses signed area, and sends the supporting
half-plane to `y ≤ 0`.  At the terminal endpoint the same directed chart
sends the preceding endpoint to `(-1,0)`; this is the reflected canonical
variant used for the left side.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957EdgeFrame

open Erdos957
open Erdos957GeometryCore

abbrev Point := Erdos957.Point
abbrev Vertex (A : Finset Point) := Erdos957GeometryCore.Vertex A

/-- The orientation-reversing orthogonal chart determined by a vector `e`.
It is an isometry exactly when `e` is a unit vector. -/
def edgePairCoord (o e q : Point) : ℝ × ℝ :=
  let v := q - o
  (e 0 * v 0 + e 1 * v 1, e 1 * v 0 - e 0 * v 1)

@[simp]
theorem edgePairCoord_self (o e : Point) :
    edgePairCoord o e o = (0, 0) := by
  simp [edgePairCoord]

/-- A unit edge vector has coordinate-square sum one. -/
theorem coordinate_sq_sum_eq_one_of_dist_eq_one {o a : Point}
    (hunit : dist o a = 1) :
    (a 0 - o 0) ^ 2 + (a 1 - o 1) ^ 2 = 1 := by
  calc
    _ = (o 0 - a 0) ^ 2 + (o 1 - a 1) ^ 2 := by ring
    _ = dist o a ^ 2 :=
      (Erdos957Cases24.dist_sq_eq_coordinates o a).symm
    _ = 1 := by rw [hunit]; norm_num

/-- Squared-distance preservation for a coordinate vector of square norm one. -/
theorem sqDist_edgePairCoord_of_sq {o e : Point}
    (he : e 0 ^ 2 + e 1 ^ 2 = 1) (q r : Point) :
    Erdos957Cases13.sqDist (edgePairCoord o e q)
        (edgePairCoord o e r) = dist q r ^ 2 := by
  rw [Erdos957Cases24.dist_sq_eq_coordinates]
  simp only [edgePairCoord, Erdos957Cases13.sqDist, PiLp.sub_apply]
  calc
    _ = ((e 0 ^ 2 + e 1 ^ 2) *
        ((q 0 - r 0) ^ 2 + (q 1 - r 1) ^ 2)) := by ring
    _ = _ := by rw [he]; ring

/-- Squared-distance preservation for the unit-edge chart. -/
theorem sqDist_edgePairCoord {o a : Point} (hunit : dist o a = 1)
    (q r : Point) :
    Erdos957Cases13.sqDist (edgePairCoord o (a - o) q)
        (edgePairCoord o (a - o) r) = dist q r ^ 2 := by
  have he := coordinate_sq_sum_eq_one_of_dist_eq_one hunit
  exact sqDist_edgePairCoord_of_sq he q r

/-- The determinant is `-1` when the coordinate vector has square norm one. -/
theorem pairCross_edgePairCoord_displacements_of_sq {o e : Point}
    (he : e 0 ^ 2 + e 1 ^ 2 = 1) (p q r : Point) :
    CyclicHullData.pairCross
        (CyclicHullData.pairSub (edgePairCoord o e q)
          (edgePairCoord o e p))
        (CyclicHullData.pairSub (edgePairCoord o e r)
          (edgePairCoord o e p)) =
      -Erdos957GeometryCore.cross (q - p) (r - p) := by
  simp only [edgePairCoord, CyclicHullData.pairCross,
    CyclicHullData.pairSub, Erdos957GeometryCore.cross, PiLp.sub_apply]
  calc
    _ = -(e 0 ^ 2 + e 1 ^ 2) *
        ((q 0 - p 0) * (r 1 - p 1) -
          (q 1 - p 1) * (r 0 - p 0)) := by ring
    _ = _ := by rw [he]; ring

/-- The determinant of the unit-edge chart is `-1`, so signed area is
reversed. -/
theorem pairCross_edgePairCoord_displacements {o a : Point}
    (hunit : dist o a = 1) (p q r : Point) :
    CyclicHullData.pairCross
        (CyclicHullData.pairSub (edgePairCoord o (a - o) q)
          (edgePairCoord o (a - o) p))
        (CyclicHullData.pairSub (edgePairCoord o (a - o) r)
          (edgePairCoord o (a - o) p)) =
      -Erdos957GeometryCore.cross (q - p) (r - p) := by
  exact pairCross_edgePairCoord_displacements_of_sq
    (coordinate_sq_sum_eq_one_of_dist_eq_one hunit) p q r

/-- The terminal endpoint of a unit edge has canonical coordinate `(1,0)`. -/
theorem edgePairCoord_terminal {o a : Point} (hunit : dist o a = 1) :
    edgePairCoord o (a - o) a = (1, 0) := by
  have he := coordinate_sq_sum_eq_one_of_dist_eq_one hunit
  apply Prod.ext
  · simp only [edgePairCoord, PiLp.sub_apply]
    nlinarith
  · simp only [edgePairCoord, PiLp.sub_apply]
    ring

/-! ## Successor-edge chart -/

variable {A : Finset Point} (P : CyclicHullData A)

abbrev HullIndex := {p // p ∈ P.H}

/-- Coordinates at `i` determined by the directed edge from `i` to its
cyclic successor. -/
def successorCoord (i : HullIndex P) (q : Vertex A) : ℝ × ℝ :=
  edgePairCoord (i.1 : Point) ((P.next i).1.1 - i.1.1) (q : Point)

@[simp]
theorem successorCoord_source (i : HullIndex P) :
    successorCoord P i i.1 = (0, 0) := by
  exact edgePairCoord_self _ _

@[simp]
theorem successorCoord_successor (i : HullIndex P)
    (hunit : dist (i.1 : Point) (P.next i).1.1 = 1) :
    successorCoord P i (P.next i).1 = (1, 0) := by
  exact edgePairCoord_terminal hunit

theorem sqDist_successorCoord (i : HullIndex P)
    (hunit : dist (i.1 : Point) (P.next i).1.1 = 1) (q r : Vertex A) :
    Erdos957Cases13.sqDist (successorCoord P i q) (successorCoord P i r) =
      dist (q : Point) (r : Point) ^ 2 := by
  exact sqDist_edgePairCoord hunit _ _

theorem pairCross_successorCoord_displacements (i : HullIndex P)
    (hunit : dist (i.1 : Point) (P.next i).1.1 = 1)
    (p q r : Vertex A) :
    CyclicHullData.pairCross
        (CyclicHullData.pairSub (successorCoord P i q) (successorCoord P i p))
        (CyclicHullData.pairSub (successorCoord P i r) (successorCoord P i p)) =
      -Erdos957GeometryCore.cross ((q : Point) - (p : Point))
        ((r : Point) - (p : Point)) := by
  exact pairCross_edgePairCoord_displacements hunit _ _ _

/-- Closed support is all that is valid uniformly: the other endpoint of
the supporting edge lies on the line. -/
theorem successorCoord_snd_nonpos (i : HullIndex P) (q : Vertex A) :
    (successorCoord P i q).2 ≤ 0 := by
  have hs := P.edge_support i q
  unfold successorCoord edgePairCoord
  dsimp only
  simp only [Erdos957GeometryCore.cross, PiLp.sub_apply] at hs ⊢
  linarith

/-! ## Predecessor-edge chart at its terminal endpoint -/

/-- At `i`, use the directed supporting edge from the predecessor to `i`.
The chosen preceding endpoint consequently has coordinate `(-1,0)`; after
the standard horizontal reflection this is the canonical `(1,0)` left-side
variant. -/
def predecessorCoord (i : HullIndex P) (q : Vertex A) : ℝ × ℝ :=
  let pred := P.next.symm i
  edgePairCoord (i.1 : Point) (i.1.1 - pred.1.1) (q : Point)

@[simp]
theorem predecessorCoord_source (i : HullIndex P) :
    predecessorCoord P i i.1 = (0, 0) := by
  exact edgePairCoord_self _ _

@[simp]
theorem predecessorCoord_predecessor (i : HullIndex P)
    (hunit : dist (P.next.symm i).1.1 (i.1 : Point) = 1) :
    predecessorCoord P i (P.next.symm i).1 = (-1, 0) := by
  have he := coordinate_sq_sum_eq_one_of_dist_eq_one hunit
  apply Prod.ext
  · simp only [predecessorCoord, edgePairCoord, PiLp.sub_apply]
    nlinarith
  · simp only [predecessorCoord, edgePairCoord, PiLp.sub_apply]
    ring

theorem sqDist_predecessorCoord (i : HullIndex P)
    (hunit : dist (P.next.symm i).1.1 (i.1 : Point) = 1) (q r : Vertex A) :
    Erdos957Cases13.sqDist (predecessorCoord P i q) (predecessorCoord P i r) =
      dist (q : Point) (r : Point) ^ 2 := by
  have he := coordinate_sq_sum_eq_one_of_dist_eq_one hunit
  exact sqDist_edgePairCoord_of_sq he _ _

theorem pairCross_predecessorCoord_displacements (i : HullIndex P)
    (hunit : dist (P.next.symm i).1.1 (i.1 : Point) = 1)
    (p q r : Vertex A) :
    CyclicHullData.pairCross
        (CyclicHullData.pairSub (predecessorCoord P i q) (predecessorCoord P i p))
        (CyclicHullData.pairSub (predecessorCoord P i r) (predecessorCoord P i p)) =
      -Erdos957GeometryCore.cross ((q : Point) - (p : Point))
        ((r : Point) - (p : Point)) := by
  have he := coordinate_sq_sum_eq_one_of_dist_eq_one hunit
  exact pairCross_edgePairCoord_displacements_of_sq he _ _ _

theorem predecessorCoord_snd_nonpos (i : HullIndex P) (q : Vertex A) :
    (predecessorCoord P i q).2 ≤ 0 := by
  let pred := P.next.symm i
  have hs := P.edge_support pred q
  have hnext : P.next pred = i := by simp [pred]
  rw [hnext] at hs
  unfold predecessorCoord edgePairCoord
  dsimp only
  simp only [Erdos957GeometryCore.cross, PiLp.sub_apply] at hs ⊢
  have htranslate :
      Erdos957GeometryCore.cross (i.1.1 - pred.1.1)
          ((q : Point) - pred.1.1) =
        Erdos957GeometryCore.cross (i.1.1 - pred.1.1)
          ((q : Point) - i.1.1) := by
    simp only [Erdos957GeometryCore.cross, PiLp.sub_apply]
    ring
  simp only [Erdos957GeometryCore.cross, PiLp.sub_apply] at htranslate
  nlinarith

/-! ## Hybrid-family adapters -/

/-- Replace one source of an aligned family by its honest unit-successor
edge chart.  This is the adapter needed to combine edge charts for the
two-extreme cases with bisector charts at all other sources. -/
def replaceWithSuccessorChart (C : P.AlignedChartData) (i : HullIndex P)
    (hunit : dist (i.1 : Point) (P.next i).1.1 = 1) :
    P.AlignedChartData where
  coord j q := if j = i then successorCoord P i q else C.coord j q
  coord_source j := by
    by_cases hji : j = i
    · subst j
      simp [successorCoord_source]
    · simp [hji, C.coord_source]
  sqDist_coord j q r := by
    by_cases hji : j = i
    · subst j
      simp [sqDist_successorCoord, hunit]
    · simp [hji, C.sqDist_coord]
  coord_snd_nonpos j q := by
    by_cases hji : j = i
    · subst j
      simpa using successorCoord_snd_nonpos P i q
    · simpa [hji] using C.coord_snd_nonpos j q
  cross_displacements j p q r := by
    by_cases hji : j = i
    · subst j
      simpa using pairCross_successorCoord_displacements P i hunit p q r
    · simpa [hji] using C.cross_displacements j p q r

/-- The analogous replacement by the directed predecessor-edge chart. -/
def replaceWithPredecessorChart (C : P.AlignedChartData) (i : HullIndex P)
    (hunit : dist (P.next.symm i).1.1 (i.1 : Point) = 1) :
    P.AlignedChartData where
  coord j q := if j = i then predecessorCoord P i q else C.coord j q
  coord_source j := by
    by_cases hji : j = i
    · subst j
      simp [predecessorCoord_source]
    · simp [hji, C.coord_source]
  sqDist_coord j q r := by
    by_cases hji : j = i
    · subst j
      simp [sqDist_predecessorCoord, hunit]
    · simp [hji, C.sqDist_coord]
  coord_snd_nonpos j q := by
    by_cases hji : j = i
    · subst j
      simpa using predecessorCoord_snd_nonpos P i q
    · simpa [hji] using C.coord_snd_nonpos j q
  cross_displacements j p q r := by
    by_cases hji : j = i
    · subst j
      simpa using pairCross_predecessorCoord_displacements P i hunit p q r
    · simpa [hji] using C.cross_displacements j p q r

/-! ## Packaging as the rigid chart consumed by Cases 2 and 4 -/

/-- Euclidean-space form of `edgePairCoord`. -/
def edgePointCoord (o e q : Point) : Point :=
  let z := edgePairCoord o e q
  Erdos957Cases24.point z.1 z.2

@[simp]
theorem edgePointCoord_apply_zero (o e q : Point) :
    edgePointCoord o e q 0 = (edgePairCoord o e q).1 := by
  simp [edgePointCoord]

@[simp]
theorem edgePointCoord_apply_one (o e q : Point) :
    edgePointCoord o e q 1 = (edgePairCoord o e q).2 := by
  simp [edgePointCoord]

/-- Explicit inverse of the edge chart when its vector has square norm one. -/
def edgePointActual (o e z : Point) : Point :=
  o + Erdos957Cases24.point
    (e 0 * z 0 + e 1 * z 1)
    (e 1 * z 0 - e 0 * z 1)

theorem edgePointActual_edgePointCoord {o e : Point}
    (he : e 0 ^ 2 + e 1 ^ 2 = 1) (q : Point) :
    edgePointActual o e (edgePointCoord o e q) = q := by
  calc
    _ = Erdos957Cases24.point (q 0) (q 1) := by
      apply Erdos957Cases24.point_ext
      · simp only [edgePointActual, edgePointCoord, edgePairCoord,
          Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
          PiLp.add_apply, PiLp.sub_apply]
        calc
          _ = o 0 + (e 0 ^ 2 + e 1 ^ 2) * (q 0 - o 0) := by ring
          _ = q 0 := by rw [he]; ring
      · simp only [edgePointActual, edgePointCoord, edgePairCoord,
          Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
          PiLp.add_apply, PiLp.sub_apply]
        calc
          _ = o 1 + (e 0 ^ 2 + e 1 ^ 2) * (q 1 - o 1) := by ring
          _ = q 1 := by rw [he]; ring
    _ = q := (Erdos957Cases24.point_ext rfl rfl).symm

theorem edgePointCoord_edgePointActual {o e : Point}
    (he : e 0 ^ 2 + e 1 ^ 2 = 1) (z : Point) :
    edgePointCoord o e (edgePointActual o e z) = z := by
  calc
    _ = Erdos957Cases24.point (z 0) (z 1) := by
      apply Erdos957Cases24.point_ext
      · simp only [edgePointActual, edgePointCoord, edgePairCoord,
          Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
          PiLp.add_apply, PiLp.sub_apply]
        calc
          _ = (e 0 ^ 2 + e 1 ^ 2) * z 0 := by ring
          _ = z 0 := by rw [he]; ring
      · simp only [edgePointActual, edgePointCoord, edgePairCoord,
          Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
          PiLp.add_apply, PiLp.sub_apply]
        calc
          _ = (e 0 ^ 2 + e 1 ^ 2) * z 1 := by ring
          _ = z 1 := by rw [he]; ring
    _ = z := (Erdos957Cases24.point_ext rfl rfl).symm

/-- The literal Euclidean equivalence underlying a unit-vector edge chart. -/
def edgePointEquiv (o e : Point) (he : e 0 ^ 2 + e 1 ^ 2 = 1) :
    Point ≃ Point where
  toFun := edgePointCoord o e
  invFun := edgePointActual o e
  left_inv := edgePointActual_edgePointCoord he
  right_inv := edgePointCoord_edgePointActual he

@[simp]
theorem edgePointEquiv_apply (o e : Point)
    (he : e 0 ^ 2 + e 1 ^ 2 = 1) (q : Point) :
    edgePointEquiv o e he q = edgePointCoord o e q := rfl

@[simp]
theorem edgePointEquiv_symm_apply (o e : Point)
    (he : e 0 ^ 2 + e 1 ^ 2 = 1) (z : Point) :
    (edgePointEquiv o e he).symm z = edgePointActual o e z := rfl

/-- The Euclidean-space edge chart preserves ordinary distance. -/
theorem dist_edgePointCoord_eq {o e : Point}
    (he : e 0 ^ 2 + e 1 ^ 2 = 1) (q r : Point) :
    dist (edgePointCoord o e q) (edgePointCoord o e r) = dist q r := by
  have hsq :
      dist (edgePointCoord o e q) (edgePointCoord o e r) ^ 2 =
        dist q r ^ 2 := by
    rw [Erdos957Cases24.dist_sq_eq_coordinates]
    simpa [edgePointCoord, Erdos957Cases13.sqDist] using
      sqDist_edgePairCoord_of_sq he q r
  nlinarith [dist_nonneg (x := edgePointCoord o e q)
    (y := edgePointCoord o e r), dist_nonneg (x := q) (y := r)]

/-- Package a unit-vector edge normalization as the exact rigid chart
consumed by `Case24Bridge.Framed`. -/
def unitVectorRigidChart (o e : Point) (he : e 0 ^ 2 + e 1 ^ 2 = 1) :
    Erdos957Case24Bridge.Framed.RigidChart where
  toCanonical := edgePointEquiv o e he
  dist_eq := dist_edgePointCoord_eq he

@[simp]
theorem unitVectorRigidChart_toCanonical (o e : Point)
    (he : e 0 ^ 2 + e 1 ^ 2 = 1) (q : Point) :
    (unitVectorRigidChart o e he).toCanonical q = edgePointCoord o e q := rfl

@[simp]
theorem unitVectorRigidChart_actual_zero (o e : Point)
    (he : e 0 ^ 2 + e 1 ^ 2 = 1) :
    (unitVectorRigidChart o e he).actual (Erdos957Cases24.point 0 0) = o := by
  change edgePointActual o e (Erdos957Cases24.point 0 0) = o
  ext j
  fin_cases j <;> simp [edgePointActual]

/-- Rigid chart whose positive horizontal unit vector is the actual edge
from `o` to `a`. -/
def unitEdgeRigidChart (o a : Point) (hunit : dist o a = 1) :
    Erdos957Case24Bridge.Framed.RigidChart :=
  unitVectorRigidChart o (a - o)
    (coordinate_sq_sum_eq_one_of_dist_eq_one hunit)

@[simp]
theorem unitEdgeRigidChart_toCanonical (o a : Point)
    (hunit : dist o a = 1) (q : Point) :
    (unitEdgeRigidChart o a hunit).toCanonical q =
      edgePointCoord o (a - o) q := rfl

@[simp]
theorem unitEdgeRigidChart_actual_case2_u (o a : Point)
    (hunit : dist o a = 1) :
    (unitEdgeRigidChart o a hunit).actual Erdos957Cases24.Case2.u = o := by
  change edgePointActual o (a - o) Erdos957Cases24.Case2.u = o
  ext j
  fin_cases j <;> simp [edgePointActual, Erdos957Cases24.Case2.u]

@[simp]
theorem unitEdgeRigidChart_actual_case2_uNext (o a : Point)
    (hunit : dist o a = 1) :
    (unitEdgeRigidChart o a hunit).actual Erdos957Cases24.Case2.uNext = a := by
  ext j
  fin_cases j
  · simp [Erdos957Case24Bridge.Framed.RigidChart.actual, edgePointEquiv,
      unitEdgeRigidChart, unitVectorRigidChart, edgePointActual,
      Erdos957Cases24.Case2.uNext]
  · simp [Erdos957Case24Bridge.Framed.RigidChart.actual, edgePointEquiv,
      unitEdgeRigidChart, unitVectorRigidChart, edgePointActual,
      Erdos957Cases24.Case2.uNext]

/-- At the terminal endpoint `o` of the directed unit edge `p → o`, this
chart maps `p` to the canonical left neighbor `(-1,0)`. -/
def terminalUnitEdgeRigidChart (p o : Point) (hunit : dist p o = 1) :
    Erdos957Case24Bridge.Framed.RigidChart :=
  unitVectorRigidChart o (o - p)
    (coordinate_sq_sum_eq_one_of_dist_eq_one hunit)

@[simp]
theorem terminalUnitEdgeRigidChart_toCanonical (p o : Point)
    (hunit : dist p o = 1) (q : Point) :
    (terminalUnitEdgeRigidChart p o hunit).toCanonical q =
      edgePointCoord o (o - p) q := rfl

@[simp]
theorem terminalUnitEdgeRigidChart_actual_case2_u (p o : Point)
    (hunit : dist p o = 1) :
    (terminalUnitEdgeRigidChart p o hunit).actual Erdos957Cases24.Case2.u = o := by
  change edgePointActual o (o - p) Erdos957Cases24.Case2.u = o
  ext j
  fin_cases j <;> simp [edgePointActual, Erdos957Cases24.Case2.u]

@[simp]
theorem terminalUnitEdgeRigidChart_actual_case2_uPrev (p o : Point)
    (hunit : dist p o = 1) :
    (terminalUnitEdgeRigidChart p o hunit).actual
        Erdos957Cases24.Case2.uPrev = p := by
  ext j
  fin_cases j
  · simp [Erdos957Case24Bridge.Framed.RigidChart.actual, edgePointEquiv,
      terminalUnitEdgeRigidChart, unitVectorRigidChart, edgePointActual,
      Erdos957Cases24.Case2.uPrev]
  · simp [Erdos957Case24Bridge.Framed.RigidChart.actual, edgePointEquiv,
      terminalUnitEdgeRigidChart, unitVectorRigidChart, edgePointActual,
      Erdos957Cases24.Case2.uPrev]

end Erdos957EdgeFrame
