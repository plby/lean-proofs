import ErdosProblems.Erdos957.CaseClassification

/-!
# Case-3 collision ABI audit

This leaf records the singleton-hull-neighbor argument which would make a
Case-3 middle arrival unique.  The current `RealizedSourceRow.case3` ABI does
not connect its classified middle to the independent middle target stored in
`PairCases.Case3ActualRow`; the final theorem below therefore states the
missing bridge explicitly.
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Erdos957Case3SameSide

open Erdos957GeometryCore
open Erdos957CaseClassification

abbrev ComplexPoint := Erdos957GeometryCore.Point

open Erdos957Cases13

/-! ## The elementary consecutive-edge obstruction

The two lemmas below are the coordinate core of the secondary/secondary
collision argument.  The point `e` is the second endpoint of an oriented
hull edge, `v` is a common unit target, and `m` is the equilateral third
point belonging to one endpoint.  If both `v` and `m` are in the supported
half-plane, the edge length is forced to be one and the third point is the
opposite endpoint. -/

private theorem negative_equilateral_supported_eq_endpoint
    {e v m : Erdos957Cases13.Point}
    (hov : sqDist origin v = 1)
    (hom : sqDist origin m = 1) (hvm : sqDist v m = 1)
    (hev : sqDist e v = 1)
    (hedge : 1 ≤ sqDist origin e)
    (hvSupport : Erdos957Case3General.crossFrom origin e v ≤ 0)
    (hmSupport : Erdos957Case3General.crossFrom origin e m ≤ 0)
    (hside : Erdos957Case3General.crossFrom origin m v < 0) :
    m = e := by
  let d : ℝ := sqDist origin e
  let D : ℝ := Erdos957Case3General.crossFrom origin e v
  let B : ℝ := Erdos957Case3General.crossFrom origin e m
  let K : ℝ := Erdos957Case3General.crossFrom origin m v
  have hd : 1 ≤ d := hedge
  have hD : D ≤ 0 := hvSupport
  have hB : B ≤ 0 := hmSupport
  have hK : K < 0 := hside
  have hdotEV : e.1 * v.1 + e.2 * v.2 = d / 2 := by
    simp only [sqDist, origin, d] at hov hev ⊢
    nlinarith
  have hdotMV : m.1 * v.1 + m.2 * v.2 = 1 / 2 := by
    simp only [sqDist, origin] at hov hom hvm ⊢
    nlinarith
  have hDsq : D ^ 2 = d - d ^ 2 / 4 := by
    have hid :
        (e.1 * v.1 + e.2 * v.2) ^ 2 + D ^ 2 =
          d * (v.1 ^ 2 + v.2 ^ 2) := by
      simp only [D, d, Erdos957Case3General.crossFrom, sqDist, origin]
      ring
    simp only [sqDist, origin] at hov
    nlinarith
  have hKsq : K ^ 2 = 3 / 4 := by
    exact Erdos957Case3General.cross_sq_eq_three_fourths_of_common_unit
      hom hov (by simpa [sqDist_comm] using hvm)
  have hBformula : B = D / 2 - d * K / 2 := by
    have hvnorm : v.1 ^ 2 + v.2 ^ 2 = 1 := by
      simpa only [sqDist, origin, zero_sub, neg_sq] using hov
    have hid :
        B * (v.1 ^ 2 + v.2 ^ 2) =
          D * (m.1 * v.1 + m.2 * v.2) -
          (e.1 * v.1 + e.2 * v.2) * K := by
      simp only [B, D, K, Erdos957Case3General.crossFrom, origin]
      ring
    rw [hvnorm, mul_one, hdotEV, hdotMV] at hid
    nlinarith [hid]
  have hdnonneg : 0 ≤ d := le_trans (by norm_num) hd
  have hdKnonpos : d * K ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hdnonneg hK.le
  have hDK : D ≤ d * K := by nlinarith [hBformula]
  have hnegDK : 0 ≤ -(d * K) := by linarith
  have hnegD : 0 ≤ -D := by linarith
  have habs : -(d * K) ≤ -D := by linarith
  have hsq : (-(d * K)) ^ 2 ≤ (-D) ^ 2 :=
    (sq_le_sq₀ hnegDK hnegD).2 habs
  have hdle : d ≤ 1 := by
    nlinarith [hsq]
  have hdeq : d = 1 := le_antisymm hdle hd
  apply Erdos957Case3General.common_unit_eq_of_cross_nonneg
      (a := origin) (b := v) (p := m) (q := e)
  · exact hov
  · exact hom
  · exact hvm
  · exact hdeq
  · simpa [sqDist_comm] using hev
  · have hcross : Erdos957Case3General.crossFrom origin v m = -K := by
      simp only [K, Erdos957Case3General.crossFrom, origin]
      ring
    rw [hcross]
    linarith
  · have hcross : Erdos957Case3General.crossFrom origin v e = -D := by
      simp only [D, Erdos957Case3General.crossFrom, origin]
      ring
    rw [hcross]
    linarith

private theorem positive_equilateral_supported_eq_origin
    {e v m : Erdos957Cases13.Point}
    (hev : sqDist e v = 1)
    (hem : sqDist e m = 1) (hvm : sqDist v m = 1)
    (hov : sqDist origin v = 1)
    (hedge : 1 ≤ sqDist origin e)
    (hvSupport : Erdos957Case3General.crossFrom origin e v ≤ 0)
    (hmSupport : Erdos957Case3General.crossFrom origin e m ≤ 0)
    (hside : 0 < Erdos957Case3General.crossFrom e m v) :
    m = origin := by
  let d : ℝ := sqDist origin e
  let D : ℝ := Erdos957Case3General.crossFrom origin e v
  let B : ℝ := Erdos957Case3General.crossFrom origin e m
  let K : ℝ := Erdos957Case3General.crossFrom e m v
  have hd : 1 ≤ d := hedge
  have hD : D ≤ 0 := hvSupport
  have hB : B ≤ 0 := hmSupport
  have hK : 0 < K := hside
  have hdotEV : e.1 * v.1 + e.2 * v.2 = d / 2 := by
    simp only [sqDist, origin, d] at hov hev ⊢
    nlinarith
  have hdotPM :
      (m.1 - e.1) * (v.1 - e.1) +
          (m.2 - e.2) * (v.2 - e.2) = 1 / 2 := by
    simp only [sqDist] at hev hem hvm ⊢
    nlinarith
  have hdotEW :
      e.1 * (v.1 - e.1) + e.2 * (v.2 - e.2) = -d / 2 := by
    have hdnorm : e.1 ^ 2 + e.2 ^ 2 = d := by
      simp [d, sqDist, origin]
    nlinarith [hdotEV, hdnorm]
  have hDsq : D ^ 2 = d - d ^ 2 / 4 := by
    have hid :
        (e.1 * v.1 + e.2 * v.2) ^ 2 + D ^ 2 =
          d * (v.1 ^ 2 + v.2 ^ 2) := by
      simp only [D, d, Erdos957Case3General.crossFrom, sqDist, origin]
      ring
    simp only [sqDist, origin] at hov
    nlinarith
  have hKsq : K ^ 2 = 3 / 4 := by
    exact Erdos957Case3General.cross_sq_eq_three_fourths_of_common_unit
      hem hev (by simpa [sqDist_comm] using hvm)
  have hBformula : B = D / 2 + d * K / 2 := by
    have hwnorm : (v.1 - e.1) ^ 2 + (v.2 - e.2) ^ 2 = 1 := by
      simp only [sqDist] at hev
      nlinarith [sq_nonneg (v.1 - e.1), sq_nonneg (v.2 - e.2)]
    have hid :
        B * ((v.1 - e.1) ^ 2 + (v.2 - e.2) ^ 2) = D *
            ((m.1 - e.1) * (v.1 - e.1) +
              (m.2 - e.2) * (v.2 - e.2)) -
          (e.1 * (v.1 - e.1) + e.2 * (v.2 - e.2)) * K := by
      simp only [B, D, K, Erdos957Case3General.crossFrom, origin]
      ring
    rw [hwnorm, mul_one, hdotPM, hdotEW] at hid
    nlinarith [hid]
  have hdnonneg : 0 ≤ d := le_trans (by norm_num) hd
  have hdKnonneg : 0 ≤ d * K := mul_nonneg hdnonneg hK.le
  have hDneg : D ≤ -(d * K) := by nlinarith [hBformula]
  have hnegDK : 0 ≤ d * K := hdKnonneg
  have hnegD : 0 ≤ -D := by linarith
  have habs : d * K ≤ -D := by linarith
  have hsq : (d * K) ^ 2 ≤ (-D) ^ 2 :=
    (sq_le_sq₀ hnegDK hnegD).2 habs
  have hdle : d ≤ 1 := by
    nlinarith [hsq]
  have hdeq : d = 1 := le_antisymm hdle hd
  apply Erdos957Case3General.common_unit_eq_of_cross_nonpos
      (a := e) (b := v) (p := m) (q := origin)
  · exact hev
  · exact hem
  · exact hvm
  · simpa only [d, sqDist_comm] using hdeq
  · simpa [sqDist_comm] using hov
  · have hcross : Erdos957Case3General.crossFrom e v m = -K := by
      simp only [K, Erdos957Case3General.crossFrom]
      ring
    rw [hcross]
    linarith
  · have hcross : Erdos957Case3General.crossFrom e v origin = D := by
      simp only [D, Erdos957Case3General.crossFrom, origin]
      ring
    rw [hcross]
    exact hD

/-- Signed area in any aligned source chart is the negative of the ambient
signed area.  In particular its value does not depend on which source chart
is used. -/
theorem crossFrom_coord_eq_neg_cross
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (i : {p // p ∈ P.H})
    (a b c : Vertex A) :
    Erdos957Case3General.crossFrom (C.coord i a) (C.coord i b) (C.coord i c) =
      -Erdos957GeometryCore.cross ((b : ComplexPoint) - (a : ComplexPoint))
        ((c : ComplexPoint) - (a : ComplexPoint)) := by
  simpa [Erdos957Case3General.crossFrom,
    Erdos957GeometryCore.CyclicHullData.pairCross,
    Erdos957GeometryCore.CyclicHullData.pairSub] using
      C.cross_displacements i a b c

/-- The predecessor half of the consecutive-edge obstruction.  A non-hull
equilateral proxy belonging to the first endpoint lies on the positive
formula side of any common unit target. -/
theorem predecessor_equilateral_orientation_positive_across_next_edge
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (s : {p // p ∈ P.H}) {v ms : Vertex A}
    (hsv : (unitDistanceGraph A).Adj s.1 v)
    (htv : (unitDistanceGraph A).Adj (P.next s).1 v)
    (hsms : (unitDistanceGraph A).Adj s.1 ms)
    (hvms : (unitDistanceGraph A).Adj v ms)
    (hmsNotHull : ms ∉ P.H) :
    0 < Erdos957Case3General.crossFrom
        (C.coord s s.1) (C.coord s ms) (C.coord s v) := by
  have hstNe : (s.1 : ComplexPoint) ≠ ((P.next s).1 : ComplexPoint) := by
    intro h
    exact P.next_ne_self s (Subtype.ext (Subtype.ext h.symm))
  have hdistEdge : 1 ≤ dist (s.1 : ComplexPoint) ((P.next s).1 : ComplexPoint) :=
    hA s.1 s.1.property (P.next s).1 (P.next s).1.property hstNe
  have hedgeSq : 1 ≤ sqDist origin (C.coord s (P.next s).1) := by
    have hsquare : sqDist origin (C.coord s (P.next s).1) =
        dist (s.1 : ComplexPoint) ((P.next s).1 : ComplexPoint) ^ 2 := by
      simpa only [origin, C.coord_source] using
        C.sqDist_coord s s.1 (P.next s).1
    rw [hsquare]
    nlinarith [dist_nonneg (x := (s.1 : ComplexPoint))
      (y := ((P.next s).1 : ComplexPoint))]
  have sq_of_adj : ∀ (a b : Vertex A), (unitDistanceGraph A).Adj a b →
      sqDist (C.coord s a) (C.coord s b) = 1 := by
    intro a b hab
    rw [C.sqDist_coord]
    have hd : dist (a : ComplexPoint) (b : ComplexPoint) = 1 := by
      simpa [unitDistanceGraph] using hab
    rw [hd]
    norm_num
  have sq_source_of_adj : ∀ (q : Vertex A),
      (unitDistanceGraph A).Adj s.1 q → sqDist origin (C.coord s q) = 1 := by
    intro q hq
    simpa only [origin, C.coord_source] using sq_of_adj s.1 q hq
  have htargetSupport : Erdos957Case3General.crossFrom origin
      (C.coord s (P.next s).1) (C.coord s v) ≤ 0 := by
    have hedge := P.edge_support s v
    have hcoord := crossFrom_coord_eq_neg_cross C s s.1 (P.next s).1 v
    have hcoord' : Erdos957Case3General.crossFrom origin
        (C.coord s (P.next s).1) (C.coord s v) =
        -Erdos957GeometryCore.cross
          (((P.next s).1 : ComplexPoint) - (s.1 : ComplexPoint))
          ((v : ComplexPoint) - (s.1 : ComplexPoint)) := by
      simpa only [origin, C.coord_source] using hcoord
    rw [hcoord']
    linarith
  have hmsSupport : Erdos957Case3General.crossFrom origin
      (C.coord s (P.next s).1) (C.coord s ms) ≤ 0 := by
    have hedge := P.edge_support s ms
    have hcoord := crossFrom_coord_eq_neg_cross C s s.1 (P.next s).1 ms
    have hcoord' : Erdos957Case3General.crossFrom origin
        (C.coord s (P.next s).1) (C.coord s ms) =
        -Erdos957GeometryCore.cross
          (((P.next s).1 : ComplexPoint) - (s.1 : ComplexPoint))
          ((ms : ComplexPoint) - (s.1 : ComplexPoint)) := by
      simpa only [origin, C.coord_source] using hcoord
    rw [hcoord']
    linarith
  by_contra hside
  have hsideLe : Erdos957Case3General.crossFrom
      (C.coord s s.1) (C.coord s ms) (C.coord s v) ≤ 0 := le_of_not_gt hside
  rw [C.coord_source] at hsideLe
  have hsideLe' : Erdos957Case3General.crossFrom origin
      (C.coord s ms) (C.coord s v) ≤ 0 := by
    simpa only [origin] using hsideLe
  have hsideSq := Erdos957Case3General.cross_sq_eq_three_fourths_of_common_unit
    (sq_source_of_adj ms hsms) (sq_source_of_adj v hsv)
    (sq_of_adj ms v ((unitDistanceGraph A).adj_symm hvms))
  have hsideLt : Erdos957Case3General.crossFrom origin
      (C.coord s ms) (C.coord s v) < 0 := by
    nlinarith [hsideLe']
  have hmsEq := negative_equilateral_supported_eq_endpoint
    (e := C.coord s (P.next s).1) (v := C.coord s v) (m := C.coord s ms)
    (sq_source_of_adj v hsv) (sq_source_of_adj ms hsms)
    (sq_of_adj v ms hvms) (sq_of_adj (P.next s).1 v htv)
    hedgeSq htargetSupport hmsSupport hsideLt
  have hvertex : ms = (P.next s).1 := C.coord_injective P s hmsEq
  exact hmsNotHull (by simpa [hvertex] using (P.next s).property)

/-- The successor half of the consecutive-edge obstruction.  A non-hull
equilateral proxy belonging to the second endpoint lies on the closed
negative formula side of any common unit target. -/
theorem successor_equilateral_orientation_nonpositive_across_next_edge
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (s : {p // p ∈ P.H}) {v mt : Vertex A}
    (hsv : (unitDistanceGraph A).Adj s.1 v)
    (htv : (unitDistanceGraph A).Adj (P.next s).1 v)
    (htmt : (unitDistanceGraph A).Adj (P.next s).1 mt)
    (hvmt : (unitDistanceGraph A).Adj v mt)
    (hmtNotHull : mt ∉ P.H) :
    Erdos957Case3General.crossFrom
        (C.coord (P.next s) (P.next s).1)
        (C.coord (P.next s) mt) (C.coord (P.next s) v) ≤ 0 := by
  have hstNe : (s.1 : ComplexPoint) ≠ ((P.next s).1 : ComplexPoint) := by
    intro h
    exact P.next_ne_self s (Subtype.ext (Subtype.ext h.symm))
  have hdistEdge : 1 ≤ dist (s.1 : ComplexPoint) ((P.next s).1 : ComplexPoint) :=
    hA s.1 s.1.property (P.next s).1 (P.next s).1.property hstNe
  have hedgeSq : 1 ≤ sqDist origin (C.coord s (P.next s).1) := by
    have hsquare : sqDist origin (C.coord s (P.next s).1) =
        dist (s.1 : ComplexPoint) ((P.next s).1 : ComplexPoint) ^ 2 := by
      simpa only [origin, C.coord_source] using
        C.sqDist_coord s s.1 (P.next s).1
    rw [hsquare]
    nlinarith [dist_nonneg (x := (s.1 : ComplexPoint))
      (y := ((P.next s).1 : ComplexPoint))]
  have sq_of_adj : ∀ (a b : Vertex A), (unitDistanceGraph A).Adj a b →
      sqDist (C.coord s a) (C.coord s b) = 1 := by
    intro a b hab
    rw [C.sqDist_coord]
    have hd : dist (a : ComplexPoint) (b : ComplexPoint) = 1 := by
      simpa [unitDistanceGraph] using hab
    rw [hd]
    norm_num
  have sq_source_of_adj : ∀ (q : Vertex A),
      (unitDistanceGraph A).Adj s.1 q → sqDist origin (C.coord s q) = 1 := by
    intro q hq
    simpa only [origin, C.coord_source] using sq_of_adj s.1 q hq
  have htargetSupport : Erdos957Case3General.crossFrom origin
      (C.coord s (P.next s).1) (C.coord s v) ≤ 0 := by
    have hedge := P.edge_support s v
    have hcoord := crossFrom_coord_eq_neg_cross C s s.1 (P.next s).1 v
    have hcoord' : Erdos957Case3General.crossFrom origin
        (C.coord s (P.next s).1) (C.coord s v) =
        -Erdos957GeometryCore.cross
          (((P.next s).1 : ComplexPoint) - (s.1 : ComplexPoint))
          ((v : ComplexPoint) - (s.1 : ComplexPoint)) := by
      simpa only [origin, C.coord_source] using hcoord
    rw [hcoord']
    linarith
  by_contra hside
  have hsidePos : 0 < Erdos957Case3General.crossFrom
      (C.coord (P.next s) (P.next s).1)
      (C.coord (P.next s) mt) (C.coord (P.next s) v) := lt_of_not_ge hside
  have hsideCommon : 0 < Erdos957Case3General.crossFrom
      (C.coord s (P.next s).1) (C.coord s mt) (C.coord s v) := by
    rw [crossFrom_coord_eq_neg_cross C (P.next s) (P.next s).1 mt v]
      at hsidePos
    rw [crossFrom_coord_eq_neg_cross C s (P.next s).1 mt v]
    exact hsidePos
  have hmtSupport : Erdos957Case3General.crossFrom origin
      (C.coord s (P.next s).1) (C.coord s mt) ≤ 0 := by
    have hedge := P.edge_support s mt
    have hcoord := crossFrom_coord_eq_neg_cross C s s.1 (P.next s).1 mt
    have hcoord' : Erdos957Case3General.crossFrom origin
        (C.coord s (P.next s).1) (C.coord s mt) =
        -Erdos957GeometryCore.cross
          (((P.next s).1 : ComplexPoint) - (s.1 : ComplexPoint))
          ((mt : ComplexPoint) - (s.1 : ComplexPoint)) := by
      simpa only [origin, C.coord_source] using hcoord
    rw [hcoord']
    linarith
  have hmtEq := positive_equilateral_supported_eq_origin
    (e := C.coord s (P.next s).1) (v := C.coord s v) (m := C.coord s mt)
    (sq_of_adj (P.next s).1 v htv) (sq_of_adj (P.next s).1 mt htmt)
    (sq_of_adj v mt hvmt) (sq_source_of_adj v hsv)
    hedgeSq htargetSupport hmtSupport hsideCommon
  have hvertex : mt = s.1 := by
    apply C.coord_injective P s
    change C.coord s mt = C.coord s s.1
    rw [C.coord_source]
    exact hmtEq
  exact hmtNotHull (by simpa [hvertex] using s.property)

/-- Consecutive hull sources carrying unit equilateral pictures at a common
target necessarily carry opposite orientations.  The predecessor's third
point is on the positive signed side, and the successor's is on the closed
negative signed side.  The proof uses only one-separation, the actual
oriented hull-edge support, and exclusion of the two third points from the
hull. -/
theorem case3_equilateral_orientations_opposite_across_next_edge
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (s : {p // p ∈ P.H}) {v ms mt : Vertex A}
    (hsv : (unitDistanceGraph A).Adj s.1 v)
    (htv : (unitDistanceGraph A).Adj (P.next s).1 v)
    (hsms : (unitDistanceGraph A).Adj s.1 ms)
    (hvms : (unitDistanceGraph A).Adj v ms)
    (htmt : (unitDistanceGraph A).Adj (P.next s).1 mt)
    (hvmt : (unitDistanceGraph A).Adj v mt)
    (hmsNotHull : ms ∉ P.H) (hmtNotHull : mt ∉ P.H) :
    0 < Erdos957Case3General.crossFrom
        (C.coord s s.1) (C.coord s ms) (C.coord s v) ∧
      Erdos957Case3General.crossFrom
        (C.coord (P.next s) (P.next s).1)
        (C.coord (P.next s) mt) (C.coord (P.next s) v) ≤ 0 := by
  have hstNe : (s.1 : ComplexPoint) ≠ ((P.next s).1 : ComplexPoint) := by
    intro h
    exact P.next_ne_self s (Subtype.ext (Subtype.ext h.symm))
  have hdistEdge : 1 ≤ dist (s.1 : ComplexPoint) ((P.next s).1 : ComplexPoint) :=
    hA s.1 s.1.property (P.next s).1 (P.next s).1.property hstNe
  have hedgeSq :
      1 ≤ sqDist origin (C.coord s (P.next s).1) := by
    have hsquare : sqDist origin (C.coord s (P.next s).1) =
        dist (s.1 : ComplexPoint) ((P.next s).1 : ComplexPoint) ^ 2 := by
      simpa only [origin, C.coord_source] using
        C.sqDist_coord s s.1 (P.next s).1
    rw [hsquare]
    nlinarith [dist_nonneg (x := (s.1 : ComplexPoint))
      (y := ((P.next s).1 : ComplexPoint))]
  have sq_of_adj : ∀ (a b : Vertex A), (unitDistanceGraph A).Adj a b →
      sqDist (C.coord s a) (C.coord s b) = 1 := by
    intro a b hab
    rw [C.sqDist_coord]
    have hd : dist (a : ComplexPoint) (b : ComplexPoint) = 1 := by
      simpa [unitDistanceGraph] using hab
    rw [hd]
    norm_num
  have sq_source_of_adj : ∀ (q : Vertex A),
      (unitDistanceGraph A).Adj s.1 q → sqDist origin (C.coord s q) = 1 := by
    intro q hq
    simpa only [origin, C.coord_source] using sq_of_adj s.1 q hq
  have htargetSupport : Erdos957Case3General.crossFrom origin
      (C.coord s (P.next s).1) (C.coord s v) ≤ 0 := by
    have hedge := P.edge_support s v
    have hcoord := crossFrom_coord_eq_neg_cross C s s.1 (P.next s).1 v
    have hcoord' : Erdos957Case3General.crossFrom origin
        (C.coord s (P.next s).1) (C.coord s v) =
        -Erdos957GeometryCore.cross
          (((P.next s).1 : ComplexPoint) - (s.1 : ComplexPoint))
          ((v : ComplexPoint) - (s.1 : ComplexPoint)) := by
      simpa only [origin, C.coord_source] using hcoord
    rw [hcoord']
    linarith
  have hmsSupport : Erdos957Case3General.crossFrom origin
      (C.coord s (P.next s).1) (C.coord s ms) ≤ 0 := by
    have hedge := P.edge_support s ms
    have hcoord := crossFrom_coord_eq_neg_cross C s s.1 (P.next s).1 ms
    have hcoord' : Erdos957Case3General.crossFrom origin
        (C.coord s (P.next s).1) (C.coord s ms) =
        -Erdos957GeometryCore.cross
          (((P.next s).1 : ComplexPoint) - (s.1 : ComplexPoint))
          ((ms : ComplexPoint) - (s.1 : ComplexPoint)) := by
      simpa only [origin, C.coord_source] using hcoord
    rw [hcoord']
    linarith
  constructor
  · by_contra hside
    have hsideLe : Erdos957Case3General.crossFrom
        (C.coord s s.1) (C.coord s ms) (C.coord s v) ≤ 0 :=
      le_of_not_gt hside
    rw [C.coord_source] at hsideLe
    have hsideLe' : Erdos957Case3General.crossFrom origin
        (C.coord s ms) (C.coord s v) ≤ 0 := by
      simpa only [origin] using hsideLe
    have hsideSq := Erdos957Case3General.cross_sq_eq_three_fourths_of_common_unit
      (sq_source_of_adj ms hsms)
      (sq_source_of_adj v hsv)
      (sq_of_adj ms v ((unitDistanceGraph A).adj_symm hvms))
    have hsideLt : Erdos957Case3General.crossFrom origin
        (C.coord s ms) (C.coord s v) < 0 := by
      nlinarith [hsideLe']
    have hmsEq := negative_equilateral_supported_eq_endpoint
      (e := C.coord s (P.next s).1) (v := C.coord s v) (m := C.coord s ms)
      (sq_source_of_adj v hsv)
      (sq_source_of_adj ms hsms)
      (sq_of_adj v ms hvms)
      (sq_of_adj (P.next s).1 v htv)
      hedgeSq htargetSupport hmsSupport hsideLt
    have hvertex : ms = (P.next s).1 := C.coord_injective P s hmsEq
    exact hmsNotHull (by simpa [hvertex] using (P.next s).property)
  · by_contra hside
    have hsidePos : 0 < Erdos957Case3General.crossFrom
        (C.coord (P.next s) (P.next s).1)
        (C.coord (P.next s) mt) (C.coord (P.next s) v) :=
      lt_of_not_ge hside
    have hsideCommon : 0 < Erdos957Case3General.crossFrom
        (C.coord s (P.next s).1) (C.coord s mt) (C.coord s v) := by
      rw [crossFrom_coord_eq_neg_cross C (P.next s) (P.next s).1 mt v]
        at hsidePos
      rw [crossFrom_coord_eq_neg_cross C s (P.next s).1 mt v]
      exact hsidePos
    have hmtSupport : Erdos957Case3General.crossFrom origin
        (C.coord s (P.next s).1) (C.coord s mt) ≤ 0 := by
      have hedge := P.edge_support s mt
      have hcoord := crossFrom_coord_eq_neg_cross C s s.1 (P.next s).1 mt
      have hcoord' : Erdos957Case3General.crossFrom origin
          (C.coord s (P.next s).1) (C.coord s mt) =
          -Erdos957GeometryCore.cross
            (((P.next s).1 : ComplexPoint) - (s.1 : ComplexPoint))
            ((mt : ComplexPoint) - (s.1 : ComplexPoint)) := by
        simpa only [origin, C.coord_source] using hcoord
      rw [hcoord']
      linarith
    have hmtEq := positive_equilateral_supported_eq_origin
      (e := C.coord s (P.next s).1) (v := C.coord s v) (m := C.coord s mt)
      (sq_of_adj (P.next s).1 v htv)
      (sq_of_adj (P.next s).1 mt htmt)
      (sq_of_adj v mt hvmt)
      (sq_source_of_adj v hsv)
      hedgeSq htargetSupport hmtSupport hsideCommon
    have hvertex : mt = s.1 := by
      apply C.coord_injective P s
      change C.coord s mt = C.coord s s.1
      rw [C.coord_source]
      exact hmtEq
    exact hmtNotHull (by simpa [hvertex] using s.property)

/-- A vertex with exactly one hull unit neighbor determines that neighbor
uniquely. -/
theorem hull_source_eq_of_singleton_unit_neighbors
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {middle : Vertex A} {s t : {p // p ∈ P.H}}
    (hone : (hullUnitNeighbors P middle).card = 1)
    (hs : (unitDistanceGraph A).Adj middle s.1)
    (ht : (unitDistanceGraph A).Adj middle t.1) : s = t := by
  have hsMem : s.1 ∈ hullUnitNeighbors P middle :=
    mem_hullUnitNeighbors.mpr ⟨s.property, hs⟩
  have htMem : t.1 ∈ hullUnitNeighbors P middle :=
    mem_hullUnitNeighbors.mpr ⟨t.property, ht⟩
  apply Subtype.ext
  exact Finset.card_le_one.mp (by omega) s.1 hsMem t.1 htMem

/-- This is the exact middle-role collision bridge available after adding
the currently absent equality between the outer classified middle and the
row's retained middle target. -/
theorem source_eq_of_case3_middle_collision
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {classifiedMiddle target : Vertex A} {s t : {p // p ∈ P.H}}
    (hone : (hullUnitNeighbors P classifiedMiddle).card = 1)
    (hsourceClassified : (unitDistanceGraph A).Adj s.1 classifiedMiddle)
    (htargetClassified : target = classifiedMiddle)
    (hotherTarget : (unitDistanceGraph A).Adj t.1 target) : s = t := by
  apply hull_source_eq_of_singleton_unit_neighbors hone
  · exact hsourceClassified.symm
  · simpa [htargetClassified] using hotherTarget.symm

/-- A proposition exposing the full Case-3 constructor without choosing
between its low and high inner rows. -/
def IsCase3Row
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (R : RealizedSourceRow P C source) : Prop :=
  ∃ (middle : Vertex A)
      (hdegree : (unitDistanceGraph A).degree middle ≤ 5)
      (hone : (hullUnitNeighbors P middle).card = 1)
      (middleCoord : Erdos957Cases13.Point)
      (row : PairCases.Case3ActualRow P C source middleCoord)
      (hmiddle : row.middleTarget.vertex = middle),
    R = .case3 middle hdegree hone middleCoord row hmiddle

private theorem adj_of_sqDist_coord_eq_one
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (i : {p // p ∈ P.H})
    (a b : Vertex A) (h : sqDist (C.coord i a) (C.coord i b) = 1) :
    (unitDistanceGraph A).Adj a b := by
  change dist (a : ComplexPoint) (b : ComplexPoint) = 1
  have hsquare := C.sqDist_coord i a b
  rw [h] at hsquare
  nlinarith [dist_nonneg (x := (a : ComplexPoint)) (y := (b : ComplexPoint))]

/-- Unpack a realized Case-3 secondary descriptor into the actual third
vertex of its equilateral source--target triangle and the signed side stored
by the descriptor. -/
theorem exists_case3_secondary_middle_of_descriptor
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P C source} {v : Vertex A}
    (D : RealizedPositiveTarget R v)
    (Arr : RealizedArrivalDescriptor R D.role D.target)
    (hR : IsCase3Row R)
    (hrole : D.role = PairCases.TargetRoleName.case3Secondary) :
    ∃ middle : Erdos957GeometryLocalRows.LocalTarget P C source,
      (unitDistanceGraph A).Adj source.1 middle.vertex ∧
      (unitDistanceGraph A).Adj v middle.vertex ∧
      ((Erdos957Case3General.crossFrom
          (C.coord source source.1) (C.coord source middle.vertex)
          (C.coord source v) ≤ 0 ∧
            Arr.association = ArrivalAssociation.fromPrevious) ∨
        (0 < Erdos957Case3General.crossFrom
          (C.coord source source.1) (C.coord source middle.vertex)
          (C.coord source v) ∧
            Arr.association = ArrivalAssociation.fromNext)) := by
  rcases hR with ⟨middle, hdegree, hone, middleCoord, row, hmiddle, rfl⟩
  cases row with
  | low middleTarget hm hu hfour =>
      have ht := D.target_at_role
      rw [hrole] at ht
      simp [RealizedSourceRow.targetAtRole] at ht
  | high secondaryCoord middleTarget secondaryTarget hm hs hu hsu hmu hne =>
      have ht := D.target_at_role
      rw [hrole] at ht
      simp only [RealizedSourceRow.targetAtRole, Option.some.injEq] at ht
      have hv : v = secondaryTarget.vertex := by
        calc
          v = D.target.vertex := D.vertex_eq
          _ = secondaryTarget.vertex := congrArg
            Erdos957GeometryLocalRows.LocalTarget.vertex ht.symm
      have hsm : (unitDistanceGraph A).Adj source.1 middleTarget.vertex := by
        apply adj_of_sqDist_coord_eq_one C source
        rw [C.coord_source, hm]
        exact hu
      have hvm : (unitDistanceGraph A).Adj v middleTarget.vertex := by
        subst v
        apply adj_of_sqDist_coord_eq_one C source
        rw [hm, hs]
        simpa [sqDist_comm] using hmu
      refine ⟨middleTarget, hsm, hvm, ?_⟩
      have hcross : Erdos957Case3General.crossFrom
          (C.coord source source.1) (C.coord source middleTarget.vertex)
          (C.coord source v) =
          Erdos957Case3General.crossFrom origin middleCoord secondaryCoord := by
        rw [C.coord_source, hm, hv, hs]
        simp only [origin]
      by_cases hc : Erdos957Case3General.crossFrom origin middleCoord
          secondaryCoord ≤ 0
      · left
        constructor
        · rw [hcross]
          exact hc
        · have ha := Arr.association_eq
          calc
            Arr.association =
                (RealizedSourceRow.case3 middle hdegree hone middleCoord
                  (PairCases.Case3ActualRow.high secondaryCoord middleTarget
                    secondaryTarget hm hs hu hsu hmu hne) hmiddle).roleAssociation
                  D.role := ha
            _ = ArrivalAssociation.fromPrevious := by
              rw [hrole]
              simp [RealizedSourceRow.roleAssociation, hc]
      · right
        have hcpos : 0 < Erdos957Case3General.crossFrom origin middleCoord
            secondaryCoord := lt_of_not_ge hc
        constructor
        · rw [hcross]
          exact hcpos
        · have ha := Arr.association_eq
          calc
            Arr.association =
                (RealizedSourceRow.case3 middle hdegree hone middleCoord
                  (PairCases.Case3ActualRow.high secondaryCoord middleTarget
                    secondaryTarget hm hs hu hsu hmu hne) hmiddle).roleAssociation
                  D.role := ha
            _ = ArrivalAssociation.fromNext := by
              rw [hrole]
              simp [RealizedSourceRow.roleAssociation, hc]

/-- Every positive target in an actual Case-3 row is a direct unit neighbor
of its emitting hull source. -/
theorem case3_target_adj_source
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P C source} {v : Vertex A}
    (D : RealizedPositiveTarget R v) (hR : IsCase3Row R) :
    (unitDistanceGraph A).Adj source.1 v := by
  rcases hR with ⟨middle, hdegree, hone, middleCoord, row, hmiddle, rfl⟩
  apply D.direct_target_adj
  · intro hrole
    have ht := D.target_at_role
    rw [hrole] at ht
    cases row <;>
      simp [RealizedSourceRow.targetAtRole] at ht
  · intro hrole
    have ht := D.target_at_role
    rw [hrole] at ht
    cases row <;>
      simp [RealizedSourceRow.targetAtRole] at ht

/-- In a faithful Case-3 row, the middle formula role really is the outer
classified middle that owns the singleton hull-neighbor certificate. -/
theorem target_eq_classifiedMiddle_of_case3Middle
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P C source} {v : Vertex A}
    (D : RealizedPositiveTarget R v) (hR : IsCase3Row R)
    (hrole : D.role = PairCases.TargetRoleName.case3Middle) :
    ∃ middle : Vertex A,
      v = middle ∧ (hullUnitNeighbors P middle).card = 1 := by
  rcases hR with ⟨middle, hdegree, hone, middleCoord, row, hmiddle, rfl⟩
  refine ⟨middle, ?_, hone⟩
  cases row with
  | low middleTarget hm hu hfour =>
      simp only [PairCases.Case3ActualRow.middleTarget] at hmiddle
      have ht := D.target_at_role
      rw [hrole] at ht
      simp only [RealizedSourceRow.targetAtRole, Option.some.injEq] at ht
      calc
        v = D.target.vertex := D.vertex_eq
        _ = middleTarget.vertex := congrArg
          Erdos957GeometryLocalRows.LocalTarget.vertex ht.symm
        _ = middle := hmiddle
  | high secondaryCoord middleTarget secondaryTarget hm hs hu hsu hmu hne =>
      simp only [PairCases.Case3ActualRow.middleTarget] at hmiddle
      have ht := D.target_at_role
      rw [hrole] at ht
      simp only [RealizedSourceRow.targetAtRole, Option.some.injEq] at ht
      calc
        v = D.target.vertex := D.vertex_eq
        _ = middleTarget.vertex := congrArg
          Erdos957GeometryLocalRows.LocalTarget.vertex ht.symm
        _ = middle := hmiddle

/-- Descriptor-level uniqueness for all Case-3 collisions in which at least
one arrival uses the middle role.  This covers middle/middle and both mixed
middle/secondary cases; no side comparison is needed. -/
theorem source_eq_of_case3_collision_of_middle_role
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {s t : {p // p ∈ P.H}}
    {Rs : RealizedSourceRow P C s} {Rt : RealizedSourceRow P C t}
    {v : Vertex A}
    (Ds : RealizedPositiveTarget Rs v) (Dt : RealizedPositiveTarget Rt v)
    (hRs : IsCase3Row Rs) (hRt : IsCase3Row Rt)
    (hmiddle : Ds.role = PairCases.TargetRoleName.case3Middle ∨
      Dt.role = PairCases.TargetRoleName.case3Middle) : s = t := by
  rcases hmiddle with hsMiddle | htMiddle
  · obtain ⟨middle, hv, hone⟩ :=
      target_eq_classifiedMiddle_of_case3Middle Ds hRs hsMiddle
    apply hull_source_eq_of_singleton_unit_neighbors hone
    · simpa [hv] using (case3_target_adj_source Ds hRs).symm
    · simpa [hv] using (case3_target_adj_source Dt hRt).symm
  · obtain ⟨middle, hv, hone⟩ :=
      target_eq_classifiedMiddle_of_case3Middle Dt hRt htMiddle
    apply hull_source_eq_of_singleton_unit_neighbors hone
    · simpa [hv] using (case3_target_adj_source Ds hRs).symm
    · simpa [hv] using (case3_target_adj_source Dt hRt).symm

/-- Two consecutive Case-3 secondary arrivals at the same actual target
receive opposite formula-derived associations. -/
theorem case3_secondary_associations_ne_across_next_edge
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (s : {p // p ∈ P.H})
    {Rs : RealizedSourceRow P C s}
    {Rt : RealizedSourceRow P C (P.next s)} {v : Vertex A}
    (Ds : RealizedPositiveTarget Rs v) (Dt : RealizedPositiveTarget Rt v)
    (As : RealizedArrivalDescriptor Rs Ds.role Ds.target)
    (At : RealizedArrivalDescriptor Rt Dt.role Dt.target)
    (hRs : IsCase3Row Rs) (hRt : IsCase3Row Rt)
    (hsRole : Ds.role = PairCases.TargetRoleName.case3Secondary)
    (htRole : Dt.role = PairCases.TargetRoleName.case3Secondary) :
    As.association ≠ At.association := by
  obtain ⟨ms, hsms, hvms, hsSide⟩ :=
    exists_case3_secondary_middle_of_descriptor Ds As hRs hsRole
  obtain ⟨mt, htmt, hvmt, htSide⟩ :=
    exists_case3_secondary_middle_of_descriptor Dt At hRt htRole
  have hsv := case3_target_adj_source Ds hRs
  have htv := case3_target_adj_source Dt hRt
  obtain ⟨hsPositive, htNonpositive⟩ :=
    case3_equilateral_orientations_opposite_across_next_edge
      hA P C s hsv htv hsms hvms htmt hvmt ms.not_hull mt.not_hull
  have hsAssoc : As.association = ArrivalAssociation.fromNext := by
    rcases hsSide with ⟨hsNonpositive, hsPrev⟩ | ⟨_, hsNext⟩
    · exfalso
      exact (not_lt_of_ge hsNonpositive) hsPositive
    · exact hsNext
  have htAssoc : At.association = ArrivalAssociation.fromPrevious := by
    rcases htSide with ⟨_, htPrev⟩ | ⟨htPositive, htNext⟩
    · exact htPrev
    · exfalso
      exact (not_lt_of_ge htNonpositive) htPositive
  rw [hsAssoc, htAssoc]
  decide

end Erdos957Case3SameSide
