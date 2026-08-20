import ErdosProblems.Erdos957.CaseClassification
import ErdosProblems.Erdos957.Case3Secondary

/-!
# Realized Case 1/3 rows from the common aligned chart

This leaf proves the Case 1 construction from degree six rather than assuming
membership/alignment of the two canonical recipients.  It also records the exact
secondary-incidence datum still needed by the formula-retaining Case 3 record.
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Erdos957Case13RealizedRows

open Erdos957GeometryCore
open Erdos957CaseClassification
open Erdos957CaseClassification.PairCases
open Erdos957Cases13
open Erdos957Case13Bridge
open Erdos957Case3General

abbrev ComplexPoint := EuclideanSpace ℝ (Fin 2)
abbrev Point := Erdos957Cases13.Point

/-- At a six-valent middle, the two canonical intersections of the source and middle unit
circles are actual members of the configuration. -/
lemma case1_canonical_mem_of_middle_degree_six {A : Finset Point} {middle : Point}
    (hsep : IsOneSeparated (A : Set Point))
    (hsource : origin ∈ A)
    (hmiddleUnit : sqDist origin middle = 1)
    (hmiddleDegree : degree A middle = 6) :
    case1Left middle ∈ A ∧ case1Right middle ∈ A := by
  have hsourceNeighbor : origin ∈ unitNeighbors A middle := by
    apply mem_unitNeighbors.mpr
    exact ⟨hsource, by simpa [sqDist_comm] using hmiddleUnit⟩
  obtain ⟨hex⟩ := exists_orderedHexagonAt_of_degree_eq_six hsep hmiddleDegree
  obtain ⟨i, hi⟩ := hex.neighbor_surjective origin hsourceNeighbor
  obtain ⟨j, k, hjk, hmj, hij, hmk, hik⟩ :=
    Erdos957Case3General.OrderedHexagonAt.exists_two_common_neighbors hex i
  have hjkPoint : hex.neighbor j ≠ hex.neighbor k := by
    exact fun h ↦ hjk (hex.neighbor_injective h)
  have hmo : sqDist middle origin = 1 := by simpa [sqDist_comm] using hmiddleUnit
  have hoj : sqDist origin (hex.neighbor j) = 1 := by simpa [hi] using hij
  have hok : sqDist origin (hex.neighbor k) = 1 := by simpa [hi] using hik
  have hleft := common_unit_eq_first_or_second hmo hmj hoj hmk hok
    (case1Left_common_unit hmiddleUnit).2
    (case1Left_common_unit hmiddleUnit).1 hjkPoint
  have hright := common_unit_eq_first_or_second hmo hmj hoj hmk hok
    (case1Right_common_unit hmiddleUnit).2
    (case1Right_common_unit hmiddleUnit).1 hjkPoint
  have hleftRight : case1Left middle ≠ case1Right middle :=
    case1Left_ne_case1Right hmiddleUnit
  have hjA : hex.neighbor j ∈ A :=
    (mem_unitNeighbors.mp (hex.neighbor_mem j)).1
  have hkA : hex.neighbor k ∈ A :=
    (mem_unitNeighbors.mp (hex.neighbor_mem k)).1
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · exact (hleftRight (hleft.trans hright.symm)).elim
  · exact ⟨hleft.symm ▸ hjA, hright.symm ▸ hkA⟩
  · exact ⟨hleft.symm ▸ hkA, hright.symm ▸ hjA⟩
  · exact (hleftRight (hleft.trans hright.symm)).elim

/-- The canonical left recipient has degree at most five, without a prescribed angular index. -/
lemma case1_left_degree_le_five_unaligned {A : Finset Point} {middle : Point}
    (hsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hsource : origin ∈ A) (hmiddle : middle ∈ A)
    (hmiddleUnit : sqDist origin middle = 1)
    (hmiddleCone : InOpenMiddleCone middle) :
    degree A (case1Left middle) ≤ 5 := by
  have hle := degree_le_six hsep (case1Left middle)
  by_contra hnot
  have hsix : degree A (case1Left middle) = 6 := by omega
  have hsourceNeighbor : origin ∈ unitNeighbors A (case1Left middle) := by
    exact mem_unitNeighbors.mpr ⟨hsource, by
      simpa [sqDist_comm] using (case1Left_common_unit hmiddleUnit).1⟩
  have hmiddleNeighbor : middle ∈ unitNeighbors A (case1Left middle) := by
    exact mem_unitNeighbors.mpr ⟨hmiddle, by
      simpa [sqDist_comm] using (case1Left_common_unit hmiddleUnit).2⟩
  have hforced := completion_mem_of_degree_eq_six hsep hsix hsourceNeighbor
    hmiddleNeighbor hmiddleUnit
  rw [← Erdos957Case13Bridge.case1_forcedLeft_eq_completion] at hforced
  exact case1_forcedAboveLeft_not_mem hsupport hmiddleCone hforced

/-- Right-hand counterpart. -/
lemma case1_right_degree_le_five_unaligned {A : Finset Point} {middle : Point}
    (hsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hsource : origin ∈ A) (hmiddle : middle ∈ A)
    (hmiddleUnit : sqDist origin middle = 1)
    (hmiddleCone : InOpenMiddleCone middle) :
    degree A (case1Right middle) ≤ 5 := by
  have hle := degree_le_six hsep (case1Right middle)
  by_contra hnot
  have hsix : degree A (case1Right middle) = 6 := by omega
  have hsourceNeighbor : origin ∈ unitNeighbors A (case1Right middle) := by
    exact mem_unitNeighbors.mpr ⟨hsource, by
      simpa [sqDist_comm] using (case1Right_common_unit hmiddleUnit).1⟩
  have hmiddleNeighbor : middle ∈ unitNeighbors A (case1Right middle) := by
    exact mem_unitNeighbors.mpr ⟨hmiddle, by
      simpa [sqDist_comm] using (case1Right_common_unit hmiddleUnit).2⟩
  have hforced := completion_mem_of_degree_eq_six hsep hsix hsourceNeighbor
    hmiddleNeighbor hmiddleUnit
  rw [← Erdos957Case13Bridge.case1_forcedRight_eq_completion] at hforced
  exact case1_forcedAboveRight_not_mem hsupport hmiddleCone hforced

/-- A singleton hull-neighbour set gives the exact coordinate uniqueness used by both Cases 1
and 3. -/
lemma unique_alignedHull_neighbor_of_card_one
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H}) (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (honeHull : (hullUnitNeighbors P middle).card = 1) :
    ∀ p ∈ alignedHull C source,
      sqDist (C.coord source middle) p = 1 → p = origin := by
  intro p hpHull hpUnit
  rcases Finset.mem_map.mp hpHull with ⟨v, hvHull, rfl⟩
  have hmv : (unitDistanceGraph A).Adj middle v := by
    have hsquare : dist (middle : ComplexPoint) (v : ComplexPoint) ^ 2 = 1 := by
      rw [← C.sqDist_coord source middle v]
      exact hpUnit
    change dist (middle : ComplexPoint) (v : ComplexPoint) = 1
    nlinarith [dist_nonneg (x := (middle : ComplexPoint)) (y := (v : ComplexPoint))]
  have hvNeighbor : v ∈ hullUnitNeighbors P middle :=
    mem_hullUnitNeighbors.mpr ⟨hvHull, hmv⟩
  have hsourceNeighbor : source.1 ∈ hullUnitNeighbors P middle :=
    mem_hullUnitNeighbors.mpr ⟨source.property, hsourceMiddle.symm⟩
  have hcardLe : (hullUnitNeighbors P middle).card ≤ 1 := by omega
  have hvs : v = source.1 :=
    Finset.card_le_one.mp hcardLe v hvNeighbor source.1 hsourceNeighbor
  subst v
  simpa [origin] using C.coord_source source

/-- The exact `Case1ActualRow` follows from the graph-theoretic Case 1 evidence.  No
`Case1Geometry` alignment premise is used. -/
theorem case1ActualRow_of_degree_six
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (_hsourceDegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (C.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 6)
    (honeHull : (hullUnitNeighbors P middle).card = 1) :
    Nonempty (Case1ActualRow P C source (C.coord source middle)) := by
  let A' := alignedConfiguration C source
  let H' := alignedHull C source
  let m : Point := C.coord source middle
  have hsep : IsOneSeparated (A' : Set Point) :=
    alignedConfiguration_oneSeparated hA C source
  have hsupport : ∀ p ∈ A', p.2 ≤ 0 := alignedConfiguration_below_support C source
  have hsourceA : origin ∈ A' := origin_mem_alignedConfiguration C source
  have hmiddleA : m ∈ A' := coord_mem_alignedConfiguration C source middle
  have hmiddleUnit : sqDist origin m = 1 := by
    change sqDist (0, 0) (C.coord source middle) = 1
    rw [← C.coord_source source, C.sqDist_coord]
    change dist (source.1 : ComplexPoint) (middle : ComplexPoint) = 1 at hsourceMiddle
    rw [hsourceMiddle]
    norm_num
  have hmiddleDegree' : degree A' m = 6 := by
    change degree (alignedConfiguration C source) (C.coord source middle) = 6
    rw [aligned_degree_coord C source middle]
    exact hmiddleDegree
  have hcanonical := case1_canonical_mem_of_middle_degree_six hsep hsourceA
    hmiddleUnit hmiddleDegree'
  obtain ⟨left, hleftCoord⟩ := exists_vertex_coord_eq C source hcanonical.1
  obtain ⟨right, hrightCoord⟩ := exists_vertex_coord_eq C source hcanonical.2
  have hsourceHullNeighbor : source.1 ∈ hullUnitNeighbors P middle := by
    exact mem_hullUnitNeighbors.mpr ⟨source.property, hsourceMiddle.symm⟩
  have huniqueHull : ∀ p ∈ H', sqDist m p = 1 → p = origin := by
    intro p hpHull hpUnit
    rcases Finset.mem_map.mp hpHull with ⟨v, hvHull, rfl⟩
    have hmv : (unitDistanceGraph A).Adj middle v := by
      have hsquare : dist (middle : ComplexPoint) (v : ComplexPoint) ^ 2 = 1 := by
        rw [← C.sqDist_coord source middle v]
        exact hpUnit
      change dist (middle : ComplexPoint) (v : ComplexPoint) = 1
      nlinarith [dist_nonneg (x := (middle : ComplexPoint)) (y := (v : ComplexPoint))]
    have hvNeighbor : v ∈ hullUnitNeighbors P middle :=
      mem_hullUnitNeighbors.mpr ⟨hvHull, hmv⟩
    have hcardLe : (hullUnitNeighbors P middle).card ≤ 1 := by omega
    have hvs : v = source.1 :=
      Finset.card_le_one.mp hcardLe v hvNeighbor source.1 hsourceHullNeighbor
    subst v
    simpa [m, origin] using C.coord_source source
  have hleftNotHull : left ∉ P.H := by
    intro hleftHull
    have heq := huniqueHull _ (coord_mem_alignedHull C source hleftHull)
      (by simpa [m, hleftCoord] using (case1Left_common_unit hmiddleUnit).2)
    have hu := (case1Left_common_unit hmiddleUnit).1
    have hcanon : case1Left m = origin := hleftCoord.symm.trans heq
    rw [hcanon, sqDist_self] at hu
    norm_num at hu
  have hrightNotHull : right ∉ P.H := by
    intro hrightHull
    have heq := huniqueHull _ (coord_mem_alignedHull C source hrightHull)
      (by simpa [m, hrightCoord] using (case1Right_common_unit hmiddleUnit).2)
    have hu := (case1Right_common_unit hmiddleUnit).1
    have hcanon : case1Right m = origin := hrightCoord.symm.trans heq
    rw [hcanon, sqDist_self] at hu
    norm_num at hu
  have hleftDegreeCoord : degree A' (case1Left m) ≤ 5 :=
    case1_left_degree_le_five_unaligned hsep hsupport hsourceA hmiddleA
      hmiddleUnit hmiddleCone
  have hrightDegreeCoord : degree A' (case1Right m) ≤ 5 :=
    case1_right_degree_le_five_unaligned hsep hsupport hsourceA hmiddleA
      hmiddleUnit hmiddleCone
  have hleftDegree : (unitDistanceGraph A).degree left ≤ 5 := by
    rw [← aligned_degree_coord C source left, hleftCoord]
    exact hleftDegreeCoord
  have hrightDegree : (unitDistanceGraph A).degree right ≤ 5 := by
    rw [← aligned_degree_coord C source right, hrightCoord]
    exact hrightDegreeCoord
  let leftTarget : Erdos957GeometryLocalRows.LocalTarget P C source :=
    Erdos957GeometryLocalRows.LocalTarget.ofCase1Left hmiddleUnit hmiddleCone
      hleftCoord hleftDegree hleftNotHull
  let rightTarget : Erdos957GeometryLocalRows.LocalTarget P C source :=
    Erdos957GeometryLocalRows.LocalTarget.ofCase1Right hmiddleUnit hmiddleCone
      hrightCoord hrightDegree hrightNotHull
  have hdistinct : leftTarget.vertex ≠ rightTarget.vertex := by
    intro h
    have hc := congrArg (C.coord source) h
    change C.coord source left = C.coord source right at hc
    rw [hleftCoord, hrightCoord] at hc
    exact (case1Left_ne_case1Right hmiddleUnit) hc
  exact ⟨{
    left := leftTarget
    right := rightTarget
    left_coordinate := hleftCoord
    right_coordinate := hrightCoord
    distinct := hdistinct }⟩

/-- Case 1 realized row from the selected middle and its exact `FourCase.case1` evidence.
The local hull window certifies that the retained middle itself is non-extreme;
the one-extreme count excludes both canonical recipients from the hull. -/
theorem exists_realized_case1
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (F.chart.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 6)
    (honeHull : (hullUnitNeighbors P middle).card = 1) :
    ∃ (R : RealizedSourceRow P F.chart source)
      (row : Case1ActualRow P F.chart source (F.chart.coord source middle)),
      R = .case1 middle hmiddleDegree honeHull (F.chart.coord source middle)
        rfl
        (middle_not_mem_hull_of_local_window F source
          ((mem_flatVertices_iff_isFlat P source).mp (source_facts hs).2.1)
          hwindow middle hsourceMiddle hmiddleCone)
        (by
          change sqDist (0, 0) (F.chart.coord source middle) = 1
          rw [← F.chart.coord_source source, F.chart.sqDist_coord]
          change dist (source.1 : ComplexPoint) (middle : ComplexPoint) = 1 at hsourceMiddle
          rw [hsourceMiddle]
          norm_num) row ∧
      R.localCase = row.localCase := by
  obtain ⟨row⟩ := case1ActualRow_of_degree_six hA F.chart source middle
    (source_facts hs).2.2 hsourceMiddle hmiddleCone hmiddleDegree honeHull
  let hunit : sqDist origin (F.chart.coord source middle) = 1 := by
    change sqDist (0, 0) (F.chart.coord source middle) = 1
    rw [← F.chart.coord_source source, F.chart.sqDist_coord]
    change dist (source.1 : ComplexPoint) (middle : ComplexPoint) = 1 at hsourceMiddle
    rw [hsourceMiddle]
    norm_num
  have hmiddleNot : middle ∉ P.H :=
    middle_not_mem_hull_of_local_window F source
      ((mem_flatVertices_iff_isFlat P source).mp (source_facts hs).2.1)
      hwindow middle hsourceMiddle hmiddleCone
  let R : RealizedSourceRow P F.chart source :=
    .case1 middle hmiddleDegree honeHull (F.chart.coord source middle) rfl
      hmiddleNot hunit row
  exact ⟨R, row, rfl, rfl⟩

/-! ## Case 3 and its remaining incidence witness -/

/-- The exact geometric datum not supplied by `FourCase.case3` or by the local hull window:
an actual second vertex joined both to the source and to the middle, lying strictly higher than
the middle in the same aligned chart. -/
structure Case3SecondaryIncidence
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H}) (middle : Vertex A) where
  secondary : Vertex A
  source_adj : (unitDistanceGraph A).Adj source.1 secondary
  middle_adj : (unitDistanceGraph A).Adj middle secondary
  higher : (C.coord source middle).2 < (C.coord source secondary).2

/-- Algebraic core of arbitrary-middle arc closeness.  The three strict orientation
hypotheses say that `q` occurs between the middle radius and the selected radius; unlike a
rotation normalization, they are invariant information available from the angular bins. -/
lemma oriented_right_arc_closeness
    {middle q t : Point}
    (hmiddleUnit : sqDist origin middle = 1)
    (hqUnit : sqDist origin q = 1)
    (hqAway : 1 ≤ sqDist middle q)
    (htUnit : sqDist middle t = 1)
    (hcrossMQ : 0 < middle.1 * q.2 - middle.2 * q.1)
    (hcrossQD : 0 < q.1 * (t.2 - middle.2) - q.2 * (t.1 - middle.1))
    (hqDotT : 0 < q.1 * t.1 + q.2 * t.2) :
    sqDist q t < 1 := by
  let d : Point := (t.1 - middle.1, t.2 - middle.2)
  let a : ℝ := middle.1 * q.1 + middle.2 * q.2
  let b : ℝ := q.1 * d.1 + q.2 * d.2
  let x : ℝ := middle.1 * q.2 - middle.2 * q.1
  let y : ℝ := q.1 * d.2 - q.2 * d.1
  have hmNorm : middle.1 ^ 2 + middle.2 ^ 2 = 1 := by
    simpa [sqDist, origin] using hmiddleUnit
  have hqNorm : q.1 ^ 2 + q.2 ^ 2 = 1 := by
    simpa [sqDist, origin] using hqUnit
  have hdNorm : d.1 ^ 2 + d.2 ^ 2 = 1 := by
    dsimp [d]
    simp only [sqDist] at htUnit
    nlinarith
  have ha : a ≤ 1 / 2 := by
    simp only [sqDist] at hqAway
    dsimp [a]
    nlinarith
  have hx : 0 < x := by simpa [x] using hcrossMQ
  have hy : 0 < y := by simpa [y, d] using hcrossQD
  have hab : 0 < a + b := by
    dsimp [a, b, d]
    nlinarith
  have hxa : x ^ 2 + a ^ 2 = 1 := by
    dsimp [x, a]
    nlinarith [hmNorm, hqNorm]
  have hyb : y ^ 2 + b ^ 2 = 1 := by
    dsimp [y, b]
    nlinarith [hqNorm, hdNorm]
  have hb : b < 1 := by
    nlinarith [sq_pos_of_pos hy]
  have hpa : 0 < 1 - a := by linarith
  have hpb : 0 < 1 - b := by linarith
  have hprod : 0 < 2 * (1 - a) * (1 - b) * (a + b) := by positivity
  have hxa' : x ^ 2 = 1 - a ^ 2 := by linarith
  have hyb' : y ^ 2 = 1 - b ^ 2 := by linarith
  have hsquareIdentity :
      (x * y) ^ 2 - ((1 - a) * (1 - b)) ^ 2 =
        2 * (1 - a) * (1 - b) * (a + b) := by
    calc
      (x * y) ^ 2 - ((1 - a) * (1 - b)) ^ 2 =
          x ^ 2 * y ^ 2 - ((1 - a) * (1 - b)) ^ 2 := by ring
      _ = (1 - a ^ 2) * (1 - b ^ 2) -
          ((1 - a) * (1 - b)) ^ 2 := by rw [hxa', hyb']
      _ = 2 * (1 - a) * (1 - b) * (a + b) := by ring
  have hsq : ((1 - a) * (1 - b)) ^ 2 < (x * y) ^ 2 := by
    linarith
  have hxy : (1 - a) * (1 - b) < x * y := by
    have hp : 0 < (1 - a) * (1 - b) := mul_pos hpa hpb
    have hxypos : 0 < x * y := mul_pos hx hy
    exact (sq_lt_sq₀ hp.le hxypos.le).mp hsq
  have hmd : middle.1 * d.1 + middle.2 * d.2 = a * b - x * y := by
    have hscaled :
        (middle.1 * d.1 + middle.2 * d.2) *
            (q.1 ^ 2 + q.2 ^ 2) = a * b - x * y := by
      dsimp [a, b, x, y]
      ring
    rw [hqNorm, mul_one] at hscaled
    exact hscaled
  have hdistExpand :
      sqDist q t - 1 =
        (q.1 ^ 2 + q.2 ^ 2) +
          (middle.1 ^ 2 + middle.2 ^ 2) + (d.1 ^ 2 + d.2 ^ 2) -
          2 * a - 2 * b +
          2 * (middle.1 * d.1 + middle.2 * d.2) - 1 := by
    simp only [sqDist]
    dsimp [a, b, d]
    ring
  have hdistIdentity :
      sqDist q t - 1 = 2 * ((1 - a) * (1 - b) - x * y) := by
    rw [hqNorm, hmNorm, hdNorm, hmd] at hdistExpand
    calc
      sqDist q t - 1 =
          1 + 1 + 1 - 2 * a - 2 * b + 2 * (a * b - x * y) - 1 :=
        hdistExpand
      _ = 2 * ((1 - a) * (1 - b) - x * y) := by ring
  linarith

/-- One-separated identification once the angular-bin orientation data have been supplied. -/
lemma right_candidate_eq_existing_arbitrary
    {middle q t : Point}
    (hmiddleUnit : sqDist origin middle = 1)
    (hqUnit : sqDist origin q = 1)
    (hqAway : 1 ≤ sqDist middle q)
    (htUnit : sqDist middle t = 1)
    (hcrossMQ : 0 < middle.1 * q.2 - middle.2 * q.1)
    (hcrossQD : 0 < q.1 * (t.2 - middle.2) - q.2 * (t.1 - middle.1))
    (hqDotT : 0 < q.1 * t.1 + q.2 * t.2)
    (hsep : q = t ∨ 1 ≤ sqDist q t) :
    q = t := by
  rcases hsep with h | h
  · exact h
  · have hclose := oriented_right_arc_closeness hmiddleUnit hqUnit hqAway
      htUnit hcrossMQ hcrossQD hqDotT
    linarith

/-- The formula retained by a Case-3 row identifies its middle target with the classified
actual middle vertex. -/
lemma case3ActualRow_middleTarget_vertex
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (middle : Vertex A)
    (row : Case3ActualRow P C source (C.coord source middle)) :
    row.middleTarget.vertex = middle := by
  cases row with
  | low middleTarget hcoord hunit hdegree =>
      exact alignedCoord_injective C source hcoord
  | high secondaryCoord middleTarget secondaryTarget hmiddle hsecondary
      hmiddleUnit hsecondarySource hsecondaryMiddle hne =>
      exact alignedCoord_injective C source hmiddle

/-- In the low Case-3 branch the refactored row retains only the actual middle target; no
secondary incidence is needed. -/
theorem case3ActualRow_low
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (source : {p // p ∈ P.H})
    (hflat : P.IsFlat source) (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (F.chart.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle ≤ 4) :
    Nonempty (Case3ActualRow P F.chart source
      (F.chart.coord source middle)) := by
  let C := F.chart
  let m : Point := C.coord source middle
  have hmiddleUnit : sqDist origin m = 1 := by
    change sqDist (0, 0) (C.coord source middle) = 1
    rw [← C.coord_source source, C.sqDist_coord]
    change dist (source.1 : ComplexPoint) (middle : ComplexPoint) = 1 at hsourceMiddle
    rw [hsourceMiddle]
    norm_num
  have hmiddleNot : middle ∉ P.H :=
    middle_not_mem_hull_of_local_window F source hflat hwindow middle
      hsourceMiddle hmiddleCone
  let middleTarget := alignedUnitLocalTarget C source middle m rfl
    hmiddleUnit (by omega) hmiddleNot
  exact ⟨.low middleTarget rfl hmiddleUnit hmiddleDegree⟩

/-- Stable realized low Case-3 constructor. -/
theorem exists_realized_case3_low
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (F.chart.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle ≤ 4)
    (honeHull : (hullUnitNeighbors P middle).card = 1) :
    ∃ (R : RealizedSourceRow P F.chart source)
      (row : Case3ActualRow P F.chart source (F.chart.coord source middle)),
      R = .case3 middle (by omega) honeHull (F.chart.coord source middle) row
        (case3ActualRow_middleTarget_vertex F.chart source middle row) ∧
      R.localCase = row.localCase := by
  obtain ⟨row⟩ := case3ActualRow_low hA F source
    ((mem_flatVertices_iff_isFlat P source).mp (source_facts hs).2.1)
    hwindow middle hsourceMiddle hmiddleCone hmiddleDegree
  let R : RealizedSourceRow P F.chart source :=
    .case3 middle (by omega) honeHull (F.chart.coord source middle) row
      (case3ActualRow_middleTarget_vertex F.chart source middle row)
  exact ⟨R, row, rfl, rfl⟩

/-- The Case 3 evidence, local hull window, and one explicit secondary incidence construct the
formula-retaining actual row.  All degree and non-hull facts for the secondary are derived. -/
theorem case3ActualRow_of_secondaryIncidence
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (source : {p // p ∈ P.H})
    (hflat : P.IsFlat source) (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsourceDegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (F.chart.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle ≤ 5)
    (honeHull : (hullUnitNeighbors P middle).card = 1)
    (S : Case3SecondaryIncidence F.chart source middle) :
    Nonempty (Case3ActualRow P F.chart source
      (F.chart.coord source middle)) := by
  let C := F.chart
  let A' := alignedConfiguration C source
  let H' := alignedHull C source
  let m : Point := C.coord source middle
  let s : Point := C.coord source S.secondary
  have hmiddleUnit : sqDist origin m = 1 := by
    change sqDist (0, 0) (C.coord source middle) = 1
    rw [← C.coord_source source, C.sqDist_coord]
    change dist (source.1 : ComplexPoint) (middle : ComplexPoint) = 1 at hsourceMiddle
    rw [hsourceMiddle]
    norm_num
  have hsecondarySource : sqDist origin s = 1 := by
    change sqDist (0, 0) (C.coord source S.secondary) = 1
    rw [← C.coord_source source, C.sqDist_coord]
    have hadj := S.source_adj
    change dist (source.1 : ComplexPoint) (S.secondary : ComplexPoint) = 1 at hadj
    rw [hadj]
    norm_num
  have hsecondaryMiddle : sqDist m s = 1 := by
    change sqDist (C.coord source middle) (C.coord source S.secondary) = 1
    rw [C.sqDist_coord]
    have hadj := S.middle_adj
    change dist (middle : ComplexPoint) (S.secondary : ComplexPoint) = 1 at hadj
    rw [hadj]
    norm_num
  have hmiddleNotActual : middle ∉ P.H :=
    middle_not_mem_hull_of_local_window F source hflat hwindow middle
      hsourceMiddle hmiddleCone
  have hmiddleNot : m ∉ H' := by
    intro hm
    rcases Finset.mem_map.mp hm with ⟨v, hv, hvm⟩
    have hvm' : v = middle := alignedCoord_injective C source hvm
    subst v
    exact hmiddleNotActual hv
  have hunique := unique_alignedHull_neighbor_of_card_one C source middle
    hsourceMiddle honeHull
  have hmiddleDegree' : degree A' m ≤ 5 := by
    change degree (alignedConfiguration C source) (C.coord source middle) ≤ 5
    rw [aligned_degree_coord C source middle]
    exact hmiddleDegree
  have hsourceDegree' : degree A' origin = 3 := by
    have horigin : origin = C.coord source source.1 := by
      simpa [origin] using (C.coord_source source).symm
    change degree (alignedConfiguration C source) origin = 3
    rw [horigin, aligned_degree_coord C source source.1]
    exact hsourceDegree
  let G : Case3Geometry A' H' m s := {
    oneSeparated := alignedConfiguration_oneSeparated hA C source
    support := alignedConfiguration_below_support C source
    source_mem := origin_mem_alignedConfiguration C source
    source_hull := origin_mem_alignedHull C source
    source_degree := hsourceDegree'
    middle_mem := coord_mem_alignedConfiguration C source middle
    secondary_mem := coord_mem_alignedConfiguration C source S.secondary
    middle_degree_le_five := hmiddleDegree'
    middle_not_hull := hmiddleNot
    unique_hull_neighbor := hunique
    middle_unit := hmiddleUnit
    middle_in_cone := hmiddleCone
    secondary_source_unit := hsecondarySource
    secondary_middle_unit := hsecondaryMiddle
    secondary_high := S.higher }
  exact G.toActualRow P C source

/-- Stable realized Case 3 constructor.  Its erasure is definitionally the retained row's
`localCase`. -/
theorem exists_realized_case3_of_secondaryIncidence
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (F.chart.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle ≤ 5)
    (honeHull : (hullUnitNeighbors P middle).card = 1)
    (S : Case3SecondaryIncidence F.chart source middle) :
    ∃ (R : RealizedSourceRow P F.chart source)
      (row : Case3ActualRow P F.chart source
        (F.chart.coord source middle)),
      R = .case3 middle hmiddleDegree honeHull
        (F.chart.coord source middle) row
          (case3ActualRow_middleTarget_vertex F.chart source middle row) ∧
      R.localCase = row.localCase := by
  obtain ⟨row⟩ := case3ActualRow_of_secondaryIncidence hA F source
    ((mem_flatVertices_iff_isFlat P source).mp (source_facts hs).2.1)
    hwindow middle (source_facts hs).2.2 hsourceMiddle hmiddleCone
    hmiddleDegree honeHull S
  let R : RealizedSourceRow P F.chart source :=
    .case3 middle hmiddleDegree honeHull (F.chart.coord source middle) row
      (case3ActualRow_middleTarget_vertex F.chart source middle row)
  exact ⟨R, row, rfl, rfl⟩

/-- The exact logical join of the refactored low branch and the geometric high branch.  The
only parameter is the still-separate degree-five incidence theorem; once that theorem is
instantiated, no witness is assumed in either realized row. -/
theorem exists_realized_case3_of_degreeFiveSecondary
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (F.chart.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle ≤ 5)
    (honeHull : (hullUnitNeighbors P middle).card = 1)
    (hsecondary : (unitDistanceGraph A).degree middle = 5 →
      Nonempty (Case3SecondaryIncidence F.chart source middle)) :
    ∃ (R : RealizedSourceRow P F.chart source)
      (row : Case3ActualRow P F.chart source (F.chart.coord source middle)),
      R = .case3 middle hmiddleDegree honeHull
        (F.chart.coord source middle) row
          (case3ActualRow_middleTarget_vertex F.chart source middle row) ∧
      R.localCase = row.localCase := by
  by_cases hfour : (unitDistanceGraph A).degree middle ≤ 4
  · obtain ⟨row⟩ := case3ActualRow_low hA F source
      ((mem_flatVertices_iff_isFlat P source).mp (source_facts hs).2.1)
      hwindow middle hsourceMiddle hmiddleCone hfour
    let R : RealizedSourceRow P F.chart source :=
      .case3 middle hmiddleDegree honeHull (F.chart.coord source middle) row
        (case3ActualRow_middleTarget_vertex F.chart source middle row)
    exact ⟨R, row, rfl, rfl⟩
  · have hfive : (unitDistanceGraph A).degree middle = 5 := by omega
    obtain ⟨S⟩ := hsecondary hfive
    obtain ⟨row⟩ := case3ActualRow_of_secondaryIncidence hA F source
      ((mem_flatVertices_iff_isFlat P source).mp (source_facts hs).2.1)
      hwindow middle (source_facts hs).2.2 hsourceMiddle hmiddleCone
      hmiddleDegree honeHull S
    let R : RealizedSourceRow P F.chart source :=
      .case3 middle hmiddleDegree honeHull (F.chart.coord source middle) row
        (case3ActualRow_middleTarget_vertex F.chart source middle row)
    exact ⟨R, row, rfl, rfl⟩

/-- The independent angular-selection theorem supplies exactly the retained incidence datum
needed by the high Case-3 row. -/
theorem case3SecondaryIncidence_of_degree_five
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0)
    (hsourceDegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (C.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 5) :
    Nonempty (Case3SecondaryIncidence C source middle) := by
  obtain ⟨secondary, hsourceSecondary, hmiddleSecondary, hhigh⟩ :=
    Erdos957Case3Secondary.exists_case3_secondary_incidence_aligned
      hA C source middle hstrict hsourceDegree hsourceMiddle
      hmiddleCone hmiddleDegree
  exact ⟨{
    secondary := secondary
    source_adj := hsourceSecondary
    middle_adj := hmiddleSecondary
    higher := hhigh }⟩

/-- Fully realized arbitrary-middle Case 3.  The low row is middle-only; in the degree-five
branch the secondary is constructed from strict support and the actual neighbor sets.  Both
branches erase definitionally to the retained row's `localCase`. -/
theorem exists_realized_case3
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (F.chart.coord source q).2 < 0)
    (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (F.chart.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle ≤ 5)
    (honeHull : (hullUnitNeighbors P middle).card = 1) :
    ∃ (R : RealizedSourceRow P F.chart source)
      (row : Case3ActualRow P F.chart source (F.chart.coord source middle)),
      R = .case3 middle hmiddleDegree honeHull
        (F.chart.coord source middle) row
          (case3ActualRow_middleTarget_vertex F.chart source middle row) ∧
      R.localCase = row.localCase := by
  apply exists_realized_case3_of_degreeFiveSecondary hA F W source hs
    hwindow middle hsourceMiddle hmiddleCone hmiddleDegree honeHull
  intro hfive
  exact case3SecondaryIncidence_of_degree_five hA F.chart source middle
    hstrict (source_facts hs).2.2 hsourceMiddle hmiddleCone hfive

end Erdos957Case13RealizedRows
