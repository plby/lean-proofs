import Mathlib
import ErdosProblems.Erdos957.CaseClassification

/-!
# Honest Case 1/3 collision facts for Erdős 957

This file records the collision information that follows already from the
formula-retaining Case 1 and Case 3 rows.

There is one small but important asymmetry in the current row interfaces.
`Case3ActualRow` retains the source-unit equation for its whole target in the
low branch and for both displayed targets in the high branch.
`Case1ActualRow` retains the two coordinate formulas, but not the hypothesis
that its parameter `middle` is a unit from the source.  The wrapper
`Case1UnitRow` below adds precisely that geometric equation.  It does not
assume a collision exclusion or a capacity bound.

The main finite conclusion says that, when a flat degree-three diameter
source sends a Case 1/3 token to `v`, its predecessor and successor cannot
both send a Case 1/3 token to the same `v`.  This is the genuine local
left/right exclusion furnished by the flat-angle argument: otherwise `v`
would be unit-adjacent to the source and to both cyclic neighbours.
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Erdos957Case13SideUniqueness

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CaseClassification.PairCases
open Erdos957Cases13

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {C : P.AlignedChartData}

/-! ## Unit-incidence consequences of retained coordinate formulas -/

/-- An exact source-chart unit equation is an actual unit-graph edge. -/
lemma adj_source_of_coord_unit (source : {p // p ∈ P.H})
    (v : Vertex A)
    (hunit : sqDist origin (C.coord source v) = 1) :
    (unitDistanceGraph A).Adj source.1 v := by
  change dist (source.1 : Point) (v : Point) = 1
  have hsq : dist (source.1 : Point) (v : Point) ^ 2 = 1 := by
    rw [← C.sqDist_coord source source.1 v, C.coord_source]
    exact hunit
  nlinarith [dist_nonneg (x := (source.1 : Point)) (y := (v : Point))]

/-- A Case 1 row together with the source--middle unit equation used to
construct its two canonical equilateral recipients. -/
structure Case1UnitRow (source : {p // p ∈ P.H}) (middle : ℝ × ℝ) where
  row : Case1ActualRow P C source middle
  middle_unit : sqDist origin middle = 1

namespace Case1UnitRow

variable {source : {p // p ∈ P.H}} {middle : ℝ × ℝ}

/-- The left Case 1 recipient is genuinely unit-adjacent to its source. -/
theorem left_adj_source (R : Case1UnitRow (P := P) (C := C) source middle) :
    (unitDistanceGraph A).Adj source.1 R.row.left.vertex := by
  apply adj_source_of_coord_unit (P := P) (C := C) source
  have hcoord : C.coord source R.row.left.vertex = case1Left middle := by
    simpa [sourceCoordinates] using R.row.left_coordinate
  rw [hcoord]
  exact (case1Left_common_unit R.middle_unit).1

/-- The right Case 1 recipient is genuinely unit-adjacent to its source. -/
theorem right_adj_source (R : Case1UnitRow (P := P) (C := C) source middle) :
    (unitDistanceGraph A).Adj source.1 R.row.right.vertex := by
  apply adj_source_of_coord_unit (P := P) (C := C) source
  have hcoord : C.coord source R.row.right.vertex = case1Right middle := by
    simpa [sourceCoordinates] using R.row.right_coordinate
  rw [hcoord]
  exact (case1Right_common_unit R.middle_unit).1

/-- Every positive token of the erased Case 1 row is on an actual unit edge
from the source. -/
theorem adj_source_of_tokens_pos
    (R : Case1UnitRow (P := P) (C := C) source middle)
    {v : Vertex A} (hv : 0 < R.row.localCase.tokens v) :
    (unitDistanceGraph A).Adj source.1 v := by
  by_cases hl : v = R.row.left.vertex
  · subst v
    exact R.left_adj_source
  · by_cases hr : v = R.row.right.vertex
    · subst v
      exact R.right_adj_source
    · simp [Case1ActualRow.localCase, LocalCase.tokens, hl, hr] at hv

end Case1UnitRow

/-- The checked Case 1 geometric constructor automatically supplies the
unit equation omitted by the bare `Case1ActualRow` record. -/
theorem Case1Geometry.toUnitActualRow
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) {middle : ℝ × ℝ}
    (G : Case1Geometry (alignedConfiguration C source)
      (alignedHull C source) middle) :
    Nonempty (Case1UnitRow (P := P) (C := C) source middle) := by
  obtain ⟨R⟩ := G.toActualRow P C source
  exact ⟨⟨R, G.middle_unit⟩⟩

namespace Case3ActualRow

variable {source : {p // p ∈ P.H}} {middle : ℝ × ℝ}

/-- The retained arbitrary-middle Case 3 formula proves that every positive
recipient is genuinely unit-adjacent to the source. -/
theorem adj_source_of_tokens_pos
    (R : Case3ActualRow P C source middle)
    {v : Vertex A} (hv : 0 < R.localCase.tokens v) :
    (unitDistanceGraph A).Adj source.1 v := by
  cases R with
  | low m hm hmu hfour =>
      by_cases hvm : v = m.vertex
      · subst v
        apply adj_source_of_coord_unit (P := P) (C := C) source
        rw [hm]
        exact hmu
      · simp [Case3ActualRow.localCase, LocalCase.tokens, hvm] at hv
  | high secondaryCoord m s hm hs hmu hsu hms hne =>
      by_cases hvm : v = m.vertex
      · subst v
        apply adj_source_of_coord_unit (P := P) (C := C) source
        rw [hm]
        exact hmu
      · by_cases hvs : v = s.vertex
        · subst v
          apply adj_source_of_coord_unit (P := P) (C := C) source
          rw [hs]
          exact hsu
        · simp [Case3ActualRow.localCase, LocalCase.tokens, hvm, hvs] at hv

end Case3ActualRow

/-! ## A common formula-retaining Case 1/3 row -/

/-- The two actual row kinds whose positive targets have retained source-unit
formulas.  This is a finite constructor sum, not a charging assumption. -/
inductive ActualRow (source : {p // p ∈ P.H}) where
  | case1 (middle : ℝ × ℝ)
      (row : Case1UnitRow (P := P) (C := C) source middle)
  | case3 (middle : ℝ × ℝ)
      (row : Case3ActualRow P C source middle)

namespace ActualRow

variable {source : {p // p ∈ P.H}}

/-- Erase the retained formulas to the local transfer row. -/
def localCase : ActualRow (P := P) (C := C) source → LocalCase P C source
  | .case1 _ R => R.row.localCase
  | .case3 _ R => R.localCase

/-- Doubled tokens sent by a formula-retaining Case 1/3 row. -/
def tokens (R : ActualRow (P := P) (C := C) source) (v : Vertex A) : ℕ :=
  R.localCase.tokens v

/-- Every positive target of a formula-retaining Case 1/3 row is an actual
unit neighbour of the source. -/
theorem adj_source_of_tokens_pos
    (R : ActualRow (P := P) (C := C) source)
    {v : Vertex A} (hv : 0 < R.tokens v) :
    (unitDistanceGraph A).Adj source.1 v := by
  cases R with
  | case1 middle R =>
      exact R.adj_source_of_tokens_pos hv
  | case3 middle R =>
      exact Case3ActualRow.adj_source_of_tokens_pos R hv

end ActualRow

/-! ## The checked finite predecessor/source/successor exclusion -/

/-- Three consecutive Case 1/3 source rows cannot all hit the same target
when the middle hull vertex is an actual flat degree-three diameter source.

The proof has no coordinate or cyclic-transition premise beyond those already
retained by the rows and by `sourceVertices`: positive formula roles give the
three unit incidences, and the existing flat-source angle theorem rules out
simultaneous predecessor and successor incidences. -/
theorem no_three_consecutive_case13_arrivals
    (hA : IsOneSeparated A) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H})
    (hsource : source.1 ∈ sourceVertices P W)
    (Rprev : ActualRow (P := P) (C := C) (P.next⁻¹ source))
    (Rself : ActualRow (P := P) (C := C) source)
    (Rnext : ActualRow (P := P) (C := C) (P.next source))
    (v : Vertex A)
    (hprev : 0 < Rprev.tokens v)
    (hself : 0 < Rself.tokens v)
    (hnext : 0 < Rnext.tokens v) : False := by
  have hsv := Rself.adj_source_of_tokens_pos hself
  have hpv := Rprev.adj_source_of_tokens_pos hprev
  have hnv := Rnext.adj_source_of_tokens_pos hnext
  exact not_both_cyclic_neighbors_adjacent_to_middle
    hA P W source hsource v hsv
      ((unitDistanceGraph A).adj_symm hpv)
      ((unitDistanceGraph A).adj_symm hnv)

/-- If the center row hits `v`, at least one of the two adjacent cyclic rows
does not.  This is the direct two-side form of the preceding theorem. -/
theorem predecessor_or_successor_misses
    (hA : IsOneSeparated A) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H})
    (hsource : source.1 ∈ sourceVertices P W)
    (Rprev : ActualRow (P := P) (C := C) (P.next⁻¹ source))
    (Rself : ActualRow (P := P) (C := C) source)
    (Rnext : ActualRow (P := P) (C := C) (P.next source))
    (v : Vertex A) (hself : 0 < Rself.tokens v) :
    Rprev.tokens v = 0 ∨ Rnext.tokens v = 0 := by
  by_contra h
  push Not at h
  have hprev : 0 < Rprev.tokens v := Nat.pos_of_ne_zero h.1
  have hnext : 0 < Rnext.tokens v := Nat.pos_of_ne_zero h.2
  exact no_three_consecutive_case13_arrivals hA W source hsource
    Rprev Rself Rnext v hprev hself hnext

/-- The three actual cyclic positions centered at a source. -/
def adjacentTriple (source : {p // p ∈ P.H}) : Finset {p // p ∈ P.H} :=
  {P.next⁻¹ source, source, P.next source}

/-- Formula-retaining Case 1/3 contributors among the predecessor, source,
and successor. -/
def adjacentContributors
    (rows : ∀ i : {p // p ∈ P.H}, ActualRow (P := P) (C := C) i)
    (source : {p // p ∈ P.H}) (v : Vertex A) : Finset {p // p ∈ P.H} :=
  (adjacentTriple (P := P) source).filter fun i ↦ 0 < (rows i).tokens v

/-- Actual finite form of the local two-side exclusion: among the three
consecutive positions centered at an emitting flat source, at most two
Case 1/3 rows can hit a fixed target. -/
theorem card_adjacentContributors_le_two
    (hA : IsOneSeparated A) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H})
    (hsource : source.1 ∈ sourceVertices P W)
    (rows : ∀ i : {p // p ∈ P.H}, ActualRow (P := P) (C := C) i)
    (v : Vertex A) :
    (adjacentContributors (P := P) (C := C) rows source v).card ≤ 2 := by
  classical
  by_cases hp : 0 < (rows (P.next⁻¹ source)).tokens v
  · by_cases hs : 0 < (rows source).tokens v
    · by_cases hn : 0 < (rows (P.next source)).tokens v
      · exact (no_three_consecutive_case13_arrivals hA W source hsource
          (rows (P.next⁻¹ source)) (rows source) (rows (P.next source))
          v hp hs hn).elim
      · refine (Finset.card_le_card (s := adjacentContributors
            (P := P) (C := C) rows source v)
            (t := {P.next⁻¹ source, source}) ?_).trans Finset.card_le_two
        intro i hi
        have hi' := (Finset.mem_filter.mp hi)
        simp only [adjacentTriple, Finset.mem_insert, Finset.mem_singleton] at hi'
        rcases hi'.1 with hip | his | hin
        · simp [hip]
        · simp [his]
        · subst i
          exact (hn hi'.2).elim
    · refine (Finset.card_le_card (s := adjacentContributors
          (P := P) (C := C) rows source v)
          (t := {P.next⁻¹ source, P.next source}) ?_).trans Finset.card_le_two
      intro i hi
      have hi' := (Finset.mem_filter.mp hi)
      simp only [adjacentTriple, Finset.mem_insert, Finset.mem_singleton] at hi'
      rcases hi'.1 with hip | his | hin
      · simp [hip]
      · subst i
        exact (hs hi'.2).elim
      · simp [hin]
  · refine (Finset.card_le_card (s := adjacentContributors
        (P := P) (C := C) rows source v)
        (t := {source, P.next source}) ?_).trans Finset.card_le_two
    intro i hi
    have hi' := (Finset.mem_filter.mp hi)
    simp only [adjacentTriple, Finset.mem_insert, Finset.mem_singleton] at hi'
    rcases hi'.1 with hip | his | hin
    · subst i
      exact (hp hi'.2).elim
    · simp [his]
    · simp [hin]

/-! ## The Case 3 primary--primary exclusion -/

/-- The actual primary (middle) vertex named by a Case 3 row. -/
def case3PrimaryVertex {source : {p // p ∈ P.H}}
    {middle : ℝ × ℝ}
    (R : Case3ActualRow P C source middle) : Vertex A :=
  match R with
  | .low m _ _ _ => m.vertex
  | .high _ m _ _ _ _ _ _ _ => m.vertex

/-- The Case 3 primary is genuinely unit-adjacent to its source. -/
theorem case3_primary_adj_source
    {source : {p // p ∈ P.H}} {middle : ℝ × ℝ}
    (R : Case3ActualRow P C source middle) :
    (unitDistanceGraph A).Adj source.1 (case3PrimaryVertex R) := by
  cases R with
  | low m hm hmu hfour =>
      change (unitDistanceGraph A).Adj source.1 m.vertex
      apply adj_source_of_coord_unit (P := P) (C := C) source
      rw [hm]
      exact hmu
  | high secondaryCoord m s hm hs hmu hsu hms hne =>
      change (unitDistanceGraph A).Adj source.1 m.vertex
      apply adj_source_of_coord_unit (P := P) (C := C) source
      rw [hm]
      exact hmu

/-- The primary's source belongs to its genuine extreme-neighbor finset. -/
theorem source_mem_case3Primary_hullUnitNeighbors
    {source : {p // p ∈ P.H}} {middle : ℝ × ℝ}
    (R : Case3ActualRow P C source middle) :
    source.1 ∈ hullUnitNeighbors P (case3PrimaryVertex R) := by
  exact mem_hullUnitNeighbors.mpr
    ⟨source.property, (unitDistanceGraph A).adj_symm
      (case3_primary_adj_source R)⟩

/-- A Case 3 row equipped with the exact one-extreme-neighbor fact from the
Case 3 branch of the four-way classification.  This is a graph cardinality
statement about the primary target, not a collision or capacity premise. -/
structure ClassifiedCase3Row (source : {p // p ∈ P.H})
    (middle : ℝ × ℝ) where
  row : Case3ActualRow P C source middle
  primary_one_extreme :
    (hullUnitNeighbors P (case3PrimaryVertex row)).card = 1

/-- The checked arbitrary-middle Case 3 constructor supplies the exact
one-extreme-neighbor classification for its primary target. -/
theorem Case3Geometry.toClassifiedActualRow
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) {middle secondary : ℝ × ℝ}
    (G : Case3Geometry (alignedConfiguration C source)
      (alignedHull C source) middle secondary) :
    Nonempty (ClassifiedCase3Row (P := P) (C := C)
      source middle) := by
  obtain ⟨R⟩ := G.toActualRow P C source
  have hprimaryCoord : C.coord source (case3PrimaryVertex R) = middle := by
    cases R with
    | low m hm hmu hfour => exact hm
    | high secondaryCoord m s hm hs hmu hsu hms hne => exact hm
  have heq : hullUnitNeighbors P (case3PrimaryVertex R) = {source.1} := by
    apply Finset.Subset.antisymm
    · intro w hw
      have hw' := mem_hullUnitNeighbors.mp hw
      have hwHull : C.coord source w ∈ alignedHull C source :=
        coord_mem_alignedHull C source hw'.1
      have hunit : sqDist middle (C.coord source w) = 1 := by
        have hsq := C.sqDist_coord source (case3PrimaryVertex R) w
        rw [hw'.2] at hsq
        norm_num at hsq
        rw [← hprimaryCoord]
        exact hsq
      have hcoord : C.coord source w = origin :=
        G.unique_hull_neighbor _ hwHull hunit
      have hsourceCoord : C.coord source source.1 = origin := by
        simpa [origin] using C.coord_source source
      have hwSource : w = source.1 :=
        C.coord_injective P source (hcoord.trans hsourceCoord.symm)
      simp [hwSource]
    · intro w hw
      have hwSource : w = source.1 := by simpa using hw
      subst w
      exact source_mem_case3Primary_hullUnitNeighbors R
  refine ⟨⟨R, ?_⟩⟩
  rw [heq]
  simp

/-- Two Case 3 primary roles which name the same actual target necessarily
come from the same hull source.  This is the `(3,3)` primary--primary
exclusion in its genuine finite form. -/
theorem case3_primary_source_unique
    {s t : {p // p ∈ P.H}}
    {ms mt : ℝ × ℝ}
    (Rs : ClassifiedCase3Row (P := P) (C := C) s ms)
    (Rt : ClassifiedCase3Row (P := P) (C := C) t mt)
    (hprimary : case3PrimaryVertex Rs.row = case3PrimaryVertex Rt.row) : s = t := by
  have hs : s.1 ∈ hullUnitNeighbors P (case3PrimaryVertex Rs.row) :=
    source_mem_case3Primary_hullUnitNeighbors Rs.row
  have ht : t.1 ∈ hullUnitNeighbors P (case3PrimaryVertex Rs.row) := by
    rw [hprimary]
    exact source_mem_case3Primary_hullUnitNeighbors Rt.row
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp Rs.primary_one_extreme
  rw [hw] at hs ht
  have hsw : s.1 = w := Finset.mem_singleton.mp hs
  have htw : t.1 = w := Finset.mem_singleton.mp ht
  have hst : s.1 = t.1 := hsw.trans htw.symm
  exact Subtype.ext hst

/-! ## Explicitly retained within-row role exclusions -/

/-- The two canonical Case 1 roles in one actual row cannot collide. -/
theorem case1_left_ne_right
    {source : {p // p ∈ P.H}} {middle : ℝ × ℝ}
    (R : Case1UnitRow (P := P) (C := C) source middle) :
    R.row.left.vertex ≠ R.row.right.vertex :=
  R.row.distinct

/-- In the high Case 3 branch the middle and secondary roles cannot collide;
the low branch has only the middle role. -/
theorem case3_middle_ne_secondary
    {source : {p // p ∈ P.H}} {middle : ℝ × ℝ}
    (R : Case3ActualRow P C source middle) :
    (match R with
      | .low _ _ _ _ => True
      | .high _ m s _ _ _ _ _ _hne => m.vertex ≠ s.vertex) := by
  cases R with
  | low m hm hmu hfour => trivial
  | high secondaryCoord m s hm hs hmu hsu hms hne => exact hne

end Erdos957Case13SideUniqueness

#print axioms Erdos957Case13SideUniqueness.no_three_consecutive_case13_arrivals
#print axioms Erdos957Case13SideUniqueness.predecessor_or_successor_misses
#print axioms Erdos957Case13SideUniqueness.card_adjacentContributors_le_two
#print axioms Erdos957Case13SideUniqueness.case3_primary_source_unique
