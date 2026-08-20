import Mathlib
import ErdosProblems.Erdos957.GeometryCore

/-!
# Per-source local rows for the geometric charging argument in Erdős 957

This file separates the row-conservation part of Dumitrescu's transfer from
the genuinely global no-overcharge theorem.  A `LocalTarget` is an actual
vertex of the original configuration, is outside the cyclic hull, lies in the
checked transfer rectangle in the source's genuine Euclidean frame, and is at
unit-graph distance at most two from the source.  A `LocalCase` is one of the
seven per-source roles obtained from the four cases in the paper.

The doubled-token row is *computed* from the constructor: it is either one
whole transfer of weight two or two distinct half transfers of weight one.
Consequently its row sum is proved rather than stored as witness data.  There
is deliberately no field about incoming tokens, competing sources, target
capacity, or final charge.

The Case 1/3 coordinate factories below use the same bisector chart and hence
can discharge their rectangle obligations directly from the checked formulas.
For Cases 2/4 the canonical formulas live in an edge chart; callers instead
use `LocalTarget.ofPath` after transporting only the sharp horizontal bound
into this aligned chart.  No equality between the two charts is assumed.
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Erdos957GeometryLocalRows

open Erdos957GeometryCore
open Erdos957Overcharge

abbrev PairPoint := Erdos957Cases13.Point
abbrev Case24Point := Erdos957Cases24.Point

/-- Pair coordinates of a point in the `Fin 2` model used by Cases 2 and 4. -/
def case24Pair (p : Case24Point) : PairPoint := (p 0, p 1)

/--
Coordinates in the same source-dependent aligned chart that is consumed by
the locality and collision arguments.  In particular this definition does
not silently switch back to `CyclicHullData.localCoord`.
-/
def sourceCoordinates {A : Finset Point} (P : CyclicHullData A)
    (C : P.AlignedChartData) (i : {p // p ∈ P.H}) (v : Vertex A) : PairPoint :=
  C.coord i v

/-- The common transfer rectangle, expressed in the Case 1/3 pair model. -/
def InLocalRectangle {A : Finset Point} (P : CyclicHullData A)
    (C : P.AlignedChartData) (i : {p // p ∈ P.H}) (v : Vertex A) : Prop :=
  Erdos957Cases13.InSourceRectangle (sourceCoordinates P C i v)

/-- The two coordinate files use exactly the same transfer rectangle. -/
lemma case24_rectangle_iff_pair_rectangle (p : Case24Point) :
    Erdos957Cases24.InTransferRectangle p ↔
      Erdos957Cases13.InSourceRectangle (case24Pair p) := by
  simp only [Erdos957Cases24.InTransferRectangle,
    Erdos957Cases13.InSourceRectangle, case24Pair]
  constructor <;> intro h <;> simpa only [neg_div] using h

/-- Every actual configuration point is on or below the normalized support line. -/
lemma sourceCoordinates_second_nonpos {A : Finset Point}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (i : {p // p ∈ P.H}) (v : Vertex A) :
    (sourceCoordinates P C i v).2 ≤ 0 :=
  C.coord_snd_nonpos i v

/-- Graph distance at most two in the actual normalized unit-distance graph. -/
def WithinTwoUnitEdges {A : Finset Point} (source target : Vertex A) : Prop :=
  (unitDistanceGraph A).Adj source target ∨
    ∃ middle, (unitDistanceGraph A).Adj source middle ∧
      (unitDistanceGraph A).Adj middle target

/-- Two actual unit edges give Euclidean distance at most two. -/
lemma dist_le_two_of_withinTwoUnitEdges {A : Finset Point}
    {source target : Vertex A} (h : WithinTwoUnitEdges source target) :
    dist (source : Point) (target : Point) ≤ 2 := by
  rcases h with hst | ⟨middle, hsm, hmt⟩
  · have hst' : dist (source : Point) (target : Point) ≤ 1 := by
      simpa [unitDistanceGraph] using hst.le
    exact hst'.trans (by norm_num)
  · calc
      dist (source : Point) (target : Point) ≤
          dist (source : Point) (middle : Point) +
            dist (middle : Point) (target : Point) := dist_triangle _ _ _
      _ = 2 := by
        rw [show dist (source : Point) (middle : Point) = 1 by
              simpa [unitDistanceGraph] using hsm,
            show dist (middle : Point) (target : Point) = 1 by
              simpa [unitDistanceGraph] using hmt]
        norm_num

/-- A genuine target selected by one local case at one actual hull source. -/
structure LocalTarget {A : Finset Point} (P : CyclicHullData A)
    (C : P.AlignedChartData) (i : {p // p ∈ P.H}) where
  vertex : Vertex A
  not_hull : vertex ∉ P.H
  degree_le_five : (unitDistanceGraph A).degree vertex ≤ 5
  in_rectangle : InLocalRectangle P C i vertex
  within_two : WithinTwoUnitEdges i.1 vertex

namespace LocalTarget

variable {A : Finset Point} {P : CyclicHullData A} {C : P.AlignedChartData}
variable {i : {p // p ∈ P.H}} {v : Vertex A}

/--
Construct a target from chart-independent incidence data and the exact
horizontal estimate needed by the paper's recipient rectangle.  The two
vertical estimates are consequences of the two-edge path, isometry of the
selected aligned chart, and its weak support half-plane.  A two-edge path
alone gives only `|x| ≤ 2`, so the sharper `7/4` horizontal bound is kept as
an explicit geometric input.
-/
def ofPath
    (hdegree : (unitDistanceGraph A).degree v ≤ 5)
    (hnotHull : v ∉ P.H) (hpath : WithinTwoUnitEdges i.1 v)
    (hleft : -(7 / 4 : ℝ) ≤ (sourceCoordinates P C i v).1)
    (hright : (sourceCoordinates P C i v).1 ≤ 7 / 4) :
    LocalTarget P C i where
  vertex := v
  not_hull := hnotHull
  degree_le_five := hdegree
  in_rectangle := by
    refine ⟨?_, hright, ?_, sourceCoordinates_second_nonpos P C i v⟩
    · norm_num at hleft ⊢
      exact hleft
    · have hdist := dist_le_two_of_withinTwoUnitEdges hpath
      have hdistNonneg : 0 ≤ dist (i.1 : Point) (v : Point) := dist_nonneg
      have hsq : Erdos957Cases13.sqDist
          (sourceCoordinates P C i i.1) (sourceCoordinates P C i v) =
            dist (i.1 : Point) (v : Point) ^ 2 := C.sqDist_coord i i.1 v
      rw [show sourceCoordinates P C i i.1 = Erdos957Cases13.origin by
        simpa [sourceCoordinates, Erdos957Cases13.origin] using C.coord_source i] at hsq
      simp only [Erdos957Cases13.sqDist_origin] at hsq
      nlinarith [sq_nonneg (sourceCoordinates P C i v).1]
  within_two := hpath

/-- Absolute-value form of `ofPath`, matching the chart-transport theorem. -/
def ofPathOfAbs
    (hdegree : (unitDistanceGraph A).degree v ≤ 5)
    (hnotHull : v ∉ P.H) (hpath : WithinTwoUnitEdges i.1 v)
    (hhorizontal : |(sourceCoordinates P C i v).1| ≤ 7 / 4) :
    LocalTarget P C i := by
  rw [abs_le] at hhorizontal
  exact ofPath hdegree hnotHull hpath hhorizontal.1 hhorizontal.2

/-- Case 1 left target: the checked common-neighbour calculation supplies its rectangle. -/
def ofCase1Left {middle : PairPoint}
    (hmiddleUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin middle = 1)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone middle)
    (hcoord : sourceCoordinates P C i v = Erdos957Cases13.case1Left middle)
    (hdegree : (unitDistanceGraph A).degree v ≤ 5)
    (hnotHull : v ∉ P.H) :
    LocalTarget P C i where
  vertex := v
  not_hull := hnotHull
  degree_le_five := hdegree
  in_rectangle := by
    rw [InLocalRectangle, hcoord]
    exact (Erdos957Cases13.case1_recipients_in_sourceRectangle
      hmiddleUnit hmiddleCone).1
  within_two := by
    apply Or.inl
    have hsquare : dist (i.1 : Point) (v : Point) ^ 2 = 1 := by
      rw [← C.sqDist_coord i i.1 v, C.coord_source]
      change Erdos957Cases13.sqDist Erdos957Cases13.origin
        (sourceCoordinates P C i v) = 1
      rw [hcoord]
      exact (Erdos957Cases13.case1Left_common_unit hmiddleUnit).1
    rcases sq_eq_one_iff.mp hsquare with h | h
    · exact h
    · exfalso
      have hnonneg : 0 ≤ dist (i.1 : Point) (v : Point) := dist_nonneg
      linarith

/-- Case 1 right target. -/
def ofCase1Right {middle : PairPoint}
    (hmiddleUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin middle = 1)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone middle)
    (hcoord : sourceCoordinates P C i v = Erdos957Cases13.case1Right middle)
    (hdegree : (unitDistanceGraph A).degree v ≤ 5)
    (hnotHull : v ∉ P.H) :
    LocalTarget P C i where
  vertex := v
  not_hull := hnotHull
  degree_le_five := hdegree
  in_rectangle := by
    rw [InLocalRectangle, hcoord]
    exact (Erdos957Cases13.case1_recipients_in_sourceRectangle
      hmiddleUnit hmiddleCone).2
  within_two := by
    apply Or.inl
    have hsquare : dist (i.1 : Point) (v : Point) ^ 2 = 1 := by
      rw [← C.sqDist_coord i i.1 v, C.coord_source]
      change Erdos957Cases13.sqDist Erdos957Cases13.origin
        (sourceCoordinates P C i v) = 1
      rw [hcoord]
      exact (Erdos957Cases13.case1Right_common_unit hmiddleUnit).1
    rcases sq_eq_one_iff.mp hsquare with h | h
    · exact h
    · exfalso
      have hnonneg : 0 ≤ dist (i.1 : Point) (v : Point) := dist_nonneg
      linarith

/-- The low/primary Case 3 target at canonical coordinate `(0,-1)`. -/
def ofCase3Middle
    (hcoord : sourceCoordinates P C i v = Erdos957Cases13.verticalDown)
    (hdegree : (unitDistanceGraph A).degree v ≤ 5)
    (hnotHull : v ∉ P.H) :
    LocalTarget P C i where
  vertex := v
  not_hull := hnotHull
  degree_le_five := hdegree
  in_rectangle := by
    rw [InLocalRectangle, hcoord]
    exact Erdos957Cases13.unit_point_in_sourceRectangle
      (by norm_num [Erdos957Cases13.sqDist, Erdos957Cases13.origin,
        Erdos957Cases13.verticalDown])
      (by norm_num [Erdos957Cases13.verticalDown])
  within_two := by
    apply Or.inl
    have hsquare : dist (i.1 : Point) (v : Point) ^ 2 = 1 := by
      rw [← C.sqDist_coord i i.1 v, C.coord_source]
      change Erdos957Cases13.sqDist Erdos957Cases13.origin
        (sourceCoordinates P C i v) = 1
      rw [hcoord]
      norm_num [Erdos957Cases13.sqDist, Erdos957Cases13.origin,
        Erdos957Cases13.verticalDown]
    rcases sq_eq_one_iff.mp hsquare with h | h
    · exact h
    · exfalso
      have hnonneg : 0 ≤ dist (i.1 : Point) (v : Point) := dist_nonneg
      linarith

/-- A secondary Case 3 common neighbour. -/
def ofCase3Secondary {q : PairPoint}
    (hqSource : Erdos957Cases13.sqDist Erdos957Cases13.origin q = 1)
    (hqMiddle : Erdos957Cases13.sqDist Erdos957Cases13.verticalDown q = 1)
    (hqBelow : q.2 ≤ 0)
    (hcoord : sourceCoordinates P C i v = q)
    (hdegree : (unitDistanceGraph A).degree v ≤ 5)
    (hnotHull : v ∉ P.H) :
    LocalTarget P C i where
  vertex := v
  not_hull := hnotHull
  degree_le_five := hdegree
  in_rectangle := by
    rw [InLocalRectangle, hcoord]
    exact (Erdos957Cases13.case3_recipient_common_unit_and_in_rectangle
      rfl hqSource hqMiddle hqBelow).2.2
  within_two := by
    apply Or.inl
    have hsquare : dist (i.1 : Point) (v : Point) ^ 2 = 1 := by
      rw [← C.sqDist_coord i i.1 v, C.coord_source]
      change Erdos957Cases13.sqDist Erdos957Cases13.origin
        (sourceCoordinates P C i v) = 1
      simpa [hcoord] using hqSource
    rcases sq_eq_one_iff.mp hsquare with h | h
    · exact h
    · exfalso
      have hnonneg : 0 ≤ dist (i.1 : Point) (v : Point) := dist_nonneg
      linarith

end LocalTarget

/-!
## The seven per-source roles

Case 4 is a two-source construction in the paper.  It is split here into the
row belonging to the primary source and the row belonging to the secondary
source.  This is the necessary per-source refinement of the coordinate
file's combined four-token Case 4 transfer.
-/

/-- An actual local case, with no incoming-charge or capacity assumptions. -/
inductive LocalCase {A : Finset Point} (P : CyclicHullData A)
    (chart : P.AlignedChartData) (i : {p // p ∈ P.H}) where
  | case1 (left right : LocalTarget P chart i)
      (distinct : left.vertex ≠ right.vertex)
  | case2 (outer secondary : LocalTarget P chart i)
      (distinct : outer.vertex ≠ secondary.vertex)
  | case3Low (middle : LocalTarget P chart i)
      (degree_le_four : (unitDistanceGraph A).degree middle.vertex ≤ 4)
  | case3High (middle secondary : LocalTarget P chart i)
      (distinct : middle.vertex ≠ secondary.vertex)
  | case4Primary (middle : LocalTarget P chart i)
      (degree_le_four : (unitDistanceGraph A).degree middle.vertex ≤ 4)
  | case4SecondaryLow (low : LocalTarget P chart i)
      (degree_le_four : (unitDistanceGraph A).degree low.vertex ≤ 4)
  | case4SecondarySplit (left right : LocalTarget P chart i)
      (distinct : left.vertex ≠ right.vertex)

namespace LocalCase

variable {A : Finset Point} {P : CyclicHullData A}
variable {chart : P.AlignedChartData}
variable {i : {p // p ∈ P.H}}

/-- The paper case represented by a per-source row role. -/
def caseTag : LocalCase P chart i → CaseNumber
  | .case1 .. => .one
  | .case2 .. => .two
  | .case3Low .. | .case3High .. => .three
  | .case4Primary .. | .case4SecondaryLow .. | .case4SecondarySplit .. => .four

/-- The actual doubled-token row computed from a local-case constructor. -/
def tokens (C : LocalCase P chart i) (v : Vertex A) : ℕ :=
  match C with
  | .case1 left right _ | .case2 left right _ |
      .case3High left right _ | .case4SecondarySplit left right _ =>
      (if v = left.vertex then 1 else 0) +
        (if v = right.vertex then 1 else 0)
  | .case3Low target _ | .case4Primary target _ | .case4SecondaryLow target _ =>
      if v = target.vertex then 2 else 0

private lemma eq_or_eq_of_split_pos {v x y : Vertex A}
    (hpos : 0 < (if v = x then 1 else 0) + (if v = y then 1 else 0)) :
    v = x ∨ v = y := by
  by_cases hx : v = x
  · exact Or.inl hx
  · by_cases hy : v = y
    · exact Or.inr hy
    · simp [hx, hy] at hpos

private lemma eq_of_whole_pos {v x : Vertex A}
    (hpos : 0 < if v = x then 2 else 0) : v = x := by
  by_contra hx
  simp [hx] at hpos

private lemma split_weight_eq_one {v x y : Vertex A} (hne : x ≠ y)
    (hpos : 0 < (if v = x then 1 else 0) + (if v = y then 1 else 0)) :
    (if v = x then 1 else 0) + (if v = y then 1 else 0) = 1 := by
  rcases eq_or_eq_of_split_pos hpos with hx | hy
  · subst v
    simp [hne]
  · subst v
    simp [hne.symm]

/-- Every local case emits exactly two doubled tokens. -/
theorem sum_tokens (C : LocalCase P chart i) :
    ∑ v, C.tokens v = 2 := by
  cases C with
  | case1 left right hne =>
      simp only [tokens, Finset.sum_add_distrib]
      simp
  | case2 outer secondary hne =>
      simp only [tokens, Finset.sum_add_distrib]
      simp
  | case3Low middle hfour =>
      simp [tokens]
  | case3High middle secondary hne =>
      simp only [tokens, Finset.sum_add_distrib]
      simp
  | case4Primary middle hfour =>
      simp [tokens]
  | case4SecondaryLow low hfour =>
      simp [tokens]
  | case4SecondarySplit left right hne =>
      simp only [tokens, Finset.sum_add_distrib]
      simp

/-- Every positive local arrival is exactly a half-token or a whole token. -/
theorem positive_weight (C : LocalCase P chart i) {v : Vertex A}
    (hpos : 0 < C.tokens v) : C.tokens v = 1 ∨ C.tokens v = 2 := by
  cases C with
  | case1 left right hne =>
      left
      exact split_weight_eq_one hne (by simpa only [tokens] using hpos)
  | case2 outer secondary hne =>
      left
      exact split_weight_eq_one hne (by simpa only [tokens] using hpos)
  | case3Low middle hfour =>
      right
      have hm := eq_of_whole_pos (by simpa only [tokens] using hpos)
      simp [tokens, hm]
  | case3High middle secondary hne =>
      left
      exact split_weight_eq_one hne (by simpa only [tokens] using hpos)
  | case4Primary middle hfour =>
      right
      have hm := eq_of_whole_pos (by simpa only [tokens] using hpos)
      simp [tokens, hm]
  | case4SecondaryLow low hfour =>
      right
      have hl := eq_of_whole_pos (by simpa only [tokens] using hpos)
      simp [tokens, hl]
  | case4SecondarySplit left right hne =>
      left
      exact split_weight_eq_one hne (by simpa only [tokens] using hpos)

/-- Case 1 has only half-token arrivals. -/
theorem case_one_weight (C : LocalCase P chart i) {v : Vertex A}
    (htag : C.caseTag = .one) (hpos : 0 < C.tokens v) : C.tokens v = 1 := by
  cases C with
  | case1 left right hne =>
      exact split_weight_eq_one hne (by simpa only [tokens] using hpos)
  | case2 outer secondary hne => simp [caseTag] at htag
  | case3Low middle hfour => simp [caseTag] at htag
  | case3High middle secondary hne => simp [caseTag] at htag
  | case4Primary middle hfour => simp [caseTag] at htag
  | case4SecondaryLow low hfour => simp [caseTag] at htag
  | case4SecondarySplit left right hne => simp [caseTag] at htag

/-- Case 2 has only half-token arrivals. -/
theorem case_two_weight (C : LocalCase P chart i) {v : Vertex A}
    (htag : C.caseTag = .two) (hpos : 0 < C.tokens v) : C.tokens v = 1 := by
  cases C with
  | case1 left right hne => simp [caseTag] at htag
  | case2 outer secondary hne =>
      exact split_weight_eq_one hne (by simpa only [tokens] using hpos)
  | case3Low middle hfour => simp [caseTag] at htag
  | case3High middle secondary hne => simp [caseTag] at htag
  | case4Primary middle hfour => simp [caseTag] at htag
  | case4SecondaryLow low hfour => simp [caseTag] at htag
  | case4SecondarySplit left right hne => simp [caseTag] at htag

/-- Positive row weight can only occur at one of the selected non-hull targets. -/
theorem target_not_hull (C : LocalCase P chart i) {v : Vertex A}
    (hpos : 0 < C.tokens v) : v ∉ P.H := by
  cases C with
  | case1 left right hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hl | hr
      · simpa [hl] using left.not_hull
      · simpa [hr] using right.not_hull
  | case2 outer secondary hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with ho | hs
      · simpa [ho] using outer.not_hull
      · simpa [hs] using secondary.not_hull
  | case3Low middle hfour =>
      simp only [tokens] at hpos
      have hm : v = middle.vertex := eq_of_whole_pos hpos
      simpa [hm] using middle.not_hull
  | case3High middle secondary hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hm | hs
      · simpa [hm] using middle.not_hull
      · simpa [hs] using secondary.not_hull
  | case4Primary middle hfour =>
      simp only [tokens] at hpos
      have hm : v = middle.vertex := eq_of_whole_pos hpos
      simpa [hm] using middle.not_hull
  | case4SecondaryLow low hfour =>
      simp only [tokens] at hpos
      have hl : v = low.vertex := eq_of_whole_pos hpos
      simpa [hl] using low.not_hull
  | case4SecondarySplit left right hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hl | hr
      · simpa [hl] using left.not_hull
      · simpa [hr] using right.not_hull

/-- Every actually selected recipient has genuine unit-graph degree at most five. -/
theorem positive_target_degree_le_five (C : LocalCase P chart i) {v : Vertex A}
    (hpos : 0 < C.tokens v) : (unitDistanceGraph A).degree v ≤ 5 := by
  cases C with
  | case1 left right hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hl | hr
      · subst v
        exact left.degree_le_five
      · subst v
        exact right.degree_le_five
  | case2 outer secondary hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with ho | hs
      · subst v
        exact outer.degree_le_five
      · subst v
        exact secondary.degree_le_five
  | case3Low middle hfour =>
      simp only [tokens] at hpos
      have hm : v = middle.vertex := eq_of_whole_pos hpos
      subst v
      exact middle.degree_le_five
  | case3High middle secondary hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hm | hs
      · subst v
        exact middle.degree_le_five
      · subst v
        exact secondary.degree_le_five
  | case4Primary middle hfour =>
      simp only [tokens] at hpos
      have hm : v = middle.vertex := eq_of_whole_pos hpos
      subst v
      exact middle.degree_le_five
  | case4SecondaryLow low hfour =>
      simp only [tokens] at hpos
      have hl : v = low.vertex := eq_of_whole_pos hpos
      subst v
      exact low.degree_le_five
  | case4SecondarySplit left right hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hl | hr
      · subst v
        exact left.degree_le_five
      · subst v
        exact right.degree_le_five

/-- A whole Case 3 arrival occurs only in the degree-at-most-four branch. -/
theorem case_three_whole_degree_le_four (C : LocalCase P chart i) {v : Vertex A}
    (htag : C.caseTag = .three) (hwhole : C.tokens v = 2) :
    (unitDistanceGraph A).degree v ≤ 4 := by
  cases C with
  | case1 left right hne => simp [caseTag] at htag
  | case2 outer secondary hne => simp [caseTag] at htag
  | case3Low middle hfour =>
      have hpos : 0 < (LocalCase.case3Low middle hfour).tokens v := by
        rw [hwhole]
        omega
      simp only [tokens] at hpos
      have hm : v = middle.vertex := eq_of_whole_pos hpos
      subst v
      exact hfour
  | case3High middle secondary hne =>
      have hpos : 0 < (LocalCase.case3High middle secondary hne).tokens v := by
        rw [hwhole]
        omega
      have hone : (LocalCase.case3High middle secondary hne).tokens v = 1 :=
        split_weight_eq_one hne (by simpa only [tokens] using hpos)
      omega
  | case4Primary middle hfour => simp [caseTag] at htag
  | case4SecondaryLow low hfour => simp [caseTag] at htag
  | case4SecondarySplit left right hne => simp [caseTag] at htag

/-- Every whole arrival belongs to an explicitly low-degree branch.

In particular, the five-valent Case 4 construction must use the split
constructor, so it cannot produce a two-token arrival. -/
theorem whole_target_degree_le_four (C : LocalCase P chart i) {v : Vertex A}
    (hwhole : C.tokens v = 2) :
    (unitDistanceGraph A).degree v ≤ 4 := by
  cases C with
  | case1 left right hne =>
      have hpos : 0 < (LocalCase.case1 left right hne).tokens v := by omega
      have hone : (LocalCase.case1 left right hne).tokens v = 1 :=
        split_weight_eq_one hne (by simpa only [tokens] using hpos)
      omega
  | case2 outer secondary hne =>
      have hpos : 0 < (LocalCase.case2 outer secondary hne).tokens v := by omega
      have hone : (LocalCase.case2 outer secondary hne).tokens v = 1 :=
        split_weight_eq_one hne (by simpa only [tokens] using hpos)
      omega
  | case3Low middle hfour =>
      have hpos : 0 < (LocalCase.case3Low middle hfour).tokens v := by omega
      simp only [tokens] at hpos
      have hm : v = middle.vertex := eq_of_whole_pos hpos
      subst v
      exact hfour
  | case3High middle secondary hne =>
      have hpos : 0 < (LocalCase.case3High middle secondary hne).tokens v := by omega
      have hone : (LocalCase.case3High middle secondary hne).tokens v = 1 :=
        split_weight_eq_one hne (by simpa only [tokens] using hpos)
      omega
  | case4Primary middle hfour =>
      have hpos : 0 < (LocalCase.case4Primary middle hfour).tokens v := by omega
      simp only [tokens] at hpos
      have hm : v = middle.vertex := eq_of_whole_pos hpos
      subst v
      exact hfour
  | case4SecondaryLow low hfour =>
      have hpos : 0 < (LocalCase.case4SecondaryLow low hfour).tokens v := by omega
      simp only [tokens] at hpos
      have hl : v = low.vertex := eq_of_whole_pos hpos
      subst v
      exact hfour
  | case4SecondarySplit left right hne =>
      have hpos : 0 <
          (LocalCase.case4SecondarySplit left right hne).tokens v := by omega
      have hone :
          (LocalCase.case4SecondarySplit left right hne).tokens v = 1 :=
        split_weight_eq_one hne (by simpa only [tokens] using hpos)
      omega

/-- Every positive target lies in the source rectangle. -/
theorem target_in_rectangle (C : LocalCase P chart i) {v : Vertex A}
    (hpos : 0 < C.tokens v) : InLocalRectangle P chart i v := by
  cases C with
  | case1 left right hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hl | hr
      · simpa [hl] using left.in_rectangle
      · simpa [hr] using right.in_rectangle
  | case2 outer secondary hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with ho | hs
      · simpa [ho] using outer.in_rectangle
      · simpa [hs] using secondary.in_rectangle
  | case3Low target hfour =>
      simp only [tokens] at hpos
      have ht : v = target.vertex := eq_of_whole_pos hpos
      simpa [ht] using target.in_rectangle
  | case3High middle secondary hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hm | hs
      · simpa [hm] using middle.in_rectangle
      · simpa [hs] using secondary.in_rectangle
  | case4Primary target hfour =>
      simp only [tokens] at hpos
      have ht : v = target.vertex := eq_of_whole_pos hpos
      simpa [ht] using target.in_rectangle
  | case4SecondaryLow target hfour =>
      simp only [tokens] at hpos
      have ht : v = target.vertex := eq_of_whole_pos hpos
      simpa [ht] using target.in_rectangle
  | case4SecondarySplit left right hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hl | hr
      · simpa [hl] using left.in_rectangle
      · simpa [hr] using right.in_rectangle

/-- Every positive target is within two actual unit edges of its source. -/
theorem target_within_two (C : LocalCase P chart i) {v : Vertex A}
    (hpos : 0 < C.tokens v) : WithinTwoUnitEdges i.1 v := by
  cases C with
  | case1 left right hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hl | hr
      · simpa [hl] using left.within_two
      · simpa [hr] using right.within_two
  | case2 outer secondary hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with ho | hs
      · simpa [ho] using outer.within_two
      · simpa [hs] using secondary.within_two
  | case3Low target hfour =>
      simp only [tokens] at hpos
      have ht : v = target.vertex := eq_of_whole_pos hpos
      simpa [ht] using target.within_two
  | case3High middle secondary hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hm | hs
      · simpa [hm] using middle.within_two
      · simpa [hs] using secondary.within_two
  | case4Primary target hfour =>
      simp only [tokens] at hpos
      have ht : v = target.vertex := eq_of_whole_pos hpos
      simpa [ht] using target.within_two
  | case4SecondaryLow target hfour =>
      simp only [tokens] at hpos
      have ht : v = target.vertex := eq_of_whole_pos hpos
      simpa [ht] using target.within_two
  | case4SecondarySplit left right hne =>
      simp only [tokens] at hpos
      rcases eq_or_eq_of_split_pos hpos with hl | hr
      · simpa [hl] using left.within_two
      · simpa [hr] using right.within_two

end LocalCase

/-! ## Combining independently supplied source rows -/

/-- The hull index canonically associated to an actual degree-three source. -/
def sourceIndex {A : Finset Point} (P : CyclicHullData A)
    (W : DiameterWitnessData P) (u : Vertex A)
    (hu : u ∈ sourceVertices P W) : {p // p ∈ P.H} :=
  ⟨u, sourceVertices_subset_hull P W hu⟩

/--
The selected per-source rows themselves.  Keeping the dependent function as
data, rather than merely asserting `Nonempty` for each source, preserves the
definitional identity of the realized geometric row for all downstream
formula and collision arguments.
-/
def HasLocalCases {A : Finset Point} (P : CyclicHullData A)
    (W : DiameterWitnessData P) (chart : P.AlignedChartData) : Type :=
  ∀ (u : Vertex A) (hu : u ∈ sourceVertices P W),
    LocalCase P chart (sourceIndex P W u hu)

/-- The actual paper-case tag attached to a source, with no default branch. -/
noncomputable def sourceCaseTag {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart)
    (u : {u // u ∈ sourceVertices P W}) :
    CaseNumber :=
  (hlocal u u.property).caseTag

/-- The chosen local row on the subtype of actual emitting sources. -/
noncomputable def sourceTransfer {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart)
    (u : {u // u ∈ sourceVertices P W})
    (v : Vertex A) : ℕ :=
  (hlocal u u.property).tokens v

theorem sourceTransfer_row_sum {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart)
    (u : {u // u ∈ sourceVertices P W}) :
    ∑ v, sourceTransfer P W chart hlocal u v = 2 :=
  LocalCase.sum_tokens (hlocal u u.property)

theorem sourceTransfer_positive_weight {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart)
    {u : {u // u ∈ sourceVertices P W}}
    {v : Vertex A} (hpos : 0 < sourceTransfer P W chart hlocal u v) :
    sourceTransfer P W chart hlocal u v = 1 ∨
      sourceTransfer P W chart hlocal u v = 2 :=
  LocalCase.positive_weight (hlocal u u.property) hpos

theorem sourceTransfer_case_one_weight {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart)
    {u : {u // u ∈ sourceVertices P W}}
    {v : Vertex A} (htag : sourceCaseTag P W chart hlocal u = .one)
    (hpos : 0 < sourceTransfer P W chart hlocal u v) :
    sourceTransfer P W chart hlocal u v = 1 :=
  LocalCase.case_one_weight (hlocal u u.property) htag hpos

theorem sourceTransfer_case_two_weight {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart)
    {u : {u // u ∈ sourceVertices P W}}
    {v : Vertex A} (htag : sourceCaseTag P W chart hlocal u = .two)
    (hpos : 0 < sourceTransfer P W chart hlocal u v) :
    sourceTransfer P W chart hlocal u v = 1 :=
  LocalCase.case_two_weight (hlocal u u.property) htag hpos

theorem sourceTransfer_positive_target_degree_le_five {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart)
    {u : {u // u ∈ sourceVertices P W}}
    {v : Vertex A} (hpos : 0 < sourceTransfer P W chart hlocal u v) :
    (unitDistanceGraph A).degree v ≤ 5 :=
  LocalCase.positive_target_degree_le_five
    (hlocal u u.property) hpos

theorem sourceTransfer_case_three_whole_degree_le_four {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart)
    {u : {u // u ∈ sourceVertices P W}}
    {v : Vertex A} (htag : sourceCaseTag P W chart hlocal u = .three)
    (hwhole : sourceTransfer P W chart hlocal u v = 2) :
    (unitDistanceGraph A).degree v ≤ 4 :=
  LocalCase.case_three_whole_degree_le_four
    (hlocal u u.property) htag hwhole

/-- Any whole selected source-row arrival, including a whole Case 4 arrival,
comes from a constructor carrying a genuine degree-at-most-four proof. -/
theorem sourceTransfer_whole_target_degree_le_four {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart)
    {u : {u // u ∈ sourceVertices P W}} {v : Vertex A}
    (hwhole : sourceTransfer P W chart hlocal u v = 2) :
    (unitDistanceGraph A).degree v ≤ 4 :=
  LocalCase.whole_target_degree_le_four
    (hlocal u u.property) hwhole

/-- Choice of the local row only when `u` is actually a source. -/
noncomputable def combinedTransfer {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart) :
    Vertex A → Vertex A → ℕ :=
  fun u v ↦ if hu : u ∈ sourceVertices P W then
    (hlocal u hu).tokens v
  else 0

/-- The combined transfer has the exact source/non-source row sums. -/
theorem combinedTransfer_row_sum {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart)
    (u : Vertex A) :
    ∑ v, combinedTransfer P W chart hlocal u v =
      if u ∈ sourceVertices P W then 2 else 0 := by
  classical
  by_cases hu : u ∈ sourceVertices P W
  · simp only [combinedTransfer, dif_pos hu, if_pos hu]
    exact LocalCase.sum_tokens (hlocal u hu)
  · simp [combinedTransfer, hu]

/-- Positive combined transfers still land outside the hull. -/
theorem combinedTransfer_target_not_hull {A : Finset Point}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (chart : P.AlignedChartData) (hlocal : HasLocalCases P W chart)
    {u v : Vertex A}
    (hpos : 0 < combinedTransfer P W chart hlocal u v) : v ∉ P.H := by
  classical
  simp only [combinedTransfer] at hpos
  split at hpos
  next hu => exact (hlocal u hu).target_not_hull hpos
  next hu => simp at hpos

end Erdos957GeometryLocalRows
