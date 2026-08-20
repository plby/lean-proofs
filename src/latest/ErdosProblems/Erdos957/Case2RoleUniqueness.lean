import ErdosProblems.Erdos957.CollisionGlue
import ErdosProblems.Erdos957.CaseClassification

/-!
# Formula-retaining Case-2/Case-4 collision data

This production module exposes the checked formula extractors used by the
remaining collision analysis.  It deliberately stops before the unresolved
cross-chart exceptional-collision theorem: no capacity or no-three property
is assumed here.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957Case2RoleUniqueness

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CollisionInstantiation
open Erdos957CaseClassification

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

/-- The formula data recovered from an anchored realized Case-2 secondary
role.  The three possible values of `secondary` are definitionally the
canonical `w`, `wNext`, and `e` selected by their checked degree branches. -/
structure Case2SecondaryFormula
    {source : {p // p ∈ P.H}} (v : Vertex A) where
  side : CyclicSide
  side_unit : dist (source.1.1 : Point)
    ((cyclicSideVertex P source side).1 : Point) = 1
  edgeFrame : Erdos957Case24Bridge.Framed.RigidChart
  edgeFrame_spec : ActualCase24Rows.SideNormalizedFrameSpec
    P source side edgeFrame
  source_actual : edgeFrame.actual Erdos957Cases24.Case2.u = source.1
  side_actual : edgeFrame.actual Erdos957Cases24.Case2.uPrev =
    cyclicSideVertex P source side
  middle : Vertex A
  middle_degree_six : (unitDistanceGraph A).degree middle = 6
  middle_not_hull : middle ∉ P.H
  middle_actual : edgeFrame.actual Erdos957Cases24.Case2.v = middle
  outer : Vertex A
  outer_not_hull : outer ∉ P.H
  outer_edge_coordinate : edgeFrame.toCanonical outer =
    Erdos957Cases24.Case2.b
  strict_support : Erdos957Case24Bridge.StrictlyBelowOutside
    (edgeFrame.image A)
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u}
  secondary : Erdos957Cases24.Point
  secondary_eq : secondary =
    Erdos957Cases24.Case2.secondaryRecipient
      (Erdos957Case24Bridge.unitDegree (edgeFrame.image A)
        Erdos957Cases24.Case2.w)
      (Erdos957Case24Bridge.unitDegree (edgeFrame.image A)
        Erdos957Cases24.Case2.wNext)
  target_edge_coordinate : edgeFrame.toCanonical v = secondary

/-- Constructor bookkeeping for the anchored exceptional role. -/
theorem exists_case2SecondaryFormula
    {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P F.chart source} {v : Vertex A}
    (D : RealizedPositiveTarget R v)
    (hrole : D.role = PairCases.TargetRoleName.case2Secondary) :
    Nonempty (Case2SecondaryFormula (P := P) (source := source) v) := by
  rcases D with ⟨role, target, htarget, hv⟩
  change role = PairCases.TargetRoleName.case2Secondary at hrole
  subst role
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case2 middle hdegree htwo hmiddleNot twoExtreme normalized row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
      subst target
      exact ⟨{
        side := twoExtreme.side
        side_unit := normalized.side_unit
        edgeFrame := normalized.frame
        edgeFrame_spec := normalized.frame_spec
        source_actual := normalized.source_actual
        side_actual := normalized.side_actual
        middle := middle
        middle_degree_six := hdegree
        middle_not_hull := hmiddleNot
        middle_actual := normalized.middle_actual
        outer := row.outer.vertex
        outer_not_hull := row.outer.not_hull
        outer_edge_coordinate := row.outer_edge_coordinate
        strict_support := normalized.strict_support
        secondary := Erdos957Cases24.Case2.secondaryRecipient
          (Erdos957Case24Bridge.unitDegree (normalized.frame.image A)
            Erdos957Cases24.Case2.w)
          (Erdos957Case24Bridge.unitDegree (normalized.frame.image A)
            Erdos957Cases24.Case2.wNext)
        secondary_eq := rfl
        target_edge_coordinate := by
          rw [hv]
          exact row.secondary_edge_coordinate }⟩
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget
  | case4 middle hdegree htwo twoExtreme normalized row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget

/-- The extractor exposes the literal three canonical secondary formulas,
without hiding the degree branch in a choice operator. -/
lemma Case2SecondaryFormula.target_edge_coordinate_cases
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.w ∨
      D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.wNext ∨
      D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.e := by
  rw [D.target_edge_coordinate, D.secondary_eq]
  simp only [Erdos957Cases24.Case2.secondaryRecipient]
  split_ifs <;> simp

/-- Scalar form of the fixed Case-2 secondary lattice alternatives. -/
lemma Case2SecondaryFormula.target_horizontal_bounds
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    0 ≤ (D.edgeFrame.toCanonical v) 0 ∧
      (D.edgeFrame.toCanonical v) 0 ≤ 3 / 2 := by
  rcases D.target_edge_coordinate_cases with h | h | h <;>
    rw [h] <;>
    norm_num [Erdos957Cases24.Case2.w,
      Erdos957Cases24.Case2.wNext, Erdos957Cases24.Case2.e]

lemma Case2SecondaryFormula.target_below_support
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    (D.edgeFrame.toCanonical v) 1 < 0 := by
  have hs : 0 < Erdos957Cases24.sqrtThree :=
    Erdos957Cases24.sqrtThree_pos
  rcases D.target_edge_coordinate_cases with h | h | h <;>
    rw [h] <;>
    simp only [Erdos957Cases24.Case2.w, Erdos957Cases24.Case2.wNext,
      Erdos957Cases24.Case2.e, Erdos957Cases24.point_apply_one] <;> linarith

/-- The cyclic partner carried by the two-extreme witness is literally the
canonical left endpoint `uPrev` in the retained source-normalized frame.
This is the reflection-safe endpoint identity needed by the exceptional
collision dispatch. -/
lemma Case2SecondaryFormula.side_edge_coordinate
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    D.edgeFrame.toCanonical (cyclicSideVertex P source D.side).1 =
      Erdos957Cases24.Case2.uPrev := by
  cases D.edgeFrame_spec with
  | previous hside hunit hframe =>
      rw [hside]
      simp only [cyclicSideVertex]
      rw [hframe]
      let frame := Erdos957EdgeFrame.terminalUnitEdgeRigidChart
        (P.next⁻¹ source).1.1 source.1.1 hunit
      have hp : frame.actual Erdos957Cases24.Case2.uPrev =
          (P.next⁻¹ source).1.1 := by
        exact Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_uPrev
          (P.next⁻¹ source).1.1 source.1.1 hunit
      calc
        frame.toCanonical (P.next⁻¹ source).1.1 =
            frame.toCanonical (frame.actual Erdos957Cases24.Case2.uPrev) :=
          congrArg frame.toCanonical hp.symm
        _ = Erdos957Cases24.Case2.uPrev := frame.toCanonical_actual _
  | next hside hunit hframe =>
      rw [hside]
      simp only [cyclicSideVertex]
      rw [hframe]
      let frame := Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
        P source hunit
      have hp : frame.actual Erdos957Cases24.Case2.uPrev =
          (P.next source).1.1 := by
        exact Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart_actual_case2_uPrev
          P source hunit
      calc
        frame.toCanonical (P.next source).1.1 =
            frame.toCanonical (frame.actual Erdos957Cases24.Case2.uPrev) :=
          congrArg frame.toCanonical hp.symm
        _ = Erdos957Cases24.Case2.uPrev := frame.toCanonical_actual _

/-- Metric fingerprint of the three Case-2 secondary roles with respect to
the emitting source.  It is invariant under the rigid edge chart and is the
first input to the cyclic-offset exclusion. -/
lemma Case2SecondaryFormula.source_target_sq_distance_cases
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    dist (source.1 : Point) (v : Point) ^ 2 = 3 ∨
      dist (source.1 : Point) (v : Point) ^ 2 = 4 := by
  have hdist : dist (source.1 : Point) (v : Point) =
      dist Erdos957Cases24.Case2.u (D.edgeFrame.toCanonical v) := by
    rw [← D.edgeFrame.dist_eq]
    rw [← D.source_actual, D.edgeFrame.toCanonical_actual]
  rcases D.target_edge_coordinate_cases with hw | hwNext | he
  · left
    rw [hdist, hw]
    have hs := Erdos957Cases24.dist_sq_eq_coordinates
      Erdos957Cases24.Case2.u Erdos957Cases24.Case2.w
    norm_num [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.w,
      Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
      Erdos957Cases24.sqrtThree_sq] at hs ⊢
    exact hs
  · right
    rw [hdist, hwNext]
    have hs := Erdos957Cases24.dist_sq_eq_coordinates
      Erdos957Cases24.Case2.u Erdos957Cases24.Case2.wNext
    norm_num [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.wNext,
      Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
      Erdos957Cases24.sqrtThree_sq] at hs ⊢
    exact hs
  · left
    rw [hdist, he]
    have hs := Erdos957Cases24.dist_sq_eq_coordinates
      Erdos957Cases24.Case2.u Erdos957Cases24.Case2.e
    norm_num [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.e,
      Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
      Erdos957Cases24.sqrtThree_sq] at hs ⊢
    nlinarith [hs, Erdos957Cases24.sqrtThree_sq]

/-- A Case-2 secondary recipient is never itself a unit neighbour of the
emitting source: its squared source distance is three or four. -/
lemma Case2SecondaryFormula.not_source_adj_target
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    ¬ (unitDistanceGraph A).Adj source.1 v := by
  intro hadj
  have hdist : dist (source.1 : Point) (v : Point) = 1 := by
    simpa [unitDistanceGraph] using hadj
  rcases D.source_target_sq_distance_cases with h | h <;>
    rw [hdist] at h <;> norm_num at h

/-- The retained Case-2 middle is the actual unit neighbour represented by
the canonical lattice point `v`. -/
lemma Case2SecondaryFormula.source_middle_adj
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    (unitDistanceGraph A).Adj source.1 D.middle := by
  change dist (source.1 : Point) (D.middle : Point) = 1
  rw [← D.source_actual, ← D.middle_actual, D.edgeFrame.dist_actual,
    Erdos957Cases24.Case2.dist_u_v]

/-- The outer half-token recipient is the actual canonical point `b` and
is unit-adjacent to the emitting source. -/
lemma Case2SecondaryFormula.source_outer_adj
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    (unitDistanceGraph A).Adj source.1 D.outer := by
  change dist (source.1 : Point) (D.outer : Point) = 1
  rw [← D.edgeFrame.dist_eq, ← D.source_actual,
    D.edgeFrame.toCanonical_actual, D.outer_edge_coordinate,
    Erdos957Cases24.Case2.dist_u_b]

/-- The middle and outer vertices are the two equilateral contacts on the
normalized source edge. -/
lemma Case2SecondaryFormula.middle_outer_adj
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    (unitDistanceGraph A).Adj D.middle D.outer := by
  change dist (D.middle : Point) (D.outer : Point) = 1
  rw [← D.edgeFrame.dist_eq, ← D.middle_actual,
    D.edgeFrame.toCanonical_actual, D.outer_edge_coordinate,
    Erdos957Cases24.Case2.dist_v_b]

/-- The exceptional secondary target retains its actual displayed contact:
`w` is adjacent to the middle, while `wNext` and `e` are adjacent to the
outer target. -/
lemma Case2SecondaryFormula.middle_or_outer_adj_target
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    (unitDistanceGraph A).Adj D.middle v ∨
      (unitDistanceGraph A).Adj D.outer v := by
  rcases D.target_edge_coordinate_cases with hw | hwNext | he
  · left
    change dist (D.middle : Point) (v : Point) = 1
    rw [← D.edgeFrame.dist_eq, ← D.middle_actual,
      D.edgeFrame.toCanonical_actual, hw,
      Erdos957Cases24.Case2.dist_v_w]
  · right
    change dist (D.outer : Point) (v : Point) = 1
    rw [← D.edgeFrame.dist_eq, D.outer_edge_coordinate, hwNext,
      Erdos957Cases24.Case2.dist_b_wNext]
  · right
    change dist (D.outer : Point) (v : Point) = 1
    rw [← D.edgeFrame.dist_eq, D.outer_edge_coordinate, he,
      Erdos957Cases24.Case2.dist_b_e]

/-- Formula-derived Figure-13 core, with no historical point
identifications assumed.  If the Case-2 secondary has been forced to the
canonical point `e`, two unit-adjacent vertices cannot form a unit triangle
with it while both lie strictly between `e` and the supporting line. -/
lemma Case2SecondaryFormula.no_unit_triangle_strictly_above_e
    {source : {p // p ∈ P.H}} {v r s : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (he : D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.e)
    (hrv : (unitDistanceGraph A).Adj r v)
    (hsv : (unitDistanceGraph A).Adj s v)
    (hrs : (unitDistanceGraph A).Adj r s)
    (hvr : (D.edgeFrame.toCanonical v) 1 <
      (D.edgeFrame.toCanonical r) 1)
    (hvs : (D.edgeFrame.toCanonical v) 1 <
      (D.edgeFrame.toCanonical s) 1)
    (hr0 : (D.edgeFrame.toCanonical r) 1 < 0)
    (hs0 : (D.edgeFrame.toCanonical s) 1 < 0) : False := by
  let zr := D.edgeFrame.toCanonical r
  let zs := D.edgeFrame.toCanonical s
  let d := D.edgeFrame.toCanonical v
  have hdist_rv : dist zr d = 1 := by
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hrv
  have hdist_sv : dist zs d = 1 := by
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hsv
  have hdist_rs : dist zr zs = 1 := by
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hrs
  have hrdsq := Erdos957Cases24.dist_sq_eq_coordinates zr d
  have hsdsq := Erdos957Cases24.dist_sq_eq_coordinates zs d
  have hrssq := Erdos957Cases24.dist_sq_eq_coordinates zr zs
  rw [hdist_rv] at hrdsq
  rw [hdist_sv] at hsdsq
  rw [hdist_rs] at hrssq
  apply Erdos957Overcharge.figure13_equilateral_hull_exclusion
    (u := (zr 0, zr 1)) (j := (zs 0, zs 1)) (d := (d 0, d 1))
  · simpa [Erdos957Overcharge.sqDist] using hrdsq.symm
  · simpa [Erdos957Overcharge.sqDist] using hsdsq.symm
  · simpa [Erdos957Overcharge.sqDist] using hrssq.symm
  · dsimp only [d]
    rw [he]
    rfl
  · exact hvr
  · exact hvs
  · exact hr0
  · exact hs0

/-- The exact normalized geometry recovered from a realized Case-4 whole
role.  Such a role can only come from the `whole` constructor: the split
constructors use `case4SplitLeft` and `case4SplitRight` instead. -/
structure Case4WholeFormula
    {source : {p // p ∈ P.H}} (v : Vertex A) where
  incidentSide : CyclicSide
  side_unit : dist (source.1.1 : Point)
    ((cyclicSideVertex P source incidentSide).1 : Point) = 1
  edgeFrame : Erdos957Case24Bridge.Framed.RigidChart
  edgeFrame_spec : ActualCase24Rows.SideNormalizedFrameSpec
    P source incidentSide edgeFrame
  source_actual : edgeFrame.actual Erdos957Cases24.Case2.u = source.1
  side : Vertex A
  side_eq : side = cyclicSideVertex P source incidentSide
  side_actual : edgeFrame.actual Erdos957Cases24.Case2.uPrev = side
  target_edge_coordinate : edgeFrame.toCanonical v =
    Erdos957Cases24.Case2.v

/-- Constructor bookkeeping for a realized Case-4 whole role. -/
theorem exists_case4WholeFormula
    {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P F.chart source} {v : Vertex A}
    (D : RealizedPositiveTarget R v)
    (hrole : D.role = PairCases.TargetRoleName.case4Primary) :
    Nonempty (Case4WholeFormula (P := P) (source := source) v) := by
  rcases D with ⟨role, target, htarget, hv⟩
  change role = PairCases.TargetRoleName.case4Primary at hrole
  subst role
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case2 middle hdegree htwo hmiddleNot twoExtreme normalized row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget
  | case4 middle hdegree htwo twoExtreme normalized row hmiddleVertex =>
      cases row with
      | whole middleTarget hcoord hfour =>
          simp [RealizedSourceRow.targetAtRole] at htarget
          subst target
          exact ⟨{
            incidentSide := twoExtreme.side
            side_unit := normalized.side_unit
            edgeFrame := normalized.frame
            edgeFrame_spec := normalized.frame_spec
            source_actual := normalized.source_actual
            side := cyclicSideVertex P source twoExtreme.side
            side_eq := rfl
            side_actual := normalized.side_actual
            target_edge_coordinate := by simpa [hv] using hcoord }⟩
      | orderedLow farthest hfive middleTarget lowTarget hm hl hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
      | orderedHigh farthest hsix recipients middleTarget sideTarget hm hs hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
      | pairedSplit commonFrame farthest branch rightSource hright middleTarget
          secondaryTarget hsource hm hs hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget

/-- A checked Case-2 descriptor exposes the reflected cyclic-side label used
by the production two-colouring. -/
theorem exists_case2Secondary_associationSide
    {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P F.chart source} {v : Vertex A}
    (D : RealizedPositiveTarget R v)
    (E : RealizedArrivalDescriptor R D.role D.target)
    (hrole : D.role = PairCases.TargetRoleName.case2Secondary) :
    ∃ side : CyclicSide,
      E.association = oppositeCyclicSideAssociation side := by
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
      rcases D with ⟨role, target, htarget, hv⟩
      change role = PairCases.TargetRoleName.case2Secondary at hrole
      subst role
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case2 middle hdegree htwo hmiddleNot T normalized row =>
      refine ⟨T.side, ?_⟩
      rw [E.association_eq]
      simp [RealizedSourceRow.roleAssociation]
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      rcases D with ⟨role, target, htarget, hv⟩
      change role = PairCases.TargetRoleName.case2Secondary at hrole
      subst role
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget
  | case4 middle hdegree htwo T normalized row hmiddleVertex =>
      rcases D with ⟨role, target, htarget, hv⟩
      change role = PairCases.TargetRoleName.case2Secondary at hrole
      subst role
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget

/-- The fixed Case-4 middle lies strictly on the incident side selected by
the reflection-correct horizontal convention. -/
lemma orientedHorizontalAssociation_case2_v (side : CyclicSide) :
    orientedHorizontalAssociation side (Erdos957Cases24.Case2.v 0) =
      cyclicSideAssociation side := by
  cases side <;>
    simp [orientedHorizontalAssociation, horizontalAssociation,
      cyclicSideAssociation, Erdos957Cases24.Case2.v]

/-- A checked Case-4 primary descriptor exposes the incident cyclic side.
This remains true under the recipient-relative ABI because the primary is
the fixed middle `v`, whose horizontal coordinate is `-1/2`. -/
theorem exists_case4Primary_associationSide
    {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P F.chart source} {v : Vertex A}
    (D : RealizedPositiveTarget R v)
    (E : RealizedArrivalDescriptor R D.role D.target)
    (hrole : D.role = PairCases.TargetRoleName.case4Primary) :
    ∃ side : CyclicSide, E.association = cyclicSideAssociation side := by
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
      rcases D with ⟨role, target, htarget, hv⟩
      change role = PairCases.TargetRoleName.case4Primary at hrole
      subst role
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case2 middle hdegree htwo hmiddleNot T normalized row =>
      rcases D with ⟨role, target, htarget, hv⟩
      change role = PairCases.TargetRoleName.case4Primary at hrole
      subst role
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      rcases D with ⟨role, target, htarget, hv⟩
      change role = PairCases.TargetRoleName.case4Primary at hrole
      subst role
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget
  | case4 middle hdegree htwo T normalized row hmiddleVertex =>
      rcases D with ⟨role, target, htarget, hv⟩
      change role = PairCases.TargetRoleName.case4Primary at hrole
      subst role
      cases row with
      | whole middleTarget hcoord hfour =>
          refine ⟨T.side, ?_⟩
          rw [E.association_eq]
          simp [RealizedSourceRow.roleAssociation,
            orientedHorizontalAssociation_case2_v]
      | orderedLow farthest hfive middleTarget lowTarget hm hl hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
      | orderedHigh farthest hsix recipients middleTarget sideTarget hm hs hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
      | pairedSplit commonFrame farthest branch rightSource hright middleTarget
          secondaryTarget hsource hm hs hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget

/-- Exact coordinate alternatives retained by the current generalized
Case-4 split-right recipient.  In particular, the target is an arbitrary
farthest residual neighbor or one of its ordered contacts; it is not
definitionally the fixed historical lattice point from Figure 13. -/
inductive Case4SplitRightFormula
    {source : {p // p ∈ P.H}} (v : Vertex A) : Type
  | orderedLow
      (side : CyclicSide)
      (side_unit : dist (source.1.1 : Point)
        ((cyclicSideVertex P source side).1 : Point) = 1)
      (frame : Erdos957Case24Bridge.Framed.RigidChart)
      (frame_spec : ActualCase24Rows.SideNormalizedFrameSpec
        P source side frame)
      (source_actual : frame.actual Erdos957Cases24.Case2.u = source.1)
      (middle : Vertex A)
      (middle_coordinate : frame.toCanonical middle =
        Erdos957Cases24.Case2.v)
      (farthest : Erdos957Case24Bridge.Case4.FarthestBelowData
        (frame.image A))
      (target_coordinate : frame.toCanonical v = farthest.point)
  | orderedHigh
      (side : CyclicSide)
      (side_unit : dist (source.1.1 : Point)
        ((cyclicSideVertex P source side).1 : Point) = 1)
      (frame : Erdos957Case24Bridge.Framed.RigidChart)
      (frame_spec : ActualCase24Rows.SideNormalizedFrameSpec
        P source side frame)
      (source_actual : frame.actual Erdos957Cases24.Case2.u = source.1)
      (middle : Vertex A)
      (middle_coordinate : frame.toCanonical middle =
        Erdos957Cases24.Case2.v)
      (farthest : Erdos957Case24Bridge.Case4.FarthestBelowData
        (frame.image A))
      (recipients : Erdos957Case24Bridge.Case4.HighFarthestRecipients
        (frame.image A) farthest)
      (target_coordinate : frame.toCanonical v = recipients.right)
  | paired
      (side : CyclicSide)
      (frame : Erdos957Case24Bridge.Framed.RigidChart)
      (farthest : Erdos957Case24Bridge.Case4.FarthestBelowData
        (frame.image A))
      (branch : Erdos957Case24Bridge.Case4.FarthestBranchData
        (frame.image A) farthest)
      (rightSource : Bool)
      (right_source_eq : rightSource =
        match side with | .previous => true | .next => false)
      (source_coordinate : frame.toCanonical source.1 =
        Erdos957Case24Bridge.Case4.sideSource rightSource)
      (middle : Vertex A)
      (middle_coordinate : frame.toCanonical middle =
        Erdos957Cases24.Case2.v)
      (target_coordinate : frame.toCanonical v =
        branch.sourceRecipient rightSource)

/-- Reflection-safe cyclic side retained by each split-right formula. -/
def Case4SplitRightFormula.incidentSide
    {source : {p // p ∈ P.H}} {v : Vertex A} :
    Case4SplitRightFormula (P := P) (source := source) v → CyclicSide
  | .orderedLow side _ _ _ _ _ _ _ _ => side
  | .orderedHigh side _ _ _ _ _ _ _ _ _ => side
  | .paired side _ _ _ _ _ _ _ _ _ => side

/-- Extract the exact low/high/paired split-right formula from the same
realized row selected by collision analysis. -/
theorem exists_case4SplitRightFormula
    {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P F.chart source} {v : Vertex A}
    (D : RealizedPositiveTarget R v)
    (hrole : D.role = PairCases.TargetRoleName.case4SplitRight) :
    Nonempty (Case4SplitRightFormula (P := P) (source := source) v) := by
  rcases D with ⟨role, target, htarget, hv⟩
  change role = PairCases.TargetRoleName.case4SplitRight at hrole
  subst role
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case2 middle hdegree htwo hmiddleNot T normalized row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget
  | case4 middle hdegree htwo T normalized row hmiddleVertex =>
      cases row with
      | whole middleTarget hm hfour =>
          simp [RealizedSourceRow.targetAtRole] at htarget
      | orderedLow farthest hfive middleTarget lowTarget hm hl hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
          subst target
          exact ⟨.orderedLow T.side normalized.side_unit normalized.frame
            normalized.frame_spec normalized.source_actual
            middle (by rw [← normalized.middle_actual,
              normalized.frame.toCanonical_actual])
            farthest (by simpa [hv] using hl)⟩
      | orderedHigh farthest hsix recipients middleTarget sideTarget hm hs hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
          subst target
          exact ⟨.orderedHigh T.side normalized.side_unit normalized.frame
            normalized.frame_spec normalized.source_actual
            middle (by rw [← normalized.middle_actual,
              normalized.frame.toCanonical_actual])
            farthest recipients (by simpa [hv] using hs)⟩
      | pairedSplit commonFrame farthest branch rightSource hright middleTarget
          secondaryTarget hsource hm hs hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
          subst target
          exact ⟨.paired T.side commonFrame farthest branch rightSource
            hright
            hsource middleTarget.vertex hm (by simpa [hv] using hs)⟩

/-- The actual middle point in the rigid chart carried by a split-right
formula.  It is deliberately a point rather than a `Vertex`: membership is
owned by the realized row, while the metric identities below need only the
checked rigid-chart formulas. -/
def Case4SplitRightFormula.middleActual
    {source : {p // p ∈ P.H}} {v : Vertex A} :
    Case4SplitRightFormula (P := P) (source := source) v → Point
  | .orderedLow _ _ _ _ _ middle _ _ _ => middle
  | .orderedHigh _ _ _ _ _ middle _ _ _ _ => middle
  | .paired _ _ _ _ _ _ _ middle _ _ => middle

/-- The same retained middle with its configuration membership restored. -/
def Case4SplitRightFormula.middleVertex
    {source : {p // p ∈ P.H}} {v : Vertex A} :
    Case4SplitRightFormula (P := P) (source := source) v → Vertex A
  | .orderedLow _ _ _ _ _ middle _ _ _ => middle
  | .orderedHigh _ _ _ _ _ middle _ _ _ _ => middle
  | .paired _ _ _ _ _ _ _ middle _ _ => middle

@[simp] lemma Case4SplitRightFormula.middleActual_eq_coe_middleVertex
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v) :
    D.middleActual = (D.middleVertex : Point) := by
  cases D <;> rfl

/-- Every generalized Case-4 split-right target is a genuine unit contact
of the middle point retained by its own rigid chart. -/
lemma Case4SplitRightFormula.middle_target_dist
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v) :
    dist D.middleActual (v : Point) = 1 := by
  cases D with
  | orderedLow side side_unit frame frame_eq source_actual middle
      middle_coordinate farthest target_coordinate =>
      change dist (middle : Point) (v : Point) = 1
      rw [← frame.dist_eq, middle_coordinate, target_coordinate]
      exact (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        farthest.point_mem).2.1
  | orderedHigh side side_unit frame frame_eq source_actual middle
      middle_coordinate farthest recipients target_coordinate =>
      change dist (middle : Point) (v : Point) = 1
      rw [← frame.dist_eq, middle_coordinate, target_coordinate]
      exact (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        recipients.right_mem).2.1
  | paired side frame farthest branch rightSource right_source_eq
      source_coordinate middle middle_coordinate target_coordinate =>
      change dist (middle : Point) (v : Point) = 1
      rw [← frame.dist_eq, middle_coordinate, target_coordinate]
      exact (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        (branch.sourceRecipient_mem rightSource)).2.1

/-- The emitting hull source is also one unit from the same retained
middle, including the unreflected common-pair chart. -/
lemma Case4SplitRightFormula.source_middle_dist
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v) :
    dist (source.1 : Point) D.middleActual = 1 := by
  cases D with
  | orderedLow side side_unit frame frame_eq source_actual middle
      middle_coordinate farthest target_coordinate =>
      change dist (source.1 : Point)
        (middle : Point) = 1
      rw [← frame.dist_eq, ← source_actual, frame.toCanonical_actual,
        middle_coordinate,
        Erdos957Cases24.Case2.dist_u_v]
  | orderedHigh side side_unit frame frame_eq source_actual middle
      middle_coordinate farthest recipients target_coordinate =>
      change dist (source.1 : Point)
        (middle : Point) = 1
      rw [← frame.dist_eq, ← source_actual, frame.toCanonical_actual,
        middle_coordinate,
        Erdos957Cases24.Case2.dist_u_v]
  | paired side frame farthest branch rightSource right_source_eq
      source_coordinate middle middle_coordinate target_coordinate =>
      change dist (source.1 : Point)
        (middle : Point) = 1
      rw [← frame.dist_eq, source_coordinate, middle_coordinate]
      cases rightSource <;>
        simp [Erdos957Case24Bridge.Case4.sideSource,
          Erdos957Cases24.Case2.dist_uPrev_v,
          Erdos957Cases24.Case2.dist_u_v]

/-- Hence a split-right recipient is reached from its emitting source by
the honest two-edge path through the retained Case-4 middle. -/
lemma Case4SplitRightFormula.source_target_dist_le_two
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v) :
    dist (source.1 : Point) (v : Point) ≤ 2 := by
  calc
    dist (source.1 : Point) (v : Point) ≤
        dist (source.1 : Point) D.middleActual +
          dist D.middleActual (v : Point) := dist_triangle _ _ _
    _ = 2 := by rw [D.source_middle_dist, D.middle_target_dist]; norm_num

/-- The target written in the rigid chart retained by its constructor. -/
def Case4SplitRightFormula.targetCanonical
    {source : {p // p ∈ P.H}} {v : Vertex A} :
    Case4SplitRightFormula (P := P) (source := source) v → Point
  | .orderedLow _ _ frame _ _ _ _ _ _ => frame.toCanonical v
  | .orderedHigh _ _ frame _ _ _ _ _ _ _ => frame.toCanonical v
  | .paired _ frame _ _ _ _ _ _ _ _ => frame.toCanonical v

/-- The production arrival association of a split-right formula.  Ordered
rows use their reflected source-normalized chart; paired rows use the common
directed-edge chart and subtract the actual endpoint coordinate.  Unlike the
old incident-side label, this definition genuinely depends on the selected
recipient. -/
def Case4SplitRightFormula.targetAssociation
    {source : {p // p ∈ P.H}} {v : Vertex A} :
    Case4SplitRightFormula (P := P) (source := source) v →
      ArrivalAssociation
  | .orderedLow side _ _ _ _ _ _ farthest _ =>
      orientedHorizontalAssociation side (farthest.point 0)
  | .orderedHigh side _ _ _ _ _ _ _ recipients _ =>
      orientedHorizontalAssociation side (recipients.right 0)
  | .paired _ _ _ branch rightSource _ _ _ _ _ =>
      commonPairHorizontalAssociation branch rightSource

/-- The exact endpoint-sensitive coordinate condition for a split-right
arrival from the global next side.  The weak inequality belongs to the
reflected ordered endpoint and to the left endpoint of a common pair; this
records the deterministic vertical-tie convention rather than erasing it
into a single signed scalar. -/
def Case4SplitRightFormula.fromNextDisplacement
    {source : {p // p ∈ P.H}} {v : Vertex A} :
    Case4SplitRightFormula (P := P) (source := source) v → Prop
  | .orderedLow side _ _ _ _ _ _ farthest _ =>
      match side with
      | .previous => 0 < farthest.point 0
      | .next => farthest.point 0 ≤ 0
  | .orderedHigh side _ _ _ _ _ _ _ recipients _ =>
      match side with
      | .previous => 0 < recipients.right 0
      | .next => recipients.right 0 ≤ 0
  | .paired _ _ _ branch rightSource _ _ _ _ _ =>
      if rightSource then
        0 < branch.sourceRecipient rightSource 0 -
          Erdos957Case24Bridge.Case4.sideSource rightSource 0
      else
        0 ≤ branch.sourceRecipient rightSource 0 -
          Erdos957Case24Bridge.Case4.sideSource rightSource 0

/-- Complementary exact coordinate condition for a split-right arrival
from the global previous side. -/
def Case4SplitRightFormula.fromPreviousDisplacement
    {source : {p // p ∈ P.H}} {v : Vertex A}
    : Case4SplitRightFormula (P := P) (source := source) v → Prop
  | .orderedLow side _ _ _ _ _ _ farthest _ =>
      match side with
      | .previous => farthest.point 0 ≤ 0
      | .next => 0 < farthest.point 0
  | .orderedHigh side _ _ _ _ _ _ _ recipients _ =>
      match side with
      | .previous => recipients.right 0 ≤ 0
      | .next => 0 < recipients.right 0
  | .paired _ _ _ branch rightSource _ _ _ _ _ =>
      if rightSource then
        branch.sourceRecipient rightSource 0 -
          Erdos957Case24Bridge.Case4.sideSource rightSource 0 ≤ 0
      else
        branch.sourceRecipient rightSource 0 -
          Erdos957Case24Bridge.Case4.sideSource rightSource 0 < 0

@[simp] lemma Case4SplitRightFormula.targetAssociation_eq_fromNext_iff
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v) :
    D.targetAssociation = .fromNext ↔ D.fromNextDisplacement := by
  cases D with
  | orderedLow side =>
      cases side <;>
        simp [Case4SplitRightFormula.targetAssociation,
          Case4SplitRightFormula.fromNextDisplacement,
          orientedHorizontalAssociation, horizontalAssociation]
  | orderedHigh side =>
      cases side <;>
        simp [Case4SplitRightFormula.targetAssociation,
          Case4SplitRightFormula.fromNextDisplacement,
          orientedHorizontalAssociation, horizontalAssociation]
  | paired _ _ _ branch rightSource =>
      cases rightSource <;>
        simp [Case4SplitRightFormula.targetAssociation,
          Case4SplitRightFormula.fromNextDisplacement,
          commonPairHorizontalAssociation, horizontalAssociation]

@[simp] lemma Case4SplitRightFormula.targetAssociation_eq_fromPrevious_iff
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v) :
    D.targetAssociation = .fromPrevious ↔ D.fromPreviousDisplacement := by
  cases D with
  | orderedLow side =>
      cases side <;>
        simp [Case4SplitRightFormula.targetAssociation,
          Case4SplitRightFormula.fromPreviousDisplacement,
          orientedHorizontalAssociation, horizontalAssociation]
  | orderedHigh side =>
      cases side <;>
        simp [Case4SplitRightFormula.targetAssociation,
          Case4SplitRightFormula.fromPreviousDisplacement,
          orientedHorizontalAssociation, horizontalAssociation]
  | paired _ _ _ branch rightSource =>
      cases rightSource <;>
        simp [Case4SplitRightFormula.targetAssociation,
          Case4SplitRightFormula.fromPreviousDisplacement,
          commonPairHorizontalAssociation, horizontalAssociation]

/-- All low/high/paired split-right recipients lie in the sharp canonical
horizontal strip used by the normalized-edge separation argument. -/
lemma Case4SplitRightFormula.target_horizontal_le_three_halves
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v) :
    |D.targetCanonical 0| ≤ 3 / 2 := by
  cases D with
  | orderedLow side side_unit frame frame_spec source_actual middle
      middle_coordinate farthest target_coordinate =>
      change |(frame.toCanonical v) 0| ≤ 3 / 2
      rw [target_coordinate]
      exact Erdos957Case24Bridge.Case4.residual_horizontal_le_three_halves
        farthest.point_mem
  | orderedHigh side side_unit frame frame_spec source_actual middle
      middle_coordinate farthest recipients target_coordinate =>
      change |(frame.toCanonical v) 0| ≤ 3 / 2
      rw [target_coordinate]
      exact Erdos957Case24Bridge.Case4.residual_horizontal_le_three_halves
        recipients.right_mem
  | paired side frame farthest branch rightSource right_source_eq
      source_coordinate middle middle_coordinate target_coordinate =>
      change |(frame.toCanonical v) 0| ≤ 3 / 2
      rw [target_coordinate]
      exact Erdos957Case24Bridge.Case4.residual_horizontal_le_three_halves
        (branch.sourceRecipient_mem rightSource)

/-- Graph-level form of the retained honest two-edge path. -/
lemma Case4SplitRightFormula.source_middle_adj
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v) :
    (unitDistanceGraph A).Adj source.1 D.middleVertex := by
  change dist (source.1 : Point) (D.middleVertex : Point) = 1
  rw [← D.middleActual_eq_coe_middleVertex]
  exact D.source_middle_dist

lemma Case4SplitRightFormula.middle_target_adj
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v) :
    (unitDistanceGraph A).Adj D.middleVertex v := by
  change dist (D.middleVertex : Point) (v : Point) = 1
  rw [← D.middleActual_eq_coe_middleVertex]
  exact D.middle_target_dist

/-- The exceptional Case-4 recipient is genuinely different from its
retained equilateral middle in every low, high, and paired branch. -/
lemma Case4SplitRightFormula.target_ne_middleVertex
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v) :
    v ≠ D.middleVertex := by
  cases D with
  | orderedLow side side_unit frame frame_spec source_actual middle
      middle_coordinate farthest target_coordinate =>
      change v ≠ middle
      intro h
      have hc := congrArg (fun z : Vertex A ↦ frame.toCanonical (z : Point)) h
      rw [target_coordinate, middle_coordinate] at hc
      have hd := (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        farthest.point_mem).2.1
      rw [hc] at hd
      simp [Erdos957Cases24.Case4.v] at hd
  | orderedHigh side side_unit frame frame_spec source_actual middle
      middle_coordinate farthest recipients target_coordinate =>
      change v ≠ middle
      intro h
      have hc := congrArg (fun z : Vertex A ↦ frame.toCanonical (z : Point)) h
      rw [target_coordinate, middle_coordinate] at hc
      have hd := (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        recipients.right_mem).2.1
      rw [hc] at hd
      simp [Erdos957Cases24.Case4.v] at hd
  | paired side frame farthest branch rightSource right_source_eq
      source_coordinate middle middle_coordinate target_coordinate =>
      change v ≠ middle
      intro h
      have hc := congrArg (fun z : Vertex A ↦ frame.toCanonical (z : Point)) h
      rw [target_coordinate, middle_coordinate] at hc
      exact branch.sourceRecipient_ne_v rightSource hc

/-! ## Formula/association bundles for the exceptional `(2,4)` dispatch -/

/-- The exact Case-2 formula and its reflection-correct arrival association,
extracted in one case split so the cyclic side cannot be lost between two
independent choice operations. -/
structure Case2SecondaryArrivalFormula
    {source : {p // p ∈ P.H}} {R : RealizedSourceRow P F.chart source}
    {v : Vertex A} (D : RealizedPositiveTarget R v)
    (E : RealizedArrivalDescriptor R D.role D.target) where
  formula : Case2SecondaryFormula (P := P) (source := source) v
  association_eq : E.association =
    oppositeCyclicSideAssociation formula.side

theorem nonempty_case2SecondaryArrivalFormula
    {source : {p // p ∈ P.H}} {R : RealizedSourceRow P F.chart source}
    {v : Vertex A} (D : RealizedPositiveTarget R v)
    (E : RealizedArrivalDescriptor R D.role D.target)
    (hrole : D.role = PairCases.TargetRoleName.case2Secondary) :
    Nonempty (Case2SecondaryArrivalFormula D E) := by
  rcases D with ⟨role, target, htarget, hv⟩
  change role = PairCases.TargetRoleName.case2Secondary at hrole
  subst role
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case2 middle hdegree htwo hmiddleNot T normalized row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
      subst target
      refine ⟨{
        formula := {
          side := T.side
          side_unit := normalized.side_unit
          edgeFrame := normalized.frame
          edgeFrame_spec := normalized.frame_spec
          source_actual := normalized.source_actual
          side_actual := normalized.side_actual
          middle := middle
          middle_degree_six := hdegree
          middle_not_hull := hmiddleNot
          middle_actual := normalized.middle_actual
          outer := row.outer.vertex
          outer_not_hull := row.outer.not_hull
          outer_edge_coordinate := row.outer_edge_coordinate
          strict_support := normalized.strict_support
          secondary := Erdos957Cases24.Case2.secondaryRecipient
            (Erdos957Case24Bridge.unitDegree (normalized.frame.image A)
              Erdos957Cases24.Case2.w)
            (Erdos957Case24Bridge.unitDegree (normalized.frame.image A)
              Erdos957Cases24.Case2.wNext)
          secondary_eq := rfl
          target_edge_coordinate := by
            rw [hv]
            exact row.secondary_edge_coordinate }
        association_eq := ?_ }⟩
      rw [E.association_eq]
      simp [RealizedSourceRow.roleAssociation]
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget
  | case4 middle hdegree htwo T normalized row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget

/-- A Case-4 whole arrival bundled with the exact normalized incident side
which computes its production association. -/
structure Case4WholeArrivalFormula
    {source : {p // p ∈ P.H}} {R : RealizedSourceRow P F.chart source}
    {v : Vertex A} (D : RealizedPositiveTarget R v)
    (E : RealizedArrivalDescriptor R D.role D.target) where
  formula : Case4WholeFormula (P := P) (source := source) v
  association_eq : E.association =
    cyclicSideAssociation formula.incidentSide

theorem nonempty_case4WholeArrivalFormula
    {source : {p // p ∈ P.H}} {R : RealizedSourceRow P F.chart source}
    {v : Vertex A} (D : RealizedPositiveTarget R v)
    (E : RealizedArrivalDescriptor R D.role D.target)
    (hrole : D.role = PairCases.TargetRoleName.case4Primary) :
    Nonempty (Case4WholeArrivalFormula D E) := by
  rcases D with ⟨role, target, htarget, hv⟩
  change role = PairCases.TargetRoleName.case4Primary at hrole
  subst role
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case2 middle hdegree htwo hmiddleNot T normalized row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget
  | case4 middle hdegree htwo T normalized row hmiddleVertex =>
      cases row with
      | whole middleTarget hcoord hfour =>
          simp [RealizedSourceRow.targetAtRole] at htarget
          subst target
          refine ⟨{
            formula := {
              incidentSide := T.side
              side_unit := normalized.side_unit
              edgeFrame := normalized.frame
              edgeFrame_spec := normalized.frame_spec
              source_actual := normalized.source_actual
              side := cyclicSideVertex P source T.side
              side_eq := rfl
              side_actual := normalized.side_actual
              target_edge_coordinate := by simpa [hv] using hcoord }
            association_eq := ?_ }⟩
          rw [E.association_eq]
          simp [RealizedSourceRow.roleAssociation,
            orientedHorizontalAssociation_case2_v]
      | orderedLow farthest hfive middleTarget lowTarget hm hl hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
      | orderedHigh farthest hsix recipients middleTarget sideTarget hm hs hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
      | pairedSplit commonFrame farthest branch rightSource hright middleTarget
          secondaryTarget hsource hm hs hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget

/-- The exact generalized split-right formula and its recipient-relative
association, again extracted together from one realized constructor. -/
structure Case4SplitRightArrivalFormula
    {source : {p // p ∈ P.H}} {R : RealizedSourceRow P F.chart source}
    {v : Vertex A} (D : RealizedPositiveTarget R v)
  (E : RealizedArrivalDescriptor R D.role D.target) where
  formula : Case4SplitRightFormula (P := P) (source := source) v
  association_eq : E.association =
    formula.targetAssociation

theorem nonempty_case4SplitRightArrivalFormula
    {source : {p // p ∈ P.H}} {R : RealizedSourceRow P F.chart source}
    {v : Vertex A} (D : RealizedPositiveTarget R v)
    (E : RealizedArrivalDescriptor R D.role D.target)
    (hrole : D.role = PairCases.TargetRoleName.case4SplitRight) :
    Nonempty (Case4SplitRightArrivalFormula D E) := by
  rcases D with ⟨role, target, htarget, hv⟩
  change role = PairCases.TargetRoleName.case4SplitRight at hrole
  subst role
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case2 middle hdegree htwo hmiddleNot T normalized row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget
  | case4 middle hdegree htwo T normalized row hmiddleVertex =>
      cases row with
      | whole middleTarget hm hfour =>
          simp [RealizedSourceRow.targetAtRole] at htarget
      | orderedLow farthest hfive middleTarget lowTarget hm hl hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
          subst target
          refine ⟨{
            formula := .orderedLow T.side normalized.side_unit
              normalized.frame normalized.frame_spec normalized.source_actual
              middle (by rw [← normalized.middle_actual,
                normalized.frame.toCanonical_actual]) farthest
              (by simpa [hv] using hl)
            association_eq := ?_ }⟩
          rw [E.association_eq]
          simp [RealizedSourceRow.roleAssociation,
            Case4SplitRightFormula.targetAssociation]
      | orderedHigh farthest hsix recipients middleTarget sideTarget hm hs hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
          subst target
          refine ⟨{
            formula := .orderedHigh T.side normalized.side_unit
              normalized.frame normalized.frame_spec normalized.source_actual
              middle (by rw [← normalized.middle_actual,
                normalized.frame.toCanonical_actual]) farthest recipients
              (by simpa [hv] using hs)
            association_eq := ?_ }⟩
          rw [E.association_eq]
          simp [RealizedSourceRow.roleAssociation,
            Case4SplitRightFormula.targetAssociation]
      | pairedSplit commonFrame farthest branch rightSource hright middleTarget
          secondaryTarget hsource hm hs hne =>
          simp [RealizedSourceRow.targetAtRole] at htarget
          subst target
          refine ⟨{
            formula := .paired T.side commonFrame farthest branch rightSource
              hright hsource middleTarget.vertex hm (by simpa [hv] using hs)
            association_eq := ?_ }⟩
          rw [E.association_eq]
          simp [RealizedSourceRow.roleAssociation,
            Case4SplitRightFormula.targetAssociation]

/-- All exact data needed by the finite offset/geometry leaf.  The corrected
Case-4 association is recipient-relative, so equal association is retained
as the exact formula equation rather than incorrectly converted into an
incident-side equation. -/
structure Case2Case4SameAssociationPlacement
    {source2 source4 : {p // p ∈ P.H}}
    {R2 : RealizedSourceRow P F.chart source2}
    {R4 : RealizedSourceRow P F.chart source4} {v : Vertex A}
    (D2 : RealizedPositiveTarget R2 v)
    (D4 : RealizedPositiveTarget R4 v)
    (E2 : RealizedArrivalDescriptor R2 D2.role D2.target)
    (E4 : RealizedArrivalDescriptor R4 D4.role D4.target) where
  case2 : Case2SecondaryArrivalFormula D2 E2
  case4 : Case4SplitRightArrivalFormula D4 E4
  offset : Fin 7
  source4_at_offset : source4 = sevenShift P.next offset source2
  association_formula_eq :
    oppositeCyclicSideAssociation case2.formula.side =
      case4.formula.targetAssociation

/-- The genuine whole Case-4 analogue of the exceptional split placement.
It retains the unit incident edge and normalized frame which the
formula-derived Figure-13 argument needs. -/
structure Case2Case4WholeSameAssociationPlacement
    {source2 source4 : {p // p ∈ P.H}}
    {R2 : RealizedSourceRow P F.chart source2}
    {R4 : RealizedSourceRow P F.chart source4} {v : Vertex A}
    (D2 : RealizedPositiveTarget R2 v)
    (D4 : RealizedPositiveTarget R4 v)
    (E2 : RealizedArrivalDescriptor R2 D2.role D2.target)
    (E4 : RealizedArrivalDescriptor R4 D4.role D4.target) where
  case2 : Case2SecondaryArrivalFormula D2 E2
  case4 : Case4WholeArrivalFormula D4 E4
  offset : Fin 7
  source4_at_offset : source4 = sevenShift P.next offset source2
  opposite_sides :
    (case2.formula.side = .previous ∧
        case4.formula.incidentSide = .next) ∨
      (case2.formula.side = .next ∧
        case4.formula.incidentSide = .previous)

theorem nonempty_case2Case4WholeSameAssociationPlacement
    {source2 source4 : {p // p ∈ P.H}}
    {R2 : RealizedSourceRow P F.chart source2}
    {R4 : RealizedSourceRow P F.chart source4} {v : Vertex A}
    (D2 : RealizedPositiveTarget R2 v)
    (D4 : RealizedPositiveTarget R4 v)
    (E2 : RealizedArrivalDescriptor R2 D2.role D2.target)
    (E4 : RealizedArrivalDescriptor R4 D4.role D4.target)
    (h2 : D2.role = PairCases.TargetRoleName.case2Secondary)
    (h4 : D4.role = PairCases.TargetRoleName.case4Primary)
    (hwindow : source4.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j source2).1))
    (hassoc : E2.association = E4.association) :
    Nonempty (Case2Case4WholeSameAssociationPlacement D2 D4 E2 E4) := by
  obtain ⟨B2⟩ := nonempty_case2SecondaryArrivalFormula D2 E2 h2
  obtain ⟨B4⟩ := nonempty_case4WholeArrivalFormula D4 E4 h4
  rcases Finset.mem_image.mp hwindow with ⟨j, hj, hjEq⟩
  have hsource : source4 = sevenShift P.next j source2 := by
    apply Subtype.ext
    exact hjEq.symm
  refine ⟨{
    case2 := B2
    case4 := B4
    offset := j
    source4_at_offset := hsource
    opposite_sides := ?_ }⟩
  have hsides : oppositeCyclicSideAssociation B2.formula.side =
      cyclicSideAssociation B4.formula.incidentSide := by
    rw [← B2.association_eq, ← B4.association_eq]
    exact hassoc
  cases h2side : B2.formula.side with
  | previous =>
      cases h4side : B4.formula.incidentSide with
      | previous =>
          exfalso
          simp [oppositeCyclicSideAssociation, cyclicSideAssociation,
            h2side, h4side] at hsides
      | next => exact Or.inl ⟨rfl, rfl⟩
  | next =>
      cases h4side : B4.formula.incidentSide with
      | previous => exact Or.inr ⟨rfl, rfl⟩
      | next =>
          exfalso
          simp [oppositeCyclicSideAssociation, cyclicSideAssociation,
            h2side, h4side] at hsides

theorem nonempty_case2Case4SameAssociationPlacement
    {source2 source4 : {p // p ∈ P.H}}
    {R2 : RealizedSourceRow P F.chart source2}
    {R4 : RealizedSourceRow P F.chart source4} {v : Vertex A}
    (D2 : RealizedPositiveTarget R2 v)
    (D4 : RealizedPositiveTarget R4 v)
    (E2 : RealizedArrivalDescriptor R2 D2.role D2.target)
    (E4 : RealizedArrivalDescriptor R4 D4.role D4.target)
    (h2 : D2.role = PairCases.TargetRoleName.case2Secondary)
    (h4 : D4.role = PairCases.TargetRoleName.case4SplitRight)
    (hwindow : source4.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j source2).1))
    (hassoc : E2.association = E4.association) :
    Nonempty (Case2Case4SameAssociationPlacement D2 D4 E2 E4) := by
  obtain ⟨B2⟩ := nonempty_case2SecondaryArrivalFormula D2 E2 h2
  obtain ⟨B4⟩ := nonempty_case4SplitRightArrivalFormula D4 E4 h4
  rcases Finset.mem_image.mp hwindow with ⟨j, hj, hjEq⟩
  have hsource : source4 = sevenShift P.next j source2 := by
    apply Subtype.ext
    exact hjEq.symm
  refine ⟨{
    case2 := B2
    case4 := B4
    offset := j
    source4_at_offset := hsource
    association_formula_eq := ?_ }⟩
  rw [← B2.association_eq, ← B4.association_eq]
  exact hassoc

/-- Equal corrected associations have the exact endpoint-sensitive meaning
required by the paper's left/right charging language.  The two predicates
retain which endpoint owns a possible vertical tie. -/
lemma Case2Case4SameAssociationPlacement.case4_displacement
    {source2 source4 : {p // p ∈ P.H}}
    {R2 : RealizedSourceRow P F.chart source2}
    {R4 : RealizedSourceRow P F.chart source4} {v : Vertex A}
    {D2 : RealizedPositiveTarget R2 v}
    {D4 : RealizedPositiveTarget R4 v}
    {E2 : RealizedArrivalDescriptor R2 D2.role D2.target}
    {E4 : RealizedArrivalDescriptor R4 D4.role D4.target}
    (X : Case2Case4SameAssociationPlacement D2 D4 E2 E4) :
    (X.case2.formula.side = .previous ∧
        X.case4.formula.fromNextDisplacement) ∨
      (X.case2.formula.side = .next ∧
        X.case4.formula.fromPreviousDisplacement) := by
  have hassoc := X.association_formula_eq
  cases hside : X.case2.formula.side with
  | previous =>
      left
      refine ⟨rfl, ?_⟩
      rw [← X.case4.formula.targetAssociation_eq_fromNext_iff]
      simpa [oppositeCyclicSideAssociation, hside] using hassoc.symm
  | next =>
      right
      refine ⟨rfl, ?_⟩
      rw [← X.case4.formula.targetAssociation_eq_fromPrevious_iff]
      simpa [oppositeCyclicSideAssociation, hside] using hassoc.symm

/-- Distinct exceptional sources occupy one of the six noncentral slots in
the genuine seven-window.  This is the finite source-position dispatch
consumed by normalized-edge growth estimates. -/
lemma Case2Case4SameAssociationPlacement.offset_cases_of_source_ne
    {source2 source4 : {p // p ∈ P.H}}
    {R2 : RealizedSourceRow P F.chart source2}
    {R4 : RealizedSourceRow P F.chart source4} {v : Vertex A}
    {D2 : RealizedPositiveTarget R2 v}
    {D4 : RealizedPositiveTarget R4 v}
    {E2 : RealizedArrivalDescriptor R2 D2.role D2.target}
    {E4 : RealizedArrivalDescriptor R4 D4.role D4.target}
    (X : Case2Case4SameAssociationPlacement D2 D4 E2 E4)
    (hne : source2 ≠ source4) :
    X.offset = 0 ∨ X.offset = 1 ∨ X.offset = 2 ∨
      X.offset = 4 ∨ X.offset = 5 ∨ X.offset = 6 := by
  by_cases h0 : X.offset = 0
  · exact Or.inl h0
  by_cases h1 : X.offset = 1
  · exact Or.inr (Or.inl h1)
  by_cases h2 : X.offset = 2
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : X.offset = 3
  · exfalso
    apply hne
    simpa [h3] using X.source4_at_offset.symm
  by_cases h4 : X.offset = 4
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  by_cases h5 : X.offset = 5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  right; right; right; right; right
  apply Fin.ext
  omega

/-- Orbit-form version of the six noncentral placements. -/
lemma Case2Case4SameAssociationPlacement.source_orbit_cases_of_ne
    {source2 source4 : {p // p ∈ P.H}}
    {R2 : RealizedSourceRow P F.chart source2}
    {R4 : RealizedSourceRow P F.chart source4} {v : Vertex A}
    {D2 : RealizedPositiveTarget R2 v}
    {D4 : RealizedPositiveTarget R4 v}
    {E2 : RealizedArrivalDescriptor R2 D2.role D2.target}
    {E4 : RealizedArrivalDescriptor R4 D4.role D4.target}
    (X : Case2Case4SameAssociationPlacement D2 D4 E2 E4)
    (hne : source2 ≠ source4) :
    source4 = (P.next⁻¹ ^ 3) source2 ∨
      source4 = (P.next⁻¹ ^ 2) source2 ∨
      source4 = P.next⁻¹ source2 ∨
      source4 = P.next source2 ∨
      source4 = (P.next ^ 2) source2 ∨
      source4 = (P.next ^ 3) source2 := by
  rcases X.offset_cases_of_source_ne hne with h | h | h | h | h | h
  · left
    simpa [h] using X.source4_at_offset
  · right; left
    simpa [h] using X.source4_at_offset
  · right; right; left
    simpa [h] using X.source4_at_offset
  · right; right; right; left
    simpa [h] using X.source4_at_offset
  · right; right; right; right; left
    simpa [h] using X.source4_at_offset
  · right; right; right; right; right
    simpa [h] using X.source4_at_offset

/-- The same finite placement classification for a whole Case-4
competitor. -/
lemma Case2Case4WholeSameAssociationPlacement.offset_cases_of_source_ne
    {source2 source4 : {p // p ∈ P.H}}
    {R2 : RealizedSourceRow P F.chart source2}
    {R4 : RealizedSourceRow P F.chart source4} {v : Vertex A}
    {D2 : RealizedPositiveTarget R2 v}
    {D4 : RealizedPositiveTarget R4 v}
    {E2 : RealizedArrivalDescriptor R2 D2.role D2.target}
    {E4 : RealizedArrivalDescriptor R4 D4.role D4.target}
    (X : Case2Case4WholeSameAssociationPlacement D2 D4 E2 E4)
    (hne : source2 ≠ source4) :
    X.offset = 0 ∨ X.offset = 1 ∨ X.offset = 2 ∨
      X.offset = 4 ∨ X.offset = 5 ∨ X.offset = 6 := by
  by_cases h0 : X.offset = 0
  · exact Or.inl h0
  by_cases h1 : X.offset = 1
  · exact Or.inr (Or.inl h1)
  by_cases h2 : X.offset = 2
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : X.offset = 3
  · exfalso
    apply hne
    simpa [h3] using X.source4_at_offset.symm
  by_cases h4 : X.offset = 4
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  by_cases h5 : X.offset = 5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  right; right; right; right; right
  apply Fin.ext
  omega

lemma Case2Case4WholeSameAssociationPlacement.source_orbit_cases_of_ne
    {source2 source4 : {p // p ∈ P.H}}
    {R2 : RealizedSourceRow P F.chart source2}
    {R4 : RealizedSourceRow P F.chart source4} {v : Vertex A}
    {D2 : RealizedPositiveTarget R2 v}
    {D4 : RealizedPositiveTarget R4 v}
    {E2 : RealizedArrivalDescriptor R2 D2.role D2.target}
    {E4 : RealizedArrivalDescriptor R4 D4.role D4.target}
    (X : Case2Case4WholeSameAssociationPlacement D2 D4 E2 E4)
    (hne : source2 ≠ source4) :
    source4 = (P.next⁻¹ ^ 3) source2 ∨
      source4 = (P.next⁻¹ ^ 2) source2 ∨
      source4 = P.next⁻¹ source2 ∨
      source4 = P.next source2 ∨
      source4 = (P.next ^ 2) source2 ∨
      source4 = (P.next ^ 3) source2 := by
  rcases X.offset_cases_of_source_ne hne with h | h | h | h | h | h
  · left
    simpa [h] using X.source4_at_offset
  · right; left
    simpa [h] using X.source4_at_offset
  · right; right; left
    simpa [h] using X.source4_at_offset
  · right; right; right; left
    simpa [h] using X.source4_at_offset
  · right; right; right; right; left
    simpa [h] using X.source4_at_offset
  · right; right; right; right; right
    simpa [h] using X.source4_at_offset

lemma opposite_side_pair_of_association_eq
    (case2Side case4Side : CyclicSide)
    (h : oppositeCyclicSideAssociation case2Side =
      cyclicSideAssociation case4Side) :
    (case2Side = .previous ∧ case4Side = .next) ∨
      (case2Side = .next ∧ case4Side = .previous) := by
  cases case2Side <;> cases case4Side <;>
    simp_all [oppositeCyclicSideAssociation, cyclicSideAssociation]

private lemma Case4WholeFormula.source_coordinate
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4WholeFormula (P := P) (source := source) v) :
    D.edgeFrame.toCanonical source.1 = Erdos957Cases24.Case2.u := by
  rw [← D.source_actual, D.edgeFrame.toCanonical_actual]

private lemma Case4WholeFormula.side_coordinate
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4WholeFormula (P := P) (source := source) v) :
    D.edgeFrame.toCanonical D.side = Erdos957Cases24.Case2.uPrev := by
  rw [← D.side_actual, D.edgeFrame.toCanonical_actual]

lemma Case4WholeFormula.source_target_adj
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4WholeFormula (P := P) (source := source) v) :
    (unitDistanceGraph A).Adj source.1 v := by
  change dist (source.1 : Point) (v : Point) = 1
  rw [← D.edgeFrame.dist_eq, D.source_coordinate,
    D.target_edge_coordinate, Erdos957Cases24.Case2.dist_u_v]

lemma Case4WholeFormula.side_target_adj
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4WholeFormula (P := P) (source := source) v) :
    (unitDistanceGraph A).Adj D.side v := by
  change dist (D.side : Point) (v : Point) = 1
  rw [← D.edgeFrame.dist_eq, D.side_coordinate,
    D.target_edge_coordinate, Erdos957Cases24.Case2.dist_uPrev_v]

lemma Case4WholeFormula.side_source_adj
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4WholeFormula (P := P) (source := source) v) :
    (unitDistanceGraph A).Adj D.side source.1 := by
  change dist (D.side : Point) (source.1 : Point) = 1
  rw [← D.edgeFrame.dist_eq, D.side_coordinate,
    D.source_coordinate, Erdos957Cases24.Case2.dist_uPrev_u]

/-- Exhaustive formula-sensitive classification of an arbitrary realized
arrival.  Seven roles are actual source edges; the only two non-direct
possibilities retain their exact Case-2 or Case-4 descriptors. -/
inductive RealizedHitFormula
    {source : {p // p ∈ P.H}} (R : RealizedSourceRow P F.chart source)
    (v : Vertex A) : Type
  | direct
      (D : RealizedPositiveTarget R v)
      (role_is_direct : IsDirectTargetRole D.role)
      (source_adj_target : (unitDistanceGraph A).Adj source.1 v)
  | case2Secondary
      (D : RealizedPositiveTarget R v)
      (role_eq : D.role = PairCases.TargetRoleName.case2Secondary)
      (formula : Case2SecondaryFormula (P := P) (source := source) v)
  | case4SplitRight
      (D : RealizedPositiveTarget R v)
      (role_eq : D.role = PairCases.TargetRoleName.case4SplitRight)
      (formula : Case4SplitRightFormula (P := P) (source := source) v)

private lemma no_realized_case4SecondaryLow
    {source : {p // p ∈ P.H}} {R : RealizedSourceRow P F.chart source}
    {v : Vertex A} (D : RealizedPositiveTarget R v)
    (hrole : D.role = PairCases.TargetRoleName.case4SecondaryLow) : False := by
  rcases D with ⟨role, target, htarget, hv⟩
  change role = PairCases.TargetRoleName.case4SecondaryLow at hrole
  subst role
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case2 middle hdegree htwo hmiddleNot twoExtreme normalized row =>
      simp [RealizedSourceRow.targetAtRole] at htarget
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget
  | case4 middle hdegree htwo twoExtreme normalized row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.targetAtRole] at htarget

/-- Every positive realized hit has exactly one of the formula shapes needed
by the remaining finite collision dispatch. -/
theorem nonempty_realizedHitFormula
    {source : {p // p ∈ P.H}} (R : RealizedSourceRow P F.chart source)
    {v : Vertex A} (hpos : 0 < R.localCase.tokens v) :
    Nonempty (RealizedHitFormula R v) := by
  obtain ⟨D⟩ := R.positive_target_role hpos
  rcases h : D.role with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)
  · exact ⟨.direct D (by simp [IsDirectTargetRole, h])
      (D.adj_source_of_directRole (by simp [IsDirectTargetRole, h]))⟩
  · exact ⟨.direct D (by simp [IsDirectTargetRole, h])
      (D.adj_source_of_directRole (by simp [IsDirectTargetRole, h]))⟩
  · exact ⟨.direct D (by simp [IsDirectTargetRole, h])
      (D.adj_source_of_directRole (by simp [IsDirectTargetRole, h]))⟩
  · obtain ⟨formula⟩ := exists_case2SecondaryFormula D h
    exact ⟨.case2Secondary D h formula⟩
  · exact ⟨.direct D (by simp [IsDirectTargetRole, h])
      (D.adj_source_of_directRole (by simp [IsDirectTargetRole, h]))⟩
  · exact ⟨.direct D (by simp [IsDirectTargetRole, h])
      (D.adj_source_of_directRole (by simp [IsDirectTargetRole, h]))⟩
  · exact ⟨.direct D (by simp [IsDirectTargetRole, h])
      (D.adj_source_of_directRole (by simp [IsDirectTargetRole, h]))⟩
  · exact (no_realized_case4SecondaryLow D h).elim
  · exact ⟨.direct D (by simp [IsDirectTargetRole, h])
      (D.adj_source_of_directRole (by simp [IsDirectTargetRole, h]))⟩
  · obtain ⟨formula⟩ := exists_case4SplitRightFormula D h
    exact ⟨.case4SplitRight D h formula⟩

/-! ## The checked Figure-13 adapter

The production analytic theorem is stated in ordinary pair coordinates.
The record below is the strictly smaller geometric bridge still required
from the `(2,4)` role dispatch: it names the three actual vertices, their
unit incidences, the old Case-2 lattice height, and the two strict
above-apex inequalities.  Strict negativity of the hull endpoints is then
derived here from the anchored Case-2 support frame.
-/

/-- Ordinary pair coordinates associated to the anchored rigid edge frame. -/
structure AnchoredCase2RoleTriple
    (rows : HasRealizedSourceRows P W F.chart)
    (s t u : Source P W) (v : Vertex A) where
  anchor : RealizedPositiveTarget (rows s.1 s.property) v
  first : RealizedPositiveTarget (rows t.1 t.property) v
  second : RealizedPositiveTarget (rows u.1 u.property) v
  anchor_role : anchor.role = PairCases.TargetRoleName.case2Secondary
  firstOffset : Fin 7
  secondOffset : Fin 7
  first_source_at_offset : sourceIndex P W t.1 t.property =
    sevenShift P.next firstOffset (sourceIndex P W s.1 s.property)
  second_source_at_offset : sourceIndex P W u.1 u.property =
    sevenShift P.next secondOffset (sourceIndex P W s.1 s.property)
  anchor_ne_first : s ≠ t
  anchor_ne_second : s ≠ u
  first_ne_second : t ≠ u

/-- The same anchored triple with the formula-derived side/weight descriptor
for each of its three retained positive targets. -/
structure AnchoredCase2ArrivalTriple
    {rows : HasRealizedSourceRows P W F.chart}
    {s t u : Source P W} {v : Vertex A}
    (T : AnchoredCase2RoleTriple rows s t u v) where
  anchorDescriptor : RealizedArrivalDescriptor
    (rows s.1 s.property) T.anchor.role T.anchor.target
  firstDescriptor : RealizedArrivalDescriptor
    (rows t.1 t.property) T.first.role T.first.target
  secondDescriptor : RealizedArrivalDescriptor
    (rows u.1 u.property) T.second.role T.second.target

/-- Arrival descriptors are chosen from the exact three row slots already
stored by the anchored triple; no new rows or targets are selected. -/
noncomputable def AnchoredCase2RoleTriple.withArrivalDescriptors
    {rows : HasRealizedSourceRows P W F.chart}
    {s t u : Source P W} {v : Vertex A}
    (T : AnchoredCase2RoleTriple rows s t u v) :
    AnchoredCase2ArrivalTriple T :=
  { anchorDescriptor := Classical.choice T.anchor.arrivalDescriptor
    firstDescriptor := Classical.choice T.first.arrivalDescriptor
    secondDescriptor := Classical.choice T.second.arrivalDescriptor }

lemma AnchoredCase2ArrivalTriple.association_pair
    {rows : HasRealizedSourceRows P W F.chart}
    {s t u : Source P W} {v : Vertex A}
    {T : AnchoredCase2RoleTriple rows s t u v}
    (E : AnchoredCase2ArrivalTriple T) :
    E.anchorDescriptor.association = E.firstDescriptor.association ∨
      E.anchorDescriptor.association = E.secondDescriptor.association ∨
      E.firstDescriptor.association = E.secondDescriptor.association := by
  cases E.anchorDescriptor.association <;>
    cases E.firstDescriptor.association <;>
    cases E.secondDescriptor.association <;> simp

/-- Recover the literal two offsets from the membership-style window
hypotheses used by `SecondaryRoleCollisionKernels`. -/
theorem nonempty_anchoredCase2RoleTriple
    {rows : HasRealizedSourceRows P W F.chart}
    {s t u : Source P W} {v : Vertex A}
    (Ds : RealizedPositiveTarget (rows s.1 s.property) v)
    (Dt : RealizedPositiveTarget (rows t.1 t.property) v)
    (Du : RealizedPositiveTarget (rows u.1 u.property) v)
    (hanchor : Ds.role = PairCases.TargetRoleName.case2Secondary)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    Nonempty (AnchoredCase2RoleTriple rows s t u v) := by
  rcases Finset.mem_image.mp htWindow with ⟨jt, hjt, ht⟩
  rcases Finset.mem_image.mp huWindow with ⟨ju, hju, hu⟩
  refine ⟨{
    anchor := Ds
    first := Dt
    second := Du
    anchor_role := hanchor
    firstOffset := jt
    secondOffset := ju
    first_source_at_offset := ?_
    second_source_at_offset := ?_
    anchor_ne_first := hst
    anchor_ne_second := hsu
    first_ne_second := htu }⟩
  · apply Subtype.ext
    exact ht.symm
  · apply Subtype.ext
    exact hu.symm

end Erdos957Case2RoleUniqueness

#print axioms Erdos957Case2RoleUniqueness.Case2Case4SameAssociationPlacement.case4_displacement
