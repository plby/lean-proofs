import ErdosProblems.Erdos957.Case13RealizedRows
import ErdosProblems.Erdos957.Case2RealizedRows
import ErdosProblems.Erdos957.RealizationWindow
import ErdosProblems.Erdos957.PartnerMiddleChoice

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957CoherentRealizedRows

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CaseClassification.ActualCase24Rows

abbrev Point := Erdos957GeometryCore.Point

namespace CommonCase4

open Erdos957CaseClassification.ActualCase24Rows

/-- A Case-4 branch keyed only by the canonical directed hull edge and the
actual equilateral middle.  In particular its type contains neither a
choice of emitting endpoint nor a reflected source chart, so the two
endpoints of one hull edge can literally share the same selected value. -/
structure EdgeCase4Branch
    {A : Finset Point} (P : CyclicHullData A)
    (base : {p // p ∈ P.H}) (middle : Vertex A) where
  edge_unit : dist (base.1.1 : Point) ((P.next base).1.1 : Point) = 1
  middle_coordinate :
    (Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      base.1.1 (P.next base).1.1 edge_unit).toCanonical middle =
        Erdos957Cases24.Case2.v
  strict_support : Erdos957Case24Bridge.StrictlyBelowOutside
    ((Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      base.1.1 (P.next base).1.1 edge_unit).image A)
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u}
  farthest : Erdos957Case24Bridge.Case4.FarthestBelowData
    ((Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      base.1.1 (P.next base).1.1 edge_unit).image A)
  branch : Erdos957Case24Bridge.Case4.FarthestBranchData
    ((Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      base.1.1 (P.next base).1.1 edge_unit).image A) farthest

/-- The literal terminal rigid chart carried by a source-free edge branch. -/
def EdgeCase4Branch.frame
    {A : Finset Point} {P : CyclicHullData A}
    {base : {p // p ∈ P.H}} {middle : Vertex A}
    (B : EdgeCase4Branch P base middle) :
    Erdos957Case24Bridge.Framed.RigidChart :=
  Erdos957EdgeFrame.terminalUnitEdgeRigidChart
    base.1.1 (P.next base).1.1 B.edge_unit

/-- Pull the branch-selected recipient back through the common directed-edge
chart.  This definition is independent of which endpoint is currently the
emitting source. -/
def EdgeCase4Branch.actualRecipient
    {A : Finset Point} {P : CyclicHullData A}
    {base : {p // p ∈ P.H}} {middle : Vertex A}
    (B : EdgeCase4Branch P base middle) (rightSource : Bool) : Vertex A :=
  let q := B.branch.sourceRecipient rightSource
  ⟨B.frame.actual q,
    B.frame.mem_image_iff.mp
      ((Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        (B.branch.sourceRecipient_mem rightSource)).1)⟩

/-- Exact output of the shared-branch Case-4 row constructor.  In addition
to the actual row it retains its two local targets, their literal
`pairedSplit` shape, and their underlying vertices.  This is the data that
must survive dependent choice in order to compare the two endpoints. -/
structure EdgePairedActualRowData
    {A : Finset Point} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (middle : Vertex A) (T : TwoExtremeCyclicWitness P source middle)
    (N : TwoExtremeNormalizedFrame source middle T)
    (B : EdgeCase4Branch P (case4PairEdgeBase T) middle)
    (rightSource : Bool) where
  middleTarget : LocalTarget P F.chart source
  secondaryTarget : LocalTarget P F.chart source
  row : Case4ActualRow F.chart source middle T N
  row_shape :
    ∃ (hright : rightSource = case4SourceIsRight T)
      (hsource : B.frame.toCanonical source.1 =
        Erdos957Case24Bridge.Case4.sideSource rightSource)
      (hmiddle : B.frame.toCanonical middleTarget.vertex =
        Erdos957Cases24.Case2.v)
      (hsecondary : B.frame.toCanonical secondaryTarget.vertex =
        B.branch.sourceRecipient rightSource)
      (hne : middleTarget.vertex ≠ secondaryTarget.vertex),
      row = .pairedSplit B.frame B.farthest B.branch rightSource hright
        middleTarget secondaryTarget hsource hmiddle hsecondary hne
  middle_vertex : middleTarget.vertex = middle
  secondary_vertex : secondaryTarget.vertex = B.actualRecipient rightSource

/-- The retained middle is also the middle target of the erased actual row. -/
theorem EdgePairedActualRowData.row_middle_vertex
    {A : Finset Point} {P : CyclicHullData A}
    {F : P.FlatAlignedFrameData} {source : {p // p ∈ P.H}}
    {middle : Vertex A} {T : TwoExtremeCyclicWitness P source middle}
    {N : TwoExtremeNormalizedFrame source middle T}
    {B : EdgeCase4Branch P (case4PairEdgeBase T) middle}
    {rightSource : Bool}
    (D : EdgePairedActualRowData F source middle T N B rightSource) :
    D.row.middleTarget.vertex = middle := by
  obtain ⟨_, _, _, _, _, hrow⟩ := D.row_shape
  rw [hrow]
  exact D.middle_vertex

/-- A Case-4 branch selected in the literal directed-edge chart shared by
both endpoints.  Unlike `Case4HullPairBranch`, its type does not contain a
source-reflected normalized frame. -/
structure CommonCase4HullPairBranch
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {middle : Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    (E : TwoExtremeCommonPairFrame source middle T) where
  farthest : Erdos957Case24Bridge.Case4.FarthestBelowData (E.frame.image A)
  branch : Erdos957Case24Bridge.Case4.FarthestBranchData
    (E.frame.image A) farthest

/-- Degree five at the shared equilateral middle supplies an ordered branch
in the common pair chart. -/
theorem nonempty_commonCase4HullPairBranch
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} {source : {p // p ∈ P.H}}
    {middle : Vertex A} {T : TwoExtremeCyclicWitness P source middle}
    (E : TwoExtremeCommonPairFrame source middle T)
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 5) :
    Nonempty (CommonCase4HullPairBranch E) := by
  have huPrevA : Erdos957Cases24.Case2.uPrev ∈ E.frame.image A := by
    apply E.frame.mem_image_iff.mpr
    cases h : case4SourceIsRight T
    · have heq : E.frame.actual Erdos957Cases24.Case2.uPrev = source.1 := by
        apply E.frame.toCanonical.injective
        rw [E.frame.toCanonical_actual, E.source_coordinate]
        simp [h, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact source.1.property
    · have heq : E.frame.actual Erdos957Cases24.Case2.uPrev =
          cyclicSideVertex P source T.side := by
        apply E.frame.toCanonical.injective
        rw [E.frame.toCanonical_actual, E.side_coordinate]
        simp [h, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (cyclicSideVertex P source T.side).property
  have huA : Erdos957Cases24.Case2.u ∈ E.frame.image A := by
    apply E.frame.mem_image_iff.mpr
    cases h : case4SourceIsRight T
    · have heq : E.frame.actual Erdos957Cases24.Case2.u =
          cyclicSideVertex P source T.side := by
        apply E.frame.toCanonical.injective
        rw [E.frame.toCanonical_actual, E.side_coordinate]
        simp [h, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (cyclicSideVertex P source T.side).property
    · have heq : E.frame.actual Erdos957Cases24.Case2.u = source.1 := by
        apply E.frame.toCanonical.injective
        rw [E.frame.toCanonical_actual, E.source_coordinate]
        simp [h, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact source.1.property
  have hvA : Erdos957Cases24.Case4.v ∈ E.frame.image A := by
    apply E.frame.mem_image_iff.mpr
    rw [Erdos957Cases24.Case4.v, E.middle_actual]
    exact middle.property
  have hvDegree : Erdos957Case24Bridge.unitDegree (E.frame.image A)
      Erdos957Cases24.Case4.v = 5 := by
    rw [E.frame.unitDegree_image_actual A, Erdos957Cases24.Case4.v,
      E.middle_actual]
    rw [← graph_degree_eq_unitDegree]
    exact hmiddleDegree
  obtain ⟨D⟩ := Erdos957Case24Bridge.Case4.exists_farthestBelowData
    huPrevA huA hvDegree
  obtain ⟨B⟩ := Erdos957ContactGraph.nonempty_farthestBranchData
    (E.frame.image_oneSeparated hA) E.strict_support hvA huPrevA huA
      hvDegree D
  exact ⟨⟨D, B⟩⟩

/-- Forgetting the endpoint-indexed wrapper produces the source-free branch
on the canonical directed edge. -/
theorem nonempty_edgeCase4Branch
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} {source : {p // p ∈ P.H}}
    {middle : Vertex A} {T : TwoExtremeCyclicWitness P source middle}
    (E : TwoExtremeCommonPairFrame source middle T)
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 5) :
    Nonempty (EdgeCase4Branch P (case4PairEdgeBase T) middle) := by
  obtain ⟨B⟩ := nonempty_commonCase4HullPairBranch hA E hmiddleDegree
  exact ⟨{
    edge_unit := E.edge_unit
    middle_coordinate := E.middle_coordinate
    strict_support := E.strict_support
    farthest := B.farthest
    branch := B.branch }⟩

/-- A canonical selection from a source-free edge/middle key.  The proof of
nonemptiness is irrelevant, hence equal edge and middle keys force literally
the same selected branch. -/
noncomputable def selectedEdgeCase4Branch
    {A : Finset Point} {P : CyclicHullData A}
    {base : {p // p ∈ P.H}} {middle : Vertex A}
    (h : Nonempty (EdgeCase4Branch P base middle)) :
    EdgeCase4Branch P base middle :=
  Classical.choice h

/-- Canonical edge-branch selection is invariant under equal directed-edge
and actual-middle keys.  This packages the dependent transports once, so
endpoint coherence never compares proof terms or separately chosen frames. -/
theorem selectedEdgeCase4Branch_actualRecipient_eq_of_keys_eq
    {A : Finset Point} {P : CyclicHullData A}
    {base₁ base₂ : {p // p ∈ P.H}} {middle₁ middle₂ : Vertex A}
    (hbase : base₁ = base₂) (hmiddle : middle₁ = middle₂)
    (h₁ : Nonempty (EdgeCase4Branch P base₁ middle₁))
    (h₂ : Nonempty (EdgeCase4Branch P base₂ middle₂))
    (rightSource : Bool) :
    (selectedEdgeCase4Branch h₁).actualRecipient rightSource =
      (selectedEdgeCase4Branch h₂).actualRecipient rightSource := by
  cases hbase
  cases hmiddle
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  cases hh
  rfl

/-- The formula-derived endpoint association is likewise invariant under
equal source-free edge/middle keys.  This is the association-level companion
to `selectedEdgeCase4Branch_actualRecipient_eq_of_keys_eq`. -/
theorem selectedEdgeCase4Branch_association_eq_of_keys_eq
    {A : Finset Point} {P : CyclicHullData A}
    {base₁ base₂ : {p // p ∈ P.H}} {middle₁ middle₂ : Vertex A}
    (hbase : base₁ = base₂) (hmiddle : middle₁ = middle₂)
    (h₁ : Nonempty (EdgeCase4Branch P base₁ middle₁))
    (h₂ : Nonempty (EdgeCase4Branch P base₂ middle₂))
    (rightSource : Bool) :
    commonPairHorizontalAssociation
        (selectedEdgeCase4Branch h₁).branch rightSource =
      commonPairHorizontalAssociation
        (selectedEdgeCase4Branch h₂).branch rightSource := by
  cases hbase
  cases hmiddle
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  cases hh
  rfl

/-- Construct one endpoint's exact split row from the branch selected on
the source-free directed edge.  The conclusion exposes the literal row
shape and both pulled-back vertices, so no information is lost behind the
existential row constructor in `CaseClassification`. -/
theorem nonempty_edgePairedActualRowData
    {A : Finset Point} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hflat : P.IsFlat source) (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (F.chart.coord source middle))
    (T : TwoExtremeCyclicWitness P source middle)
    (N : TwoExtremeNormalizedFrame source middle T)
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 5)
    (B : EdgeCase4Branch P (case4PairEdgeBase T) middle)
    (rightSource : Bool)
    (hrightSource : rightSource = case4SourceIsRight T)
    (hsourceCommon : B.frame.toCanonical source.1 =
      Erdos957Case24Bridge.Case4.sideSource rightSource)
    (hsideCommon : B.frame.toCanonical
      (cyclicSideVertex P source T.side) =
        Erdos957Case24Bridge.Case4.sideSource (!rightSource))
    (hmiddleCommon : B.frame.toCanonical middle =
      Erdos957Cases24.Case2.v) :
    Nonempty (EdgePairedActualRowData F source middle T N B rightSource) := by
  let q := B.branch.sourceRecipient rightSource
  have hqResidual : q ∈ Erdos957Case24Bridge.Case4.residualNeighbors
      (B.frame.image A) := B.branch.sourceRecipient_mem rightSource
  have hqImage : q ∈ B.frame.image A :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqResidual).1
  have hqA : B.frame.actual q ∈ A := B.frame.mem_image_iff.mp hqImage
  let qVertex := actualVertex B.frame q hqA
  have hmiddleNot : middle ∉ P.H :=
    middle_not_mem_hull_of_local_window F source hflat hwindow middle
      hsourceMiddle hmiddleCone
  have hmiddleUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (F.chart.coord source middle) = 1 := by
    rw [show Erdos957Cases13.origin = F.chart.coord source source.1 by
      simpa [Erdos957Cases13.origin] using
        (F.chart.coord_source source).symm]
    rw [F.chart.sqDist_coord]
    change dist (source.1 : Point) (middle : Point) = 1 at hsourceMiddle
    rw [hsourceMiddle]
    norm_num
  have hmiddleX :=
    Erdos957MiddleLocalization.abs_fst_lt_half_of_unit_of_middleCone
      hmiddleUnit hmiddleCone
  have hmiddleHorizontal : |(F.chart.coord source middle).1| ≤ (7 : ℝ) / 4 := by
    rw [abs_le]
    constructor <;> linarith
  let middleTarget := LocalTarget.ofPathOfAbs
    (by omega : (unitDistanceGraph A).degree middle ≤ 5)
    hmiddleNot (Or.inl hsourceMiddle) hmiddleHorizontal
  have hqDist : dist Erdos957Cases24.Case2.v q = 1 :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqResidual).2.1
  have hmiddleQ : (unitDistanceGraph A).Adj middle qVertex := by
    change dist (middle : Point) (B.frame.actual q) = 1
    rw [← B.frame.dist_eq, hmiddleCommon, B.frame.toCanonical_actual, hqDist]
  have hqNeSideSource (b : Bool) :
      q ≠ Erdos957Case24Bridge.Case4.sideSource b := by
    cases b
    · exact (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        hqResidual).2.2.1
    · exact (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        hqResidual).2.2.2
  have hqNeSource : qVertex ≠ source.1 := by
    intro h
    apply hqNeSideSource rightSource
    rw [← hsourceCommon]
    rw [← B.frame.toCanonical_actual q]
    exact congrArg (fun x : Vertex A ↦ B.frame.toCanonical (x : Point)) h
  have hqNeSide : qVertex ≠ cyclicSideVertex P source T.side := by
    intro h
    apply hqNeSideSource (!rightSource)
    rw [← hsideCommon]
    rw [← B.frame.toCanonical_actual q]
    exact congrArg (fun x : Vertex A ↦ B.frame.toCanonical (x : Point)) h
  have hqNot : qVertex ∉ P.H :=
    not_mem_hull_of_adj_middle_of_twoExtreme T hmiddleQ hqNeSource hqNeSide
  have hqDegree : (unitDistanceGraph A).degree qVertex ≤ 5 := by
    rw [graph_degree_eq_unitDegree]
    change Erdos957Case24Bridge.unitDegree A (B.frame.actual q) ≤ 5
    rw [← B.frame.unitDegree_image_actual A q]
    exact B.branch.sourceRecipient_degree_le_five rightSource
  have hqPath : WithinTwoUnitEdges source.1 qVertex :=
    Or.inr ⟨middle, hsourceMiddle, hmiddleQ⟩
  have hdiff := Erdos957MiddleLocalization.abs_fst_sub_le_one_of_adj
    F.chart source hmiddleQ
  have hqHorizontal : |(F.chart.coord source qVertex).1| ≤ (7 : ℝ) / 4 := by
    rw [abs_le] at hdiff ⊢
    constructor <;> linarith
  let qTarget := LocalTarget.ofPathOfAbs hqDegree hqNot hqPath hqHorizontal
  have hqCommon : B.frame.toCanonical qTarget.vertex = q := by
    change B.frame.toCanonical (B.frame.actual q) = q
    exact B.frame.toCanonical_actual q
  have hne : middleTarget.vertex ≠ qTarget.vertex := hmiddleQ.ne
  let row : Case4ActualRow F.chart source middle T N :=
    .pairedSplit B.frame B.farthest B.branch rightSource hrightSource
      middleTarget qTarget hsourceCommon hmiddleCommon hqCommon hne
  refine ⟨{
    middleTarget := middleTarget
    secondaryTarget := qTarget
    row := row
    row_shape := ?_
    middle_vertex := rfl
    secondary_vertex := ?_ }⟩
  · exact ⟨hrightSource, hsourceCommon, hmiddleCommon, hqCommon, hne, rfl⟩
  · apply Subtype.ext
    rfl

/-- The actual source-specific recipient of a shared pair branch. -/
def CommonCase4HullPairBranch.actualRecipient
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {middle : Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    {E : TwoExtremeCommonPairFrame source middle T}
    (B : CommonCase4HullPairBranch E) (rightSource : Bool) : Vertex A :=
  let q := B.branch.sourceRecipient rightSource
  ⟨E.frame.actual q,
    E.frame.mem_image_iff.mp
      ((Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        (B.branch.sourceRecipient_mem rightSource)).1)⟩

/-- Equality of the two complementary branch recipients can occur only in
the low-farthest branch.  In the high branch they are the retained distinct
left and right contacts. -/
theorem farthestBranchData_eq_low_of_complementaryRecipients_eq
    {A : Finset Erdos957Cases24.Point}
    {D : Erdos957Case24Bridge.Case4.FarthestBelowData A}
    (B : Erdos957Case24Bridge.Case4.FarthestBranchData A D)
    (rightSource : Bool)
    (h : B.sourceRecipient rightSource =
      B.sourceRecipient (!rightSource)) :
    ∃ hdegree : Erdos957Case24Bridge.unitDegree A D.point ≤ 5,
      B = .low hdegree := by
  cases B with
  | low hdegree => exact ⟨hdegree, rfl⟩
  | high hdegree recipients =>
      cases rightSource
      · simp only [Bool.not_false,
          Erdos957Case24Bridge.Case4.FarthestBranchData.sourceRecipient_high,
          Erdos957Case24Bridge.Case4.HighFarthestRecipients.sourceRecipient_false,
          Erdos957Case24Bridge.Case4.HighFarthestRecipients.sourceRecipient_true]
          at h
        exact (recipients.distinct h).elim
      · simp only [Bool.not_true,
          Erdos957Case24Bridge.Case4.FarthestBranchData.sourceRecipient_high,
          Erdos957Case24Bridge.Case4.HighFarthestRecipients.sourceRecipient_false,
          Erdos957Case24Bridge.Case4.HighFarthestRecipients.sourceRecipient_true]
          at h
        exact (recipients.distinct h.symm).elim

/-- Pulled-back version for the actual vertices retained by a common
Case-4 hull-pair branch. -/
theorem CommonCase4HullPairBranch.eq_low_of_actualRecipients_eq
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {middle : Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    {E : TwoExtremeCommonPairFrame source middle T}
    (B : CommonCase4HullPairBranch E) (rightSource : Bool)
    (h : B.actualRecipient rightSource =
      B.actualRecipient (!rightSource)) :
    ∃ hdegree : Erdos957Case24Bridge.unitDegree
        (E.frame.image A) B.farthest.point ≤ 5,
      B.branch = .low hdegree := by
  have hactual := congrArg (fun q : Vertex A ↦ (q : Point)) h
  change E.frame.actual (B.branch.sourceRecipient rightSource) =
    E.frame.actual (B.branch.sourceRecipient (!rightSource)) at hactual
  have hcanonical := E.frame.actual_injective hactual
  exact farthestBranchData_eq_low_of_complementaryRecipients_eq
    B.branch rightSource hcanonical

/-- Exact data retained by the degree-at-most-four Case-4 row. -/
structure Case4WholeActualRowData
    {A : Finset Point} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (middle : Vertex A) (T : TwoExtremeCyclicWitness P source middle)
    (N : TwoExtremeNormalizedFrame source middle T) where
  middleTarget : LocalTarget P F.chart source
  middle_edge_coordinate :
    N.frame.toCanonical middleTarget.vertex = Erdos957Cases24.Case2.v
  middle_degree_le_four : (unitDistanceGraph A).degree middleTarget.vertex ≤ 4
  middle_vertex : middleTarget.vertex = middle

def Case4WholeActualRowData.row
    {A : Finset Point} {P : CyclicHullData A}
    {F : P.FlatAlignedFrameData} {source : {p // p ∈ P.H}}
    {middle : Vertex A} {T : TwoExtremeCyclicWitness P source middle}
    {N : TwoExtremeNormalizedFrame source middle T}
    (D : Case4WholeActualRowData F source middle T N) :
    Case4ActualRow F.chart source middle T N :=
  .whole D.middleTarget D.middle_edge_coordinate D.middle_degree_le_four

/-- The degree-at-most-four Case-4 row needs only the actual middle, and its
exact `whole` shape is retained. -/
theorem nonempty_case4WholeActualRowData
    {A : Finset Point} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hflat : P.IsFlat source) (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (F.chart.coord source middle))
    (T : TwoExtremeCyclicWitness P source middle)
    (N : TwoExtremeNormalizedFrame source middle T)
    (hmiddleDegree : (unitDistanceGraph A).degree middle ≤ 4) :
    Nonempty (Case4WholeActualRowData F source middle T N) := by
  have hmiddleNot : middle ∉ P.H :=
    middle_not_mem_hull_of_local_window F source hflat hwindow middle
      hsourceMiddle hmiddleCone
  have hmiddleUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (F.chart.coord source middle) = 1 := by
    rw [show Erdos957Cases13.origin = F.chart.coord source source.1 by
      simpa [Erdos957Cases13.origin] using
        (F.chart.coord_source source).symm]
    rw [F.chart.sqDist_coord]
    change dist (source.1 : Point) (middle : Point) = 1 at hsourceMiddle
    rw [hsourceMiddle]
    norm_num
  have hmiddleX :=
    Erdos957MiddleLocalization.abs_fst_lt_half_of_unit_of_middleCone
      hmiddleUnit hmiddleCone
  have hmiddleHorizontal : |(F.chart.coord source middle).1| ≤ (7 : ℝ) / 4 := by
    rw [abs_le]
    constructor <;> linarith
  let middleTarget := LocalTarget.ofPathOfAbs (by omega) hmiddleNot
    (Or.inl hsourceMiddle) hmiddleHorizontal
  have hmiddleEdge : N.frame.toCanonical middleTarget.vertex =
      Erdos957Cases24.Case2.v := by
    change N.frame.toCanonical middle = _
    rw [← N.middle_actual, N.frame.toCanonical_actual]
  exact ⟨{
    middleTarget := middleTarget
    middle_edge_coordinate := hmiddleEdge
    middle_degree_le_four := hmiddleDegree
    middle_vertex := rfl }⟩

/-- Weak erasure of `nonempty_case4WholeActualRowData`, retained for the
source-local row API. -/
theorem case4ActualRow_whole
    {A : Finset Point} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hflat : P.IsFlat source) (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (F.chart.coord source middle))
    (T : TwoExtremeCyclicWitness P source middle)
    (N : TwoExtremeNormalizedFrame source middle T)
    (hmiddleDegree : (unitDistanceGraph A).degree middle ≤ 4) :
    Nonempty (Case4ActualRow F.chart source middle T N) := by
  obtain ⟨D⟩ := nonempty_case4WholeActualRowData F source hflat hwindow middle
    hsourceMiddle hmiddleCone T N hmiddleDegree
  exact ⟨D.row⟩

end CommonCase4

/-- The local hull-window statement implies the exact seven-window premise
used by the exhaustive four-case classifier. -/
theorem middleHullNeighbors_mem_sevenWindow
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} (hwindow : LocalHullWindowHypothesis P source)
    {middle : Vertex A}
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle) :
    ∀ w : Vertex A, w ∈ P.H → (unitDistanceGraph A).Adj middle w →
      w ∈ Erdos957MiddleLocalization.sevenHullWindow P source := by
  intro w hw hmw
  exact hwindow w hw (Or.inr ⟨middle, hsourceMiddle, hmw⟩)

/-- If the cyclic-side endpoint of a produced two-extreme row is itself a
source, its deterministic bisector middle is the same equilateral point.
This is the choice-coherence step needed before selecting pair data. -/
theorem partner_bisectorSourceMiddle_eq
    {A : Finset Point} (hA : IsOneSeparated A)
    (O : Erdos957.CyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder O)
    (W : DiameterWitnessData
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L))
    (source : {p // p ∈
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L).H})
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (T : TwoExtremeCyclicWitness
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L) source middle)
    (N : Erdos957CaseClassification.ActualCase24Rows.TwoExtremeNormalizedFrame
      source middle T)
    (hp : cyclicSideVertex
        (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L) source T.side ∈
      sourceVertices
        (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L) W) :
    PairCases.bisectorSourceMiddle hA O L W
      ⟨cyclicSideVertex
          (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L) source T.side,
        sourceVertices_subset_hull
          (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L) W hp⟩ hp =
      middle := by
  let P := Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L
  let partner : {p // p ∈ P.H} :=
    ⟨cyclicSideVertex P source T.side, sourceVertices_subset_hull P W hp⟩
  have hsourceSide : (unitDistanceGraph A).Adj source.1 partner.1 := by
    change dist (source.1 : Point) (partner.1 : Point) = 1
    simpa [partner, P] using N.side_unit
  have hpartnerMiddle : (unitDistanceGraph A).Adj partner.1 middle := by
    exact (unitDistanceGraph A).adj_symm (by simpa [partner, P] using T.side_adjacent)
  by_cases hside : T.side = .previous
  · have hnextPartner : P.next partner = source := by
      dsimp [partner]
      simpa [cyclicSideVertex, hside]
    apply Erdos957PartnerMiddleChoice.bisectorSourceMiddle_eq_of_next
      hA O L W partner hp middle
    · rw [hnextPartner]
      exact hsourceSide.symm
    · exact hpartnerMiddle
    · rw [hnextPartner]
      exact hsourceMiddle
  · have hnext : T.side = .next := by
      cases hs : T.side
      · exact (hside hs).elim
      · rfl
    have hprevPartner : P.next⁻¹ partner = source := by
      dsimp [partner]
      simpa [cyclicSideVertex, hnext]
    apply Erdos957PartnerMiddleChoice.bisectorSourceMiddle_eq_of_previous
      hA O L W partner hp middle
    · rw [hprevPartner]
      exact hsourceSide.symm
    · exact hpartnerMiddle
    · rw [hprevPartner]
      exact hsourceMiddle

/-- When the cyclic-side endpoint is itself an emitting source, its honest
two-extreme witness points back across the same edge.  The same-side
alternative would make its selected middle adjacent to both cyclic hull
neighbours, contradicting flatness. -/
theorem partner_twoExtreme_side_eq_opposite
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (T : TwoExtremeCyclicWitness P source middle)
    (hp : cyclicSideVertex P source T.side ∈ sourceVertices P W)
    (Tpartner : TwoExtremeCyclicWitness P
      (sourceIndex P W (cyclicSideVertex P source T.side) hp) middle) :
    Tpartner.side = match T.side with
      | .previous => .next
      | .next => .previous := by
  rcases T with ⟨side, hneighbors, hsideAdjacent⟩
  cases side with
  | previous =>
      let partner := sourceIndex P W (P.next⁻¹ source).1 hp
      have hpartnerMiddle : (unitDistanceGraph A).Adj partner.1 middle := by
        change (unitDistanceGraph A).Adj (P.next⁻¹ source).1 middle
        exact (unitDistanceGraph A).adj_symm hsideAdjacent
      have hpartner : partner = P.next⁻¹ source := by
        apply Subtype.ext
        rfl
      have hnextPartner : P.next partner = source := by
        rw [hpartner]
        simp
      cases hpartnerSide : Tpartner.side with
      | previous =>
          exfalso
          apply not_both_cyclic_neighbors_adjacent_to_middle
            hA P W partner hp middle hpartnerMiddle
          · change (unitDistanceGraph A).Adj middle
              (P.next⁻¹ (sourceIndex P W (P.next⁻¹ source).1 hp)).1
            simpa [cyclicSideVertex, hpartnerSide] using
              Tpartner.side_adjacent
          · rw [hnextPartner]
            exact (unitDistanceGraph A).adj_symm hsourceMiddle
      | next => rfl
  | next =>
      let partner := sourceIndex P W (P.next source).1 hp
      have hpartnerMiddle : (unitDistanceGraph A).Adj partner.1 middle := by
        change (unitDistanceGraph A).Adj (P.next source).1 middle
        exact (unitDistanceGraph A).adj_symm hsideAdjacent
      have hpartner : partner = P.next source := by
        apply Subtype.ext
        rfl
      have hprevPartner : P.next⁻¹ partner = source := by
        rw [hpartner]
        simp
      cases hpartnerSide : Tpartner.side with
      | previous => rfl
      | next =>
          exfalso
          apply not_both_cyclic_neighbors_adjacent_to_middle
            hA P W partner hp middle hpartnerMiddle
          · rw [hprevPartner]
            exact (unitDistanceGraph A).adj_symm hsourceMiddle
          · change (unitDistanceGraph A).Adj middle
              (P.next (sourceIndex P W (P.next source).1 hp)).1
            simpa [cyclicSideVertex, hpartnerSide] using
              Tpartner.side_adjacent

/-- Both endpoints of a coherent two-extreme pair compute the same
source-free directed-edge key. -/
theorem partner_case4PairEdgeBase_eq
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (T : TwoExtremeCyclicWitness P source middle)
    (hp : cyclicSideVertex P source T.side ∈ sourceVertices P W)
    (Tpartner : TwoExtremeCyclicWitness P
      (sourceIndex P W (cyclicSideVertex P source T.side) hp) middle) :
    case4PairEdgeBase Tpartner = case4PairEdgeBase T := by
  rcases T with ⟨side, hneighbors, hsideAdjacent⟩
  cases side with
  | previous =>
      have hopposite := partner_twoExtreme_side_eq_opposite hA W source hs
        middle hsourceMiddle
          (⟨.previous, hneighbors, hsideAdjacent⟩ :
            TwoExtremeCyclicWitness P source middle) hp Tpartner
      simp at hopposite
      simp only [case4PairEdgeBase, hopposite]
      apply Subtype.ext
      rfl
  | next =>
      have hopposite := partner_twoExtreme_side_eq_opposite hA W source hs
        middle hsourceMiddle
          (⟨.next, hneighbors, hsideAdjacent⟩ :
            TwoExtremeCyclicWitness P source middle) hp Tpartner
      simp at hopposite
      simp only [case4PairEdgeBase, hopposite]
      have hpartner : sourceIndex P W (P.next source).1 hp = P.next source := by
        apply Subtype.ext
        rfl
      have hprev := congrArg (fun x ↦ (P.next⁻¹) x) hpartner
      simpa [cyclicSideVertex] using hprev

/-- The same pair-key identity also makes the endpoint selector bits
complementary. -/
theorem partner_case4SourceIsRight_eq_not
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (T : TwoExtremeCyclicWitness P source middle)
    (hp : cyclicSideVertex P source T.side ∈ sourceVertices P W)
    (Tpartner : TwoExtremeCyclicWitness P
      (sourceIndex P W (cyclicSideVertex P source T.side) hp) middle) :
    case4SourceIsRight Tpartner = !(case4SourceIsRight T) := by
  rcases T with ⟨side, hneighbors, hsideAdjacent⟩
  cases side with
  | previous =>
      have hopposite := partner_twoExtreme_side_eq_opposite hA W source hs
        middle hsourceMiddle
          (⟨.previous, hneighbors, hsideAdjacent⟩ :
            TwoExtremeCyclicWitness P source middle) hp Tpartner
      simp [case4SourceIsRight, hopposite]
  | next =>
      have hopposite := partner_twoExtreme_side_eq_opposite hA W source hs
        middle hsourceMiddle
          (⟨.next, hneighbors, hsideAdjacent⟩ :
            TwoExtremeCyclicWitness P source middle) hp Tpartner
      simp [case4SourceIsRight, hopposite]

/-- Middle-transported form of `partner_case4PairEdgeBase_eq`. -/
theorem partner_case4PairEdgeBase_eq_of_middle_eq
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (middle partnerMiddle : Vertex A)
    (hmiddle : partnerMiddle = middle)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (T : TwoExtremeCyclicWitness P source middle)
    (hp : cyclicSideVertex P source T.side ∈ sourceVertices P W)
    (Tpartner : TwoExtremeCyclicWitness P
      (sourceIndex P W (cyclicSideVertex P source T.side) hp) partnerMiddle) :
    case4PairEdgeBase Tpartner = case4PairEdgeBase T := by
  subst partnerMiddle
  exact partner_case4PairEdgeBase_eq hA W source hs middle hsourceMiddle
    T hp Tpartner

/-- Middle-transported form of `partner_case4SourceIsRight_eq_not`. -/
theorem partner_case4SourceIsRight_eq_not_of_middle_eq
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (middle partnerMiddle : Vertex A)
    (hmiddle : partnerMiddle = middle)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (T : TwoExtremeCyclicWitness P source middle)
    (hp : cyclicSideVertex P source T.side ∈ sourceVertices P W)
    (Tpartner : TwoExtremeCyclicWitness P
      (sourceIndex P W (cyclicSideVertex P source T.side) hp) partnerMiddle) :
    case4SourceIsRight Tpartner = !(case4SourceIsRight T) := by
  subst partnerMiddle
  exact partner_case4SourceIsRight_eq_not hA W source hs middle
    hsourceMiddle T hp Tpartner

/-- Formula-retaining Case 4 for one source.  In the degree-five branch the
row already stores the unreflected common edge frame and the shared branch;
no source-reflected lexicographic choice is made. -/
theorem exists_realized_case4
    {A : Finset Point} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (F.chart.coord source q).2 < 0)
    (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (F.chart.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle ≤ 5)
    (htwo : (hullUnitNeighbors P middle).card = 2) :
    Nonempty (RealizedSourceRow P F.chart source) := by
  have hseven := middleHullNeighbors_mem_sevenWindow hwindow hsourceMiddle
  obtain ⟨T⟩ := twoExtremeCyclicWitness_of_seven_window hA P F W source
    middle hs hsourceMiddle hmiddleCone hseven htwo
  obtain ⟨N⟩ := Erdos957CaseClassification.ActualCase24Rows.exists_twoExtremeNormalizedFrame
    hA P F.chart source middle T hstrict (source_facts hs).2.2
      hsourceMiddle hmiddleCone
  by_cases hfour : (unitDistanceGraph A).degree middle ≤ 4
  · obtain ⟨D⟩ := CommonCase4.nonempty_case4WholeActualRowData F source
      (source_isFlat P W source hs) hwindow middle hsourceMiddle hmiddleCone
      T N hfour
    exact ⟨RealizedSourceRow.case4 middle hmiddleDegree htwo T N D.row
      D.middle_vertex⟩
  · have hfive : (unitDistanceGraph A).degree middle = 5 := by omega
    obtain ⟨E⟩ := Erdos957CaseClassification.ActualCase24Rows.exists_twoExtremeCommonPairFrame
      hA P F.chart source middle T hstrict (source_facts hs).2.2
        hsourceMiddle hmiddleCone
    obtain ⟨B⟩ := CommonCase4.nonempty_commonCase4HullPairBranch
      hA E hfive
    obtain ⟨row, hmiddleVertex⟩ :=
      Erdos957CaseClassification.ActualCase24Rows.case4PairedActualRow_of_commonBranch
      F source (source_isFlat P W source hs) hwindow middle hsourceMiddle
      hmiddleCone T N hfive E.frame B.farthest B.branch
      (Erdos957CaseClassification.ActualCase24Rows.case4SourceIsRight T) rfl E.source_coordinate
      E.side_coordinate E.middle_coordinate
    exact ⟨RealizedSourceRow.case4 middle hmiddleDegree htwo T N row
      hmiddleVertex⟩

/-! ## Unconditional produced realized rows -/

/-- The pointwise data selected before erasing to a `RealizedSourceRow`.
The nonsplit alternative records the exact numerical reason it cannot be
degree-five Case 4.  The split alternative stores the canonical
source-free edge branch itself and the exact paired row built from it. -/
inductive ProducedRowSelection
    {A : Finset Point} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (W : DiameterWitnessData P)
    (u : Vertex A) (hu : u ∈ sourceVertices P W)
    (middle : Vertex A) : Type
  | nonsplit
      (row : RealizedSourceRow P F.chart (sourceIndex P W u hu))
      (not_split : ¬ row.IsCase4Split)
      (not_five_two : ¬ ((unitDistanceGraph A).degree middle = 5 ∧
        (hullUnitNeighbors P middle).card = 2))
  | split
      (middle_degree_five : (unitDistanceGraph A).degree middle = 5)
      (two_hull_neighbors : (hullUnitNeighbors P middle).card = 2)
      (twoExtreme : TwoExtremeCyclicWitness P
        (sourceIndex P W u hu) middle)
      (normalized : TwoExtremeNormalizedFrame
        (sourceIndex P W u hu) middle twoExtreme)
      (branch_exists : Nonempty (CommonCase4.EdgeCase4Branch P
        (case4PairEdgeBase twoExtreme) middle))
      (rightSource : Bool)
      (right_source_eq : rightSource = case4SourceIsRight twoExtreme)
      (data : CommonCase4.EdgePairedActualRowData F
        (sourceIndex P W u hu) middle twoExtreme normalized
        (CommonCase4.selectedEdgeCase4Branch branch_exists) rightSource)

/-- Erase the classified selection to the exact row consumed by transfer
and collision code. -/
def ProducedRowSelection.row
    {A : Finset Point} {P : CyclicHullData A}
    {F : P.FlatAlignedFrameData} {W : DiameterWitnessData P}
    {u : Vertex A} {hu : u ∈ sourceVertices P W} {middle : Vertex A} :
    ProducedRowSelection F W u hu middle →
      RealizedSourceRow P F.chart (sourceIndex P W u hu)
  | .nonsplit row _ _ => row
  | .split hfive htwo T N hexists right hright data =>
      .case4 middle (by omega) htwo T N data.row data.row_middle_vertex

/-- A split selection has its right target definitionally in the retained
paired row. -/
theorem ProducedRowSelection.isCase4Split_of_split
    {A : Finset Point} {P : CyclicHullData A}
    {F : P.FlatAlignedFrameData} {W : DiameterWitnessData P}
    {u : Vertex A} {hu : u ∈ sourceVertices P W} {middle : Vertex A}
    (hfive : (unitDistanceGraph A).degree middle = 5)
    (htwo : (hullUnitNeighbors P middle).card = 2)
    (T : TwoExtremeCyclicWitness P (sourceIndex P W u hu) middle)
    (N : TwoExtremeNormalizedFrame (sourceIndex P W u hu) middle T)
    (hexists : Nonempty (CommonCase4.EdgeCase4Branch P
      (case4PairEdgeBase T) middle))
    (right : Bool) (hright : right = case4SourceIsRight T)
    (D : CommonCase4.EdgePairedActualRowData F (sourceIndex P W u hu)
      middle T N (CommonCase4.selectedEdgeCase4Branch hexists) right) :
    (ProducedRowSelection.split hfive htwo T N hexists right hright D).row.IsCase4Split := by
  obtain ⟨hr, hs, hm, hq, hne, hrow⟩ := D.row_shape
  refine ⟨D.secondaryTarget, ?_⟩
  simp [ProducedRowSelection.row, RealizedSourceRow.IsCase4Split,
    RealizedSourceRow.targetAtRole, hrow]

theorem ProducedRowSelection.split_middle_role
    {A : Finset Point} {P : CyclicHullData A}
    {F : P.FlatAlignedFrameData} {W : DiameterWitnessData P}
    {u : Vertex A} {hu : u ∈ sourceVertices P W} {middle : Vertex A}
    (hfive : (unitDistanceGraph A).degree middle = 5)
    (htwo : (hullUnitNeighbors P middle).card = 2)
    (T : TwoExtremeCyclicWitness P (sourceIndex P W u hu) middle)
    (N : TwoExtremeNormalizedFrame (sourceIndex P W u hu) middle T)
    (hexists : Nonempty (CommonCase4.EdgeCase4Branch P
      (case4PairEdgeBase T) middle))
    (right : Bool) (hright : right = case4SourceIsRight T)
    (D : CommonCase4.EdgePairedActualRowData F (sourceIndex P W u hu)
      middle T N (CommonCase4.selectedEdgeCase4Branch hexists) right) :
    (ProducedRowSelection.split hfive htwo T N hexists right hright D).row.targetAtRole
        PairCases.TargetRoleName.case4SplitLeft = some D.middleTarget := by
  obtain ⟨hr, hs, hm, hq, hne, hrow⟩ := D.row_shape
  simp [ProducedRowSelection.row, RealizedSourceRow.targetAtRole, hrow]

theorem ProducedRowSelection.split_secondary_role
    {A : Finset Point} {P : CyclicHullData A}
    {F : P.FlatAlignedFrameData} {W : DiameterWitnessData P}
    {u : Vertex A} {hu : u ∈ sourceVertices P W} {middle : Vertex A}
    (hfive : (unitDistanceGraph A).degree middle = 5)
    (htwo : (hullUnitNeighbors P middle).card = 2)
    (T : TwoExtremeCyclicWitness P (sourceIndex P W u hu) middle)
    (N : TwoExtremeNormalizedFrame (sourceIndex P W u hu) middle T)
    (hexists : Nonempty (CommonCase4.EdgeCase4Branch P
      (case4PairEdgeBase T) middle))
    (right : Bool) (hright : right = case4SourceIsRight T)
    (D : CommonCase4.EdgePairedActualRowData F (sourceIndex P W u hu)
      middle T N (CommonCase4.selectedEdgeCase4Branch hexists) right) :
    (ProducedRowSelection.split hfive htwo T N hexists right hright D).row.targetAtRole
        PairCases.TargetRoleName.case4SplitRight = some D.secondaryTarget := by
  obtain ⟨hr, hs, hm, hq, hne, hrow⟩ := D.row_shape
  simp [ProducedRowSelection.row, RealizedSourceRow.targetAtRole, hrow]

/-- Every actual emitting source in the produced cyclic hull has one of the
four formula-retaining realized rows.  The selected middle, strict support,
seven-window localization, and the four-way split are all the canonical
produced objects; no collision or capacity hypothesis occurs here. -/
theorem nonempty_realizedSourceRow
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L))
    (u : Vertex A)
    (hu : u ∈ sourceVertices
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W) :
    Nonempty (RealizedSourceRow
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)
      (Erdos957BisectorFrame.bisectorAlignedChartData R.order L)
      (sourceIndex
        (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W u hu)) := by
  let P := Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L
  let F := Erdos957BisectorPolar.bisectorFlatAlignedFrameData R.order L hA
  let C := Erdos957BisectorFrame.bisectorAlignedChartData R.order L
  let source := sourceIndex P W u hu
  let middle := PairCases.bisectorSourceMiddle hA R.order L W source hu
  have hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0 := by
    intro q hq
    exact Erdos957BisectorFrame.bisectorAlignedChartData_coord_snd_neg
      R.order L source q hq
  have hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle := by
    exact PairCases.bisectorSourceMiddle_adj hA R.order L W source hu
  have hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (C.coord source middle) := by
    exact PairCases.bisectorSourceMiddle_in_open_cone
      hA R.order L W source hu
  let windowGeometry :=
    Erdos957CyclicWindowConstructor.cyclicWindowGeometry hA R L W
  have hwindow : LocalHullWindowHypothesis P source := by
    simpa [source, P, F] using
      Erdos957RealizationWindow.localHullWindowHypothesis windowGeometry
        (⟨u, hu⟩ : Erdos957CollisionInstantiation.Source P W)
  have hseven := middleHullNeighbors_mem_sevenWindow hwindow hsourceMiddle
  have hfour : FourCase P middle := by
    exact four_cases_of_seven_window hA P F W source middle hu
      hsourceMiddle hmiddleCone hseven
  cases hfour with
  | case1 hdegree hone =>
      obtain ⟨realized, _row, _hrealized, _herasure⟩ :=
        Erdos957Case13RealizedRows.exists_realized_case1
          hA F W source hu hwindow middle hsourceMiddle hmiddleCone
            hdegree hone
      exact ⟨realized⟩
  | case2 hdegree htwo =>
      obtain ⟨_T, _N, _row, realized, _hrealized, _herasure⟩ :=
        Erdos957Case2RealizedRows.exists_realized_case2
          hA R.order L W source hu hwindow middle hsourceMiddle
            hmiddleCone hdegree htwo
      exact ⟨realized⟩
  | case3 hdegree hone =>
      obtain ⟨realized, _row, _hrealized, _herasure⟩ :=
        Erdos957Case13RealizedRows.exists_realized_case3
          hA F W source hu hstrict hwindow middle hsourceMiddle
            hmiddleCone hdegree hone
      exact ⟨realized⟩
  | case4 hdegree htwo =>
      exact exists_realized_case4 hA F W source hu hstrict hwindow middle
        hsourceMiddle hmiddleCone hdegree htwo

/-- Strong pointwise production theorem.  Unlike
`nonempty_realizedSourceRow`, its degree-five Case-4 branch is selected from
the source-free directed-edge key and retains the exact split targets. -/
theorem nonempty_producedRowSelection
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L))
    (u : Vertex A)
    (hu : u ∈ sourceVertices
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W) :
    Nonempty (ProducedRowSelection
      (Erdos957BisectorPolar.bisectorFlatAlignedFrameData R.order L hA)
      W u hu
      (PairCases.bisectorSourceMiddle hA R.order L W
        (sourceIndex
          (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W u hu)
        hu)) := by
  let P := Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L
  let F := Erdos957BisectorPolar.bisectorFlatAlignedFrameData R.order L hA
  let C := Erdos957BisectorFrame.bisectorAlignedChartData R.order L
  let source := sourceIndex P W u hu
  let middle := PairCases.bisectorSourceMiddle hA R.order L W source hu
  have hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0 := by
    intro q hq
    exact Erdos957BisectorFrame.bisectorAlignedChartData_coord_snd_neg
      R.order L source q hq
  have hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle :=
    PairCases.bisectorSourceMiddle_adj hA R.order L W source hu
  have hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (C.coord source middle) :=
    PairCases.bisectorSourceMiddle_in_open_cone hA R.order L W source hu
  let windowGeometry :=
    Erdos957CyclicWindowConstructor.cyclicWindowGeometry hA R L W
  have hwindow : LocalHullWindowHypothesis P source := by
    simpa [source, P, F] using
      Erdos957RealizationWindow.localHullWindowHypothesis windowGeometry
        (⟨u, hu⟩ : Erdos957CollisionInstantiation.Source P W)
  have hseven := middleHullNeighbors_mem_sevenWindow hwindow hsourceMiddle
  have hfour : FourCase P middle :=
    four_cases_of_seven_window hA P F W source middle hu
      hsourceMiddle hmiddleCone hseven
  cases hfour with
  | case1 hdegree hone =>
      obtain ⟨realized, _row, hrealized, _herasure⟩ :=
        Erdos957Case13RealizedRows.exists_realized_case1
          hA F W source hu hwindow middle hsourceMiddle hmiddleCone
            hdegree hone
      refine ⟨.nonsplit realized ?_ ?_⟩
      · rw [hrealized]
        simp [RealizedSourceRow.IsCase4Split,
          RealizedSourceRow.targetAtRole]
      · change ¬ ((unitDistanceGraph A).degree middle = 5 ∧
          (hullUnitNeighbors P middle).card = 2)
        rintro ⟨hfive, _⟩
        omega
  | case2 hdegree htwo =>
      obtain ⟨_T, _N, _row, realized, hrealized, _herasure⟩ :=
        Erdos957Case2RealizedRows.exists_realized_case2
          hA R.order L W source hu hwindow middle hsourceMiddle
            hmiddleCone hdegree htwo
      refine ⟨.nonsplit realized ?_ ?_⟩
      · rw [hrealized]
        simp [RealizedSourceRow.IsCase4Split,
          RealizedSourceRow.targetAtRole]
      · change ¬ ((unitDistanceGraph A).degree middle = 5 ∧
          (hullUnitNeighbors P middle).card = 2)
        rintro ⟨hfive, _⟩
        omega
  | case3 hdegree hone =>
      obtain ⟨realized, _row, hrealized, _herasure⟩ :=
        Erdos957Case13RealizedRows.exists_realized_case3
          hA F W source hu hstrict hwindow middle hsourceMiddle
            hmiddleCone hdegree hone
      refine ⟨.nonsplit realized ?_ ?_⟩
      · rw [hrealized]
        simp [RealizedSourceRow.IsCase4Split,
          RealizedSourceRow.targetAtRole]
      · change ¬ ((unitDistanceGraph A).degree middle = 5 ∧
          (hullUnitNeighbors P middle).card = 2)
        rintro ⟨_, htwo⟩
        omega
  | case4 hdegree htwo =>
      obtain ⟨T⟩ := twoExtremeCyclicWitness_of_seven_window hA P F W source
        middle hu hsourceMiddle hmiddleCone hseven htwo
      obtain ⟨N⟩ := ActualCase24Rows.exists_twoExtremeNormalizedFrame
        hA P F.chart source middle T hstrict (source_facts hu).2.2
          hsourceMiddle hmiddleCone
      by_cases hfour : (unitDistanceGraph A).degree middle ≤ 4
      · obtain ⟨D⟩ := CommonCase4.nonempty_case4WholeActualRowData
          F source (source_isFlat P W source hu) hwindow middle
            hsourceMiddle hmiddleCone T N hfour
        let realized : RealizedSourceRow P F.chart source :=
          .case4 middle hdegree htwo T N D.row D.middle_vertex
        refine ⟨.nonsplit realized ?_ ?_⟩
        · simp [realized, CommonCase4.Case4WholeActualRowData.row,
            RealizedSourceRow.IsCase4Split,
            RealizedSourceRow.targetAtRole]
        · change ¬ ((unitDistanceGraph A).degree middle = 5 ∧
            (hullUnitNeighbors P middle).card = 2)
          rintro ⟨hfive, _⟩
          omega
      · have hfive : (unitDistanceGraph A).degree middle = 5 := by omega
        obtain ⟨E⟩ := ActualCase24Rows.exists_twoExtremeCommonPairFrame
          hA P F.chart source middle T hstrict (source_facts hu).2.2
            hsourceMiddle hmiddleCone
        have hexists : Nonempty (CommonCase4.EdgeCase4Branch P
            (case4PairEdgeBase T) middle) :=
          CommonCase4.nonempty_edgeCase4Branch hA E hfive
        let B := CommonCase4.selectedEdgeCase4Branch hexists
        let EB : TwoExtremeCommonPairFrame source middle T := {
          edge_unit := B.edge_unit
          middle_coordinate := B.middle_coordinate
          strict_support := B.strict_support }
        have hsourceCommon : B.frame.toCanonical source.1 =
            Erdos957Case24Bridge.Case4.sideSource
              (case4SourceIsRight T) := by
          change EB.frame.toCanonical source.1 = _
          exact EB.source_coordinate
        have hsideCommon : B.frame.toCanonical
            (cyclicSideVertex P source T.side) =
              Erdos957Case24Bridge.Case4.sideSource
                (!(case4SourceIsRight T)) := by
          change EB.frame.toCanonical (cyclicSideVertex P source T.side) = _
          exact EB.side_coordinate
        obtain ⟨D⟩ := CommonCase4.nonempty_edgePairedActualRowData
          F source (source_isFlat P W source hu) hwindow middle
            hsourceMiddle hmiddleCone T N hfive B (case4SourceIsRight T) rfl
            hsourceCommon hsideCommon B.middle_coordinate
        exact ⟨.split hfive htwo T N hexists (case4SourceIsRight T) rfl D⟩

/-- The canonical classified selection at one source. -/
noncomputable def producedRowSelection
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L))
    (u : Vertex A)
    (hu : u ∈ sourceVertices
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W) :=
  Classical.choice (nonempty_producedRowSelection hA R L W u hu)

/-- The actual dependent formula-row choice for every source.  Choice is
only used to select among already proved finite geometric witnesses; each
selected value itself retains all exact row equations. -/
noncomputable def producedHasRealizedSourceRows
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)) :
    HasRealizedSourceRows
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W
      (Erdos957BisectorFrame.bisectorAlignedChartData R.order L) :=
  fun u hu ↦ (producedRowSelection hA R L W u hu).row

/-- Existence form of `producedHasRealizedSourceRows`, convenient for final
composition records which quantify over a chosen dependent family. -/
theorem nonempty_hasRealizedSourceRows
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)) :
    Nonempty (HasRealizedSourceRows
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W
      (Erdos957BisectorFrame.bisectorAlignedChartData R.order L)) :=
  ⟨producedHasRealizedSourceRows hA R L W⟩

/-- Exact erasure of the produced enriched rows to the local-case function
consumed by transfer assembly. -/
noncomputable def producedHasLocalCases
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)) :
    HasLocalCases
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W
      (Erdos957BisectorFrame.bisectorAlignedChartData R.order L) :=
  (producedHasRealizedSourceRows hA R L W).hasLocalCases

/-! ## Reflection-safe global coherence interface -/

/-- The exact pair certificate retained for a selected degree-five Case-4
row.  Its branch is indexed by the common directed-edge chart, rather than
by either endpoint's reflected normalized chart. -/
structure CommonPairedCase4Rows
    {A : Finset Point} {P : CyclicHullData A}
    {W : DiameterWitnessData P} {C : P.AlignedChartData}
    (rows : HasRealizedSourceRows P W C)
    (u : Vertex A) (hu : u ∈ sourceVertices P W) where
  middle : Vertex A
  middle_degree_five : (unitDistanceGraph A).degree middle = 5
  twoExtreme : TwoExtremeCyclicWitness P
    (sourceIndex P W u hu) middle
  normalized :
    Erdos957CaseClassification.ActualCase24Rows.TwoExtremeNormalizedFrame
      (sourceIndex P W u hu) middle twoExtreme
  commonFrame :
    Erdos957CaseClassification.ActualCase24Rows.TwoExtremeCommonPairFrame
      (sourceIndex P W u hu) middle twoExtreme
  pairBranch : CommonCase4.CommonCase4HullPairBranch commonFrame
  currentMiddleTarget :
    LocalTarget P C (sourceIndex P W u hu)
  currentSecondaryTarget :
    LocalTarget P C (sourceIndex P W u hu)
  current_middle_role :
    (rows u hu).targetAtRole PairCases.TargetRoleName.case4SplitLeft =
      some currentMiddleTarget
  current_secondary_role :
    (rows u hu).targetAtRole PairCases.TargetRoleName.case4SplitRight =
      some currentSecondaryTarget
  current_secondary_association :
    (rows u hu).roleAssociation PairCases.TargetRoleName.case4SplitRight =
      commonPairHorizontalAssociation pairBranch.branch
        (Erdos957CaseClassification.ActualCase24Rows.case4SourceIsRight
          twoExtreme)
  current_middle_vertex : currentMiddleTarget.vertex = middle
  current_secondary_vertex : currentSecondaryTarget.vertex =
    pairBranch.actualRecipient
      (Erdos957CaseClassification.ActualCase24Rows.case4SourceIsRight
        twoExtreme)
  partner_absent_or_coherent :
    cyclicSideVertex P (sourceIndex P W u hu) twoExtreme.side ∉
        sourceVertices P W ∨
      ∀ hp : cyclicSideVertex P (sourceIndex P W u hu) twoExtreme.side ∈
          sourceVertices P W,
        ∃ (partnerMiddleTarget partnerSecondaryTarget :
            LocalTarget P C
              (sourceIndex P W
                (cyclicSideVertex P (sourceIndex P W u hu) twoExtreme.side)
                hp)),
          (rows (cyclicSideVertex P (sourceIndex P W u hu) twoExtreme.side)
              hp).targetAtRole PairCases.TargetRoleName.case4SplitLeft =
                some partnerMiddleTarget ∧
          (rows (cyclicSideVertex P (sourceIndex P W u hu) twoExtreme.side)
              hp).targetAtRole PairCases.TargetRoleName.case4SplitRight =
                some partnerSecondaryTarget ∧
          partnerMiddleTarget.vertex = middle ∧
          partnerSecondaryTarget.vertex = pairBranch.actualRecipient
            (!(Erdos957CaseClassification.ActualCase24Rows.case4SourceIsRight
              twoExtreme)) ∧
          (rows (cyclicSideVertex P
              (sourceIndex P W u hu) twoExtreme.side) hp).roleAssociation
                PairCases.TargetRoleName.case4SplitRight =
            commonPairHorizontalAssociation pairBranch.branch
              (!(Erdos957CaseClassification.ActualCase24Rows.case4SourceIsRight
                twoExtreme))

/-- The partner half of produced Case-4 coherence.  Factoring this dependent
selection argument out of the final structure constructor keeps each proof
under the default heartbeat limit. -/
theorem produced_partner_split_targets
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L))
    (u : Vertex A)
    (hu : u ∈ sourceVertices
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W)
    (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj
      (sourceIndex
        (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W u hu).1
      middle)
    (hfive : (unitDistanceGraph A).degree middle = 5)
    (htwo : (hullUnitNeighbors
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) middle).card = 2)
    (T : TwoExtremeCyclicWitness
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)
      (sourceIndex
        (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W u hu)
      middle)
    (N : TwoExtremeNormalizedFrame
      (sourceIndex
        (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W u hu)
      middle T)
    (hexists : Nonempty (CommonCase4.EdgeCase4Branch
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)
      (case4PairEdgeBase T) middle))
    (right : Bool) (hright : right = case4SourceIsRight T)
    (hp : cyclicSideVertex
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)
      (sourceIndex
        (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W u hu)
      T.side ∈ sourceVertices
        (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W) :
    ∃ (partnerMiddleTarget partnerSecondaryTarget :
        LocalTarget
          (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)
          (Erdos957BisectorFrame.bisectorAlignedChartData R.order L)
          (sourceIndex
            (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W
            (cyclicSideVertex
              (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)
              (sourceIndex
                (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W u hu)
              T.side) hp)),
      ((producedHasRealizedSourceRows hA R L W)
        (cyclicSideVertex
          (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)
          (sourceIndex
            (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W u hu)
          T.side) hp).targetAtRole PairCases.TargetRoleName.case4SplitLeft =
          some partnerMiddleTarget ∧
      ((producedHasRealizedSourceRows hA R L W)
        (cyclicSideVertex
          (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)
          (sourceIndex
            (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W u hu)
          T.side) hp).targetAtRole PairCases.TargetRoleName.case4SplitRight =
          some partnerSecondaryTarget ∧
      partnerMiddleTarget.vertex = middle ∧
      partnerSecondaryTarget.vertex =
        (CommonCase4.selectedEdgeCase4Branch hexists).actualRecipient (!right) ∧
      ((producedHasRealizedSourceRows hA R L W)
        (cyclicSideVertex
          (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)
          (sourceIndex
            (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W u hu)
          T.side) hp).roleAssociation PairCases.TargetRoleName.case4SplitRight =
        commonPairHorizontalAssociation
          (CommonCase4.selectedEdgeCase4Branch hexists).branch (!right) := by
  let P := Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L
  let source := sourceIndex P W u hu
  let partner := sourceIndex P W (cyclicSideVertex P source T.side) hp
  let partnerMiddle :=
    PairCases.bisectorSourceMiddle hA R.order L W partner hp
  have hpartnerMiddle : partnerMiddle = middle :=
    partner_bisectorSourceMiddle_eq hA R.order L W source middle
      hsourceMiddle T N hp
  have hsourceMem : source.1 ∈ sourceVertices P W := by
    change u ∈ sourceVertices P W
    exact hu
  cases hpartnerSelection :
      producedRowSelection hA R L W (cyclicSideVertex P source T.side) hp with
  | nonsplit partnerRow partnerNotSplit partnerNotFiveTwo =>
      exfalso
      apply partnerNotFiveTwo
      constructor
      · exact (congrArg (fun v : Vertex A ↦
          (unitDistanceGraph A).degree v) hpartnerMiddle).trans hfive
      · exact (congrArg (fun v : Vertex A ↦
          (hullUnitNeighbors P v).card) hpartnerMiddle).trans htwo
  | split hpartnerFive hpartnerTwo Tpartner Npartner
        hpartnerExists partnerRight hpartnerRight Dpartner =>
      have hbase := partner_case4PairEdgeBase_eq_of_middle_eq hA W source
        hsourceMem middle partnerMiddle hpartnerMiddle hsourceMiddle T hp Tpartner
      have hrightBits :=
        partner_case4SourceIsRight_eq_not_of_middle_eq hA W source hsourceMem
          middle partnerMiddle hpartnerMiddle hsourceMiddle T hp Tpartner
      have hpartnerRightEq : partnerRight = !right := by
        calc
          partnerRight = case4SourceIsRight Tpartner := hpartnerRight
          _ = !(case4SourceIsRight T) := hrightBits
          _ = !right := congrArg Bool.not hright.symm
      have hpartnerMiddleRole :=
        ProducedRowSelection.split_middle_role hpartnerFive hpartnerTwo
          Tpartner Npartner hpartnerExists partnerRight hpartnerRight Dpartner
      have hpartnerSecondaryRole :=
        ProducedRowSelection.split_secondary_role hpartnerFive hpartnerTwo
          Tpartner Npartner hpartnerExists partnerRight hpartnerRight Dpartner
      refine ⟨Dpartner.middleTarget, Dpartner.secondaryTarget, ?_, ?_,
        Dpartner.middle_vertex.trans hpartnerMiddle, ?_, ?_⟩
      · change ((producedRowSelection hA R L W
            (cyclicSideVertex P source T.side) hp).row).targetAtRole
              PairCases.TargetRoleName.case4SplitLeft =
            some Dpartner.middleTarget
        rw [hpartnerSelection]
        exact hpartnerMiddleRole
      · change ((producedRowSelection hA R L W
            (cyclicSideVertex P source T.side) hp).row).targetAtRole
              PairCases.TargetRoleName.case4SplitRight =
            some Dpartner.secondaryTarget
        rw [hpartnerSelection]
        exact hpartnerSecondaryRole
      · calc
          Dpartner.secondaryTarget.vertex =
              (CommonCase4.selectedEdgeCase4Branch hpartnerExists).actualRecipient
                partnerRight := Dpartner.secondary_vertex
          _ = (CommonCase4.selectedEdgeCase4Branch hpartnerExists).actualRecipient
                (!right) := by rw [hpartnerRightEq]
          _ = (CommonCase4.selectedEdgeCase4Branch hexists).actualRecipient
                (!right) :=
            CommonCase4.selectedEdgeCase4Branch_actualRecipient_eq_of_keys_eq
              hbase hpartnerMiddle hpartnerExists hexists (!right)
      · obtain ⟨_, _, _, _, _, hrow⟩ := Dpartner.row_shape
        change ((producedRowSelection hA R L W
          (cyclicSideVertex P source T.side) hp).row).roleAssociation
            PairCases.TargetRoleName.case4SplitRight = _
        rw [hpartnerSelection]
        simp only [Erdos957HullGeometryBridge.cyclicHullDataOfOrder_H,
    Erdos957HullGeometryBridge.cyclicHullDataOfOrder_next]
        exact CommonCase4.selectedEdgeCase4Branch_association_eq_of_keys_eq
          hbase hpartnerMiddle hpartnerExists hexists (!right)

/-- Globally selected realized rows with reflection-safe conditional
coherence for every split Case-4 row. -/
structure CommonCoherentRealizedSourceRows
    {A : Finset Point} (P : CyclicHullData A)
    (W : DiameterWitnessData P) (C : P.AlignedChartData) where
  rows : HasRealizedSourceRows P W C
  case4_pair : ∀ (u : Vertex A) (hu : u ∈ sourceVertices P W),
    (rows u hu).IsCase4Split → CommonPairedCase4Rows rows u hu

/-- The canonical produced family, with every degree-five Case-4 pair
selected from its source-free directed-edge key.  If the other hull
endpoint is also an emitter, its canonical middle, edge key, selector bit,
and pulled-back branch recipient are proved coherent with the current row. -/
noncomputable def producedCommonCoherentRealizedSourceRows
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L)) :
    CommonCoherentRealizedSourceRows
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L) W
      (Erdos957BisectorFrame.bisectorAlignedChartData R.order L) := by
  let P := Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L
  let F := Erdos957BisectorPolar.bisectorFlatAlignedFrameData R.order L hA
  let rows := producedHasRealizedSourceRows hA R L W
  refine { rows := rows, case4_pair := ?_ }
  intro u hu hsplit
  change ((producedRowSelection hA R L W u hu).row).IsCase4Split at hsplit
  cases hselection : producedRowSelection hA R L W u hu with
  | nonsplit row hnotSplit hnotFiveTwo =>
      exfalso
      apply hnotSplit
      simpa only [hselection, ProducedRowSelection.row] using hsplit
  | split hfive htwo T N hexists right hright D =>
      let source := sourceIndex P W u hu
      let middle := PairCases.bisectorSourceMiddle hA R.order L W source hu
      let B := CommonCase4.selectedEdgeCase4Branch hexists
      let E : TwoExtremeCommonPairFrame source middle T := {
        edge_unit := B.edge_unit
        middle_coordinate := B.middle_coordinate
        strict_support := B.strict_support }
      let pairBranch : CommonCase4.CommonCase4HullPairBranch E := {
        farthest := B.farthest
        branch := B.branch }
      have hframe : E.frame = B.frame := rfl
      have hactualRecipient (b : Bool) :
          pairBranch.actualRecipient b = B.actualRecipient b := by
        apply Subtype.ext
        rfl
      have hcurrentMiddleRole :
          (rows u hu).targetAtRole PairCases.TargetRoleName.case4SplitLeft =
            some D.middleTarget := by
        simpa [rows, producedHasRealizedSourceRows, hselection,
          Erdos957BisectorPolar.bisectorFlatAlignedFrameData] using
          (ProducedRowSelection.split_middle_role hfive htwo T N hexists
            right hright D)
      have hcurrentSecondaryRole :
          (rows u hu).targetAtRole PairCases.TargetRoleName.case4SplitRight =
            some D.secondaryTarget := by
        simpa [rows, producedHasRealizedSourceRows, hselection,
          Erdos957BisectorPolar.bisectorFlatAlignedFrameData] using
          (ProducedRowSelection.split_secondary_role hfive htwo T N hexists
            right hright D)
      refine {
        middle := middle
        middle_degree_five := hfive
        twoExtreme := T
        normalized := N
        commonFrame := E
        pairBranch := pairBranch
        currentMiddleTarget := D.middleTarget
        currentSecondaryTarget := D.secondaryTarget
        current_middle_role := hcurrentMiddleRole
        current_secondary_role := hcurrentSecondaryRole
        current_secondary_association := by
          obtain ⟨hright', hsource', hmiddle', hsecondary', hdistinct',
              hrow⟩ := D.row_shape
          simp [rows, producedHasRealizedSourceRows, hselection,
            Erdos957BisectorPolar.bisectorFlatAlignedFrameData,
            ProducedRowSelection.row, RealizedSourceRow.roleAssociation,
            hrow, pairBranch, B, hright]
          rfl
        current_middle_vertex := D.middle_vertex
        current_secondary_vertex := ?_
        partner_absent_or_coherent := ?_ }
      · rw [← hright]
        exact D.secondary_vertex.trans (hactualRecipient right).symm
      · by_cases habsent : cyclicSideVertex P source T.side ∉ sourceVertices P W
        · exact Or.inl habsent
        · push_neg at habsent
          right
          intro hp
          have hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle := by
            exact PairCases.bisectorSourceMiddle_adj
              hA R.order L W source hu
          obtain ⟨partnerMiddleTarget, partnerSecondaryTarget,
              hpartnerMiddleRole, hpartnerSecondaryRole,
              hpartnerMiddleVertex, hpartnerSecondaryVertex,
              hpartnerSecondaryAssociation⟩ :=
            produced_partner_split_targets hA R L W u hu middle hsourceMiddle
              hfive htwo T N hexists right hright hp
          refine ⟨partnerMiddleTarget, partnerSecondaryTarget,
            ?_, ?_, hpartnerMiddleVertex, ?_, ?_⟩
          · exact hpartnerMiddleRole
          · exact hpartnerSecondaryRole
          · rw [← hright]
            exact hpartnerSecondaryVertex.trans
              (hactualRecipient (!right)).symm
          · rw [← hright]
            exact hpartnerSecondaryAssociation.trans
              (CommonCase4.selectedEdgeCase4Branch_association_eq_of_keys_eq
                rfl rfl hexists hexists (!right))

/-- Erasure of a coherent family is definitionally the exact dependent
local-case function selected by its realized rows. -/
def CommonCoherentRealizedSourceRows.hasLocalCases
    {A : Finset Point} {P : CyclicHullData A}
    {W : DiameterWitnessData P} {C : P.AlignedChartData}
    (R : CommonCoherentRealizedSourceRows P W C) :
    HasLocalCases P W C :=
  R.rows.hasLocalCases

end Erdos957CoherentRealizedRows
