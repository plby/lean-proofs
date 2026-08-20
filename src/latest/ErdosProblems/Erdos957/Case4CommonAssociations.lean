import ErdosProblems.Erdos957.CoherentRealizedRows
import ErdosProblems.Erdos957.RoleCollisions

/-!
# Common-edge association calculations for coherent Case 4 rows

The two endpoints of a coherent Case-4 pair use one literal terminal-edge
chart.  These lemmas classify the selected secondary when it is also a unit
neighbor of either endpoint and compute its endpoint-sensitive arrival
association.  They are formula facts, not collision or capacity assumptions.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957Case4CommonAssociations

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CoherentRealizedRows
open Erdos957RoleCollisions

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P}

/-- The other lower common unit neighbor of `uPrev` and `v`. -/
def leftContact : Point :=
  Erdos957Cases24.point (-(3 / 2)) (-(Erdos957Cases24.sqrtThree / 2))

/-- The two common unit neighbors of the canonical right endpoint `u` and
the equilateral middle `v` are the other endpoint and `b`. -/
lemma eq_uPrev_or_b_of_unit_to_u_v {x : Point}
    (hxu : dist x Erdos957Cases24.Case2.u = 1)
    (hxv : dist x Erdos957Cases24.Case2.v = 1) :
    x = Erdos957Cases24.Case2.uPrev ∨ x = Erdos957Cases24.Case2.b := by
  have hu := congrArg (fun t : ℝ ↦ t ^ 2) hxu
  have hv := congrArg (fun t : ℝ ↦ t ^ 2) hxv
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hu hv
  simp only [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.uPrev,
    Erdos957Cases24.Case2.v, Erdos957Cases24.Case2.b,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    one_pow, sub_zero] at hu hv ⊢
  have hline : x 0 + Erdos957Cases24.sqrtThree * x 1 + 1 = 0 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hsy : Erdos957Cases24.sqrtThree * x 1 = -(x 0 + 1) := by
    linarith
  have hsySq := congrArg (fun t : ℝ ↦ t ^ 2) hsy
  rw [mul_pow, Erdos957Cases24.sqrtThree_sq] at hsySq
  have hfactor : (x 0 + 1) * (2 * x 0 - 1) = 0 := by
    nlinarith [hsySq]
  rcases mul_eq_zero.mp hfactor with hx | hx
  · left
    have hx0 : x 0 = -1 := by linarith
    have hx1 : x 1 = 0 := by
      apply (mul_left_cancel₀ Erdos957Cases24.sqrtThree_ne_zero)
      rw [hsy, hx0]
      norm_num
    exact Erdos957Cases24.point_ext hx0 hx1
  · right
    have hx0 : x 0 = 1 / 2 := by linarith
    have hx1 : x 1 = -(Erdos957Cases24.sqrtThree / 2) := by
      apply (mul_left_cancel₀ Erdos957Cases24.sqrtThree_ne_zero)
      rw [hsy, hx0]
      nlinarith [Erdos957Cases24.sqrtThree_sq]
    exact Erdos957Cases24.point_ext hx0 hx1

/-- The two common unit neighbors of the canonical left endpoint `uPrev`
and the equilateral middle `v` are the other endpoint and its reflected
lower contact. -/
lemma eq_u_or_leftContact_of_unit_to_uPrev_v {x : Point}
    (hxu : dist x Erdos957Cases24.Case2.uPrev = 1)
    (hxv : dist x Erdos957Cases24.Case2.v = 1) :
    x = Erdos957Cases24.Case2.u ∨ x = leftContact := by
  have hu := congrArg (fun t : ℝ ↦ t ^ 2) hxu
  have hv := congrArg (fun t : ℝ ↦ t ^ 2) hxv
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hu hv
  simp only [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.uPrev,
    Erdos957Cases24.Case2.v, leftContact,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    one_pow, sub_zero] at hu hv ⊢
  have hline : Erdos957Cases24.sqrtThree * x 1 = x 0 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hsySq := congrArg (fun t : ℝ ↦ t ^ 2) hline
  rw [mul_pow, Erdos957Cases24.sqrtThree_sq] at hsySq
  have hfactor : x 0 * (2 * x 0 + 3) = 0 := by
    nlinarith [hsySq]
  rcases mul_eq_zero.mp hfactor with hx | hx
  · left
    have hx0 : x 0 = 0 := hx
    have hx1 : x 1 = 0 := by
      apply (mul_left_cancel₀ Erdos957Cases24.sqrtThree_ne_zero)
      rw [hline, hx0]
      simp
    exact Erdos957Cases24.point_ext hx0 hx1
  · right
    have hx0 : x 0 = -(3 / 2) := by linarith
    have hx1 : x 1 = -(Erdos957Cases24.sqrtThree / 2) := by
      apply (mul_left_cancel₀ Erdos957Cases24.sqrtThree_ne_zero)
      rw [hline, hx0]
      nlinarith [Erdos957Cases24.sqrtThree_sq]
    exact Erdos957Cases24.point_ext hx0 hx1

private lemma dist_canonical_of_adj
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    {x y : Vertex A} (hxy : (unitDistanceGraph A).Adj x y) :
    dist (E.toCanonical x) (E.toCanonical y) = 1 := by
  rw [E.dist_eq]
  exact hxy

/-- If the selected secondary is also unit-adjacent to the current endpoint,
its endpoint-sensitive association is opposite the incident-pair side. -/
lemma CommonPairedCase4Rows.secondary_association_eq_opposite_of_adj_source
    {C : P.AlignedChartData} {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu)
    (hadj : (unitDistanceGraph A).Adj u Q.currentSecondaryTarget.vertex) :
    (rows u hu).roleAssociation PairCases.TargetRoleName.case4SplitRight =
      oppositeCyclicSideAssociation Q.twoExtreme.side := by
  let b := ActualCase24Rows.case4SourceIsRight Q.twoExtreme
  let q := Q.pairBranch.branch.sourceRecipient b
  have hqMem := Q.pairBranch.branch.sourceRecipient_mem b
  have hqV : dist q Erdos957Cases24.Case2.v = 1 := by
    simpa [q, Erdos957Cases24.Case4.v, dist_comm] using
      (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqMem).2.1
  have hqSource :
      dist q (Erdos957Case24Bridge.Case4.sideSource b) = 1 := by
    have h := dist_canonical_of_adj Q.commonFrame.frame hadj
    rw [Q.current_secondary_vertex] at h
    change dist (Q.commonFrame.frame.toCanonical u)
      (Q.commonFrame.frame.toCanonical
        (Q.pairBranch.actualRecipient b)) = 1 at h
    have hsourceCoordinate :
        Q.commonFrame.frame.toCanonical u =
          Erdos957Case24Bridge.Case4.sideSource b := by
      simpa [sourceIndex, b] using Q.commonFrame.source_coordinate
    rw [hsourceCoordinate] at h
    simpa [q, CommonCase4.CommonCase4HullPairBranch.actualRecipient,
      dist_comm] using h
  have hqNeLeft : q ≠ Erdos957Cases24.Case2.uPrev :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqMem).2.2.1
  have hqNeRight : q ≠ Erdos957Cases24.Case2.u :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqMem).2.2.2
  rw [Q.current_secondary_association]
  cases hside : Q.twoExtreme.side with
  | previous =>
      have hb : b = true := by
        simp [b, ActualCase24Rows.case4SourceIsRight, hside]
      rw [hb] at hqSource
      simp only [Erdos957Case24Bridge.Case4.sideSource] at hqSource
      have hq : q = Erdos957Cases24.Case2.b :=
        (eq_uPrev_or_b_of_unit_to_u_v hqSource hqV).resolve_left hqNeLeft
      have hqActual : Q.pairBranch.branch.sourceRecipient true =
          Erdos957Cases24.Case2.b := by
        simpa [q, hb] using hq
      change commonPairHorizontalAssociation Q.pairBranch.branch b = _
      rw [hb]
      simp [hqActual, oppositeCyclicSideAssociation,
        commonPairHorizontalAssociation_right, horizontalAssociation,
        Erdos957Case24Bridge.Case4.sideSource,
        Erdos957Cases24.Case2.b, Erdos957Cases24.Case2.u,
        Erdos957Cases24.point] <;> norm_num
  | next =>
      have hb : b = false := by
        simp [b, ActualCase24Rows.case4SourceIsRight, hside]
      rw [hb] at hqSource
      simp only [Erdos957Case24Bridge.Case4.sideSource] at hqSource
      have hq : q = leftContact :=
        (eq_u_or_leftContact_of_unit_to_uPrev_v hqSource hqV).resolve_left
          hqNeRight
      have hqActual : Q.pairBranch.branch.sourceRecipient false =
          leftContact := by
        simpa [q, hb] using hq
      change commonPairHorizontalAssociation Q.pairBranch.branch b = _
      rw [hb]
      simp [hqActual, leftContact, oppositeCyclicSideAssociation,
        commonPairHorizontalAssociation_left,
        Erdos957Case24Bridge.Case4.sideSource,
        Erdos957Cases24.Case2.uPrev, Erdos957Cases24.point] <;> norm_num

/-- If the selected secondary is unit-adjacent to the incident endpoint,
its endpoint-sensitive association is the incident-pair side. -/
lemma CommonPairedCase4Rows.secondary_association_eq_side_of_adj_partner
    {C : P.AlignedChartData} {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu)
    (hadj : (unitDistanceGraph A).Adj
      (cyclicSideVertex P (sourceIndex P W u hu) Q.twoExtreme.side)
      Q.currentSecondaryTarget.vertex) :
    (rows u hu).roleAssociation PairCases.TargetRoleName.case4SplitRight =
      cyclicSideAssociation Q.twoExtreme.side := by
  let b := ActualCase24Rows.case4SourceIsRight Q.twoExtreme
  let q := Q.pairBranch.branch.sourceRecipient b
  have hqMem := Q.pairBranch.branch.sourceRecipient_mem b
  have hqV : dist q Erdos957Cases24.Case2.v = 1 := by
    simpa [q, Erdos957Cases24.Case4.v, dist_comm] using
      (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqMem).2.1
  have hqSide :
      dist q (Erdos957Case24Bridge.Case4.sideSource (!b)) = 1 := by
    have h := dist_canonical_of_adj Q.commonFrame.frame hadj
    rw [Q.current_secondary_vertex] at h
    change dist
      (Q.commonFrame.frame.toCanonical
        (cyclicSideVertex P (sourceIndex P W u hu) Q.twoExtreme.side))
      (Q.commonFrame.frame.toCanonical
        (Q.pairBranch.actualRecipient b)) = 1 at h
    rw [Q.commonFrame.side_coordinate] at h
    simpa [q, CommonCase4.CommonCase4HullPairBranch.actualRecipient,
      dist_comm] using h
  have hqNeLeft : q ≠ Erdos957Cases24.Case2.uPrev :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqMem).2.2.1
  have hqNeRight : q ≠ Erdos957Cases24.Case2.u :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqMem).2.2.2
  rw [Q.current_secondary_association]
  cases hside : Q.twoExtreme.side with
  | previous =>
      have hb : b = true := by
        simp [b, ActualCase24Rows.case4SourceIsRight, hside]
      rw [hb] at hqSide
      simp only [Bool.not_true, Erdos957Case24Bridge.Case4.sideSource] at hqSide
      have hq : q = leftContact :=
        (eq_u_or_leftContact_of_unit_to_uPrev_v hqSide hqV).resolve_left
          hqNeRight
      have hqActual : Q.pairBranch.branch.sourceRecipient true =
          leftContact := by
        simpa [q, hb] using hq
      change commonPairHorizontalAssociation Q.pairBranch.branch b = _
      rw [hb]
      simp [hqActual, leftContact, cyclicSideAssociation,
        commonPairHorizontalAssociation_right, horizontalAssociation,
        Erdos957Case24Bridge.Case4.sideSource,
        Erdos957Cases24.Case2.u, Erdos957Cases24.point] <;> norm_num
  | next =>
      have hb : b = false := by
        simp [b, ActualCase24Rows.case4SourceIsRight, hside]
      rw [hb] at hqSide
      simp only [Bool.not_false, Erdos957Case24Bridge.Case4.sideSource]
        at hqSide
      have hq : q = Erdos957Cases24.Case2.b :=
        (eq_uPrev_or_b_of_unit_to_u_v hqSide hqV).resolve_left hqNeLeft
      have hqActual : Q.pairBranch.branch.sourceRecipient false =
          Erdos957Cases24.Case2.b := by
        simpa [q, hb] using hq
      change commonPairHorizontalAssociation Q.pairBranch.branch b = _
      rw [hb]
      simp [hqActual, cyclicSideAssociation,
        commonPairHorizontalAssociation_left,
        Erdos957Case24Bridge.Case4.sideSource,
        Erdos957Cases24.Case2.b, Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.point] <;> norm_num

end Erdos957Case4CommonAssociations

#print axioms Erdos957Case4CommonAssociations.eq_uPrev_or_b_of_unit_to_u_v
#print axioms Erdos957Case4CommonAssociations.eq_u_or_leftContact_of_unit_to_uPrev_v
#print axioms Erdos957Case4CommonAssociations.CommonPairedCase4Rows.secondary_association_eq_opposite_of_adj_source
#print axioms Erdos957Case4CommonAssociations.CommonPairedCase4Rows.secondary_association_eq_side_of_adj_partner
