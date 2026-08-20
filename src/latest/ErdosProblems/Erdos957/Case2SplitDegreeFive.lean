import ErdosProblems.Erdos957.Case2WeightedAssembly
import ErdosProblems.Erdos957.Case2Case4SameSide

/-!
# Degree-five mixed Case-2/Case-4 split geometry

This downstream leaf keeps the remaining weighted exceptional geometry out of
the frozen Case-2 collision core.  It records the exact source-position
consequence of a same-associated Case-2 secondary / Case-4 split-right pair at
a degree-five target.  No (false) mixed pairwise uniqueness is asserted.
-/

noncomputable section

namespace Erdos957Case2SplitDegreeFive

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CollisionInstantiation
open Erdos957CaseClassification
open Erdos957Case2RoleUniqueness
open Erdos957Case2SecondaryNoThree
open Erdos957Case2Case4SameSide
open Erdos957CoherentRealizedRows
open Erdos957RoleCollisions

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

/-- At a degree-five Case-2 target, one further Case-2 source and one
Case-4 split source occupy two distinct members of the exact three-slot
set consisting of the incident partner and the first two away vertices.
This is the finite orbit normal form for the remaining weighted geometry. -/
theorem case2_split_near_pair_cases
    (hA : IsOneSeparated A)
    {s t u : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (G : Case4SplitRightFormula (P := P)
      (source := sourceIndex P W u.1 u.property) v)
    (F : P.FlatAlignedFrameData)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    let i := incidentHullVertex P
      (sourceIndex P W s.1 s.property) D.side 0
    let a₀ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 0
    let a₁ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 1
    (sourceIndex P W t.1 t.property = i ∧
        sourceIndex P W u.1 u.property = a₀) ∨
      (sourceIndex P W t.1 t.property = i ∧
        sourceIndex P W u.1 u.property = a₁) ∨
      (sourceIndex P W t.1 t.property = a₀ ∧
        sourceIndex P W u.1 u.property = i) ∨
      (sourceIndex P W t.1 t.property = a₀ ∧
        sourceIndex P W u.1 u.property = a₁) ∨
      (sourceIndex P W t.1 t.property = a₁ ∧
        sourceIndex P W u.1 u.property = i) ∨
      (sourceIndex P W t.1 t.property = a₁ ∧
        sourceIndex P W u.1 u.property = a₀) := by
  have ht := Case2SecondaryFormula.case2_competitor_near_slots_of_degree_five
    hA D E F hdegree htWindow hst
  have hu :=
    Case2SecondaryFormula.case4SplitRight_competitor_near_slots_of_degree_five
      hA D G F hdegree huWindow hsu
  rcases ht with ht | ht | ht <;> rcases hu with hu | hu | hu
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)
  · exact Or.inl ⟨ht, hu⟩
  · exact Or.inr (Or.inl ⟨ht, hu⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ht, hu⟩))
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hu⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hu⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, hu⟩))))
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)

/-- The analogous six-slot normal form for two distinct Case-4 split
competitors of one degree-five Case-2 secondary target. -/
theorem two_split_near_pair_cases
    (hA : IsOneSeparated A)
    {s t u : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case4SplitRightFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (G : Case4SplitRightFormula (P := P)
      (source := sourceIndex P W u.1 u.property) v)
    (F : P.FlatAlignedFrameData)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    let i := incidentHullVertex P
      (sourceIndex P W s.1 s.property) D.side 0
    let a₀ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 0
    let a₁ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 1
    (sourceIndex P W t.1 t.property = i ∧
        sourceIndex P W u.1 u.property = a₀) ∨
      (sourceIndex P W t.1 t.property = i ∧
        sourceIndex P W u.1 u.property = a₁) ∨
      (sourceIndex P W t.1 t.property = a₀ ∧
        sourceIndex P W u.1 u.property = i) ∨
      (sourceIndex P W t.1 t.property = a₀ ∧
        sourceIndex P W u.1 u.property = a₁) ∨
      (sourceIndex P W t.1 t.property = a₁ ∧
        sourceIndex P W u.1 u.property = i) ∨
      (sourceIndex P W t.1 t.property = a₁ ∧
        sourceIndex P W u.1 u.property = a₀) := by
  have ht :=
    Case2SecondaryFormula.case4SplitRight_competitor_near_slots_of_degree_five
      hA D E F hdegree htWindow hst
  have hu :=
    Case2SecondaryFormula.case4SplitRight_competitor_near_slots_of_degree_five
      hA D G F hdegree huWindow hsu
  rcases ht with ht | ht | ht <;> rcases hu with hu | hu | hu
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)
  · exact Or.inl ⟨ht, hu⟩
  · exact Or.inr (Or.inl ⟨ht, hu⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ht, hu⟩))
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hu⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hu⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, hu⟩))))
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)

/-- The two unit circles centered at the canonical incident endpoint and at
the first lower Case-2 continuation are tangent at the canonical middle. -/
private lemma eq_case2_v_of_unit_to_uPrev_w
    {x : Erdos957Cases24.Point}
    (hprev : dist Erdos957Cases24.Case2.uPrev x = 1)
    (hw : dist Erdos957Cases24.Case2.w x = 1) :
    x = Erdos957Cases24.Case2.v := by
  have hprevSq := congrArg (fun r : ℝ ↦ r ^ 2) hprev
  have hwSq := congrArg (fun r : ℝ ↦ r ^ 2) hw
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hprevSq hwSq
  apply Erdos957Cases24.point_ext
  · simp only [Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.w, Erdos957Cases24.Case2.v,
      Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at hprevSq hwSq ⊢
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  · simp only [Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.w, Erdos957Cases24.Case2.v,
      Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at hprevSq hwSq ⊢
    nlinarith [Erdos957Cases24.sqrtThree_sq]

/-- A degree-five Case-2 secondary cannot also be selected by a split Case-4
source at the Case-2 incident endpoint.  If the Case-2 target is `wNext`, its
distance from that endpoint is already greater than two.  If it is `w`, the
retained Case-4 middle is the unique common unit neighbour of `uPrev,w`, hence
is the Case-2 degree-six middle, contradicting the Case-4 middle degree five.

This is independent of the two arrival associations and is the first genuine
strict exceptional reduction beyond the three-slot metric normal form. -/
theorem no_case4SplitRight_at_incident_of_case2_degree_five
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htIncident :
      let B := Classical.choice
        (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
      sourceIndex P W t.1 t.property =
        incidentHullVertex P (sourceIndex P W s.1 s.property)
          B.formula.side 0) : False := by
  let B := Classical.choice
    (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
  obtain ⟨E⟩ := exists_case4SplitRightFormula T.target htRole
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  have htCoord : B.formula.edgeFrame.toCanonical
      (sourceIndex P W t.1 t.property).1 =
        Erdos957Cases24.Case2.uPrev := by
    rw [htIncident]
    have hside0 : incidentHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0 =
          cyclicSideVertex P (sourceIndex P W s.1 s.property)
            B.formula.side := by
      cases B.formula.side <;>
        simp [incidentHullVertex, cyclicSideVertex]
    rw [hside0, ← B.formula.side_actual,
      B.formula.edgeFrame.toCanonical_actual]
  have hslot : T.target.target = Qt.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← T.target.target_at_role, htRole, Qt.current_secondary_role]
  have hvSecondary : Qt.currentSecondaryTarget.vertex = v := by
    calc
      Qt.currentSecondaryTarget.vertex = T.target.target.vertex :=
        congrArg LocalTarget.vertex hslot.symm
      _ = v := T.target.vertex_eq.symm
  have htarget :=
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.target_eq_w_or_wNext_of_degree_five
      hA B.formula hdegree
  rcases htarget with hw | hwNext
  · have htMiddle : dist
        ((sourceIndex P W t.1 t.property).1 : Point)
        (Qt.middle : Point) = 1 := by
      calc
        _ = dist
            (Qt.normalized.frame.toCanonical
              (sourceIndex P W t.1 t.property).1)
            (Qt.normalized.frame.toCanonical Qt.middle) :=
              (Qt.normalized.frame.dist_eq _ _).symm
        _ = dist Erdos957Cases24.Case2.u
            Erdos957Cases24.Case2.v := by
          rw [← Qt.normalized.source_actual,
            ← Qt.normalized.middle_actual,
            Qt.normalized.frame.toCanonical_actual,
            Qt.normalized.frame.toCanonical_actual]
        _ = 1 := Erdos957Cases24.Case2.dist_u_v
    have hprev : dist Erdos957Cases24.Case2.uPrev
        (B.formula.edgeFrame.toCanonical Qt.middle) = 1 := by
      calc
        _ = dist
            (B.formula.edgeFrame.toCanonical
              (sourceIndex P W t.1 t.property).1)
            (B.formula.edgeFrame.toCanonical Qt.middle) := by rw [htCoord]
        _ = dist ((sourceIndex P W t.1 t.property).1 : Point)
            (Qt.middle : Point) := B.formula.edgeFrame.dist_eq _ _
        _ = 1 := htMiddle
    have hmiddleSecondary :=
      Erdos957Case4SplitClassification.CommonPairedCase4Rows.middle_adj_currentSecondary Qt
    have hmiddleV : dist (Qt.middle : Point) (v : Point) = 1 := by
      change dist (Qt.middle : Point)
        (Qt.currentSecondaryTarget.vertex : Point) = 1 at hmiddleSecondary
      simpa [hvSecondary] using hmiddleSecondary
    have hwUnit : dist Erdos957Cases24.Case2.w
        (B.formula.edgeFrame.toCanonical Qt.middle) = 1 := by
      calc
        _ = dist (B.formula.edgeFrame.toCanonical v)
            (B.formula.edgeFrame.toCanonical Qt.middle) := by rw [hw]
        _ = dist (v : Point) (Qt.middle : Point) :=
          B.formula.edgeFrame.dist_eq _ _
        _ = 1 := by simpa [dist_comm] using hmiddleV
    have hmiddleCoord := eq_case2_v_of_unit_to_uPrev_w hprev hwUnit
    have hmiddleEq : Qt.middle = B.formula.middle := by
      apply Subtype.ext
      apply B.formula.edgeFrame.toCanonical.injective
      rw [hmiddleCoord, ← B.formula.middle_actual,
        B.formula.edgeFrame.toCanonical_actual]
    have hmiddleDegree := B.formula.middle_degree_six
    rw [← hmiddleEq, Qt.middle_degree_five] at hmiddleDegree
    omega
  · have hdistLe : dist Erdos957Cases24.Case2.uPrev
        Erdos957Cases24.Case2.wNext ≤ 2 := by
      calc
        _ = dist
            (B.formula.edgeFrame.toCanonical
              (sourceIndex P W t.1 t.property).1)
            (B.formula.edgeFrame.toCanonical v) := by
          rw [htCoord, hwNext]
        _ = dist ((sourceIndex P W t.1 t.property).1 : Point)
            (v : Point) := B.formula.edgeFrame.dist_eq _ _
        _ ≤ 2 := E.source_target_dist_le_two
    have hsq := Erdos957Cases24.dist_sq_eq_coordinates
      Erdos957Cases24.Case2.uPrev Erdos957Cases24.Case2.wNext
    simp only [Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.wNext,
      Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at hsq
    have hnonneg := dist_nonneg
      (x := Erdos957Cases24.Case2.uPrev)
      (y := Erdos957Cases24.Case2.wNext)
    have hdistSqLe : dist Erdos957Cases24.Case2.uPrev
        Erdos957Cases24.Case2.wNext ^ 2 ≤ 4 := by
      nlinarith only [hdistLe, hnonneg]
    norm_num [Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.wNext] at hsq
    change (dist (Erdos957Cases24.point (-1) 0)
      (Erdos957Cases24.point 1 (-Erdos957Cases24.sqrtThree))) ^ 2 ≤ 4 at hdistSqLe
    nlinarith only [hsq, hdistSqLe, Erdos957Cases24.sqrtThree_sq]

/-- At degree five, a distinct same-associated Case-4 split source relative
to a Case-2 secondary anchor can only be the incident endpoint or the first
source continuing away from the Case-2 edge.  The general metric reduction
leaves three slots; the second away slot has the opposite recipient-relative
association by the checked two-edge transport theorem.

The incident alternative is intentionally retained: excluding it (when its
Case-4 edge points outward) and handling the surviving away-first pair require
the final strict-turn/equilateral triple argument. -/
theorem case2Secondary_case4SplitRight_same_association_near_slots
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t)
    (hassoc : S.descriptor.association = T.descriptor.association) :
    let B := Classical.choice
      (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
    sourceIndex P W t.1 t.property =
        incidentHullVertex P (sourceIndex P W s.1 s.property)
          B.formula.side 0 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property)
          B.formula.side 0 := by
  let B := Classical.choice
    (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
  obtain ⟨E⟩ := exists_case4SplitRightFormula T.target htRole
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  rcases
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.case4SplitRight_competitor_near_slots_of_degree_five
        hA B.formula E F hdegree htWindow hst with
    hincident | haway | hawaySecond
  · exact Or.inl hincident
  · exact Or.inr haway
  · exact (case2Secondary_case4SplitRight_associations_ne_at_away_second
      hA Q S T hsRole htRole B Qt hawaySecond hassoc).elim

/-- With the degree-five incident endpoint now excluded, the surviving
same-associated mixed pair has one exact source position: the first hull
vertex continuing away from the Case-2 incident edge. -/
theorem case2Secondary_case4SplitRight_same_association_eq_away_first
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t)
    (hassoc : S.descriptor.association = T.descriptor.association) :
    let B := Classical.choice
      (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
    sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0 := by
  rcases case2Secondary_case4SplitRight_same_association_near_slots
      hA Q S T hsRole htRole hdegree htWindow hst hassoc with
    hincident | haway
  · exact (no_case4SplitRight_at_incident_of_case2_degree_five
      hA Q S T hsRole htRole hdegree hincident).elim
  · exact haway

/-- If the second Case-2 source is the incident endpoint, the common
degree-five target is the nearer canonical continuation `w`. -/
theorem target_eq_w_of_case2Secondary_at_incident_of_degree_five
    (hA : IsOneSeparated A)
    {s t : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htIndex : sourceIndex P W t.1 t.property =
      incidentHullVertex P (sourceIndex P W s.1 s.property) D.side 0) :
    D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.w := by
  have htCoord : D.edgeFrame.toCanonical
      (sourceIndex P W t.1 t.property).1 =
      Erdos957Cases24.Case2.uPrev := by
    rw [htIndex]
    have heq :
        incidentHullVertex P (sourceIndex P W s.1 s.property) D.side 0 =
          cyclicSideVertex P (sourceIndex P W s.1 s.property) D.side := by
      cases D.side <;> simp [incidentHullVertex, cyclicSideVertex]
    rw [heq]
    exact D.side_edge_coordinate
  rcases Case2SecondaryFormula.target_eq_w_or_wNext_of_degree_five
      hA D hdegree with hw | hwNext
  · exact hw
  · have hmetric := E.source_target_sq_distance_cases
    have htransport : dist Erdos957Cases24.Case2.uPrev
        Erdos957Cases24.Case2.wNext =
        dist ((sourceIndex P W t.1 t.property).1 : Point) (v : Point) := by
      calc
        _ = dist (D.edgeFrame.toCanonical
            (sourceIndex P W t.1 t.property).1)
            (D.edgeFrame.toCanonical v) := by rw [htCoord, hwNext]
        _ = _ := D.edgeFrame.dist_eq _ _
    have hdist : dist Erdos957Cases24.Case2.uPrev
        Erdos957Cases24.Case2.wNext ^ 2 = 3 ∨
        dist Erdos957Cases24.Case2.uPrev
          Erdos957Cases24.Case2.wNext ^ 2 = 4 := by
      rw [htransport]
      exact hmetric
    have hsq := Erdos957Cases24.dist_sq_eq_coordinates
      Erdos957Cases24.Case2.uPrev Erdos957Cases24.Case2.wNext
    rcases hdist with hdist | hdist <;>
      rw [hsq] at hdist <;>
      simp only [Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.wNext,
        Erdos957Cases24.point_apply_zero,
        Erdos957Cases24.point_apply_one] at hdist <;>
      nlinarith [Erdos957Cases24.sqrtThree_sq]

/-- If the Case-2 target is canonical `w`, a split Case-4 source cannot be
the second source on the away prefix: the flat-prefix bounds place it more
than two units from `w`. -/
theorem no_case4SplitRight_at_away_second_of_target_eq_w
    {s t : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (G : Case4SplitRightFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (F : P.FlatAlignedFrameData)
    (hw : D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.w)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) D.side 1) : False := by
  let z := D.edgeFrame.toCanonical (sourceIndex P W t.1 t.property).1
  have hi := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s
  have hmetric := Case2SecondaryFormula.away_prefix_bounds D F hi 1
  have hmetric' : z 1 < 0 ∧ (2 : ℝ) * (399 / 400 : ℝ) < z 0 ∧
      -z 1 ≤ z 0 / 10 := by
    change (D.edgeFrame.toCanonical
        (Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 1).1) 1 < 0 ∧
      (2 : ℝ) * (399 / 400 : ℝ) <
        (D.edgeFrame.toCanonical
          (Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) D.side 1).1) 0 ∧
      -(D.edgeFrame.toCanonical
          (Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) D.side 1).1) 1 ≤
        (D.edgeFrame.toCanonical
          (Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) D.side 1).1) 0 / 10 at hmetric
    rw [← htIndex] at hmetric
    exact hmetric
  rcases hmetric' with ⟨hyNeg, hx, hy⟩
  have hdist : dist z Erdos957Cases24.Case2.w ≤ 2 := by
    calc
      _ = dist (D.edgeFrame.toCanonical
          (sourceIndex P W t.1 t.property).1)
          (D.edgeFrame.toCanonical v) := by rw [hw]
      _ = dist ((sourceIndex P W t.1 t.property).1 : Point) (v : Point) :=
        D.edgeFrame.dist_eq _ _
      _ ≤ 2 := G.source_target_dist_le_two
  have hsq := Erdos957Cases24.dist_sq_eq_coordinates
    z Erdos957Cases24.Case2.w
  have hdistNonneg := dist_nonneg (x := z) (y := Erdos957Cases24.Case2.w)
  have hsqLe : (z 0) ^ 2 +
      (z 1 + Erdos957Cases24.sqrtThree) ^ 2 ≤ 4 := by
    have hdistSq : dist z Erdos957Cases24.Case2.w ^ 2 ≤ 4 := by
      nlinarith only [hdist, hdistNonneg]
    rw [hsq] at hdistSq
    simpa only [Erdos957Cases24.Case2.w,
      Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one, sub_zero,
      sub_neg_eq_add] using hdistSq
  have hxUpper : z 0 ≤ 2 := by
    nlinarith only [hsqLe,
      sq_nonneg (z 1 + Erdos957Cases24.sqrtThree)]
  have hyLower : -(1 / 5 : ℝ) ≤ z 1 := by
    linarith only [hy, hxUpper]
  have hsqrtLower : (3 / 2 : ℝ) < Erdos957Cases24.sqrtThree := by
    nlinarith [Erdos957Cases24.sqrtThree_sq,
      Erdos957Cases24.sqrtThree_pos]
  have hxLower : (19 / 10 : ℝ) < z 0 := by linarith only [hx]
  have hysLower : (13 / 10 : ℝ) <
      z 1 + Erdos957Cases24.sqrtThree := by
    linarith only [hyLower, hsqrtLower]
  have hxSq : (19 / 10 : ℝ) ^ 2 < (z 0) ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by linarith only [hxLower])).2 hxLower
  have hysSq : (13 / 10 : ℝ) ^ 2 <
      (z 1 + Erdos957Cases24.sqrtThree) ^ 2 :=
    (sq_lt_sq₀ (by norm_num) (by linarith only [hysLower])).2 hysLower
  nlinarith only [hsqLe, hxSq, hysSq]

/-- A split source in the first away slot cannot select the edge back toward
the Case-2 anchor.  If it did, the anchor would be the coherent partner of a
selected split row, contradicting the anchor row's retained Case-2 shape. -/
theorem case4SplitRight_side_ne_case2_side_at_away_first
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (B : Case2SecondaryArrivalFormula S.target S.descriptor)
    (Qt : CommonPairedCase4Rows Q.rows t.1 t.property)
    (htAway : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0) :
    Qt.twoExtreme.side ≠ B.formula.side := by
  intro hside
  apply no_case2Secondary_at_incident_partner_of_case4SplitRight
    Q S T hsRole htRole Qt
  cases hB : B.formula.side <;>
    cases hQ : Qt.twoExtreme.side <;>
    simp_all [Erdos957Case4NoThree.awayHullVertex, cyclicSideVertex]

/-- The six metric position pairs for two Case-2 arrivals and one split
arrival collapse to two genuine configurations.  In both, the split source
is the first away source.  The other Case-2 source is either the incident
endpoint or the second away source. -/
theorem case2_split_near_pair_cases_reduced
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case2Secondary)
    (huRole : U.target.role = PairCases.TargetRoleName.case4SplitRight)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    let B := Classical.choice
      (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
    let i := incidentHullVertex P
      (sourceIndex P W s.1 s.property) B.formula.side 0
    let a₀ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) B.formula.side 0
    let a₁ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) B.formula.side 1
    (sourceIndex P W t.1 t.property = i ∧
        sourceIndex P W u.1 u.property = a₀) ∨
      (sourceIndex P W t.1 t.property = a₀ ∧
        sourceIndex P W u.1 u.property = a₁) ∨
      (sourceIndex P W t.1 t.property = a₁ ∧
        sourceIndex P W u.1 u.property = a₀) := by
  let Bs := Classical.choice
    (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
  let Bt := Classical.choice
    (nonempty_case2SecondaryArrivalFormula T.target T.descriptor htRole)
  obtain ⟨G⟩ := exists_case4SplitRightFormula U.target huRole
  rcases case2_split_near_pair_cases hA Bs.formula Bt.formula G F hdegree
      htWindow huWindow hst hsu htu with
    hIA₀ | hIA₁ | hA₀I | hA₀A₁ | hA₁I | hA₁A₀
  · exact Or.inl hIA₀
  · rcases hIA₁ with ⟨htI, huA₁⟩
    have hw := target_eq_w_of_case2Secondary_at_incident_of_degree_five
      hA Bs.formula Bt.formula hdegree htI
    exact (no_case4SplitRight_at_away_second_of_target_eq_w
      Bs.formula G F hw huA₁).elim
  · exact (no_case4SplitRight_at_incident_of_case2_degree_five
      hA Q S U hsRole huRole hdegree hA₀I.2).elim
  · exact Or.inr (Or.inl hA₀A₁)
  · exact (no_case4SplitRight_at_incident_of_case2_degree_five
      hA Q S U hsRole huRole hdegree hA₁I.2).elim
  · exact Or.inr (Or.inr hA₁A₀)

/-- If the second Case-2 source is the second away source and the split
source is the first away source, the split's selected edge must point
outward.  Its other endpoint is therefore exactly the second Case-2 source,
which pair coherence excludes. -/
theorem no_case2_away_second_case4_away_first
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (B : Case2SecondaryArrivalFormula S.target S.descriptor)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case2Secondary)
    (huRole : U.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1)
    (huIndex : sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0) : False := by
  let Qu := Q.case4_pair u.1 u.property
    ⟨U.target.target, by simpa [huRole] using U.target.target_at_role⟩
  have hsideNe := case4SplitRight_side_ne_case2_side_at_away_first
    Q S U hsRole huRole B Qu huIndex
  apply no_case2Secondary_at_incident_partner_of_case4SplitRight
    Q T U htRole huRole Qu
  rw [htIndex]
  apply Subtype.ext
  cases hB : B.formula.side <;>
    cases hQ : Qu.twoExtreme.side <;>
    simp_all [Erdos957Case4NoThree.awayHullVertex,
      cyclicSideVertex, pow_succ]

end Erdos957Case2SplitDegreeFive

namespace Erdos957Case2SplitDegreeFive

#print axioms case2Secondary_case4SplitRight_same_association_near_slots
#print axioms case2_split_near_pair_cases
#print axioms two_split_near_pair_cases
#print axioms no_case4SplitRight_at_incident_of_case2_degree_five
#print axioms case2Secondary_case4SplitRight_same_association_eq_away_first
#print axioms target_eq_w_of_case2Secondary_at_incident_of_degree_five
#print axioms no_case4SplitRight_at_away_second_of_target_eq_w
#print axioms case4SplitRight_side_ne_case2_side_at_away_first
#print axioms case2_split_near_pair_cases_reduced
#print axioms no_case2_away_second_case4_away_first

end Erdos957Case2SplitDegreeFive
