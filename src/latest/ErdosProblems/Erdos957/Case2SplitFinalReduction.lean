import ErdosProblems.Erdos957.Case2SplitDegreeFive

/-!
# Final finite reduction for the degree-five Case-2 split residuals

The metric/window classification leaves three exact source slots relative to
the Case-2 anchor: the incident endpoint and the first two vertices continuing
away from that endpoint.  The checked incident and second-away eliminators
remove every branch except three ordered Case-2/split configurations and one
unordered split/split configuration.  This file packages precisely those four
outward-facing geometric leaves, without asserting any pairwise uniqueness.
-/

noncomputable section

namespace Erdos957Case2SplitFinalReduction

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CollisionInstantiation
open Erdos957CaseClassification
open Erdos957Case2RoleUniqueness
open Erdos957Case2SecondaryNoThree
open Erdos957CoherentRealizedRows
open Erdos957RoleCollisions
open Erdos957Case2SplitDegreeFive
open Erdos957Case4SplitClassification

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

private lemma incident_away_first_same_side
    (source : {p // p ∈ P.H}) (side : CyclicSide) :
    incidentHullVertex P
      (Erdos957Case4NoThree.awayHullVertex P source side 0) side 0 =
        source := by
  cases side <;>
    simp [Erdos957Case4NoThree.awayHullVertex,
      incidentHullVertex, pow_succ]

private lemma away_second_eq_away_first_twice
    (source : {p // p ∈ P.H}) (side : CyclicSide) :
    Erdos957Case4NoThree.awayHullVertex P source side 1 =
      Erdos957Case4NoThree.awayHullVertex P
        (Erdos957Case4NoThree.awayHullVertex P source side 0) side 0 := by
  cases side <;>
    simp [Erdos957Case4NoThree.awayHullVertex, pow_succ]

private lemma away_second_eq_incident_away_first_of_side_ne
    (source : {p // p ∈ P.H}) {side other : CyclicSide}
    (hne : other ≠ side) :
    Erdos957Case4NoThree.awayHullVertex P source side 1 =
      incidentHullVertex P
        (Erdos957Case4NoThree.awayHullVertex P source side 0) other 0 := by
  cases side <;> cases other <;>
    simp_all [Erdos957Case4NoThree.awayHullVertex,
      incidentHullVertex, pow_succ]

/-- A unit edge controls horizontal displacement in any retained rigid
chart.  This public copy is kept in the final reduction module because the
corresponding Case-4 classification helper is intentionally private. -/
lemma abs_fst_sub_le_one_of_adj
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    {a b : Vertex A} (hab : (unitDistanceGraph A).Adj a b) :
    |(E.toCanonical a) 0 - (E.toCanonical b) 0| ≤ 1 := by
  have hdist : dist (E.toCanonical a) (E.toCanonical b) = 1 := by
    rw [E.dist_eq]
    exact hab
  have hs := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical a) (E.toCanonical b)
  rw [hdist] at hs
  have hy : 0 ≤ ((E.toCanonical a) 1 - (E.toCanonical b) 1) ^ 2 :=
    sq_nonneg _
  have hx : ((E.toCanonical a) 0 - (E.toCanonical b) 0) ^ 2 ≤ 1 := by
    nlinarith only [hs, hy]
  rw [abs_le]
  constructor <;> nlinarith only [hx,
    sq_nonneg ((E.toCanonical a) 0 - (E.toCanonical b) 0 - 1),
    sq_nonneg ((E.toCanonical a) 0 - (E.toCanonical b) 0 + 1)]

/-- A common unit neighbour of the endpoints of an almost-horizontal edge
whose first endpoint is already past `399/400` lies strictly past `x=1`.
This is the exact analytic kernel needed by the outward mixed branch. -/
lemma common_unit_neighbor_fst_gt_one_of_flat_second_edge
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    {a b m : Vertex A}
    (ha : (399 / 400 : ℝ) < (E.toCanonical a) 0)
    (habx : (399 / 400 : ℝ) <
      (E.toCanonical b) 0 - (E.toCanonical a) 0)
    (hab : (unitDistanceGraph A).Adj a b)
    (ham : (unitDistanceGraph A).Adj a m)
    (hbm : (unitDistanceGraph A).Adj b m) :
    1 < (E.toCanonical m) 0 := by
  let dx := (E.toCanonical b) 0 - (E.toCanonical a) 0
  let dy := (E.toCanonical b) 1 - (E.toCanonical a) 1
  let ex := (E.toCanonical m) 0 - (E.toCanonical a) 0
  let ey := (E.toCanonical m) 1 - (E.toCanonical a) 1
  have habDist : dist (E.toCanonical a) (E.toCanonical b) = 1 := by
    rw [E.dist_eq]
    exact hab
  have hamDist : dist (E.toCanonical a) (E.toCanonical m) = 1 := by
    rw [E.dist_eq]
    exact ham
  have hbmDist : dist (E.toCanonical b) (E.toCanonical m) = 1 := by
    rw [E.dist_eq]
    exact hbm
  have habSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical a) (E.toCanonical b)
  have hamSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical a) (E.toCanonical m)
  have hbmSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical b) (E.toCanonical m)
  rw [habDist] at habSq
  rw [hamDist] at hamSq
  rw [hbmDist] at hbmSq
  norm_num at habSq hamSq hbmSq
  have hedge : dx ^ 2 + dy ^ 2 = 1 := by
    dsimp [dx, dy]
    nlinarith only [habSq]
  have hmiddle : ex ^ 2 + ey ^ 2 = 1 := by
    dsimp [ex, ey]
    nlinarith only [hamSq]
  have hother : (ex - dx) ^ 2 + (ey - dy) ^ 2 = 1 := by
    dsimp [dx, dy, ex, ey]
    nlinarith only [hbmSq]
  have hdot : dx * ex + dy * ey = 1 / 2 := by
    nlinarith only [hedge, hmiddle, hother]
  have hdx : (399 / 400 : ℝ) < dx := by
    simpa only [dx] using habx
  have hdxpos : 0 < dx := by
    norm_num at hdx ⊢
    linarith only [hdx]
  have hdxSq : (399 / 400 : ℝ) ^ 2 < dx ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hdxpos.le).2 hdx
  have hdySq : dy ^ 2 < (1 / 10 : ℝ) ^ 2 := by
    norm_num at hdxSq ⊢
    nlinarith only [hedge, hdxSq]
  have heySq : ey ^ 2 ≤ 1 := by
    nlinarith only [hmiddle, sq_nonneg ex]
  have hprodSq : (dy * ey) ^ 2 < (1 / 10 : ℝ) ^ 2 := by
    calc
      (dy * ey) ^ 2 = dy ^ 2 * ey ^ 2 := by ring
      _ ≤ dy ^ 2 := by
        simpa only [mul_comm] using
          (mul_le_of_le_one_left (sq_nonneg dy) heySq)
      _ < (1 / 10 : ℝ) ^ 2 := hdySq
  have hprodAbsSq : |dy * ey| ^ 2 < (1 / 10 : ℝ) ^ 2 := by
    simpa only [sq_abs] using hprodSq
  have hprodAbs : |dy * ey| < (1 / 10 : ℝ) :=
    (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).1 hprodAbsSq
  have hprodUpper : dy * ey < (1 / 10 : ℝ) := (abs_lt.mp hprodAbs).2
  have hdex : (2 / 5 : ℝ) < dx * ex := by
    nlinarith only [hdot, hprodUpper]
  have hdxSqLe : dx ^ 2 ≤ (1 : ℝ) ^ 2 := by
    nlinarith only [hedge, sq_nonneg dy]
  have hdxLe : dx ≤ 1 :=
    (sq_le_sq₀ hdxpos.le (by norm_num)).1 hdxSqLe
  have hdexPos : 0 < dx * ex := by
    norm_num at hdex ⊢
    linarith only [hdex]
  have hexpos : 0 < ex := by
    rcases mul_pos_iff.mp hdexPos with h | h
    · exact h.2
    · exact (not_lt_of_ge hdxpos.le h.1).elim
  have hdexLe : dx * ex ≤ ex := by
    simpa only [mul_comm] using
      (mul_le_of_le_one_left hexpos.le hdxLe)
  dsimp [ex] at hexpos hdexLe ⊢
  linarith only [ha, hdex, hdexLe]

/-- Packaged form of the outward-middle estimate.  It exposes exactly the
coordinate bound needed by the final two-split strict-boundary argument,
without requiring that argument to reconstruct the common-edge algebra. -/
theorem case4SplitRight_outward_away_first_middle_fst_gt_one
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (huRole : U.target.role = PairCases.TargetRoleName.case4SplitRight)
    (B : Case2SecondaryArrivalFormula S.target S.descriptor)
    (huAway : sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0) :
    1 < (B.formula.edgeFrame.toCanonical
      (Q.case4_pair u.1 u.property
        ⟨U.target.target,
          by simpa [huRole] using U.target.target_at_role⟩).middle) 0 := by
  let Qu := Q.case4_pair u.1 u.property
    ⟨U.target.target, by simpa [huRole] using U.target.target_at_role⟩
  have hsideNe : Qu.twoExtreme.side ≠ B.formula.side :=
    case4SplitRight_side_ne_case2_side_at_away_first
      Q S U hsRole huRole B Qu huAway
  have hendpoint : cyclicSideVertex P
      (sourceIndex P W u.1 u.property) Qu.twoExtreme.side =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1 := by
    apply Subtype.ext
    have huValue := congrArg Subtype.val huAway
    cases hs : B.formula.side <;>
      cases hu : Qu.twoExtreme.side <;>
      simp_all [Erdos957Case4NoThree.awayHullVertex,
        cyclicSideVertex, pow_succ]
  have hi := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s
  have ha := (Case2SecondaryFormula.away_prefix_bounds
    B.formula F hi 0).2.1
  norm_num at ha
  have habx := Case2SecondaryFormula.away_second_increment_gt
    B.formula F hi
  have hab : (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0).1
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1).1 := by
    rw [← huAway, ← hendpoint]
    exact Qu.normalized.side_unit
  have ham : (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0).1 Qu.middle := by
    rw [← huAway]
    exact CommonPairedCase4Rows.source_adj_middle Qu
  have hbm : (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1).1 Qu.middle := by
    rw [← hendpoint]
    exact Qu.twoExtreme.side_adjacent.symm
  exact common_unit_neighbor_fst_gt_one_of_flat_second_edge
    B.formula.edgeFrame ha habx hab ham hbm

/-- The mixed outward branch with the other Case-2 source at the incident
endpoint is impossible.  That source pins the target to canonical `w`, while
the outward Case-4 middle lies past `x=1` and is unit-adjacent to a target at
`x=0`. -/
theorem no_case4SplitRight_at_outward_away_first_of_target_eq_w
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (huRole : U.target.role = PairCases.TargetRoleName.case4SplitRight)
    (B : Case2SecondaryArrivalFormula S.target S.descriptor)
    (hw : B.formula.edgeFrame.toCanonical v = Erdos957Cases24.Case2.w)
    (huAway : sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0) : False := by
  let Qu := Q.case4_pair u.1 u.property
    ⟨U.target.target, by simpa [huRole] using U.target.target_at_role⟩
  have hsideNe : Qu.twoExtreme.side ≠ B.formula.side :=
    case4SplitRight_side_ne_case2_side_at_away_first
      Q S U hsRole huRole B Qu huAway
  have hendpoint : cyclicSideVertex P
      (sourceIndex P W u.1 u.property) Qu.twoExtreme.side =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1 := by
    apply Subtype.ext
    have huValue := congrArg Subtype.val huAway
    cases hs : B.formula.side <;>
      cases hu : Qu.twoExtreme.side <;>
      simp_all [Erdos957Case4NoThree.awayHullVertex,
        cyclicSideVertex, pow_succ]
  have hi := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s
  have ha := (Case2SecondaryFormula.away_prefix_bounds
    B.formula F hi 0).2.1
  norm_num at ha
  have habx := Case2SecondaryFormula.away_second_increment_gt
    B.formula F hi
  have hab : (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0).1
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1).1 := by
    rw [← huAway, ← hendpoint]
    exact Qu.normalized.side_unit
  have ham : (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0).1 Qu.middle := by
    rw [← huAway]
    exact CommonPairedCase4Rows.source_adj_middle Qu
  have hbm : (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1).1 Qu.middle := by
    rw [← hendpoint]
    exact Qu.twoExtreme.side_adjacent.symm
  have hmX : 1 < (B.formula.edgeFrame.toCanonical Qu.middle) 0 := by
    exact common_unit_neighbor_fst_gt_one_of_flat_second_edge
      B.formula.edgeFrame ha habx hab ham hbm
  have htarget : U.target.target = Qu.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← U.target.target_at_role, huRole, Qu.current_secondary_role]
  have hv : Qu.currentSecondaryTarget.vertex = v := by
    calc
      Qu.currentSecondaryTarget.vertex = U.target.target.vertex :=
        congrArg LocalTarget.vertex htarget.symm
      _ = v := U.target.vertex_eq.symm
  have hmv := CommonPairedCase4Rows.middle_adj_currentSecondary Qu
  have hhorizontal := abs_fst_sub_le_one_of_adj B.formula.edgeFrame hmv
  rw [hv, hw] at hhorizontal
  norm_num [Erdos957Cases24.Case2.w] at hhorizontal
  have hmUpper : (B.formula.edgeFrame.toCanonical Qu.middle) 0 ≤ 1 :=
    (abs_le.mp hhorizontal).2
  linarith only [hmX, hmUpper]

/-- The entire mixed degree-five field is now contradiction-free of any
residual premise.  In the only nontrivial adjacent-away orientation, recenter
at the second Case-2 source.  Its retained side either makes the split source
the incident endpoint, or makes the first Case-2 source incident and reduces
to `no_case4SplitRight_at_outward_away_first_of_target_eq_w`. -/
theorem no_case2_case2_case4SplitRight_degree_five
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
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) : False := by
  let Bs := Classical.choice
    (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
  let Bt := Classical.choice
    (nonempty_case2SecondaryArrivalFormula T.target T.descriptor htRole)
  obtain ⟨G⟩ := exists_case4SplitRightFormula U.target huRole
  rcases case2_split_near_pair_cases hA Bs.formula Bt.formula G F hdegree
      htWindow huWindow hst hsu htu with
    hIA₀ | hIA₁ | hA₀I | hA₀A₁ | hA₁I | hA₁A₀
  · have hw := target_eq_w_of_case2Secondary_at_incident_of_degree_five
        hA Bs.formula Bt.formula hdegree hIA₀.1
    exact no_case4SplitRight_at_outward_away_first_of_target_eq_w
      Q S U hsRole huRole Bs hw hIA₀.2
  · have hw := target_eq_w_of_case2Secondary_at_incident_of_degree_five
        hA Bs.formula Bt.formula hdegree hIA₁.1
    exact no_case4SplitRight_at_away_second_of_target_eq_w
      Bs.formula G F hw hIA₁.2
  · exact no_case4SplitRight_at_incident_of_case2_degree_five
      hA Q S U hsRole huRole hdegree hA₀I.2
  · by_cases hside : Bt.formula.side = Bs.formula.side
    · have hsIncident : sourceIndex P W s.1 s.property =
          incidentHullVertex P (sourceIndex P W t.1 t.property)
            Bt.formula.side 0 := by
        calc
          sourceIndex P W s.1 s.property =
              incidentHullVertex P
                (Erdos957Case4NoThree.awayHullVertex P
                  (sourceIndex P W s.1 s.property) Bs.formula.side 0)
                Bs.formula.side 0 :=
            (incident_away_first_same_side
              (sourceIndex P W s.1 s.property) Bs.formula.side).symm
          _ = incidentHullVertex P (sourceIndex P W t.1 t.property)
                Bs.formula.side 0 := congrArg
            (fun z ↦ incidentHullVertex P z Bs.formula.side 0)
              hA₀A₁.1.symm
          _ = incidentHullVertex P (sourceIndex P W t.1 t.property)
                Bt.formula.side 0 := congrArg
            (fun side ↦ incidentHullVertex P
              (sourceIndex P W t.1 t.property) side 0) hside.symm
      have huAway : sourceIndex P W u.1 u.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W t.1 t.property) Bt.formula.side 0 := by
        calc
          sourceIndex P W u.1 u.property =
              Erdos957Case4NoThree.awayHullVertex P
                (sourceIndex P W s.1 s.property) Bs.formula.side 1 :=
            hA₀A₁.2
          _ = Erdos957Case4NoThree.awayHullVertex P
                (Erdos957Case4NoThree.awayHullVertex P
                  (sourceIndex P W s.1 s.property) Bs.formula.side 0)
                Bs.formula.side 0 :=
            away_second_eq_away_first_twice
              (sourceIndex P W s.1 s.property) Bs.formula.side
          _ = Erdos957Case4NoThree.awayHullVertex P
                (sourceIndex P W t.1 t.property) Bs.formula.side 0 :=
            congrArg
              (fun z ↦ Erdos957Case4NoThree.awayHullVertex P z
                Bs.formula.side 0) hA₀A₁.1.symm
          _ = Erdos957Case4NoThree.awayHullVertex P
                (sourceIndex P W t.1 t.property) Bt.formula.side 0 :=
            congrArg
              (fun side ↦ Erdos957Case4NoThree.awayHullVertex P
                (sourceIndex P W t.1 t.property) side 0) hside.symm
      have hw := target_eq_w_of_case2Secondary_at_incident_of_degree_five
        hA Bt.formula Bs.formula hdegree hsIncident
      exact no_case4SplitRight_at_outward_away_first_of_target_eq_w
        Q T U htRole huRole Bt hw huAway
    · have huIncident : sourceIndex P W u.1 u.property =
          incidentHullVertex P (sourceIndex P W t.1 t.property)
            Bt.formula.side 0 := by
        calc
          sourceIndex P W u.1 u.property =
              Erdos957Case4NoThree.awayHullVertex P
                (sourceIndex P W s.1 s.property) Bs.formula.side 1 :=
            hA₀A₁.2
          _ = incidentHullVertex P
                (Erdos957Case4NoThree.awayHullVertex P
                  (sourceIndex P W s.1 s.property) Bs.formula.side 0)
                Bt.formula.side 0 :=
            away_second_eq_incident_away_first_of_side_ne
              (sourceIndex P W s.1 s.property) hside
          _ = incidentHullVertex P (sourceIndex P W t.1 t.property)
                Bt.formula.side 0 := congrArg
            (fun z ↦ incidentHullVertex P z Bt.formula.side 0)
              hA₀A₁.1.symm
      exact no_case4SplitRight_at_incident_of_case2_degree_five
        hA Q T U htRole huRole hdegree huIncident
  · exact no_case4SplitRight_at_incident_of_case2_degree_five
      hA Q S U hsRole huRole hdegree hA₁I.2
  · exact no_case2_away_second_case4_away_first
      Q S T U Bs hsRole htRole huRole hA₁A₀.1 hA₁A₀.2

/-- The four outward-facing normal forms left by the exact three-slot
classification.  The last field is stated in one orientation because its two
split arrivals may be exchanged by the final dispatcher. -/
structure Case2SplitOutwardResiduals
    (Q : CommonCoherentRealizedSourceRows P W F.chart) where
  case2_incident_split_away_first :
    ∀ {s t u : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v)
      (U : RealizedArrivalAt (F := F) Q.rows u v)
      (B : Case2SecondaryArrivalFormula S.target S.descriptor),
      S.target.role = PairCases.TargetRoleName.case2Secondary →
      T.target.role = PairCases.TargetRoleName.case2Secondary →
      U.target.role = PairCases.TargetRoleName.case4SplitRight →
      (unitDistanceGraph A).degree v = 5 →
      sourceIndex P W t.1 t.property =
        incidentHullVertex P (sourceIndex P W s.1 s.property)
          B.formula.side 0 →
      sourceIndex P W u.1 u.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) B.formula.side 0 →
      s ≠ t → s ≠ u → t ≠ u → False
  case2_away_first_split_away_second :
    ∀ {s t u : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v)
      (U : RealizedArrivalAt (F := F) Q.rows u v)
      (B : Case2SecondaryArrivalFormula S.target S.descriptor),
      S.target.role = PairCases.TargetRoleName.case2Secondary →
      T.target.role = PairCases.TargetRoleName.case2Secondary →
      U.target.role = PairCases.TargetRoleName.case4SplitRight →
      (unitDistanceGraph A).degree v = 5 →
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) B.formula.side 0 →
      sourceIndex P W u.1 u.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) B.formula.side 1 →
      s ≠ t → s ≠ u → t ≠ u → False
  case2_away_second_split_away_first :
    ∀ {s t u : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v)
      (U : RealizedArrivalAt (F := F) Q.rows u v)
      (B : Case2SecondaryArrivalFormula S.target S.descriptor),
      S.target.role = PairCases.TargetRoleName.case2Secondary →
      T.target.role = PairCases.TargetRoleName.case2Secondary →
      U.target.role = PairCases.TargetRoleName.case4SplitRight →
      (unitDistanceGraph A).degree v = 5 →
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) B.formula.side 1 →
      sourceIndex P W u.1 u.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) B.formula.side 0 →
      s ≠ t → s ≠ u → t ≠ u → False
  two_split_away_first_second :
    ∀ {s t u : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v)
      (U : RealizedArrivalAt (F := F) Q.rows u v)
      (B : Case2SecondaryArrivalFormula S.target S.descriptor),
      S.target.role = PairCases.TargetRoleName.case2Secondary →
      T.target.role = PairCases.TargetRoleName.case4SplitRight →
      U.target.role = PairCases.TargetRoleName.case4SplitRight →
      (unitDistanceGraph A).degree v = 5 →
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) B.formula.side 0 →
      sourceIndex P W u.1 u.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) B.formula.side 1 →
      s ≠ t → s ≠ u → t ≠ u → False

/-- The outward record is exactly sufficient for the two remaining weighted
degree-five fields.  All other members of the two six-way finite dispatches
are eliminated by the incident Case-4 contradiction or, in the one mixed
branch, by forcing the Case-2 target to `w` and applying the second-away
distance bound. -/
theorem case2SecondarySplitDegreeFiveResiduals_of_outward
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (K : Case2SplitOutwardResiduals Q) :
    Case2SecondarySplitDegreeFiveResiduals (F := F) Q.rows where
  case2_split_right := by
    intro s t u v S T U hsRole htRole huRole hdegree
      htWindow huWindow hst hsu htu
    let B := Classical.choice
      (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
    obtain ⟨E⟩ := exists_case2SecondaryFormula T.target htRole
    obtain ⟨G⟩ := exists_case4SplitRightFormula U.target huRole
    rcases case2_split_near_pair_cases hA B.formula E G F hdegree
        htWindow huWindow hst hsu htu with
      hIA | hIA2 | hAI | hAA | hA2I | hA2A
    · exact K.case2_incident_split_away_first S T U B hsRole htRole
        huRole hdegree hIA.1 hIA.2 hst hsu htu
    · have hw := target_eq_w_of_case2Secondary_at_incident_of_degree_five
          hA B.formula E hdegree hIA2.1
      exact no_case4SplitRight_at_away_second_of_target_eq_w
        B.formula G F hw hIA2.2
    · exact no_case4SplitRight_at_incident_of_case2_degree_five
        hA Q S U hsRole huRole hdegree hAI.2
    · exact K.case2_away_first_split_away_second S T U B hsRole
        htRole huRole hdegree hAA.1 hAA.2 hst hsu htu
    · exact no_case4SplitRight_at_incident_of_case2_degree_five
        hA Q S U hsRole huRole hdegree hA2I.2
    · exact K.case2_away_second_split_away_first S T U B hsRole
        htRole huRole hdegree hA2A.1 hA2A.2 hst hsu htu
  two_split_right := by
    intro s t u v S T U hsRole htRole huRole hdegree
      htWindow huWindow hst hsu htu
    let B := Classical.choice
      (nonempty_case2SecondaryArrivalFormula S.target S.descriptor hsRole)
    obtain ⟨E⟩ := exists_case4SplitRightFormula T.target htRole
    obtain ⟨G⟩ := exists_case4SplitRightFormula U.target huRole
    rcases two_split_near_pair_cases hA B.formula E G F hdegree
        htWindow huWindow hst hsu htu with
      hIA | hIA2 | hAI | hAA | hA2I | hA2A
    · exact no_case4SplitRight_at_incident_of_case2_degree_five
        hA Q S T hsRole htRole hdegree hIA.1
    · exact no_case4SplitRight_at_incident_of_case2_degree_five
        hA Q S T hsRole htRole hdegree hIA2.1
    · exact no_case4SplitRight_at_incident_of_case2_degree_five
        hA Q S U hsRole huRole hdegree hAI.2
    · exact K.two_split_away_first_second S T U B hsRole htRole
        huRole hdegree hAA.1 hAA.2 hst hsu htu
    · exact no_case4SplitRight_at_incident_of_case2_degree_five
        hA Q S U hsRole huRole hdegree hA2I.2
    · exact K.two_split_away_first_second S U T B hsRole huRole
        htRole hdegree hA2A.2 hA2A.1 hsu hst htu.symm

end Erdos957Case2SplitFinalReduction

namespace Erdos957Case2SplitFinalReduction

#print axioms case2SecondarySplitDegreeFiveResiduals_of_outward

end Erdos957Case2SplitFinalReduction
