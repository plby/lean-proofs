import ErdosProblems.Erdos957.Case4DirectDisplacement

/-!
# Outer direct arrivals near a selected Case-4 recipient

The outer direct role retains a non-hull equilateral proxy.  In either of
the two cyclic slots left by the metric reduction, the wrong orientation
would place that proxy at distance strictly less than one from an endpoint
of the supporting hull edge.  One-separation therefore fixes its arrival
association, oppositely to the selected Case-4 secondary.
-/

noncomputable section

namespace Erdos957Case4OuterDirect

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CollisionInstantiation
open Erdos957CoherentRealizedRows
open Erdos957RoleCollisions
open Erdos957DirectSameSide
open Erdos957Case4CollisionLeaves

abbrev Point := Erdos957GeometryCore.Point

/-- On the negative side of a shallow unit-edge frame, the wrong
equilateral completion is strictly within one unit of the left endpoint. -/
lemma left_wrong_proxy_close
    {tx ty qx qy rx ry s : ℝ}
    (hspos : 0 < s) (hssq : s ^ 2 = 3)
    (htx : tx < -(399 / 200))
    (hty : ty < 0) (htcone : -ty ≤ (-tx) / 10)
    (hqxl : -(3 / 2) ≤ qx)
    (hqy : qy ≤ -(s / 2))
    (htq : (tx - qx) ^ 2 + (ty - qy) ^ 2 = 1)
    (htr : (tx - rx) ^ 2 + (ty - ry) ^ 2 = 1)
    (hqr : (qx - rx) ^ 2 + (qy - ry) ^ 2 = 1)
    (hcross : (rx - tx) * (qy - ty) -
      (ry - ty) * (qx - tx) ≤ 0) :
    (rx + 1) ^ 2 + ry ^ 2 < 1 := by
  let ax := qx - tx
  let ay := qy - ty
  let bx := rx - tx
  let byv := ry - ty
  let c := bx * ay - byv * ax
  have haz : ax ^ 2 + ay ^ 2 = 1 := by
    dsimp [ax, ay]
    nlinarith only [htq]
  have hbz : bx ^ 2 + byv ^ 2 = 1 := by
    dsimp [bx, byv]
    nlinarith only [htr]
  have hdiff : (ax - bx) ^ 2 + (ay - byv) ^ 2 = 1 := by
    dsimp [ax, ay, bx, byv]
    nlinarith only [hqr]
  have hdot : ax * bx + ay * byv = 1 / 2 := by
    nlinarith only [haz, hbz, hdiff]
  have hcrossSq : c ^ 2 = 3 / 4 := by
    dsimp [c]
    have hid : (bx * ay - byv * ax) ^ 2 +
        (ax * bx + ay * byv) ^ 2 =
        (ax ^ 2 + ay ^ 2) * (bx ^ 2 + byv ^ 2) := by ring
    nlinarith only [hid, haz, hbz, hdot]
  have hcNonpos : c ≤ 0 := by
    simpa [c, ax, ay, bx, byv] using hcross
  have hc : c = -(s / 2) := by
    nlinarith only [hcrossSq, hssq, hspos, hcNonpos]
  have hc' : bx * ay - byv * ax = -(s / 2) := by
    simpa only [c] using hc
  have hbx : bx = (1 / 2) * ax - (s / 2) * ay := by
    have hid : bx * (ax ^ 2 + ay ^ 2) =
        (ax * bx + ay * byv) * ax +
          (bx * ay - byv * ax) * ay := by ring
    rw [haz, hdot, hc'] at hid
    nlinarith only [hid]
  have hby : byv = (1 / 2) * ay + (s / 2) * ax := by
    have hid : byv * (ax ^ 2 + ay ^ 2) =
        (ax * bx + ay * byv) * ay -
          (bx * ay - byv * ax) * ax := by ring
    rw [haz, hdot, hc'] at hid
    nlinarith only [hid]
  have hsLower : 17 / 10 < s := by
    nlinarith only [hssq, hspos, sq_nonneg (s - 17 / 10)]
  have hsUpper : s < 7 / 4 := by
    nlinarith only [hssq, hspos, sq_nonneg (s - 7 / 4)]
  have haxLower : 99 / 200 < ax := by
    dsimp [ax]
    nlinarith only [hqxl, htx]
  have haxUpper : ax ≤ 1 := by
    nlinarith only [haz, haxLower, sq_nonneg ay, sq_nonneg (ax - 1)]
  have hayLower : -1 ≤ ay := by
    nlinarith only [haz, sq_nonneg ax, sq_nonneg (ay + 1)]
  have htxLower : -(5 / 2) ≤ tx := by
    dsimp [ax] at haxUpper
    nlinarith only [hqxl, haxUpper]
  have htyLower : -(1 / 4) ≤ ty := by
    nlinarith only [htcone, htxLower]
  have hayUpper : ay < -(3 / 5) := by
    dsimp [ay]
    nlinarith only [hqy, htyLower, hsLower]
  dsimp [ax, ay, bx, byv] at hbx hby haxLower haxUpper hayLower hayUpper
  have hrxLower : -(1 / 2) < rx + 1 := by
    nlinarith only [hbx, haxUpper, hayUpper, hqxl, hsLower]
  have hsNegAyUpper : s * (-(qy - ty)) ≤ s := by
    calc
      s * (-(qy - ty)) ≤ s * 1 :=
        mul_le_mul_of_nonneg_left (by linarith only [hayLower]) hspos.le
      _ = s := by ring
  have hrxUpper : rx + 1 < 1 / 2 := by
    nlinarith only [hbx, haxUpper, htx, hsUpper, hsNegAyUpper]
  have hryLower : -(1 / 2) < ry := by
    nlinarith only [hby, haxLower, hayLower, htyLower, hsLower]
  have hsAxUpper : s * (qx - tx) ≤ s := by
    calc
      s * (qx - tx) ≤ s * 1 :=
        mul_le_mul_of_nonneg_left haxUpper hspos.le
      _ = s := by ring
  have hryUpper : ry < 1 / 2 := by
    nlinarith only [hby, hqy, hty, hsUpper, hsAxUpper]
  have hxProd : 0 < ((rx + 1) + 1 / 2) * (1 / 2 - (rx + 1)) :=
    mul_pos (by linarith) (by linarith)
  have hyProd : 0 < (ry + 1 / 2) * (1 / 2 - ry) :=
    mul_pos (by linarith) (by linarith)
  nlinarith only [hxProd, hyProd]

/-- Reflected positive-side version of `left_wrong_proxy_close`. -/
lemma right_wrong_proxy_close
    {tx ty qx qy rx ry s : ℝ}
    (hspos : 0 < s) (hssq : s ^ 2 = 3)
    (htx : 399 / 400 < tx)
    (hty : ty < 0) (htcone : -ty ≤ tx / 10)
    (hqxl : -(3 / 2) ≤ qx) (hqxupper : qx ≤ 1 / 2)
    (hqy : qy ≤ -(s / 2))
    (htq : (tx - qx) ^ 2 + (ty - qy) ^ 2 = 1)
    (htr : (tx - rx) ^ 2 + (ty - ry) ^ 2 = 1)
    (hqr : (qx - rx) ^ 2 + (qy - ry) ^ 2 = 1)
    (hcross : 0 ≤
      (rx - tx) * (qy - ty) - (ry - ty) * (qx - tx)) :
    rx ^ 2 + ry ^ 2 < 1 := by
  have h := left_wrong_proxy_close
    (tx := -tx - 1) (ty := ty)
    (qx := -qx - 1) (qy := qy)
    (rx := -rx - 1) (ry := ry) (s := s)
    hspos hssq
    (by linarith only [htx]) hty
    (by linarith only [htcone])
    (by linarith only [hqxupper]) hqy
    (by nlinarith only [htq])
    (by nlinarith only [htr])
    (by nlinarith only [hqr])
    (by linarith only [hcross])
  nlinarith only [h]

/-- The normalized Case-4 frame and an arbitrary aligned source chart
have the same signed area on the predecessor branch and opposite signed
area on the reflected successor branch. -/
lemma normalizedCross_relation
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {middle : Vertex A}
    (C : P.AlignedChartData)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (i : {p // p ∈ P.H}) (a b c : Vertex A) :
    let Dn := Erdos957Case3General.crossFrom
      ((N.frame.toCanonical a) 0, (N.frame.toCanonical a) 1)
      ((N.frame.toCanonical b) 0, (N.frame.toCanonical b) 1)
      ((N.frame.toCanonical c) 0, (N.frame.toCanonical c) 1)
    let Dc := Erdos957Case3General.crossFrom
      (C.coord i a) (C.coord i b) (C.coord i c)
    (T.side = .previous ∧ Dn = Dc) ∨
      (T.side = .next ∧ Dn = -Dc) := by
  let Dn := Erdos957Case3General.crossFrom
    ((N.frame.toCanonical a) 0, (N.frame.toCanonical a) 1)
    ((N.frame.toCanonical b) 0, (N.frame.toCanonical b) 1)
    ((N.frame.toCanonical c) 0, (N.frame.toCanonical c) 1)
  let Dc := Erdos957Case3General.crossFrom
    (C.coord i a) (C.coord i b) (C.coord i c)
  have haligned := Erdos957Case3SameSide.crossFrom_coord_eq_neg_cross
    C i a b c
  cases N.frame_spec with
  | previous hside hunit hframe =>
      left
      refine ⟨hside, ?_⟩
      have hrigid := Erdos957DirectSameSide.crossFrom_terminalUnitEdgeRigidChart
        (P.next⁻¹ source).1.1 source.1.1 a b c hunit
      rw [← hframe] at hrigid
      change Dn = _ at hrigid
      change Dc = _ at haligned
      linarith
  | next hside hunit hframe =>
      right
      refine ⟨hside, ?_⟩
      have hrigid :=
        Erdos957DirectSameSide.crossFrom_reflectedSuccessorUnitEdgeRigidChart
          P source hunit a b c
      rw [← hframe] at hrigid
      change Dn = _ at hrigid
      change Dc = _ at haligned
      linarith

/-- The outer equilateral-proxy direct form has the opposite association
from a selected Case-4 secondary in either remaining near source slot. -/
lemma outer_direct_near_two_associations_ne
    {A : Finset Point} {P : CyclicHullData A}
    {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htDirect : IsDirectTargetRole T.target.role)
    (O : OuterDirectFormula F.chart
      (sourceIndex P W t.1 t.property) v T.descriptor.association)
    (hnear :
      let Qs := Q.case4_pair s.1 s.property
        ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
      sourceIndex P W t.1 t.property =
          incidentContinuationHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
        sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0) :
    S.descriptor.association ≠ T.descriptor.association := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at hnear
  have hslot : S.target.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← S.target.target_at_role, hsRole, Qs.current_secondary_role]
  have hv : v = Qs.currentSecondaryTarget.vertex := by
    calc
      v = S.target.target.vertex := S.target.vertex_eq
      _ = Qs.currentSecondaryTarget.vertex := congrArg LocalTarget.vertex hslot
  have hadj : (unitDistanceGraph A).Adj
      (sourceIndex P W t.1 t.property).1
      Qs.currentSecondaryTarget.vertex := by
    rw [← hv]
    exact T.target.adj_source_of_directRole htDirect
  have hiS := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s
  have hanchor :=
    Erdos957Case4DirectSameSide.current_secondary_association_of_adj_near_source
      hA F Qs hiS hadj hnear
  have hslotsNe :
      incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ≠
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 := by
    intro heq
    have hiBound := Erdos957Case4NoThree.normalizedFrame_incident_prefix_metric_bounds
      F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
        Qs.normalized hiS 1
    have haBound := Erdos957Case4NoThree.normalizedFrame_away_prefix_bounds
      F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
        Qs.normalized hiS 0
    change Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at heq
    rw [heq] at hiBound
    norm_num at hiBound haBound
    linarith [hiBound.1, haBound.2.1]
  have hsDescriptor : S.descriptor.association =
      (Q.rows s.1 s.property).roleAssociation .case4SplitRight := by
    calc
      S.descriptor.association =
          (Q.rows s.1 s.property).roleAssociation S.target.role :=
        S.descriptor.association_eq
      _ = _ := by rw [hsRole]
  let tc := Qs.normalized.frame.toCanonical
    (sourceIndex P W t.1 t.property).1
  let qc := Qs.normalized.frame.toCanonical v
  let rc := Qs.normalized.frame.toCanonical O.proxy
  let Dn := Erdos957Case3General.crossFrom
    (tc 0, tc 1) (rc 0, rc 1) (qc 0, qc 1)
  let Da := Erdos957Case3General.crossFrom
    (F.chart.coord (sourceIndex P W t.1 t.property)
      (sourceIndex P W t.1 t.property).1)
    (F.chart.coord (sourceIndex P W t.1 t.property) O.proxy)
    (F.chart.coord (sourceIndex P W t.1 t.property) v)
  have hcrossRelation := normalizedCross_relation F.chart Qs.twoExtreme
    Qs.normalized (sourceIndex P W t.1 t.property)
      (sourceIndex P W t.1 t.property).1 O.proxy v
  change (Qs.twoExtreme.side = .previous ∧ Dn = Da) ∨
    (Qs.twoExtreme.side = .next ∧ Dn = -Da) at hcrossRelation
  have hqMem : qc ∈ Erdos957Case24Bridge.Case4.residualNeighbors
      (Qs.normalized.frame.image A) := by
    dsimp [qc]
    rw [hv]
    exact Erdos957Case4SplitClassification.CommonPairedCase4Rows.normalized_currentSecondary_mem_residual Qs
  have hqBounds :=
    Erdos957Case4SplitClassification.residual_fst_mem_sharp_interval hqMem
  have huPrev : Erdos957Cases24.Case2.uPrev ∈
      Qs.normalized.frame.image A := by
    apply Qs.normalized.frame.mem_image_iff.mpr
    rw [Qs.normalized.side_actual]
    exact (cyclicSideVertex P (sourceIndex P W s.1 s.property)
      Qs.twoExtreme.side).property
  have huCanon : Erdos957Cases24.Case2.u ∈
      Qs.normalized.frame.image A := by
    apply Qs.normalized.frame.mem_image_iff.mpr
    rw [Qs.normalized.source_actual]
    exact (sourceIndex P W s.1 s.property).1.property
  have hqy : qc 1 ≤ -(Erdos957Cases24.sqrtThree / 2) := by
    have h := Erdos957Case4SplitClassification.residual_centered_snd_nonpos
      (Qs.normalized.frame.image_oneSeparated hA) huPrev huCanon hqMem
    change qc 1 - Erdos957Cases24.Case4.v 1 ≤ 0 at h
    simpa [Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v] using
      (sub_nonpos.mp h)
  have htqDist : dist tc qc = 1 := by
    dsimp [tc, qc]
    rw [Qs.normalized.frame.dist_eq]
    simpa [unitDistanceGraph, hv] using hadj
  have htrDist : dist tc rc = 1 := by
    dsimp [tc, rc]
    rw [Qs.normalized.frame.dist_eq]
    simpa [unitDistanceGraph] using O.source_proxy
  have hqrDist : dist qc rc = 1 := by
    dsimp [qc, rc]
    rw [Qs.normalized.frame.dist_eq]
    simpa [unitDistanceGraph] using O.target_proxy
  have htqSq : (tc 0 - qc 0) ^ 2 + (tc 1 - qc 1) ^ 2 = 1 := by
    have h := Erdos957Cases24.dist_sq_eq_coordinates tc qc
    rw [htqDist] at h
    norm_num at h
    exact h.symm
  have htrSq : (tc 0 - rc 0) ^ 2 + (tc 1 - rc 1) ^ 2 = 1 := by
    have h := Erdos957Cases24.dist_sq_eq_coordinates tc rc
    rw [htrDist] at h
    norm_num at h
    exact h.symm
  have hqrSq : (qc 0 - rc 0) ^ 2 + (qc 1 - rc 1) ^ 2 = 1 := by
    have h := Erdos957Cases24.dist_sq_eq_coordinates qc rc
    rw [hqrDist] at h
    norm_num at h
    exact h.symm
  have hrcMem : rc ∈ Qs.normalized.frame.image A :=
    Finset.mem_image.mpr ⟨O.proxy, O.proxy.property, rfl⟩
  have hSideHull :
      cyclicSideVertex P (sourceIndex P W s.1 s.property)
        Qs.twoExtreme.side ∈ P.H := by
    cases Qs.twoExtreme.side <;> simp [cyclicSideVertex]
  have hrcNotEndpoints : rc ∉
      ({Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.u} : Finset Point) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hr
      apply O.proxy_not_hull
      have hp : O.proxy = cyclicSideVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side := by
        apply Subtype.ext
        apply Qs.normalized.frame.toCanonical.injective
        rw [← Qs.normalized.side_actual,
          Qs.normalized.frame.toCanonical_actual]
        exact hr
      exact hp ▸ hSideHull
    · intro hr
      apply O.proxy_not_hull
      have hp : O.proxy = (sourceIndex P W s.1 s.property).1 := by
        apply Subtype.ext
        apply Qs.normalized.frame.toCanonical.injective
        rw [← Qs.normalized.source_actual,
          Qs.normalized.frame.toCanonical_actual]
        exact hr
      exact hp ▸ (sourceIndex P W s.1 s.property).property
  have hry : rc 1 < 0 :=
    Qs.normalized.strict_support rc hrcMem hrcNotEndpoints
  have hsepLeft : 1 ≤ dist (O.proxy : Point)
      (cyclicSideVertex P (sourceIndex P W s.1 s.property)
        Qs.twoExtreme.side : Point) := by
    apply hA O.proxy O.proxy.property
      (cyclicSideVertex P (sourceIndex P W s.1 s.property)
        Qs.twoExtreme.side)
      (cyclicSideVertex P (sourceIndex P W s.1 s.property)
        Qs.twoExtreme.side).property
    intro heq
    apply O.proxy_not_hull
    have hvEq : O.proxy = cyclicSideVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side :=
      Subtype.ext heq
    exact hvEq ▸ hSideHull
  have hsepRight : 1 ≤ dist (O.proxy : Point)
      ((sourceIndex P W s.1 s.property).1 : Point) := by
    apply hA O.proxy O.proxy.property
      (sourceIndex P W s.1 s.property).1
      (sourceIndex P W s.1 s.property).1.property
    intro heq
    apply O.proxy_not_hull
    have hvEq : O.proxy = (sourceIndex P W s.1 s.property).1 :=
      Subtype.ext heq
    exact hvEq ▸ (sourceIndex P W s.1 s.property).property
  have hincidentCross :
      sourceIndex P W t.1 t.property =
          incidentContinuationHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 →
        0 < Dn := by
    intro hincident
    have hp := Erdos957Case4NoThree.normalizedFrame_incident_prefix_metric_bounds
      F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
        Qs.normalized hiS 1
    change (2 : ℝ) * (399 / 400) <
        -(Qs.normalized.frame.toCanonical
          (incidentContinuationHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1) 0 ∧
      -(Qs.normalized.frame.toCanonical
          (incidentContinuationHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1) 1 ≤
        -(Qs.normalized.frame.toCanonical
          (incidentContinuationHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1) 0 / 10 at hp
    rw [← hincident] at hp
    norm_num at hp
    have htcMem : tc ∈ Qs.normalized.frame.image A :=
      Finset.mem_image.mpr
        ⟨(sourceIndex P W t.1 t.property).1,
          (sourceIndex P W t.1 t.property).1.property, rfl⟩
    have htcNotEndpoints : tc ∉
        ({Erdos957Cases24.Case2.uPrev,
          Erdos957Cases24.Case2.u} : Finset Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor <;> intro hz
      all_goals
        rw [show Qs.normalized.frame.toCanonical
          (sourceIndex P W t.1 t.property).1 = _ by exact hz] at hp
        norm_num [Erdos957Cases24.Case2.uPrev,
          Erdos957Cases24.Case2.u] at hp
    have hty : tc 1 < 0 :=
      Qs.normalized.strict_support tc htcMem htcNotEndpoints
    by_contra hn
    have hclose := left_wrong_proxy_close
      Erdos957Cases24.sqrtThree_pos Erdos957Cases24.sqrtThree_sq
      (by linarith only [hp.1]) hty hp.2 hqBounds.1 hqy
      htqSq htrSq hqrSq
      (by
        change Dn ≤ 0
        exact le_of_not_gt hn)
    have hdistSq := Erdos957Cases24.dist_sq_eq_coordinates rc
      (Qs.normalized.frame.toCanonical
        (cyclicSideVertex P (sourceIndex P W s.1 s.property)
          Qs.twoExtreme.side))
    rw [Qs.normalized.frame.dist_eq] at hdistSq
    have hsideCoord : Qs.normalized.frame.toCanonical
        (cyclicSideVertex P (sourceIndex P W s.1 s.property)
          Qs.twoExtreme.side) = Erdos957Cases24.Case2.uPrev := by
      rw [← Qs.normalized.side_actual,
        Qs.normalized.frame.toCanonical_actual]
    rw [hsideCoord] at hdistSq
    simp only [Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at hdistSq
    nlinarith [dist_nonneg (x := (O.proxy : Point))
      (y := (cyclicSideVertex P (sourceIndex P W s.1 s.property)
        Qs.twoExtreme.side : Point))]
  have hawayCross :
      sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 →
        Dn < 0 := by
    intro haway
    have hp := Erdos957Case4NoThree.normalizedFrame_away_prefix_bounds
      F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
        Qs.normalized hiS 0
    rw [← haway] at hp
    norm_num at hp
    by_contra hn
    have hclose := right_wrong_proxy_close
      Erdos957Cases24.sqrtThree_pos Erdos957Cases24.sqrtThree_sq
      hp.2.1 hp.1 hp.2.2 hqBounds.1 hqBounds.2 hqy
      htqSq htrSq hqrSq
      (by
        change 0 ≤ Dn
        exact le_of_not_gt hn)
    have hdistSq := Erdos957Cases24.dist_sq_eq_coordinates rc
      (Qs.normalized.frame.toCanonical
        (sourceIndex P W s.1 s.property).1)
    rw [Qs.normalized.frame.dist_eq] at hdistSq
    have hsourceCoord : Qs.normalized.frame.toCanonical
        (sourceIndex P W s.1 s.property).1 =
          Erdos957Cases24.Case2.u := by
      rw [← Qs.normalized.source_actual,
        Qs.normalized.frame.toCanonical_actual]
    rw [hsourceCoord] at hdistSq
    simp only [Erdos957Cases24.Case2.u,
      Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at hdistSq
    nlinarith [dist_nonneg (x := (O.proxy : Point))
      (y := ((sourceIndex P W s.1 s.property).1 : Point))]
  intro hassoc
  rcases hnear with hincident | haway
  · have hDn := hincidentCross hincident
    rcases hcrossRelation with hprev | hnext
    · have hDa : 0 < Da := by linarith [hprev.2]
      have htAssoc : T.descriptor.association = .fromNext := by
        rcases O.association_side with h | h
        · have hh : Da ≤ 0 := by exact h.1
          linarith
        · exact h.2
      have hsAssoc : S.descriptor.association = .fromPrevious := by
        rw [hsDescriptor]
        rcases hanchor with ha | ha
        · rw [ha.2, hprev.1]
          rfl
        · exact (hslotsNe (hincident.symm.trans ha.1)).elim
      rw [hsAssoc, htAssoc] at hassoc
      contradiction
    · have hDa : Da < 0 := by linarith [hnext.2]
      have htAssoc : T.descriptor.association = .fromPrevious := by
        rcases O.association_side with h | h
        · exact h.2
        · have hh : 0 < Da := by exact h.1
          linarith
      have hsAssoc : S.descriptor.association = .fromNext := by
        rw [hsDescriptor]
        rcases hanchor with ha | ha
        · rw [ha.2, hnext.1]
          rfl
        · exact (hslotsNe (hincident.symm.trans ha.1)).elim
      rw [hsAssoc, htAssoc] at hassoc
      contradiction
  · have hDn := hawayCross haway
    rcases hcrossRelation with hprev | hnext
    · have hDa : Da < 0 := by linarith [hprev.2]
      have htAssoc : T.descriptor.association = .fromPrevious := by
        rcases O.association_side with h | h
        · exact h.2
        · have hh : 0 < Da := by exact h.1
          linarith
      have hsAssoc : S.descriptor.association = .fromNext := by
        rw [hsDescriptor]
        rcases hanchor with ha | ha
        · exact (hslotsNe (ha.1.symm.trans haway)).elim
        · rw [ha.2, hprev.1]
          rfl
      rw [hsAssoc, htAssoc] at hassoc
      contradiction
    · have hDa : 0 < Da := by linarith [hnext.2]
      have htAssoc : T.descriptor.association = .fromNext := by
        rcases O.association_side with h | h
        · have hh : Da ≤ 0 := by exact h.1
          linarith
        · exact h.2
      have hsAssoc : S.descriptor.association = .fromPrevious := by
        rw [hsDescriptor]
        rcases hanchor with ha | ha
        · exact (hslotsNe (ha.1.symm.trans haway)).elim
        · rw [ha.2, hnext.1]
          rfl
      rw [hsAssoc, htAssoc] at hassoc
      contradiction

end Erdos957Case4OuterDirect

#print axioms Erdos957Case4OuterDirect.left_wrong_proxy_close
#print axioms Erdos957Case4OuterDirect.outer_direct_near_two_associations_ne
