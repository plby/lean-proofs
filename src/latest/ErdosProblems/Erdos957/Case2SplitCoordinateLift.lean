import ErdosProblems.Erdos957.Case2SplitDegreeFive

/-!
# Coordinate transport for the final Case-2 / split Case-4 boundary

This leaf contains only two geometry-neutral coordinate adapters.  It sits
below `Case2SplitStrict` and the final residual assembly so those modules can
consume it without an import cycle.
-/

noncomputable section

namespace Erdos957Case2SplitCoordinateLift

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CoherentRealizedRows

abbrev Point := Erdos957GeometryCore.Point

open Erdos957Cases24

/-- Pure coordinate core for the final split/split exclusion.  `S` is the
anchor source, `Q` is canonical `wNext`, and `B=(S+Q)/2` is the retained
Case-2 outer point, all expressed in the reflected frame of the first
Case-4 source. -/
lemma third_arc_close_to_source_or_outer
    {sx sy qx qy nx ny : ℝ}
    (hsx : (399 / 400 : ℝ) < sx)
    (hsy : sy < 0) (hshallow : -sy ≤ sx / 10)
    (hqxLower : -1 ≤ qx) (hqxUpper : qx ≤ 0)
    (hqy : qy ≤ -sqrtThree)
    (hsq : (sx - qx) ^ 2 + (sy - qy) ^ 2 = 4)
    (hnorm : nx ^ 2 + ny ^ 2 = 1)
    (hnx : (1 / 2 : ℝ) ≤ nx) (hny : ny < 0) :
    (nx - sx) ^ 2 + (ny - sy) ^ 2 < 1 ∨
      (nx - (sx + qx) / 2) ^ 2 +
          (ny - (sy + qy) / 2) ^ 2 < 1 := by
  have hsqrtLower : (17 / 10 : ℝ) < sqrtThree := by
    nlinarith only [sqrtThree_sq, sqrtThree_pos,
      sq_nonneg (sqrtThree - 17 / 10)]
  have hsqrtUpper : sqrtThree < (7 / 4 : ℝ) := by
    nlinarith only [sqrtThree_sq, sqrtThree_pos,
      sq_nonneg (sqrtThree + 7 / 4)]
  have hsxPos : 0 < sx := by
    norm_num at hsx ⊢
    linarith only [hsx]
  have hdxPos : 0 < sx - qx := by linarith only [hsxPos, hqxUpper]
  have hdxSqLe : (sx - qx) ^ 2 ≤ 4 := by
    nlinarith only [hsq, sq_nonneg (sy - qy)]
  have hdxLe : sx - qx ≤ 2 := by
    nlinarith only [hdxSqLe, hdxPos, sq_nonneg (sx - qx + 2)]
  have hsxLeTwo : sx ≤ 2 := by linarith only [hqxUpper, hdxLe]
  have hdyLower : sqrtThree - sx / 10 ≤ sy - qy := by
    linarith only [hshallow, hqy]
  have hdyPos : 0 < sy - qy := by
    nlinarith only [hdyLower, hsxLeTwo, hsqrtLower]
  have hsxUpper : sx < (6 / 5 : ℝ) := by
    by_contra h
    have hsxGe : (6 / 5 : ℝ) ≤ sx := le_of_not_gt h
    have hsxSqLe : sx ^ 2 ≤ (sx - qx) ^ 2 :=
      (sq_le_sq₀ hsxPos.le hdxPos.le).2 (by linarith only [hqxUpper])
    have hlowPos : 0 < sqrtThree - sx / 10 := by
      nlinarith only [hsxLeTwo, hsqrtLower]
    have hlowSqLe : (sqrtThree - sx / 10) ^ 2 ≤ (sy - qy) ^ 2 :=
      (sq_le_sq₀ hlowPos.le hdyPos.le).2 hdyLower
    have hbase : 4 <
        (6 / 5 : ℝ) ^ 2 + (sqrtThree - (6 / 5 : ℝ) / 10) ^ 2 := by
      nlinarith only [sqrtThree_sq, hsqrtUpper]
    have hfactor : 0 ≤
        (sx - 6 / 5) *
          ((101 / 100) * (sx + 6 / 5) - sqrtThree / 5) := by
      apply mul_nonneg
      · linarith only [hsxGe]
      · nlinarith only [hsxGe, hsqrtUpper]
    have hmono :
        (6 / 5 : ℝ) ^ 2 + (sqrtThree - (6 / 5 : ℝ) / 10) ^ 2 ≤
          sx ^ 2 + (sqrtThree - sx / 10) ^ 2 := by
      nlinarith only [hfactor]
    nlinarith only [hsq, hsxSqLe, hlowSqLe, hbase, hmono]
  have hsyLower : -(3 / 25 : ℝ) < sy := by
    nlinarith only [hshallow, hsxUpper]
  have hdyThreeHalves : (3 / 2 : ℝ) < sy - qy := by
    nlinarith only [hdyLower, hsxUpper, hsqrtLower]
  have hqxStrict : -(1 / 3 : ℝ) < qx := by
    by_contra h
    have hqxLe : qx ≤ -(1 / 3 : ℝ) := le_of_not_gt h
    have hdxLower : (53 / 40 : ℝ) < sx - qx := by
      nlinarith only [hsx, hqxLe]
    have hdxSq : (53 / 40 : ℝ) ^ 2 < (sx - qx) ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hdxPos.le).2 hdxLower
    have hdySq : (3 / 2 : ℝ) ^ 2 < (sy - qy) ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hdyPos.le).2 hdyThreeHalves
    nlinarith only [hsq, hdxSq, hdySq]
  have hdyUpper : sy - qy < (7 / 4 : ℝ) := by
    have hdxSq : (399 / 400 : ℝ) ^ 2 < (sx - qx) ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hdxPos.le).2
        (by linarith only [hsx, hqxUpper])
    have hdySq : (sy - qy) ^ 2 < (7 / 4 : ℝ) ^ 2 := by
      nlinarith only [hsq, hdxSq]
    exact (sq_lt_sq₀ hdyPos.le (by norm_num)).1 hdySq
  have hbxLower : (33 / 100 : ℝ) < (sx + qx) / 2 := by
    nlinarith only [hsx, hqxStrict]
  have hbxUpper : (sx + qx) / 2 < (3 / 5 : ℝ) := by
    nlinarith only [hsxUpper, hqxUpper]
  have hbyLower : -(1 : ℝ) < (sy + qy) / 2 := by
    have hqyEq : qy = sy - (sy - qy) := by ring
    rw [hqyEq]
    nlinarith only [hsyLower, hdyUpper]
  have hsqrtEightFifths : (8 / 5 : ℝ) < sqrtThree := by
    nlinarith only [sqrtThree_sq, sqrtThree_pos,
      sq_nonneg (sqrtThree - 8 / 5)]
  have hbyUpper : (sy + qy) / 2 < -(4 / 5 : ℝ) := by
    nlinarith only [hsy, hqy, hsqrtEightFifths]
  have hnxPos : 0 < nx := by nlinarith only [hnx]
  have hnxUpper : nx ≤ 1 := by
    have : nx ^ 2 ≤ 1 := by nlinarith only [hnorm, sq_nonneg ny]
    nlinarith only [this, hnxPos, sq_nonneg (nx + 1)]
  have hnyLower : -(9 / 10 : ℝ) < ny := by
    by_contra h
    have hnyLe : ny ≤ -(9 / 10 : ℝ) := le_of_not_gt h
    nlinarith only [hnorm, hnx, hnyLe,
      mul_nonneg (sub_nonneg.mpr hnx) (by linarith only [hnx] : 0 ≤ nx + 1 / 2),
      mul_nonneg (by linarith only [hnyLe] : 0 ≤ -ny - 9 / 10)
        (by linarith only [hnyLe] : 0 ≤ -ny + 9 / 10)]
  by_cases hnyHalf : -(1 / 2 : ℝ) ≤ ny
  · left
    have hxLo : -(7 / 10 : ℝ) < nx - sx := by
      nlinarith only [hnx, hsxUpper]
    have hxHi : nx - sx < (7 / 10 : ℝ) := by
      nlinarith only [hnxUpper, hsx]
    have hyLo : -(1 / 2 : ℝ) < ny - sy := by
      nlinarith only [hnyHalf, hsy]
    have hyHi : ny - sy < (1 / 2 : ℝ) := by
      nlinarith only [hny, hsyLower]
    have hxProd : 0 <
        ((7 / 10 : ℝ) - (nx - sx)) * ((7 / 10 : ℝ) + (nx - sx)) :=
      mul_pos (by linarith only [hxHi]) (by linarith only [hxLo])
    have hyProd : 0 <
        ((1 / 2 : ℝ) - (ny - sy)) * ((1 / 2 : ℝ) + (ny - sy)) :=
      mul_pos (by linarith only [hyHi]) (by linarith only [hyLo])
    nlinarith only [hxProd, hyProd]

  · right
    have hnyUpper : ny < -(1 / 2 : ℝ) := lt_of_not_ge hnyHalf
    have hxLo : -(67 / 100 : ℝ) < nx - (sx + qx) / 2 := by
      nlinarith only [hnx, hbxUpper]
    have hxHi : nx - (sx + qx) / 2 < (67 / 100 : ℝ) := by
      nlinarith only [hnxUpper, hbxLower]
    have hyLo : -(1 / 2 : ℝ) < ny - (sy + qy) / 2 := by
      nlinarith only [hnyLower, hbyUpper]
    have hyHi : ny - (sy + qy) / 2 < (1 / 2 : ℝ) := by
      nlinarith only [hnyUpper, hbyLower]
    have hxProd : 0 <
        ((67 / 100 : ℝ) - (nx - (sx + qx) / 2)) *
          ((67 / 100 : ℝ) + (nx - (sx + qx) / 2)) :=
      mul_pos (by linarith only [hxHi]) (by linarith only [hxLo])
    have hyProd : 0 <
        ((1 / 2 : ℝ) - (ny - (sy + qy) / 2)) *
          ((1 / 2 : ℝ) + (ny - (sy + qy) / 2)) :=
      mul_pos (by linarith only [hyHi]) (by linarith only [hyLo])
    nlinarith only [hxProd, hyProd]

/-- The lower unit-circle arc beginning at horizontal coordinate `1/2`
lies above the canonical `-sqrtThree/2` latitude. -/
lemma lower_unit_arc_snd_ge_neg_sqrtThree_half
    {nx ny : ℝ} (hnorm : nx ^ 2 + ny ^ 2 = 1)
    (hnx : (1 / 2 : ℝ) ≤ nx) (hny : ny < 0) :
    -(sqrtThree / 2) ≤ ny := by
  have hnxSq : (1 / 2 : ℝ) ^ 2 ≤ nx ^ 2 := by
    nlinarith only [hnx,
      mul_nonneg (sub_nonneg.mpr hnx)
        (by linarith only [hnx] : 0 ≤ nx + 1 / 2)]
  have hnySq : ny ^ 2 ≤ (sqrtThree / 2) ^ 2 := by
    nlinarith only [hnorm, hnxSq, sqrtThree_sq]
  have hsPos : 0 < sqrtThree / 2 := by
    nlinarith only [sqrtThree_pos]
  have hnegSq : (-ny) ^ 2 ≤ (sqrtThree / 2) ^ 2 := by
    simpa only [neg_sq] using hnySq
  have hneg : -ny ≤ sqrtThree / 2 :=
    (sq_le_sq₀ (by linarith only [hny]) hsPos.le).1 hnegSq
  linarith only [hneg]

/-- A rigid chart carries the metric midpoint of a length-two segment to
the coordinate midpoint.  This uses only the retained metric API of
`RigidChart`, rather than assuming an affine-map field. -/
lemma toCanonical_midpoint_of_dist_two_unit_unit
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    (s q b : Point)
    (hsq : dist s q = 2) (hsb : dist s b = 1) (hbq : dist b q = 1) :
    E.toCanonical b = (1 / 2 : ℝ) • (E.toCanonical s + E.toCanonical q) := by
  have hsq' : dist (E.toCanonical s) (E.toCanonical q) = 2 := by
    rw [E.dist_eq, hsq]
  have hsb' : dist (E.toCanonical s) (E.toCanonical b) = 1 := by
    rw [E.dist_eq, hsb]
  have hbq' : dist (E.toCanonical b) (E.toCanonical q) = 1 := by
    rw [E.dist_eq, hbq]
  have hsqSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical s) (E.toCanonical q)
  have hsbSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical s) (E.toCanonical b)
  have hbqSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical b) (E.toCanonical q)
  rw [hsq'] at hsqSq
  rw [hsb'] at hsbSq
  rw [hbq'] at hbqSq
  ext i
  fin_cases i
  · change (E.toCanonical b) 0 =
      (1 / 2 : ℝ) * ((E.toCanonical s) 0 + (E.toCanonical q) 0)
    have hzero :
        (2 * (E.toCanonical b) 0 -
            (E.toCanonical s) 0 - (E.toCanonical q) 0) ^ 2 +
          (2 * (E.toCanonical b) 1 -
            (E.toCanonical s) 1 - (E.toCanonical q) 1) ^ 2 = 0 := by
      nlinarith only [hsqSq, hsbSq, hbqSq]
    have hx : 2 * (E.toCanonical b) 0 -
          (E.toCanonical s) 0 - (E.toCanonical q) 0 = 0 := by
      nlinarith only [hzero,
        sq_nonneg (2 * (E.toCanonical b) 1 -
          (E.toCanonical s) 1 - (E.toCanonical q) 1)]
    linarith only [hx]
  · change (E.toCanonical b) 1 =
      (1 / 2 : ℝ) * ((E.toCanonical s) 1 + (E.toCanonical q) 1)
    have hzero :
        (2 * (E.toCanonical b) 0 -
            (E.toCanonical s) 0 - (E.toCanonical q) 0) ^ 2 +
          (2 * (E.toCanonical b) 1 -
            (E.toCanonical s) 1 - (E.toCanonical q) 1) ^ 2 = 0 := by
      nlinarith only [hsqSq, hsbSq, hbqSq]
    have hy : 2 * (E.toCanonical b) 1 -
          (E.toCanonical s) 1 - (E.toCanonical q) 1 = 0 := by
      nlinarith only [hzero,
        sq_nonneg (2 * (E.toCanonical b) 0 -
          (E.toCanonical s) 0 - (E.toCanonical q) 0)]
    linarith only [hy]

/-- The endpoint-normalized Case-4 chart is the common directed-edge chart
on the predecessor side, and its endpoint-swapping reflection on the
successor side.  In particular the second coordinate is identical in both
charts, while `[-1,0]` is invariant under the horizontal swap. -/
lemma CommonPairedCase4Rows.normalized_common_coordinates
    {A : Finset Point} {P : CyclicHullData A}
    {W : DiameterWitnessData P} {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu) (q : Point) :
    (Q.twoExtreme.side = .previous ∧
        Q.normalized.frame.toCanonical q =
          Q.commonFrame.frame.toCanonical q) ∨
      (Q.twoExtreme.side = .next ∧
        Q.normalized.frame.toCanonical q =
          Erdos957TwoExtremeAligned.swapEndpointCoord
            (Q.commonFrame.frame.toCanonical q)) := by
  cases hside : Q.twoExtreme.side with
  | previous =>
      left
      refine ⟨rfl, ?_⟩
      cases Q.normalized.frame_spec with
      | previous _hside hunit hframe =>
          rw [hframe]
          simp only [ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
            ActualCase24Rows.case4PairEdgeBase, hside,
            Erdos957EdgeFrame.terminalUnitEdgeRigidChart_toCanonical]
          have hnextValue :
              (P.next (P.next⁻¹ (sourceIndex P W u hu))).1.1 =
                (sourceIndex P W u hu).1.1 := by simp
          rw [hnextValue]
      | next hcontra _hunit _hframe =>
          simp [hside] at hcontra
  | next =>
      right
      refine ⟨rfl, ?_⟩
      cases Q.normalized.frame_spec with
      | previous hcontra _hunit _hframe =>
          simp [hside] at hcontra
      | next _hside hunit hframe =>
          rw [hframe]
          simp only [ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
            ActualCase24Rows.case4PairEdgeBase, hside,
            Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart]
          rfl

/-- Metric wrapper around the scalar arc cover.  The second disk in the
scalar statement is converted to the actual retained outer vertex using
the checked `2-1-1` midpoint characterization, and one-separation turns
strict closeness into an equality alternative. -/
lemma third_arc_vertex_eq_source_or_outer
    {A : Finset Point} (hA : Erdos957Cases24.IsOneSeparated A)
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    (source target outer n : Vertex A)
    (hsx : (399 / 400 : ℝ) < (E.toCanonical source) 0)
    (hsy : (E.toCanonical source) 1 < 0)
    (hshallow : -(E.toCanonical source) 1 ≤
      (E.toCanonical source) 0 / 10)
    (hqxLower : -1 ≤ (E.toCanonical target) 0)
    (hqxUpper : (E.toCanonical target) 0 ≤ 0)
    (hqy : (E.toCanonical target) 1 ≤ -Erdos957Cases24.sqrtThree)
    (hsq : dist (source : Point) target = 2)
    (hsb : dist (source : Point) outer = 1)
    (hbq : dist (outer : Point) target = 1)
    (hnorm : (E.toCanonical n) 0 ^ 2 +
      (E.toCanonical n) 1 ^ 2 = 1)
    (hnx : (1 / 2 : ℝ) ≤ (E.toCanonical n) 0)
    (hny : (E.toCanonical n) 1 < 0) :
    n = source ∨ n = outer := by
  have hsqCoord := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical source) (E.toCanonical target)
  have hdistCoord : dist (E.toCanonical source)
      (E.toCanonical target) = 2 := by
    rw [E.dist_eq, hsq]
  rw [hdistCoord] at hsqCoord
  have hcover := third_arc_close_to_source_or_outer
    hsx hsy hshallow hqxLower hqxUpper hqy
    (by nlinarith only [hsqCoord]) hnorm hnx hny
  have hmid := toCanonical_midpoint_of_dist_two_unit_unit
    E source target outer hsq hsb hbq
  rcases hcover with hcloseSource | hcloseOuter
  · have hdistSq := Erdos957Cases24.dist_sq_eq_coordinates
      (E.toCanonical n) (E.toCanonical source)
    have hdistSqLt : dist (E.toCanonical n)
        (E.toCanonical source) ^ 2 < 1 := by
      rw [hdistSq]
      exact hcloseSource
    have hcanonicalLt : dist (E.toCanonical n)
        (E.toCanonical source) < 1 := by
      nlinarith only [hdistSqLt,
        dist_nonneg (x := E.toCanonical n) (y := E.toCanonical source),
        sq_nonneg (dist (E.toCanonical n) (E.toCanonical source) + 1)]
    have hdistLt : dist (n : Point) source < 1 := by
      rw [← E.dist_eq]
      exact hcanonicalLt
    left
    by_contra hne
    have hsep := hA n n.property source source.property
      (fun h ↦ hne (Subtype.ext h))
    linarith only [hdistLt, hsep]
  · have hmid0 := congrArg (fun z : Point ↦ z 0) hmid
    have hmid1 := congrArg (fun z : Point ↦ z 1) hmid
    norm_num [PiLp.smul_apply] at hmid0 hmid1
    have hmid0' : (E.toCanonical outer) 0 =
        ((E.toCanonical source) 0 + (E.toCanonical target) 0) / 2 := by
      linarith only [hmid0]
    have hmid1' : (E.toCanonical outer) 1 =
        ((E.toCanonical source) 1 + (E.toCanonical target) 1) / 2 := by
      linarith only [hmid1]
    have hdistSq := Erdos957Cases24.dist_sq_eq_coordinates
      (E.toCanonical n) (E.toCanonical outer)
    have hdistSqLt : dist (E.toCanonical n)
        (E.toCanonical outer) ^ 2 < 1 := by
      rw [hdistSq, hmid0', hmid1']
      exact hcloseOuter
    have hcanonicalLt : dist (E.toCanonical n)
        (E.toCanonical outer) < 1 := by
      nlinarith only [hdistSqLt,
        dist_nonneg (x := E.toCanonical n) (y := E.toCanonical outer),
        sq_nonneg (dist (E.toCanonical n) (E.toCanonical outer) + 1)]
    have hdistLt : dist (n : Point) outer < 1 := by
      rw [← E.dist_eq]
      exact hcanonicalLt
    right
    by_contra hne
    have hsep := hA n n.property outer outer.property
      (fun h ↦ hne (Subtype.ext h))
    linarith only [hdistLt, hsep]

end Erdos957Case2SplitCoordinateLift

#print axioms Erdos957Case2SplitCoordinateLift.third_arc_close_to_source_or_outer
#print axioms Erdos957Case2SplitCoordinateLift.lower_unit_arc_snd_ge_neg_sqrtThree_half
#print axioms Erdos957Case2SplitCoordinateLift.toCanonical_midpoint_of_dist_two_unit_unit
#print axioms Erdos957Case2SplitCoordinateLift.CommonPairedCase4Rows.normalized_common_coordinates
#print axioms Erdos957Case2SplitCoordinateLift.third_arc_vertex_eq_source_or_outer
