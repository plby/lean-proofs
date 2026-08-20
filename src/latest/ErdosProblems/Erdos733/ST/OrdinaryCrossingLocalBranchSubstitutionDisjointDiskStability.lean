import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchGateCarrier
import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchDataPrefixTruncation
import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchDataSuffixTruncation
import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchDataThreePiecePrefixLift
import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchDataThreePieceSuffixLift
import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchSubstitution
import ErdosProblems.Erdos733.ST.PolygonalArcCarrierCompact
import ErdosProblems.Erdos733.ST.PolygonalArcRetainedOpenSubsegmentSingleLift

open Classical
noncomputable section


-- [TABLET NODE: OrdinaryCrossingLocalBranchSubstitutionDisjointDiskStability]
lemma OrdinaryCrossingLocalBranchSubstitutionDisjointDiskStability {ι : Type*}
    (Q bridge : PolygonalArc)
    (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (branch : OrdinaryCrossingLocalBranchData Q p radius)
    (center : ι → EuclideanSpace ℝ (Fin 2))
    (otherRadius : ι → ℝ)
    (otherBranch : ∀ a, OrdinaryCrossingLocalBranchData Q (center a) (otherRadius a)) :
    Q.source ∉ Metric.closedBall p radius →
      Q.target ∉ Metric.closedBall p radius →
        bridge.source = branch.beforeGate →
          bridge.target = branch.afterGate →
            bridge.carrier ⊆ Metric.closedBall p radius →
              bridge.relativeInterior ⊆ Metric.ball p radius →
                (∀ a, Disjoint (Metric.closedBall p radius)
                  (Metric.closedBall (center a) (otherRadius a))) →
                  ∃ Q' : PolygonalArc,
                    Q'.source = Q.source ∧
                    Q'.target = Q.target ∧
                    Q'.carrier =
                      (Q.carrier \ Metric.ball p radius) ∪ bridge.carrier ∧
                    Q'.carrier \ Metric.ball p radius =
                      Q.carrier \ Metric.ball p radius ∧
                    Q'.carrier ∩ Metric.ball p radius =
                      bridge.carrier ∩ Metric.ball p radius ∧
                    bridge.relativeInterior ⊆ Q'.relativeInterior ∧
                    (∀ z m (hm : m + 1 < bridge.vertices.length),
                      z ∈ openSegment ℝ bridge.vertices[m] bridge.vertices[m + 1] →
                        ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
                          z ∈ openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
                          ∃ c : ℝ, c ≠ 0 ∧
                            Q'.vertices[j + 1] - Q'.vertices[j] =
                              c • (bridge.vertices[m + 1] - bridge.vertices[m])) ∧
                    (∀ z i (hi : i + 1 < Q.vertices.length),
                      z ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1] →
                        z ∉ Metric.closedBall p radius →
                          ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
                            z ∈ openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
                            ∃ c : ℝ, c ≠ 0 ∧
                              Q'.vertices[j + 1] - Q'.vertices[j] =
                                c • (Q.vertices[i + 1] - Q.vertices[i])) ∧
                    ∀ a,
                      Metric.closedBall (center a) (otherRadius a) ∩ Q'.carrier =
                        Metric.closedBall (center a) (otherRadius a) ∩ Q.carrier ∧
                      Metric.sphere (center a) (otherRadius a) ∩ Q'.carrier =
                        Metric.sphere (center a) (otherRadius a) ∩ Q.carrier ∧
                      (∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
                        openSegment ℝ (otherBranch a).beforeGate (center a) ⊆
                            openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
                          ∃ c : ℝ, c ≠ 0 ∧
                            Q'.vertices[j + 1] - Q'.vertices[j] =
                              c •
                                (Q.vertices.get
                                    ⟨(otherBranch a).beforeIndex + 1,
                                      (otherBranch a).beforeIndex_valid⟩ -
                                  Q.vertices.get
                                    ⟨(otherBranch a).beforeIndex,
                                      Nat.lt_of_succ_lt
                                        (otherBranch a).beforeIndex_valid⟩)) ∧
                      (∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
                        openSegment ℝ (center a) (otherBranch a).afterGate ⊆
                            openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
                          ∃ c : ℝ, c ≠ 0 ∧
                            Q'.vertices[j + 1] - Q'.vertices[j] =
                              c •
                                (Q.vertices.get
                                    ⟨(otherBranch a).afterIndex + 1,
                                      (otherBranch a).afterIndex_valid⟩ -
                                  Q.vertices.get
                                    ⟨(otherBranch a).afterIndex,
                                      Nat.lt_of_succ_lt
                                        (otherBranch a).afterIndex_valid⟩)) ∧
                      ∃ branch' : OrdinaryCrossingLocalBranchData Q'
                          (center a) (otherRadius a),
                        branch'.beforeGate = (otherBranch a).beforeGate ∧
                          branch'.afterGate = (otherBranch a).afterGate := by
-- BODY
  intro hsource htarget hbridgeSource hbridgeTarget hbridgeClosed hbridgeOpen hdisjoint
  rcases OrdinaryCrossingLocalBranchSubstitution Q bridge p radius branch
      hsource htarget hbridgeSource hbridgeTarget hbridgeClosed hbridgeOpen with
    ⟨Q', hQsource, hQtarget, hcarrier, houtside, hinside, hbridgeInterior,
      hbridgeTransfer, holdTransfer, prefixArc, suffixArc, hprefixVertices,
      hsuffixVertices, hQvertices, hattach, hprefixSubset, hsuffixSubset,
      houtsidePieces, hpiecesDisjoint⟩
  have open_left_trans :
      ∀ {a b c x : EuclideanSpace ℝ (Fin 2)},
        b ∈ openSegment ℝ a c → x ∈ openSegment ℝ a b →
          x ∈ openSegment ℝ a c := by
    intro a b c x hb hx
    rw [openSegment_eq_image_lineMap] at hb hx ⊢
    rcases hb with ⟨t, ht, hbt⟩
    rcases hx with ⟨s, hs, hxs⟩
    refine ⟨s * t, ⟨mul_pos hs.1 ht.1, ?_⟩, ?_⟩
    · have hlt : s * t < t := by
        simpa using mul_lt_mul_of_pos_right hs.2 ht.1
      exact hlt.trans ht.2
    · rw [← hxs, ← hbt]
      exact (AffineMap.lineMap_lineMap_right a c t s).symm
  have open_right_trans :
      ∀ {a b c x : EuclideanSpace ℝ (Fin 2)},
        b ∈ openSegment ℝ a c → x ∈ openSegment ℝ b c →
          x ∈ openSegment ℝ a c := by
    intro a b c x hb hx
    rw [openSegment_eq_image_lineMap] at hb hx ⊢
    rcases hb with ⟨t, ht, hbt⟩
    rcases hx with ⟨s, hs, hxs⟩
    refine ⟨1 - (1 - s) * (1 - t), ⟨?_, ?_⟩, ?_⟩
    · have hpos : 0 < t + s * (1 - t) :=
        add_pos ht.1 (mul_pos hs.1 (sub_pos.mpr ht.2))
      have heq : 1 - (1 - s) * (1 - t) = t + s * (1 - t) := by
        ring
      rw [heq]
      exact hpos
    · nlinarith [mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr ht.2)]
    · rw [← hxs, ← hbt]
      exact (AffineMap.lineMap_lineMap_left a c t s).symm
  have hprocessedBefore0 : branch.beforeIndex < Q.vertices.length :=
    Nat.lt_of_succ_lt branch.beforeIndex_valid
  have processed_before_open_full : branch.beforeGate ∈ openSegment ℝ
      (Q.vertices.get ⟨branch.beforeIndex, hprocessedBefore0⟩)
        (Q.vertices.get ⟨branch.beforeIndex + 1, branch.beforeIndex_valid⟩) := by
    rcases branch.center_case with hcenter | hcenter
    · simpa only [List.get_eq_getElem] using
        open_left_trans hcenter.2 branch.beforeGate_open
    · simpa only [List.get_eq_getElem, hcenter.1, hcenter.2] using
        branch.beforeGate_open
  have hprocessedAfter0 : branch.afterIndex < Q.vertices.length :=
    Nat.lt_of_succ_lt branch.afterIndex_valid
  have processed_after_open_full : branch.afterGate ∈ openSegment ℝ
      (Q.vertices.get ⟨branch.afterIndex, hprocessedAfter0⟩)
        (Q.vertices.get ⟨branch.afterIndex + 1, branch.afterIndex_valid⟩) := by
    rcases branch.center_case with hcenter | hcenter
    · have hfull := open_right_trans hcenter.2 (by
        simpa only [hcenter.1] using branch.afterGate_open)
      simpa only [List.get_eq_getElem, hcenter.1] using hfull
    · simpa only [List.get_eq_getElem, hcenter.1, hcenter.2] using
        branch.afterGate_open
  have before_open_full : ∀ a z,
      z ∈ openSegment ℝ (otherBranch a).beforeGate (center a) →
        z ∈ openSegment ℝ
          (Q.vertices.get
            ⟨(otherBranch a).beforeIndex,
              Nat.lt_of_succ_lt (otherBranch a).beforeIndex_valid⟩)
          (Q.vertices.get
            ⟨(otherBranch a).beforeIndex + 1,
              (otherBranch a).beforeIndex_valid⟩) := by
    intro a z hz
    have hzlocal := open_right_trans (otherBranch a).beforeGate_open hz
    rcases (otherBranch a).center_case with hcenter | hcenter
    · exact open_left_trans hcenter.2 hzlocal
    · simpa [hcenter.1, hcenter.2] using hzlocal
  have after_open_full : ∀ a z,
      z ∈ openSegment ℝ (center a) (otherBranch a).afterGate →
        z ∈ openSegment ℝ
          (Q.vertices.get
            ⟨(otherBranch a).afterIndex,
              Nat.lt_of_succ_lt (otherBranch a).afterIndex_valid⟩)
          (Q.vertices.get
            ⟨(otherBranch a).afterIndex + 1,
              (otherBranch a).afterIndex_valid⟩) := by
    intro a z hz
    have hzlocal := open_left_trans (otherBranch a).afterGate_open hz
    rcases (otherBranch a).center_case with hcenter | hcenter
    · apply open_right_trans (by simpa [hcenter.1] using hcenter.2)
      simpa [hcenter.1] using hzlocal
    · simpa [hcenter.1, hcenter.2] using hzlocal
  have before_direction : ∀ a,
      ∃ d : ℝ, d ≠ 0 ∧
        center a - (otherBranch a).beforeGate =
          d •
            (Q.vertices.get
                ⟨(otherBranch a).beforeIndex + 1,
                  (otherBranch a).beforeIndex_valid⟩ -
              Q.vertices.get
                ⟨(otherBranch a).beforeIndex,
                  Nat.lt_of_succ_lt (otherBranch a).beforeIndex_valid⟩) := by
    intro a
    let x := center a
    let g := (otherBranch a).beforeGate
    let v0 := Q.vertices.get
      ⟨(otherBranch a).beforeIndex,
        Nat.lt_of_succ_lt (otherBranch a).beforeIndex_valid⟩
    let v1 := Q.vertices.get
      ⟨(otherBranch a).beforeIndex + 1,
        (otherBranch a).beforeIndex_valid⟩
    have hgateOpen := (otherBranch a).beforeGate_open
    rw [openSegment_eq_image_lineMap] at hgateOpen
    rcases hgateOpen with ⟨t, ht, hgate⟩
    rcases (otherBranch a).center_case with hcenter | hcenter
    · rw [openSegment_eq_image_lineMap] at hcenter
      rcases hcenter.2 with ⟨u, hu, hcenterEq⟩
      refine ⟨(1 - t) * u, mul_ne_zero (sub_ne_zero.mpr (ne_of_gt ht.2))
        (ne_of_gt hu.1), ?_⟩
      change x - g = ((1 - t) * u) • (v1 - v0)
      have hg : g = AffineMap.lineMap v0 x t := by
        simpa [g, v0, x] using hgate.symm
      have hx : x = AffineMap.lineMap v0 v1 u := by
        simpa [x, v0, v1] using hcenterEq.symm
      rw [hg, hx]
      simp only [AffineMap.lineMap_apply_module']
      module
    · refine ⟨1 - t, sub_ne_zero.mpr (ne_of_gt ht.2), ?_⟩
      change x - g = (1 - t) • (v1 - v0)
      have hg : g = AffineMap.lineMap v0 x t := by
        simpa [g, v0, x] using hgate.symm
      have hx : x = v1 := by
        simpa [x, v1, hcenter.1] using hcenter.2
      rw [hg, hx]
      simp only [AffineMap.lineMap_apply_module']
      module
  have after_direction : ∀ a,
      ∃ d : ℝ, d ≠ 0 ∧
        (otherBranch a).afterGate - center a =
          d •
            (Q.vertices.get
                ⟨(otherBranch a).afterIndex + 1,
                  (otherBranch a).afterIndex_valid⟩ -
              Q.vertices.get
                ⟨(otherBranch a).afterIndex,
                  Nat.lt_of_succ_lt (otherBranch a).afterIndex_valid⟩) := by
    intro a
    let x := center a
    let g := (otherBranch a).afterGate
    let v0 := Q.vertices.get
      ⟨(otherBranch a).afterIndex,
        Nat.lt_of_succ_lt (otherBranch a).afterIndex_valid⟩
    let v1 := Q.vertices.get
      ⟨(otherBranch a).afterIndex + 1,
        (otherBranch a).afterIndex_valid⟩
    have hgateOpen := (otherBranch a).afterGate_open
    rw [openSegment_eq_image_lineMap] at hgateOpen
    rcases hgateOpen with ⟨t, ht, hgate⟩
    rcases (otherBranch a).center_case with hcenter | hcenter
    · rw [openSegment_eq_image_lineMap] at hcenter
      rcases hcenter.2 with ⟨u, hu, hcenterEq⟩
      refine ⟨t * (1 - u), mul_ne_zero (ne_of_gt ht.1)
        (sub_ne_zero.mpr (ne_of_gt hu.2)), ?_⟩
      change g - x = (t * (1 - u)) • (v1 - v0)
      have hg : g = AffineMap.lineMap x v1 t := by
        simpa [g, v1, x] using hgate.symm
      have hx : x = AffineMap.lineMap v0 v1 u := by
        simpa [x, v0, v1, hcenter.1] using hcenterEq.symm
      rw [hg, hx]
      simp only [AffineMap.lineMap_apply_module']
      module
    · refine ⟨t, ne_of_gt ht.1, ?_⟩
      change g - x = t • (v1 - v0)
      have hg : g = AffineMap.lineMap x v1 t := by
        simpa [g, v1, x] using hgate.symm
      have hx : x = v0 := by
        simpa [x, v0] using hcenter.2
      rw [hg, hx]
      simp only [AffineMap.lineMap_apply_module']
      module
  have subsegment_outside : ∀ a z,
      z ∈ segment ℝ (otherBranch a).beforeGate (center a) ∨
        z ∈ segment ℝ (center a) (otherBranch a).afterGate →
          z ∉ Metric.closedBall p radius := by
    intro a z hz hzp
    have hgateBefore : (otherBranch a).beforeGate ∈
        Metric.closedBall (center a) (otherRadius a) :=
      Metric.sphere_subset_closedBall (otherBranch a).beforeGate_on_sphere
    have hgateAfter : (otherBranch a).afterGate ∈
        Metric.closedBall (center a) (otherRadius a) :=
      Metric.sphere_subset_closedBall (otherBranch a).afterGate_on_sphere
    have hcenterClosed : center a ∈
        Metric.closedBall (center a) (otherRadius a) := by
      simpa [Metric.mem_closedBall] using (le_of_lt (otherBranch a).radius_pos)
    have hzother : z ∈ Metric.closedBall (center a) (otherRadius a) := by
      rcases hz with hz | hz
      · exact (convex_closedBall (center a) (otherRadius a)).segment_subset
          hgateBefore hcenterClosed hz
      · exact (convex_closedBall (center a) (otherRadius a)).segment_subset
          hcenterClosed hgateAfter hz
    exact (Set.disjoint_left.mp (hdisjoint a) hzp) hzother
  refine ⟨Q', hQsource, hQtarget, hcarrier, houtside, hinside,
    hbridgeInterior, hbridgeTransfer, holdTransfer, ?_⟩
  intro a
  have hlocal : Metric.closedBall (center a) (otherRadius a) ∩ Q'.carrier =
      Metric.closedBall (center a) (otherRadius a) ∩ Q.carrier := by
    ext z
    constructor
    · intro hz
      have hzout : z ∉ Metric.ball p radius := by
        intro hzball
        exact (Set.disjoint_left.mp (hdisjoint a)
          (Metric.ball_subset_closedBall hzball)) hz.1
      have hzold := Set.ext_iff.mp houtside z
      exact ⟨hz.1, (hzold.mp ⟨hz.2, hzout⟩).1⟩
    · intro hz
      have hzout : z ∉ Metric.ball p radius := by
        intro hzball
        have hzp := Metric.ball_subset_closedBall hzball
        exact (Set.disjoint_left.mp (hdisjoint a) hzp) hz.1
      have hzold := Set.ext_iff.mp houtside z
      exact ⟨hz.1, (hzold.mpr ⟨hz.2, hzout⟩).1⟩
  have hsphere : Metric.sphere (center a) (otherRadius a) ∩ Q'.carrier =
      Metric.sphere (center a) (otherRadius a) ∩ Q.carrier := by
    ext z
    constructor
    · intro hz
      have hzclosed := Metric.sphere_subset_closedBall hz.1
      exact ⟨hz.1, (Set.ext_iff.mp hlocal z).mp ⟨hzclosed, hz.2⟩ |>.2⟩
    · intro hz
      have hzclosed := Metric.sphere_subset_closedBall hz.1
      exact ⟨hz.1, (Set.ext_iff.mp hlocal z).mpr ⟨hzclosed, hz.2⟩ |>.2⟩
  have hbeforeTransfer : ∀ z,
      z ∈ openSegment ℝ (otherBranch a).beforeGate (center a) →
        ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
          z ∈ openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
            ∃ c : ℝ, c ≠ 0 ∧
              Q'.vertices[j + 1] - Q'.vertices[j] =
                c •
                  (Q.vertices.get
                      ⟨(otherBranch a).beforeIndex + 1,
                        (otherBranch a).beforeIndex_valid⟩ -
                    Q.vertices.get
                      ⟨(otherBranch a).beforeIndex,
                        Nat.lt_of_succ_lt
                          (otherBranch a).beforeIndex_valid⟩) := by
    intro z hz
    exact holdTransfer z (otherBranch a).beforeIndex
      (otherBranch a).beforeIndex_valid (before_open_full a z hz)
      (subsegment_outside a z (Or.inl
        (openSegment_subset_segment ℝ _ _ hz)))
  have hafterTransfer : ∀ z,
      z ∈ openSegment ℝ (center a) (otherBranch a).afterGate →
        ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
          z ∈ openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
            ∃ c : ℝ, c ≠ 0 ∧
              Q'.vertices[j + 1] - Q'.vertices[j] =
                c •
                  (Q.vertices.get
                      ⟨(otherBranch a).afterIndex + 1,
                        (otherBranch a).afterIndex_valid⟩ -
                    Q.vertices.get
                      ⟨(otherBranch a).afterIndex,
                        Nat.lt_of_succ_lt
                          (otherBranch a).afterIndex_valid⟩) := by
    intro z hz
    exact holdTransfer z (otherBranch a).afterIndex
      (otherBranch a).afterIndex_valid (after_open_full a z hz)
      (subsegment_outside a z (Or.inr
        (openSegment_subset_segment ℝ _ _ hz)))
  have hbeforeLift := PolygonalArcRetainedOpenSubsegmentSingleLift Q Q'
    (otherBranch a).beforeGate (center a) (otherBranch a).beforeIndex
    (otherBranch a).beforeIndex_valid (before_direction a) hbeforeTransfer
  have hafterLift := PolygonalArcRetainedOpenSubsegmentSingleLift Q Q'
    (center a) (otherBranch a).afterGate (otherBranch a).afterIndex
    (otherBranch a).afterIndex_valid (after_direction a) hafterTransfer
  let K : Set (EuclideanSpace ℝ (Fin 2)) :=
    segment ℝ (otherBranch a).beforeGate (center a) ∪
      segment ℝ (center a) (otherBranch a).afterGate
  have hKexact : Metric.closedBall (center a) (otherRadius a) ∩ Q.carrier = K := by
    simpa only [K] using OrdinaryCrossingLocalBranchGateCarrier Q (center a)
      (otherRadius a) (otherBranch a)
  have hKpre : IsPreconnected K := by
    dsimp only [K]
    exact (convex_segment (otherBranch a).beforeGate (center a)).isPreconnected.union
      (center a) (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _)
      (convex_segment (center a) (otherBranch a).afterGate).isPreconnected
  have hKsubset : K ⊆ prefixArc.carrier ∪ suffixArc.carrier := by
    intro z hz
    have hzBoth : z ∈ Metric.closedBall (center a) (otherRadius a) ∩ Q.carrier := by
      rw [hKexact]
      exact hz
    have hzOut : z ∉ Metric.ball p radius := by
      intro hzBall
      exact (Set.disjoint_left.mp (hdisjoint a)
        (Metric.ball_subset_closedBall hzBall)) hzBoth.1
    rw [houtsidePieces]
    exact ⟨hzBoth.2, hzOut⟩
  have hKpiecesEmpty :
      K ∩ (prefixArc.carrier ∩ suffixArc.carrier) = ∅ := by
    ext z
    constructor
    · intro hz
      exact False.elim ((Set.disjoint_left.mp hpiecesDisjoint hz.2.1) hz.2.2)
    · intro hz
      exact hz.elim
  have hKpiece : K ⊆ prefixArc.carrier ∨ K ⊆ suffixArc.carrier :=
    (isPreconnected_iff_subset_of_disjoint_closed.mp hKpre)
      prefixArc.carrier suffixArc.carrier
      (PolygonalArcCarrierCompact prefixArc).isClosed
      (PolygonalArcCarrierCompact suffixArc).isClosed
      hKsubset hKpiecesEmpty
  have hbranch' : ∃ branch' : OrdinaryCrossingLocalBranchData Q'
      (center a) (otherRadius a),
      branch'.beforeGate = (otherBranch a).beforeGate ∧
        branch'.afterGate = (otherBranch a).afterGate := by
    rcases hKpiece with hKprefix | hKsuffix
    · have hprefixClosed : Metric.closedBall (center a) (otherRadius a) ∩
          prefixArc.carrier =
            Metric.closedBall (center a) (otherRadius a) ∩ Q.carrier := by
        apply Set.Subset.antisymm
        · rintro z ⟨hzBall, hzPrefix⟩
          exact ⟨hzBall, hprefixSubset hzPrefix⟩
        · intro z hz
          refine ⟨hz.1, hKprefix ?_⟩
          rw [← hKexact]
          exact hz
      have hprefixSphere : Metric.sphere (center a) (otherRadius a) ∩
          prefixArc.carrier =
            Metric.sphere (center a) (otherRadius a) ∩ Q.carrier := by
        apply Set.Subset.antisymm
        · rintro z ⟨hzSphere, hzPrefix⟩
          exact ⟨hzSphere, hprefixSubset hzPrefix⟩
        · intro z hz
          refine ⟨hz.1, hKprefix ?_⟩
          rw [← hKexact]
          exact ⟨Metric.sphere_subset_closedBall hz.1, hz.2⟩
      have hcutOutside : branch.beforeGate ∉
          Metric.closedBall (center a) (otherRadius a) := by
        intro hcutOther
        exact (Set.disjoint_left.mp (hdisjoint a)
          (Metric.sphere_subset_closedBall branch.beforeGate_on_sphere)) hcutOther
      obtain ⟨branchPrefix, hbeforePrefix, hafterPrefix⟩ :=
        OrdinaryCrossingLocalBranchDataPrefixTruncation Q prefixArc
          branch.beforeGate (center a) (otherRadius a) branch.beforeIndex
          branch.beforeIndex_valid processed_before_open_full hprefixVertices
          (otherBranch a) hcutOutside hKprefix hprefixClosed hprefixSphere
      obtain ⟨branchFinal, hbeforeFinal, hafterFinal⟩ :=
        OrdinaryCrossingLocalBranchDataThreePiecePrefixLift
          prefixArc bridge suffixArc Q' (center a) (otherRadius a) branchPrefix
          hQvertices (hlocal.trans hprefixClosed.symm)
          (hsphere.trans hprefixSphere.symm)
      exact ⟨branchFinal, hbeforeFinal.trans hbeforePrefix,
        hafterFinal.trans hafterPrefix⟩
    · have hsuffixClosed : Metric.closedBall (center a) (otherRadius a) ∩
          suffixArc.carrier =
            Metric.closedBall (center a) (otherRadius a) ∩ Q.carrier := by
        apply Set.Subset.antisymm
        · rintro z ⟨hzBall, hzSuffix⟩
          exact ⟨hzBall, hsuffixSubset hzSuffix⟩
        · intro z hz
          refine ⟨hz.1, hKsuffix ?_⟩
          rw [← hKexact]
          exact hz
      have hsuffixSphere : Metric.sphere (center a) (otherRadius a) ∩
          suffixArc.carrier =
            Metric.sphere (center a) (otherRadius a) ∩ Q.carrier := by
        apply Set.Subset.antisymm
        · rintro z ⟨hzSphere, hzSuffix⟩
          exact ⟨hzSphere, hsuffixSubset hzSuffix⟩
        · intro z hz
          refine ⟨hz.1, hKsuffix ?_⟩
          rw [← hKexact]
          exact ⟨Metric.sphere_subset_closedBall hz.1, hz.2⟩
      have hcutOutside : branch.afterGate ∉
          Metric.closedBall (center a) (otherRadius a) := by
        intro hcutOther
        exact (Set.disjoint_left.mp (hdisjoint a)
          (Metric.sphere_subset_closedBall branch.afterGate_on_sphere)) hcutOther
      obtain ⟨branchSuffix, hbeforeSuffix, hafterSuffix⟩ :=
        OrdinaryCrossingLocalBranchDataSuffixTruncation Q suffixArc
          branch.afterGate (center a) (otherRadius a) branch.afterIndex
          branch.afterIndex_valid processed_after_open_full hsuffixVertices
          (otherBranch a) hcutOutside hKsuffix hsuffixClosed hsuffixSphere
      obtain ⟨branchFinal, hbeforeFinal, hafterFinal⟩ :=
        OrdinaryCrossingLocalBranchDataThreePieceSuffixLift
          prefixArc bridge suffixArc Q' (center a) (otherRadius a) branchSuffix
          hQvertices hattach (hlocal.trans hsuffixClosed.symm)
          (hsphere.trans hsuffixSphere.symm)
      exact ⟨branchFinal, hbeforeFinal.trans hbeforeSuffix,
        hafterFinal.trans hafterSuffix⟩
  exact ⟨hlocal, hsphere, hbeforeLift, hafterLift, hbranch'⟩
