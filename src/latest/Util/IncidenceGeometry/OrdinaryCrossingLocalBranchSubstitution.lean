import Util.IncidenceGeometry.OrdinaryCrossingLocalBranchData
import Util.IncidenceGeometry.PolygonalArcFirstBallCutDataExists
import Util.IncidenceGeometry.PolygonalArcInteriorPointCutDataExists
import Util.IncidenceGeometry.PolygonalArcOrderedThreePieceSplice
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Tactic

open Classical
noncomputable section

private lemma ocOpenLeftTrans
    {a b c x : EuclideanSpace ℝ (Fin 2)}
    (hb : b ∈ openSegment ℝ a c) (hx : x ∈ openSegment ℝ a b) :
    x ∈ openSegment ℝ a c := by
  rw [openSegment_eq_image_lineMap] at hb hx ⊢
  rcases hb with ⟨t, ht, hbt⟩
  rcases hx with ⟨s, hs, hxs⟩
  refine ⟨s * t, ⟨mul_pos hs.1 ht.1, ?_⟩, ?_⟩
  · have hlt : s * t < t := by
      simpa using mul_lt_mul_of_pos_right hs.2 ht.1
    exact hlt.trans ht.2
  · rw [← hxs, ← hbt]
    exact (AffineMap.lineMap_lineMap_right a c t s).symm

private lemma ocOpenRightTrans
    {a b c x : EuclideanSpace ℝ (Fin 2)}
    (hb : b ∈ openSegment ℝ a c) (hx : x ∈ openSegment ℝ b c) :
    x ∈ openSegment ℝ a c := by
  rw [openSegment_eq_image_lineMap] at hb hx ⊢
  rcases hb with ⟨t, ht, hbt⟩
  rcases hx with ⟨s, hs, hxs⟩
  refine ⟨1 - (1 - s) * (1 - t), ⟨?_, ?_⟩, ?_⟩
  · have hpos : 0 < t + s * (1 - t) :=
      add_pos ht.1 (mul_pos hs.1 (sub_pos.mpr ht.2))
    nlinarith [hpos]
  · nlinarith [mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr ht.2)]
  · rw [← hxs, ← hbt]
    exact (AffineMap.lineMap_lineMap_left a c t s).symm

private lemma ocOpenBeforeLater
    {a b c d : EuclideanSpace ℝ (Fin 2)}
    (hb : b ∈ openSegment ℝ a c) (hd : d ∈ openSegment ℝ b c) :
    b ∈ openSegment ℝ a d := by
  rw [openSegment_eq_image_lineMap] at hb hd ⊢
  rcases hb with ⟨t, ht, hbt⟩
  rcases hd with ⟨s, hs, hds⟩
  let u : ℝ := 1 - (1 - s) * (1 - t)
  have hu_pos : 0 < u := by
    dsimp [u]
    have hpos : 0 < t + s * (1 - t) :=
      add_pos ht.1 (mul_pos hs.1 (sub_pos.mpr ht.2))
    nlinarith [hpos]
  have htu : t < u := by
    dsimp [u]
    nlinarith [mul_pos hs.1 (sub_pos.mpr ht.2)]
  have hdu : AffineMap.lineMap a c u = d := by
    rw [← hds, ← hbt]
    dsimp [u]
    exact (AffineMap.lineMap_lineMap_left a c t s).symm
  refine ⟨t / u, ⟨div_pos ht.1 hu_pos, (div_lt_one hu_pos).2 htu⟩, ?_⟩
  rw [← hbt, ← hdu, AffineMap.lineMap_lineMap_right]
  congr 1
  field_simp

private lemma ocOpenAfterEarlier
    {a b c d : EuclideanSpace ℝ (Fin 2)}
    (hb : b ∈ openSegment ℝ a c) (hc : c ∈ openSegment ℝ a d) :
    c ∈ openSegment ℝ b d := by
  rw [openSegment_symm ℝ a c] at hb
  rw [openSegment_symm ℝ a d] at hc
  have h := ocOpenBeforeLater hc hb
  simpa only [openSegment_symm ℝ d b] using h

private lemma ocOpenIndexUnique
    (R : PolygonalArc) (q : EuclideanSpace ℝ (Fin 2)) (s t : ℕ)
    (hs : s + 1 < R.vertices.length) (ht : t + 1 < R.vertices.length)
    (hqopen : q ∈ openSegment ℝ R.vertices[s] R.vertices[s + 1])
    (hqseg : q ∈ segment ℝ R.vertices[t] R.vertices[t + 1]) : s = t := by
  have hq_not_vertex : q ∉ R.vertices := by
    intro hqmem
    obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hqmem
    have hend_ne : R.vertices[s] ≠ R.vertices[s + 1] := by
      have hrel := R.simple_vertices.rel_get_of_lt
        (a := ⟨s, by omega⟩) (b := ⟨s + 1, by omega⟩) (by simp)
      simpa [List.get_eq_getElem] using hrel
    by_cases hks : k = s
    · have hqeq : q = R.vertices[s] := by simpa [hks] using hkeq.symm
      have hleft : R.vertices[s] ∈
          openSegment ℝ R.vertices[s] R.vertices[s + 1] := by
        simpa [hqeq] using hqopen
      exact hend_ne (left_mem_openSegment_iff.mp hleft)
    by_cases hks1 : k = s + 1
    · have hqeq : q = R.vertices[s + 1] := by
        simpa [hks1] using hkeq.symm
      have hright : R.vertices[s + 1] ∈
          openSegment ℝ R.vertices[s] R.vertices[s + 1] := by
        simpa [hqeq] using hqopen
      exact hend_ne (right_mem_openSegment_iff.mp hright)
    exact R.vertices_avoid_nonincident_interiors hs hk hks hks1
      (by simpa [hkeq] using hqopen)
  by_contra hst
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · have hinter := R.segment_intersections hs ht hlt
    have hqinter :
        q ∈ segment ℝ R.vertices[s] R.vertices[s + 1] ∩
          segment ℝ R.vertices[t] R.vertices[t + 1] :=
      ⟨openSegment_subset_segment ℝ _ _ hqopen, hqseg⟩
    rw [hinter] at hqinter
    split at hqinter
    · have hqeq : q = R.vertices[t] := by simpa using hqinter
      exact hq_not_vertex (by rw [hqeq]; exact List.getElem_mem _)
    · exact hqinter
  · have hinter := R.segment_intersections ht hs hgt
    have hqinter :
        q ∈ segment ℝ R.vertices[t] R.vertices[t + 1] ∩
          segment ℝ R.vertices[s] R.vertices[s + 1] :=
      ⟨hqseg, openSegment_subset_segment ℝ _ _ hqopen⟩
    rw [hinter] at hqinter
    split at hqinter
    · have hqeq : q = R.vertices[s] := by simpa using hqinter
      exact hq_not_vertex (by rw [hqeq]; exact List.getElem_mem _)
    · exact hqinter

private lemma ocOutwardSegment
    {p g v : EuclideanSpace ℝ (Fin 2)} {radius : ℝ}
    (hgopen : g ∈ openSegment ℝ p v) (hgsphere : g ∈ Metric.sphere p radius) :
    Disjoint (segment ℝ g v) (Metric.ball p radius) := by
  rw [Set.disjoint_left]
  intro z hzseg hzball
  rw [openSegment_eq_image_lineMap] at hgopen
  rcases hgopen with ⟨t, ht, hgt⟩
  rw [segment_eq_image_lineMap] at hzseg
  rcases hzseg with ⟨s, hs, hzs⟩
  let u : ℝ := 1 - (1 - s) * (1 - t)
  have htu : t ≤ u := by
    dsimp [u]
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr ht.2.le)]
  have hu0 : 0 ≤ u := ht.1.le.trans htu
  have hzline : AffineMap.lineMap p v u = z := by
    rw [← hzs, ← hgt]
    dsimp [u]
    exact (AffineMap.lineMap_lineMap_left p v t s).symm
  have hdistg : dist g p = t * dist p v := by
    rw [← hgt, dist_lineMap_left, Real.norm_of_nonneg ht.1.le]
  have hdistz : dist z p = u * dist p v := by
    rw [← hzline, dist_lineMap_left, Real.norm_of_nonneg hu0]
  rw [Metric.mem_sphere] at hgsphere
  rw [Metric.mem_ball] at hzball
  have hdist_nonneg : 0 ≤ dist p v := dist_nonneg
  nlinarith

private lemma ocArcSourceMemCarrier (R : PolygonalArc) : R.source ∈ R.carrier := by
  rw [R.carrier_eq]
  have hlen := R.length_ge_two
  refine ⟨0, by omega, ?_⟩
  have hzero : R.vertices[0] = R.source := by
    have hhead := R.source_eq_head
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
    exact Option.some.inj hhead
  rw [hzero]
  exact left_mem_segment ℝ R.source R.vertices[1]

private lemma ocArcTargetMemCarrier (R : PolygonalArc) : R.target ∈ R.carrier := by
  rw [R.carrier_eq]
  let m := R.vertices.length - 2
  have hm : m + 1 < R.vertices.length := by
    have hlen := R.length_ge_two
    dsimp [m]
    omega
  refine ⟨m, hm, ?_⟩
  have hlast : R.vertices[m + 1] = R.target := by
    have hlast_get := R.target_eq_last
    rw [List.getLast?_eq_getElem?] at hlast_get
    have hidx : R.vertices.length - 1 < R.vertices.length := by
      have hlen := R.length_ge_two
      omega
    rw [List.getElem?_eq_getElem hidx] at hlast_get
    have hm_eq : m + 1 = R.vertices.length - 1 := by
      dsimp [m]
      omega
    simpa [hm_eq] using Option.some.inj hlast_get
  rw [hlast]
  exact right_mem_segment ℝ R.vertices[m] R.target

private lemma ocGateMemRelativeInterior
    (Q : PolygonalArc) (p q : EuclideanSpace ℝ (Fin 2)) (radius : ℝ) (i : ℕ)
    (hi : i + 1 < Q.vertices.length)
    (hqOpen : q ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1])
    (hqClosed : q ∈ Metric.closedBall p radius)
    (hsource : Q.source ∉ Metric.closedBall p radius)
    (htarget : Q.target ∉ Metric.closedBall p radius) :
    q ∈ Q.relativeInterior := by
  rw [Q.relativeInterior_eq]
  refine ⟨?_, ?_⟩
  · rw [Q.carrier_eq]
    exact ⟨i, hi, openSegment_subset_segment ℝ _ _ hqOpen⟩
  · intro hends
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
    rcases hends with hends | hends
    · apply hsource
      rw [← hends]
      exact hqClosed
    · apply htarget
      rw [← hends]
      exact hqClosed

private lemma ocAfterGateMemClosure
    (Q : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (branch : OrdinaryCrossingLocalBranchData Q p radius) :
    branch.afterGate ∈ closure (Q.carrier ∩ Metric.ball p radius) := by
  have hpClosed : p ∈ Metric.closedBall p radius := by
    rw [Metric.mem_closedBall, dist_self]
    exact branch.radius_pos.le
  have hafterClosed : branch.afterGate ∈ Metric.closedBall p radius :=
    Metric.sphere_subset_closedBall branch.afterGate_on_sphere
  have hafterLt : branch.afterIndex < Q.vertices.length :=
    Nat.lt_of_succ_lt branch.afterIndex_valid
  have hafterSucc : branch.afterIndex + 1 < Q.vertices.length :=
    branch.afterIndex_valid
  have hopenSubset : openSegment ℝ p branch.afterGate ⊆
      Q.carrier ∩ Metric.ball p radius := by
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [Q.carrier_eq]
      refine ⟨branch.afterIndex, branch.afterIndex_valid, ?_⟩
      have hseg : segment ℝ p branch.afterGate ⊆
          segment ℝ p
            (Q.vertices[branch.afterIndex + 1]'hafterSucc) :=
        (convex_segment p
          (Q.vertices[branch.afterIndex + 1]'hafterSucc)).segment_subset
          (left_mem_segment ℝ p
            (Q.vertices[branch.afterIndex + 1]'hafterSucc))
          (openSegment_subset_segment ℝ _ _ branch.afterGate_open)
      have hz' := hseg (openSegment_subset_segment ℝ _ _ hz)
      rcases branch.center_case with hcenter | hcenter
      · have hpFull : p ∈ segment ℝ (Q.vertices[branch.afterIndex]'hafterLt)
            (Q.vertices[branch.afterIndex + 1]'hafterSucc) := by
          simpa [hcenter.1] using
            (openSegment_subset_segment ℝ _ _ hcenter.2)
        exact (convex_segment (Q.vertices[branch.afterIndex]'hafterLt)
            (Q.vertices[branch.afterIndex + 1]'hafterSucc)).segment_subset hpFull
          (right_mem_segment ℝ _ _) hz'
      · simpa [hcenter.1, hcenter.2] using hz'
    · exact openSegment_subset_ball_of_ne hpClosed hafterClosed
        (by
          intro h
          have hpSphere := Metric.mem_sphere.mp branch.afterGate_on_sphere
          rw [← h, dist_self] at hpSphere
          linarith [branch.radius_pos]) hz
  exact segment_subset_closure_openSegment
    (right_mem_segment ℝ p branch.afterGate) |>
      closure_mono hopenSubset

private lemma ocSphereOfClosedNotBall
    {p z : EuclideanSpace ℝ (Fin 2)} {radius : ℝ}
    (hzClosed : z ∈ Metric.closedBall p radius)
    (hzBall : z ∉ Metric.ball p radius) : z ∈ Metric.sphere p radius := by
  rw [Metric.mem_closedBall] at hzClosed
  rw [Metric.mem_sphere]
  apply le_antisymm hzClosed
  exact le_of_not_gt (by
    intro hlt
    apply hzBall
    exact Metric.mem_ball.mpr hlt)

lemma OrdinaryCrossingLocalBranchSubstitution
    (Q bridge : PolygonalArc)
    (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (branch : OrdinaryCrossingLocalBranchData Q p radius) :
    Q.source ∉ Metric.closedBall p radius →
      Q.target ∉ Metric.closedBall p radius →
        bridge.source = branch.beforeGate →
          bridge.target = branch.afterGate →
            bridge.carrier ⊆ Metric.closedBall p radius →
              bridge.relativeInterior ⊆ Metric.ball p radius →
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
                              z ∈ openSegment ℝ bridge.vertices[m]
                                  bridge.vertices[m + 1] →
                                ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
                                  z ∈ openSegment ℝ Q'.vertices[j]
                                      Q'.vertices[j + 1] ∧
                                    ∃ c : ℝ, c ≠ 0 ∧
                                      Q'.vertices[j + 1] - Q'.vertices[j] =
                                        c • (bridge.vertices[m + 1] -
                                          bridge.vertices[m])) ∧
                              (∀ z i (hi : i + 1 < Q.vertices.length),
                                z ∈ openSegment ℝ Q.vertices[i]
                                    Q.vertices[i + 1] →
                                  z ∉ Metric.closedBall p radius →
                                    ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
                                      z ∈ openSegment ℝ Q'.vertices[j]
                                          Q'.vertices[j + 1] ∧
                                        ∃ c : ℝ, c ≠ 0 ∧
                                          Q'.vertices[j + 1] - Q'.vertices[j] =
                                            c • (Q.vertices[i + 1] -
                                              Q.vertices[i])) ∧
                              ∃ prefixArc suffixArc : PolygonalArc,
                                prefixArc.vertices =
                                    Q.vertices.take (branch.beforeIndex + 1) ++
                                      [branch.beforeGate] ∧
                                  suffixArc.vertices =
                                    branch.afterGate ::
                                      Q.vertices.drop (branch.afterIndex + 1) ∧
                                  Q'.vertices =
                                    PolygonalArcEndpointGluedVertices
                                      [prefixArc, bridge, suffixArc] ∧
                                  bridge.target = suffixArc.source ∧
                                  prefixArc.carrier ⊆ Q.carrier ∧
                                  suffixArc.carrier ⊆ Q.carrier ∧
                                  prefixArc.carrier ∪ suffixArc.carrier =
                                    Q.carrier \ Metric.ball p radius ∧
                                  Disjoint prefixArc.carrier suffixArc.carrier := by
  intro hsource htarget hbridgeSource hbridgeTarget hbridgeClosed hbridgeOpen
  have hbeforeLt : branch.beforeIndex < Q.vertices.length :=
    Nat.lt_of_succ_lt branch.beforeIndex_valid
  have hafterLt : branch.afterIndex < Q.vertices.length :=
    Nat.lt_of_succ_lt branch.afterIndex_valid
  have hbeforeOpenFull :
      branch.beforeGate ∈
        openSegment ℝ
          (Q.vertices[branch.beforeIndex]'hbeforeLt)
          (Q.vertices[branch.beforeIndex + 1]'branch.beforeIndex_valid) := by
    rcases branch.center_case with hcenter | hcenter
    · exact ocOpenLeftTrans hcenter.2 branch.beforeGate_open
    · simpa [hcenter.1, hcenter.2] using branch.beforeGate_open
  have hafterOpenFull :
      branch.afterGate ∈
        openSegment ℝ
          (Q.vertices[branch.afterIndex]'hafterLt)
          (Q.vertices[branch.afterIndex + 1]'branch.afterIndex_valid) := by
    rcases branch.center_case with hcenter | hcenter
    · apply ocOpenRightTrans (by simpa [hcenter.1] using hcenter.2)
      simpa [hcenter.1] using branch.afterGate_open
    · simpa [hcenter.1, hcenter.2, Nat.add_assoc] using branch.afterGate_open
  have hpCarrier : p ∈ Q.carrier := by
    rw [Q.carrier_eq]
    rcases branch.center_case with hcenter | hcenter
    · exact ⟨branch.beforeIndex, branch.beforeIndex_valid,
          openSegment_subset_segment ℝ _ _ hcenter.2⟩
    · refine ⟨branch.beforeIndex, branch.beforeIndex_valid, ?_⟩
      simpa [hcenter.1, hcenter.2] using
        (right_mem_segment ℝ
          (Q.vertices[branch.beforeIndex]'hbeforeLt)
          (Q.vertices[branch.beforeIndex + 1]'branch.beforeIndex_valid))
  have hpBall : p ∈ Metric.ball p radius := by
    simpa [Metric.mem_ball] using branch.radius_pos
  have hhitRel : (Q.relativeInterior ∩ Metric.ball p radius).Nonempty := by
    refine ⟨p, ?_, hpBall⟩
    rw [Q.relativeInterior_eq]
    refine ⟨hpCarrier, ?_⟩
    intro hpEnds
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpEnds
    rcases hpEnds with rfl | rfl
    · exact hsource (Metric.ball_subset_closedBall hpBall)
    · exact htarget (Metric.ball_subset_closedBall hpBall)
  obtain ⟨A⟩ := PolygonalArcFirstBallCutDataExists Q p radius hsource
    (fun hp => htarget (Metric.ball_subset_closedBall hp)) hhitRel
  have hAgateOptions :
      A.gate = branch.beforeGate ∨ A.gate = branch.afterGate := by
    have hgateCarrier : A.gate ∈ Q.carrier := by
      have hrel := A.gate_mem_relativeInterior
      rw [Q.relativeInterior_eq] at hrel
      exact hrel.1
    have hboth : A.gate ∈ Metric.sphere p radius ∩ Q.carrier :=
      ⟨A.gate_mem_sphere, hgateCarrier⟩
    rw [branch.sphere_carrier_eq] at hboth
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hboth
  have hAgate : A.gate = branch.beforeGate := by
    rcases hAgateOptions with hbefore | hafter
    · exact hbefore
    · exfalso
      have hcutIndex : A.cut.cutIndex = branch.afterIndex :=
        (ocOpenIndexUnique Q branch.afterGate branch.afterIndex A.cut.cutIndex
          branch.afterIndex_valid A.cut.cutIndex_valid hafterOpenFull
          (by simpa [hafter] using A.cut.cut_mem_segment)).symm
      have hpPrefix : p ∈ A.cut.prefixArc.carrier := by
        rw [A.cut.prefix_carrier_region]
        rcases branch.center_case with hcenter | hcenter
        · right
          have hpSeg : p ∈
              segment ℝ Q.vertices[branch.beforeIndex]
                branch.afterGate :=
            openSegment_subset_segment ℝ _ _
              (ocOpenBeforeLater hcenter.2
                (by simpa [hcenter.1] using branch.afterGate_open))
          simpa only [hcutIndex, hcenter.1, hafter] using hpSeg
        · left
          refine ⟨branch.beforeIndex, branch.beforeIndex_valid, ?_, ?_⟩
          · rw [hcutIndex, hcenter.1]
            omega
          · simpa [hcenter.1, hcenter.2] using
              (right_mem_segment ℝ Q.vertices[branch.beforeIndex]
                Q.vertices[branch.beforeIndex + 1])
      exact (Set.disjoint_left.mp A.prefix_avoids_ball hpPrefix) hpBall
  have hAcutIndex : A.cut.cutIndex = branch.beforeIndex :=
    (ocOpenIndexUnique Q branch.beforeGate branch.beforeIndex A.cut.cutIndex
      branch.beforeIndex_valid A.cut.cutIndex_valid hbeforeOpenFull
      (by simpa [hAgate] using A.cut.cut_mem_segment)).symm
  have hAdrop : A.cut.suffixDropIndex = branch.beforeIndex + 1 := by
    rcases A.cut.suffix_drop_index_spec with hdrop | hdrop
    · simpa [hAcutIndex] using hdrop.1
    · exfalso
      have heq : branch.beforeGate =
          Q.vertices[branch.beforeIndex + 1]'branch.beforeIndex_valid := by
        simpa only [hAgate, hAcutIndex] using hdrop.2
      have hright : (Q.vertices[branch.beforeIndex + 1]'branch.beforeIndex_valid) ∈
          openSegment ℝ (Q.vertices[branch.beforeIndex]'hbeforeLt)
            (Q.vertices[branch.beforeIndex + 1]'branch.beforeIndex_valid) := by
        simpa only [heq] using hbeforeOpenFull
      have hend_ne : (Q.vertices[branch.beforeIndex]'hbeforeLt) ≠
          (Q.vertices[branch.beforeIndex + 1]'branch.beforeIndex_valid) := by
        have hrel := Q.simple_vertices.rel_get_of_lt
          (a := ⟨branch.beforeIndex, hbeforeLt⟩)
          (b := ⟨branch.beforeIndex + 1, branch.beforeIndex_valid⟩) (by simp)
        simpa [List.get_eq_getElem] using hrel
      exact hend_ne (right_mem_openSegment_iff.mp hright)
  let T := A.cut.suffixArc
  have hTvertices :
      T.vertices = branch.beforeGate :: Q.vertices.drop (branch.beforeIndex + 1) := by
    dsimp [T]
    rw [A.cut.suffix_vertices_exact, hAdrop, hAgate]
  have hTlen : 2 ≤ T.vertices.length := T.length_ge_two
  have hTzero : T.vertices[0] = branch.beforeGate := by
    have hhead := T.source_eq_head
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
    calc
      T.vertices[0] = T.source := Option.some.inj hhead
      _ = A.gate := by simpa only [T] using A.cut.suffix_source
      _ = branch.beforeGate := hAgate
  have hTget : ∀ n (hn : n + 1 < T.vertices.length),
      T.vertices[n + 1] = Q.vertices[branch.beforeIndex + 1 + n]'(by
        rw [hTvertices] at hn
        simp at hn
        omega) := by
    intro n hn
    have hdropLen : n < (Q.vertices.drop (branch.beforeIndex + 1)).length := by
      rw [hTvertices] at hn
      simpa using hn
    have hopt := congrArg
      (fun xs : List (EuclideanSpace ℝ (Fin 2)) => xs[n + 1]?) hTvertices
    change T.vertices[n + 1]? =
      (branch.beforeGate :: Q.vertices.drop (branch.beforeIndex + 1))[n + 1]?
      at hopt
    rw [List.getElem?_eq_getElem hn,
      List.getElem?_eq_getElem (by simpa using hdropLen)] at hopt
    simpa using Option.some.inj hopt
  obtain ⟨k, hk, hafterT, hkCase⟩ :
      ∃ k : ℕ, ∃ hk : k + 1 < T.vertices.length,
        branch.afterGate ∈ openSegment ℝ T.vertices[k] T.vertices[k + 1] ∧
          ((branch.afterIndex = branch.beforeIndex ∧ k = 0) ∨
            (branch.afterIndex = branch.beforeIndex + 1 ∧ k = 1)) := by
    rcases branch.center_case with hcenter | hcenter
    · have hk0 : 0 + 1 < T.vertices.length := by omega
      have hTone : T.vertices[1] =
          Q.vertices[branch.beforeIndex + 1]'branch.beforeIndex_valid := by
        simpa using hTget 0 hk0
      have hpOpen : p ∈
          openSegment ℝ branch.beforeGate
            (Q.vertices[branch.beforeIndex + 1]'branch.beforeIndex_valid) :=
        ocOpenAfterEarlier branch.beforeGate_open hcenter.2
      refine ⟨0, hk0, ?_, Or.inl ⟨hcenter.1, rfl⟩⟩
      simpa [hTzero, hTone, hcenter.1] using
        ocOpenRightTrans hpOpen
          (by simpa [hcenter.1] using branch.afterGate_open)
    · have hbeforeTwo : branch.beforeIndex + 2 < Q.vertices.length := by
        have hvalid := branch.afterIndex_valid
        omega
      have hk1 : 1 + 1 < T.vertices.length := by
        rw [hTvertices]
        simp [List.length_drop]
        omega
      have hTone : T.vertices[1] =
          Q.vertices[branch.beforeIndex + 1]'branch.beforeIndex_valid := by
        simpa using hTget 0 (by omega : 0 + 1 < T.vertices.length)
      have hTtwo : T.vertices[2] =
          Q.vertices[branch.beforeIndex + 2]'hbeforeTwo := by
        simpa [Nat.add_assoc] using hTget 1 hk1
      refine ⟨1, hk1, ?_, Or.inr ⟨hcenter.1, rfl⟩⟩
      change branch.afterGate ∈ openSegment ℝ T.vertices[1] T.vertices[2]
      rw [hTone, hTtwo]
      simpa [hcenter.1, hcenter.2, Nat.add_assoc] using branch.afterGate_open
  obtain ⟨B⟩ := PolygonalArcInteriorPointCutDataExists T k hk
    branch.afterGate hafterT
  have hBcutIndex : B.cutIndex = k :=
    (ocOpenIndexUnique T branch.afterGate k B.cutIndex hk B.cutIndex_valid
      hafterT B.cut_mem_segment).symm
  have hBdrop : B.suffixDropIndex = k + 1 := by
    rcases B.suffix_drop_index_spec with hdrop | hdrop
    · omega
    · have hdropGate : branch.afterGate = T.vertices[k + 1] := by
        simpa only [hBcutIndex] using hdrop.2
      have hright : T.vertices[k + 1] ∈
          openSegment ℝ T.vertices[k] T.vertices[k + 1] := by
        simpa only [hdropGate] using hafterT
      have hend_ne : T.vertices[k] ≠ T.vertices[k + 1] := by
        have hrel := T.simple_vertices.rel_get_of_lt
          (a := ⟨k, Nat.lt_of_succ_lt hk⟩) (b := ⟨k + 1, hk⟩) (by simp)
        simpa [List.get_eq_getElem] using hrel
      exact False.elim (hend_ne (right_mem_openSegment_iff.mp hright))
  have hprefixVertices : A.cut.prefixArc.vertices =
      Q.vertices.take (branch.beforeIndex + 1) ++ [branch.beforeGate] := by
    rw [A.cut.prefix_vertices_exact, hAcutIndex, hAgate]
  have hsuffixVertices : B.suffixArc.vertices =
      branch.afterGate :: Q.vertices.drop (branch.afterIndex + 1) := by
    rw [B.suffix_vertices_exact, hBdrop]
    rcases hkCase with hsame | hvertex
    · rw [hsame.1, hsame.2]
      simp [hTvertices]
    · rw [hvertex.1, hvertex.2]
      simp [hTvertices, List.drop_drop]
  have hbeforeClosed : branch.beforeGate ∈ Metric.closedBall p radius :=
    Metric.sphere_subset_closedBall branch.beforeGate_on_sphere
  have hafterClosed : branch.afterGate ∈ Metric.closedBall p radius :=
    Metric.sphere_subset_closedBall branch.afterGate_on_sphere
  have hpClosed : p ∈ Metric.closedBall p radius :=
    Metric.ball_subset_closedBall hpBall
  have center_vertex_of_indices
      (hidx : branch.afterIndex = branch.beforeIndex + 1) :
      p = Q.vertices[branch.afterIndex] := by
    rcases branch.center_case with h | h
    · omega
    · exact h.2
  have hmiddleClosed : B.prefixArc.carrier ⊆ Metric.closedBall p radius := by
    intro z hz
    rw [B.prefix_carrier_region] at hz
    rcases hkCase with hsame | hvertex
    · rcases hz with hzEarly | hzLast
      · rcases hzEarly with ⟨m, _hm, hmk, _hzm⟩
        rw [hBcutIndex, hsame.2] at hmk
        omega
      · have hzSeg : z ∈ segment ℝ branch.beforeGate branch.afterGate := by
          simpa only [hBcutIndex, hsame.2, hTzero] using hzLast
        exact (convex_closedBall p radius).segment_subset
          hbeforeClosed hafterClosed hzSeg
    · have hTone : T.vertices[1] = p := by
        calc
          T.vertices[1] = Q.vertices[branch.beforeIndex + 1] :=
            hTget 0 (by omega)
          _ = Q.vertices[branch.afterIndex] := by simpa only [hvertex.1]
          _ = p := (center_vertex_of_indices hvertex.1).symm
      rcases hz with hzEarly | hzLast
      · rcases hzEarly with ⟨m, hm, hmk, hzm⟩
        rw [hBcutIndex, hvertex.2] at hmk
        have hm0 : m = 0 := by omega
        subst m
        have hzSeg : z ∈ segment ℝ branch.beforeGate p := by
          have hzm' : z ∈ segment ℝ T.vertices[0] T.vertices[1] := by
            simpa using hzm
          have hzm'' : z ∈ segment ℝ branch.beforeGate T.vertices[1] := by
            simpa only [hTzero] using hzm'
          convert hzm'' using 1
          exact congrArg (fun x => segment ℝ branch.beforeGate x) hTone.symm
        exact (convex_closedBall p radius).segment_subset
          hbeforeClosed hpClosed hzSeg
      · have hzSeg : z ∈ segment ℝ p branch.afterGate := by
          have hzLast' : z ∈ segment ℝ T.vertices[1] branch.afterGate := by
            simpa only [hBcutIndex, hvertex.2] using hzLast
          simpa only [hTone] using hzLast'
        exact (convex_closedBall p radius).segment_subset
          hpClosed hafterClosed hzSeg
  have hTlength : T.vertices.length = Q.vertices.length - branch.beforeIndex := by
    rw [hTvertices]
    simp [List.length_drop]
    omega
  have hTpos : ∀ m (hmpos : 0 < m) (hm : m + 1 < T.vertices.length),
      T.vertices[m] = Q.vertices[branch.beforeIndex + m]'(by
        rw [hTlength] at hm
        omega) := by
    intro m hmpos hm
    have hprev := hTget (m - 1) (by omega)
    have hleft : m - 1 + 1 = m := by omega
    have hright : branch.beforeIndex + 1 + (m - 1) =
        branch.beforeIndex + m := by omega
    simpa only [hleft, hright] using hprev
  have hsuffixAvoids :
      Disjoint B.suffixArc.carrier (Metric.ball p radius) := by
    rw [Set.disjoint_left]
    intro z hzSuffix hzBall
    rw [B.suffix_carrier_region] at hzSuffix
    rcases hkCase with hsame | hvertex
    · have hTone : T.vertices[1] = Q.vertices[branch.beforeIndex + 1] :=
        hTget 0 (by omega)
      have hafterOut : Disjoint
          (segment ℝ branch.afterGate T.vertices[1])
          (Metric.ball p radius) := by
        apply ocOutwardSegment
        · simpa only [hTone, hsame.1] using branch.afterGate_open
        · exact branch.afterGate_on_sphere
      rcases hzSuffix with hzFirst | hzLater
      · exact (Set.disjoint_left.mp hafterOut
          (by simpa only [hBcutIndex, hsame.2] using hzFirst)) hzBall
      · rcases hzLater with ⟨m, hm, hkm, hzm⟩
        rw [hBcutIndex, hsame.2] at hkm
        have hmpos : 0 < m := by omega
        have hjvalid : branch.beforeIndex + m + 1 < Q.vertices.length := by
          rw [hTlength] at hm
          omega
        have hleft := hTpos m hmpos hm
        have hright := hTget m hm
        have hzQseg : z ∈
            segment ℝ Q.vertices[branch.beforeIndex + m]
              Q.vertices[branch.beforeIndex + m + 1] := by
          simpa [hleft, hright, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            using hzm
        have hzQ : z ∈ Q.carrier := by
          rw [Q.carrier_eq]
          exact ⟨branch.beforeIndex + m, by simpa [Nat.add_assoc] using hjvalid,
            hzQseg⟩
        have hzLocal : z ∈
            segment ℝ Q.vertices[branch.beforeIndex]
                Q.vertices[branch.beforeIndex + 1] := by
          have hzClosed : z ∈ Metric.closedBall p radius :=
            Metric.ball_subset_closedBall hzBall
          have hzBoth : z ∈ Metric.closedBall p radius ∩ Q.carrier :=
            ⟨hzClosed, hzQ⟩
          rw [branch.closedBall_carrier_eq] at hzBoth
          rcases hzBoth.2 with hz | hz
          · exact hz
          · simpa only [hsame.1] using hz
        have hinter := Q.segment_intersections branch.beforeIndex_valid
          (by simpa [Nat.add_assoc] using hjvalid)
          (by omega : branch.beforeIndex < branch.beforeIndex + m)
        have hzBoth : z ∈
            segment ℝ Q.vertices[branch.beforeIndex]
                Q.vertices[branch.beforeIndex + 1] ∩
              segment ℝ Q.vertices[branch.beforeIndex + m]
                Q.vertices[branch.beforeIndex + m + 1] :=
          ⟨hzLocal, hzQseg⟩
        rw [hinter] at hzBoth
        split at hzBoth
        · have hm1 : m = 1 := by omega
          subst m
          have hzEq : z = T.vertices[1] := by simpa [hTone] using hzBoth
          have hTball : T.vertices[1] ∈ Metric.ball p radius := by
            simpa only [← hzEq] using hzBall
          exact (Set.disjoint_left.mp hafterOut
            (right_mem_segment ℝ branch.afterGate T.vertices[1])) hTball
        · exact hzBoth
    · have hbeforeTwo : branch.beforeIndex + 2 < Q.vertices.length := by
        have hvalid := branch.afterIndex_valid
        omega
      have hTone : T.vertices[1] = p := by
        calc
          T.vertices[1] = Q.vertices[branch.beforeIndex + 1] := hTget 0 (by omega)
          _ = Q.vertices[branch.afterIndex] := by simpa only [hvertex.1]
          _ = p := (center_vertex_of_indices hvertex.1).symm
      have hTtwo : T.vertices[2] = Q.vertices[branch.beforeIndex + 2] := by
        simpa [Nat.add_assoc] using hTget 1 (by
          rw [hTlength]
          omega)
      have hafterOut : Disjoint
          (segment ℝ branch.afterGate T.vertices[2])
          (Metric.ball p radius) := by
        apply ocOutwardSegment
        · simpa [hTtwo, hvertex.1, Nat.add_assoc] using branch.afterGate_open
        · exact branch.afterGate_on_sphere
      rcases hzSuffix with hzFirst | hzLater
      · exact (Set.disjoint_left.mp hafterOut
          (by simpa only [hBcutIndex, hvertex.2] using hzFirst)) hzBall
      · rcases hzLater with ⟨m, hm, hkm, hzm⟩
        rw [hBcutIndex, hvertex.2] at hkm
        have hmpos : 0 < m := by omega
        have hjvalid : branch.beforeIndex + m + 1 < Q.vertices.length := by
          rw [hTlength] at hm
          omega
        have hleft := hTpos m hmpos hm
        have hright := hTget m hm
        have hzQseg : z ∈
            segment ℝ Q.vertices[branch.beforeIndex + m]
              Q.vertices[branch.beforeIndex + m + 1] := by
          simpa [hleft, hright, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            using hzm
        have hzQ : z ∈ Q.carrier := by
          rw [Q.carrier_eq]
          exact ⟨branch.beforeIndex + m, by simpa [Nat.add_assoc] using hjvalid,
            hzQseg⟩
        have hzClosed : z ∈ Metric.closedBall p radius :=
          Metric.ball_subset_closedBall hzBall
        have hzBoth : z ∈ Metric.closedBall p radius ∩ Q.carrier :=
          ⟨hzClosed, hzQ⟩
        rw [branch.closedBall_carrier_eq] at hzBoth
        rcases hzBoth.2 with hzBefore | hzAfter
        · have hinter := Q.segment_intersections branch.beforeIndex_valid
            (by simpa [Nat.add_assoc] using hjvalid)
            (by omega : branch.beforeIndex < branch.beforeIndex + m)
          have hzInter : z ∈
              segment ℝ Q.vertices[branch.beforeIndex]
                  Q.vertices[branch.beforeIndex + 1] ∩
                segment ℝ Q.vertices[branch.beforeIndex + m]
                  Q.vertices[branch.beforeIndex + m + 1] :=
            ⟨hzBefore, hzQseg⟩
          rw [hinter] at hzInter
          split at hzInter
          · omega
          · exact hzInter
        · have hafterIndexValid : branch.beforeIndex + 1 + 1 <
              Q.vertices.length := by simpa [hvertex.1] using branch.afterIndex_valid
          have hinter := Q.segment_intersections hafterIndexValid
            (by simpa [Nat.add_assoc] using hjvalid)
            (by omega : branch.beforeIndex + 1 < branch.beforeIndex + m)
          have hzInter : z ∈
              segment ℝ Q.vertices[branch.beforeIndex + 1]
                  Q.vertices[branch.beforeIndex + 1 + 1] ∩
                segment ℝ Q.vertices[branch.beforeIndex + m]
                  Q.vertices[branch.beforeIndex + m + 1] :=
            ⟨by simpa [hvertex.1] using hzAfter, hzQseg⟩
          rw [hinter] at hzInter
          split at hzInter
          · have hm2 : m = 2 := by omega
            subst m
            have hzEq : z = T.vertices[2] := by simpa [hTtwo] using hzInter
            have hTball : T.vertices[2] ∈ Metric.ball p radius := by
              simpa only [← hzEq] using hzBall
            exact (Set.disjoint_left.mp hafterOut
              (right_mem_segment ℝ branch.afterGate T.vertices[2])) hTball
          · exact hzInter
  have hbeforeQri : branch.beforeGate ∈ Q.relativeInterior :=
    ocGateMemRelativeInterior Q p branch.beforeGate radius branch.beforeIndex
      branch.beforeIndex_valid hbeforeOpenFull hbeforeClosed hsource htarget
  have hafterQri : branch.afterGate ∈ Q.relativeInterior :=
    ocGateMemRelativeInterior Q p branch.afterGate radius branch.afterIndex
      branch.afterIndex_valid hafterOpenFull hafterClosed hsource htarget
  have hafterClosure : branch.afterGate ∈
      closure (Q.carrier ∩ Metric.ball p radius) :=
    ocAfterGateMemClosure Q p radius branch
  have hprefixMiddle :
      A.cut.prefixArc.carrier ∩ B.prefixArc.carrier =
        ({branch.beforeGate} : Set (EuclideanSpace ℝ (Fin 2))) := by
    apply Set.Subset.antisymm
    · intro z hz
      have hzT : z ∈ T.carrier := B.prefix_carrier_subset hz.2
      have hzInter : z ∈ A.cut.prefixArc.carrier ∩ A.cut.suffixArc.carrier :=
        ⟨hz.1, by simpa only [T] using hzT⟩
      rw [A.cut.carrier_intersection] at hzInter
      simpa only [hAgate] using hzInter
    · intro z hz
      have hzEq : z = branch.beforeGate := by simpa using hz
      subst z
      refine ⟨?_, ?_⟩
      · have hmem : A.gate ∈ A.cut.prefixArc.carrier := by
          simpa only [A.cut.prefix_target] using
            ocArcTargetMemCarrier A.cut.prefixArc
        simpa only [hAgate] using hmem
      · have hsrc : B.prefixArc.source = branch.beforeGate := by
          calc
            B.prefixArc.source = T.source := B.prefix_source
            _ = A.gate := by simpa only [T] using A.cut.suffix_source
            _ = branch.beforeGate := hAgate
        rw [← hsrc]
        exact ocArcSourceMemCarrier B.prefixArc
  have hmiddleSuffix :
      B.prefixArc.carrier ∩ B.suffixArc.carrier =
        ({branch.afterGate} : Set (EuclideanSpace ℝ (Fin 2))) :=
    B.carrier_intersection
  have hprefixSuffix :
      Disjoint A.cut.prefixArc.carrier B.suffixArc.carrier := by
    rw [Set.disjoint_left]
    intro z hzPrefix hzSuffix
    have hzT : z ∈ T.carrier := B.suffix_carrier_subset hzSuffix
    have hzA : z ∈ ({A.gate} : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [← A.cut.carrier_intersection]
      exact ⟨hzPrefix, by simpa only [T] using hzT⟩
    have hzBefore : z = branch.beforeGate := by
      simpa only [Set.mem_singleton_iff, hAgate] using hzA
    have hzBprefix : z ∈ B.prefixArc.carrier := by
      rw [hzBefore]
      have hsrc : B.prefixArc.source = branch.beforeGate := by
        calc
          B.prefixArc.source = T.source := B.prefix_source
          _ = A.gate := by simpa only [T] using A.cut.suffix_source
          _ = branch.beforeGate := hAgate
      rw [← hsrc]
      exact ocArcSourceMemCarrier B.prefixArc
    have hzAfter : z = branch.afterGate := by
      have hzInter : z ∈ ({branch.afterGate} : Set _) := by
        rw [← hmiddleSuffix]
        exact ⟨hzBprefix, hzSuffix⟩
      simpa using hzInter
    exact branch.gates_ne (hzBefore.symm.trans hzAfter)
  have hballMiddle :
      Q.carrier ∩ Metric.ball p radius ⊆ B.prefixArc.relativeInterior := by
    intro z hz
    have hzTrel : z ∈ A.cut.suffixArc.relativeInterior :=
      A.ball_part_in_suffix hz
    have hzT : z ∈ T.carrier := by
      have hzT' : z ∈ A.cut.suffixArc.carrier := by
        rw [A.cut.suffixArc.relativeInterior_eq] at hzTrel
        exact hzTrel.1
      simpa only [T] using hzT'
    have hzPieces : z ∈ B.prefixArc.carrier ∨ z ∈ B.suffixArc.carrier := by
      have hzUnion : z ∈ B.prefixArc.carrier ∪ B.suffixArc.carrier := by
        rw [← B.carrier_decomposition]
        exact hzT
      exact hzUnion
    have hzPrefix : z ∈ B.prefixArc.carrier := by
      rcases hzPieces with hzPrefix | hzSuffix
      · exact hzPrefix
      · exact False.elim ((Set.disjoint_left.mp hsuffixAvoids hzSuffix) hz.2)
    rw [B.prefixArc.relativeInterior_eq]
    refine ⟨hzPrefix, ?_⟩
    intro hends
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
    rcases hends with hsourceEq | htargetEq
    · have hsrc : B.prefixArc.source = branch.beforeGate := by
        calc
          B.prefixArc.source = T.source := B.prefix_source
          _ = A.gate := by simpa only [T] using A.cut.suffix_source
          _ = branch.beforeGate := hAgate
      have : branch.beforeGate ∈ Metric.ball p radius := by
        simpa only [hsourceEq, hsrc] using hz.2
      exact (Metric.mem_sphere.mp branch.beforeGate_on_sphere).not_lt
        (Metric.mem_ball.mp this)
    · have : branch.afterGate ∈ Metric.ball p radius := by
        simpa only [htargetEq, B.prefix_target] using hz.2
      exact (Metric.mem_sphere.mp branch.afterGate_on_sphere).not_lt
        (Metric.mem_ball.mp this)
  let D : PolygonalArcOrderedBallCutData Q p radius := {
    qminus := branch.beforeGate
    qplus := branch.afterGate
    prefixArc := A.cut.prefixArc
    middleArc := B.prefixArc
    suffixArc := B.suffixArc
    qminus_ne_qplus := branch.gates_ne
    qminus_mem_relativeInterior := hbeforeQri
    qplus_mem_relativeInterior := hafterQri
    qminus_mem_sphere := branch.beforeGate_on_sphere
    qplus_mem_sphere := branch.afterGate_on_sphere
    qminus_mem_closure_ball_part := by simpa only [hAgate] using
      A.gate_mem_closure_ball_part
    qplus_mem_closure_ball_part := hafterClosure
    source_not_mem_closedBall := hsource
    target_not_mem_closedBall := htarget
    prefix_source := A.cut.prefix_source
    prefix_target := by simpa only [hAgate] using A.cut.prefix_target
    middle_source := by
      calc
        B.prefixArc.source = T.source := B.prefix_source
        _ = A.gate := by simpa only [T] using A.cut.suffix_source
        _ = branch.beforeGate := hAgate
    middle_target := B.prefix_target
    suffix_source := B.suffix_source
    suffix_target := by
      calc
        B.suffixArc.target = T.target := B.suffix_target
        _ = Q.target := by simpa only [T] using A.cut.suffix_target
    prefix_carrier_subset := A.cut.prefix_carrier_subset
    middle_carrier_subset := fun z hz => A.cut.suffix_carrier_subset
      (by simpa only [T] using B.prefix_carrier_subset hz)
    suffix_carrier_subset := fun z hz => A.cut.suffix_carrier_subset
      (by simpa only [T] using B.suffix_carrier_subset hz)
    carrier_decomposition := by
      rw [A.cut.carrier_decomposition]
      have hB := B.carrier_decomposition
      change A.cut.suffixArc.carrier = _ at hB
      rw [hB]
      simp only [Set.union_assoc]
    prefix_middle_intersection := hprefixMiddle
    middle_suffix_intersection := hmiddleSuffix
    prefix_suffix_disjoint := hprefixSuffix
    prefix_avoids_ball := A.prefix_avoids_ball
    suffix_avoids_ball := hsuffixAvoids
    ball_part_in_middle := hballMiddle
    middle_meets_ball := ⟨p, hballMiddle ⟨hpCarrier, hpBall⟩, hpBall⟩
    prefix_segment_transfer := by
      intro z i hi hzOpen hzPrefix hzOutside
      apply A.cut.prefix_segment_transfer z i hi hzOpen hzPrefix
      intro hzGate
      apply hzOutside
      rw [hzGate, hAgate]
      exact hbeforeClosed
    suffix_segment_transfer := by
      intro z i hi hzOpen hzSuffix hzOutside
      have hzT : z ∈ T.carrier := B.suffix_carrier_subset hzSuffix
      rcases A.cut.suffix_segment_transfer z i hi hzOpen
          (by simpa only [T] using hzT) (by
            intro hzGate
            apply hzOutside
            rw [hzGate, hAgate]
            exact hbeforeClosed) with
        ⟨m, hm, hzTOpen, c₁, hc₁, hdir₁⟩
      rcases B.suffix_segment_transfer z m hm hzTOpen hzSuffix (by
          intro hzGate
          apply hzOutside
          rw [hzGate]
          exact hafterClosed) with
        ⟨j, hj, hzFinal, c₂, hc₂, hdir₂⟩
      refine ⟨j, hj, hzFinal, c₂ * c₁, mul_ne_zero hc₂ hc₁, ?_⟩
      rw [hdir₂, hdir₁, smul_smul]
    protected_first_vertices := by
      intro hi hfirst
      apply A.cut.protected_first_vertices hi
      intro hgate
      apply (Set.disjoint_left.mp hfirst hgate)
      simpa only [hAgate] using hbeforeClosed
  }
  have hprefixBridge0 :
      A.cut.prefixArc.carrier ∩ bridge.carrier =
        ({branch.beforeGate} : Set (EuclideanSpace ℝ (Fin 2))) := by
    apply Set.Subset.antisymm
    · intro z hz
      by_cases hends : z ∈ ({bridge.source, bridge.target} : Set _)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
        rcases hends with hsrc | htgt
        · simpa only [Set.mem_singleton_iff, hsrc, hbridgeSource]
        · have hzAfter : z = branch.afterGate := htgt.trans hbridgeTarget
          have hzSuffix : z ∈ B.suffixArc.carrier := by
            have hmem := ocArcSourceMemCarrier B.suffixArc
            simpa only [B.suffix_source, hzAfter] using hmem
          exact False.elim ((Set.disjoint_left.mp hprefixSuffix hz.1) hzSuffix)
      · have hzri : z ∈ bridge.relativeInterior := by
          rw [bridge.relativeInterior_eq]
          exact ⟨hz.2, hends⟩
        exact False.elim
          ((Set.disjoint_left.mp A.prefix_avoids_ball hz.1) (hbridgeOpen hzri))
    · intro z hz
      have hzEq : z = branch.beforeGate := by simpa using hz
      subst z
      refine ⟨?_, ?_⟩
      · have hmem : A.gate ∈ A.cut.prefixArc.carrier := by
          simpa only [A.cut.prefix_target] using
            ocArcTargetMemCarrier A.cut.prefixArc
        simpa only [hAgate] using hmem
      · simpa only [hbridgeSource] using ocArcSourceMemCarrier bridge
  have hbridgeSuffix0 :
      bridge.carrier ∩ B.suffixArc.carrier =
        ({branch.afterGate} : Set (EuclideanSpace ℝ (Fin 2))) := by
    apply Set.Subset.antisymm
    · intro z hz
      by_cases hends : z ∈ ({bridge.source, bridge.target} : Set _)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
        rcases hends with hsrc | htgt
        · have hzBefore : z = branch.beforeGate := hsrc.trans hbridgeSource
          have hzPrefix : z ∈ A.cut.prefixArc.carrier := by
            have hmem : A.gate ∈ A.cut.prefixArc.carrier := by
              simpa only [A.cut.prefix_target] using
                ocArcTargetMemCarrier A.cut.prefixArc
            simpa only [hzBefore, hAgate] using hmem
          exact False.elim ((Set.disjoint_left.mp hprefixSuffix hzPrefix) hz.2)
        · simpa only [Set.mem_singleton_iff, htgt, hbridgeTarget]
      · have hzri : z ∈ bridge.relativeInterior := by
          rw [bridge.relativeInterior_eq]
          exact ⟨hz.1, hends⟩
        exact False.elim
          ((Set.disjoint_left.mp hsuffixAvoids hz.2) (hbridgeOpen hzri))
    · intro z hz
      have hzEq : z = branch.afterGate := by simpa using hz
      subst z
      refine ⟨?_, ?_⟩
      · simpa only [hbridgeTarget] using ocArcTargetMemCarrier bridge
      · simpa only [B.suffix_source] using ocArcSourceMemCarrier B.suffixArc
  have holdOutsidePieces :
      Q.carrier \ Metric.ball p radius =
        A.cut.prefixArc.carrier ∪ B.suffixArc.carrier := by
    apply Set.Subset.antisymm
    · intro z hz
      have hzPieces : z ∈ A.cut.prefixArc.carrier ∪
          B.prefixArc.carrier ∪ B.suffixArc.carrier := by
        have hz' : z ∈ D.prefixArc.carrier ∪ D.middleArc.carrier ∪
            D.suffixArc.carrier := by
          rw [← D.carrier_decomposition]
          exact hz.1
        simpa only [D] using hz'
      rcases hzPieces with (hzPrefix | hzMiddle) | hzSuffix
      · exact Or.inl hzPrefix
      · have hzSphere := ocSphereOfClosedNotBall
          (hmiddleClosed hzMiddle) hz.2
        have hzQ : z ∈ Q.carrier := D.middle_carrier_subset
          (by simpa only [D] using hzMiddle)
        have hzGates : z = branch.beforeGate ∨ z = branch.afterGate := by
          have hzBoth : z ∈ Metric.sphere p radius ∩ Q.carrier :=
            ⟨hzSphere, hzQ⟩
          rw [branch.sphere_carrier_eq] at hzBoth
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzBoth
        rcases hzGates with hzBefore | hzAfter
        · left
          have hmem : A.gate ∈ A.cut.prefixArc.carrier := by
            simpa only [A.cut.prefix_target] using
              ocArcTargetMemCarrier A.cut.prefixArc
          simpa only [hzBefore, hAgate] using hmem
        · right
          have hmem := ocArcSourceMemCarrier B.suffixArc
          simpa only [B.suffix_source, hzAfter] using hmem
      · exact Or.inr hzSuffix
    · intro z hz
      rcases hz with hzPrefix | hzSuffix
      · refine ⟨A.cut.prefix_carrier_subset hzPrefix, ?_⟩
        exact fun hzBall =>
          (Set.disjoint_left.mp A.prefix_avoids_ball hzPrefix) hzBall
      · refine ⟨D.suffix_carrier_subset (by simpa only [D] using hzSuffix), ?_⟩
        exact fun hzBall =>
          (Set.disjoint_left.mp hsuffixAvoids hzSuffix) hzBall
  have hbridgeOutsideOld :
      bridge.carrier \ Metric.ball p radius ⊆
        Q.carrier \ Metric.ball p radius := by
    intro z hz
    refine ⟨?_, hz.2⟩
    have hnotri : z ∉ bridge.relativeInterior := by
      intro hzri
      exact hz.2 (hbridgeOpen hzri)
    have hends : z ∈ ({bridge.source, bridge.target} : Set _) := by
      by_contra hnotends
      apply hnotri
      rw [bridge.relativeInterior_eq]
      exact ⟨hz.1, hnotends⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
    rcases hends with hsrc | htgt
    · have hzEq : z = branch.beforeGate := hsrc.trans hbridgeSource
      rw [hzEq]
      have hri := hbeforeQri
      rw [Q.relativeInterior_eq] at hri
      exact hri.1
    · have hzEq : z = branch.afterGate := htgt.trans hbridgeTarget
      rw [hzEq]
      have hri := hafterQri
      rw [Q.relativeInterior_eq] at hri
      exact hri.1
  rcases PolygonalArcOrderedThreePieceSplice Q bridge p radius D
      hbridgeSource hbridgeTarget hbridgeOpen
      (by simpa only [D] using hprefixBridge0)
      (by simpa only [D] using hbridgeSuffix0) with
    ⟨Q', hQvertices, hQsource, hQtarget, hQcarrier,
      _hQinterior, _hprefixInterior, hbridgeInterior,
      _hsuffixInterior, hbridgeTransfer, holdTransfer⟩
  have hcarrierExact : Q'.carrier =
      (Q.carrier \ Metric.ball p radius) ∪ bridge.carrier := by
    have hcarrierPieces : Q'.carrier =
        A.cut.prefixArc.carrier ∪ bridge.carrier ∪ B.suffixArc.carrier := by
      simpa only [D] using hQcarrier
    rw [hcarrierPieces, holdOutsidePieces]
    simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm]
  have houtsideExact :
      Q'.carrier \ Metric.ball p radius =
        Q.carrier \ Metric.ball p radius := by
    apply Set.Subset.antisymm
    · intro z hz
      rw [hcarrierExact] at hz
      rcases hz.1 with hzOld | hzBridge
      · exact hzOld
      · exact hbridgeOutsideOld ⟨hzBridge, hz.2⟩
    · intro z hz
      refine ⟨?_, hz.2⟩
      rw [hcarrierExact]
      exact Or.inl hz
  have hinsideExact :
      Q'.carrier ∩ Metric.ball p radius =
        bridge.carrier ∩ Metric.ball p radius := by
    apply Set.Subset.antisymm
    · intro z hz
      rw [hcarrierExact] at hz
      rcases hz.1 with hzOld | hzBridge
      · exact False.elim (hzOld.2 hz.2)
      · exact ⟨hzBridge, hz.2⟩
    · intro z hz
      refine ⟨?_, hz.2⟩
      rw [hcarrierExact]
      exact Or.inr hz.1
  refine ⟨Q', hQsource, hQtarget, hcarrierExact, houtsideExact,
    hinsideExact, hbridgeInterior, hbridgeTransfer, ?_, ?_⟩
  · intro z i hi hzOpen hzOutside
    apply holdTransfer z i hi hzOpen
    · rw [hcarrierExact]
      apply Or.inl
      refine ⟨?_, ?_⟩
      · rw [Q.carrier_eq]
        exact ⟨i, hi, openSegment_subset_segment ℝ _ _ hzOpen⟩
      · intro hzBall
        exact hzOutside (Metric.ball_subset_closedBall hzBall)
    · exact hzOutside
  · refine ⟨A.cut.prefixArc, B.suffixArc, hprefixVertices,
      hsuffixVertices, ?_, ?_, A.cut.prefix_carrier_subset, ?_, ?_, hprefixSuffix⟩
    · simpa only [D] using hQvertices
    · exact hbridgeTarget.trans B.suffix_source.symm
    · exact fun z hz => A.cut.suffix_carrier_subset
        (by simpa only [T] using B.suffix_carrier_subset hz)
    · exact holdOutsidePieces.symm
