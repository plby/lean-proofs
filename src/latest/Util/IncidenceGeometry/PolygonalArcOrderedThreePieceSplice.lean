import Util.IncidenceGeometry.PolygonalArcFromEndpointGluedPieces
import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentCertificates
import Util.IncidenceGeometry.PolygonalArcOrderedBallCutData

open Classical
noncomputable section

lemma PolygonalArcOrderedThreePieceSplice
    (Q bridge : PolygonalArc)
    (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (D : PolygonalArcOrderedBallCutData Q p radius) :
    bridge.source = D.qminus →
      bridge.target = D.qplus →
      bridge.relativeInterior ⊆ Metric.ball p radius →
      D.prefixArc.carrier ∩ bridge.carrier = {D.qminus} →
      bridge.carrier ∩ D.suffixArc.carrier = {D.qplus} →
      ∃ Q' : PolygonalArc,
        Q'.vertices =
            PolygonalArcEndpointGluedVertices
              [D.prefixArc, bridge, D.suffixArc] ∧
          Q'.source = Q.source ∧
          Q'.target = Q.target ∧
          Q'.carrier =
            D.prefixArc.carrier ∪ bridge.carrier ∪ D.suffixArc.carrier ∧
          Q'.relativeInterior =
            (D.prefixArc.carrier ∪ bridge.carrier ∪ D.suffixArc.carrier) \
              ({Q.source, Q.target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
          D.prefixArc.relativeInterior ⊆ Q'.relativeInterior ∧
          bridge.relativeInterior ⊆ Q'.relativeInterior ∧
          D.suffixArc.relativeInterior ⊆ Q'.relativeInterior ∧
          (∀ z m (hm : m + 1 < bridge.vertices.length),
            z ∈ openSegment ℝ bridge.vertices[m] bridge.vertices[m + 1] →
            ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
              z ∈ openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
                ∃ c : ℝ, c ≠ 0 ∧
                  Q'.vertices[j + 1] - Q'.vertices[j] =
                    c • (bridge.vertices[m + 1] - bridge.vertices[m])) ∧
          ∀ z i (hi : i + 1 < Q.vertices.length),
            z ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1] →
            z ∈ Q'.carrier →
            z ∉ Metric.closedBall p radius →
            ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
              z ∈ openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
                ∃ c : ℝ, c ≠ 0 ∧
                  Q'.vertices[j + 1] - Q'.vertices[j] =
                    c • (Q.vertices[i + 1] - Q.vertices[i]) := by
  intro hbridge_source hbridge_target hbridge_ball
    hprefix_bridge hbridge_suffix
  let pieces : List PolygonalArc := [D.prefixArc, bridge, D.suffixArc]
  have hsuccessive :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).target = (pieces[n + 1]).source := by
    intro n hn
    have hn_cases : n = 0 ∨ n = 1 := by
      simp [pieces] at hn
      omega
    rcases hn_cases with rfl | rfl
    · simpa [pieces, D.prefix_target] using hbridge_source.symm
    · simpa [pieces, D.suffix_source] using hbridge_target
  have hsegmentCerts :=
    PolygonalArcEndpointGluedSegmentCertificates pieces hsuccessive
      (by
        intro n hn
        have hn_cases : n = 0 ∨ n = 1 := by
          simp [pieces] at hn
          omega
        rcases hn_cases with rfl | rfl
        · intro z hz
          change z ∈ D.prefixArc.carrier ∩ bridge.carrier at hz
          change z ∈ ({D.prefixArc.target} :
            Set (EuclideanSpace ℝ (Fin 2)))
          rw [hprefix_bridge] at hz
          simpa [D.prefix_target] using hz
        · intro z hz
          change z ∈ bridge.carrier ∩ D.suffixArc.carrier at hz
          change z ∈ ({bridge.target} :
            Set (EuclideanSpace ℝ (Fin 2)))
          rw [hbridge_suffix] at hz
          simpa [hbridge_target] using hz)
      (by
        intro k l hk hl hkl
        simp [pieces] at hk hl
        have hcases : (k = 0 ∧ l = 2) ∨ (k = 2 ∧ l = 0) := by
          omega
        rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa [pieces] using D.prefix_suffix_disjoint
        · simpa [pieces] using D.prefix_suffix_disjoint.symm)
  have hsource_mem_prefix : Q.source ∈ D.prefixArc.carrier := by
    rw [D.prefixArc.carrier_eq]
    have hlen := D.prefixArc.length_ge_two
    refine ⟨0, by omega, ?_⟩
    have hzero : D.prefixArc.vertices[0] = D.prefixArc.source := by
      have hhead := D.prefixArc.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    rw [hzero, D.prefix_source]
    exact left_mem_segment ℝ Q.source D.prefixArc.vertices[1]
  have htarget_mem_suffix : Q.target ∈ D.suffixArc.carrier := by
    rw [D.suffixArc.carrier_eq]
    let m := D.suffixArc.vertices.length - 2
    have hm : m + 1 < D.suffixArc.vertices.length := by
      have hlen := D.suffixArc.length_ge_two
      dsimp [m]
      omega
    refine ⟨m, hm, ?_⟩
    have hlast : D.suffixArc.vertices[m + 1] = D.suffixArc.target := by
      have hlast_get := D.suffixArc.target_eq_last
      rw [List.getLast?_eq_getElem?] at hlast_get
      have hidx : D.suffixArc.vertices.length - 1 < D.suffixArc.vertices.length := by
        have hlen := D.suffixArc.length_ge_two
        omega
      rw [List.getElem?_eq_getElem hidx] at hlast_get
      have hm_eq : m + 1 = D.suffixArc.vertices.length - 1 := by
        dsimp [m]
        omega
      simpa [hm_eq] using Option.some.inj hlast_get
    rw [hlast, D.suffix_target]
    exact right_mem_segment ℝ D.suffixArc.vertices[m] Q.target
  have hpiece_avoids :
      ∀ Γ, Γ ∈ pieces →
        Disjoint Γ.relativeInterior
          ({Q.source, Q.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro Γ hΓ
    simp [pieces] at hΓ
    rcases hΓ with rfl | rfl | rfl
    · rw [Set.disjoint_left]
      intro z hz hzendpoint
      have hz_not_own :
          z ∉ ({D.prefixArc.source, D.prefixArc.target} :
            Set (EuclideanSpace ℝ (Fin 2))) := by
        have hz' := hz
        rw [D.prefixArc.relativeInterior_eq] at hz'
        exact hz'.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzendpoint
      rcases hzendpoint with rfl | rfl
      · exact hz_not_own (by simp [D.prefix_source])
      · have hzcarrier : Q.target ∈ D.prefixArc.carrier := by
          have hz' := hz
          rw [D.prefixArc.relativeInterior_eq] at hz'
          exact hz'.1
        exact (Set.disjoint_left.mp D.prefix_suffix_disjoint hzcarrier)
          htarget_mem_suffix
    · rw [Set.disjoint_left]
      intro z hz hzendpoint
      have hzball : z ∈ Metric.closedBall p radius :=
        Metric.ball_subset_closedBall (hbridge_ball hz)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzendpoint
      rcases hzendpoint with rfl | rfl
      · exact D.source_not_mem_closedBall hzball
      · exact D.target_not_mem_closedBall hzball
    · rw [Set.disjoint_left]
      intro z hz hzendpoint
      have hz_not_own :
          z ∉ ({D.suffixArc.source, D.suffixArc.target} :
            Set (EuclideanSpace ℝ (Fin 2))) := by
        have hz' := hz
        rw [D.suffixArc.relativeInterior_eq] at hz'
        exact hz'.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzendpoint
      rcases hzendpoint with rfl | rfl
      · have hzcarrier : Q.source ∈ D.suffixArc.carrier := by
          have hz' := hz
          rw [D.suffixArc.relativeInterior_eq] at hz'
          exact hz'.1
        exact (Set.disjoint_left.mp D.prefix_suffix_disjoint
          hsource_mem_prefix) hzcarrier
      · exact hz_not_own (by simp [D.suffix_target])
  have htransfer :=
    PolygonalArcEndpointGluedSegmentTransfer pieces hsuccessive
  rcases PolygonalArcFromEndpointGluedPieces
      (pieces := pieces) (source := Q.source) (target := Q.target)
      (hpieces := by simp [pieces])
      (first_source := by
        intro Γ hΓ
        simp [pieces] at hΓ
        subst Γ
        exact D.prefix_source)
      (last_target := by
        intro Γ hΓ
        simp [pieces] at hΓ
        subst Γ
        exact D.suffix_target)
      (successive_attach := hsuccessive)
      (glued_segment_endpoints_distinct := by
        intro i hi
        rcases htransfer.2 i hi with
          ⟨piece, _hpiece, m, hm, hmatch | hmatch⟩
        · intro hglued
          have hlocal : piece.vertices[m] = piece.vertices[m + 1] := by
            calc
              piece.vertices[m] =
                  (PolygonalArcEndpointGluedVertices pieces)[i] := hmatch.1.symm
              _ = (PolygonalArcEndpointGluedVertices pieces)[i + 1] := hglued
              _ = piece.vertices[m + 1] := hmatch.2
          exact (Nat.ne_of_lt (by omega : m < m + 1))
            ((piece.simple_vertices.getElem_inj_iff
              (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 hlocal)
        · intro hglued
          have hlocal : piece.vertices[m] = piece.vertices[m + 1] := by
            calc
              piece.vertices[m] =
                  (PolygonalArcEndpointGluedVertices pieces)[i + 1] := hmatch.2.symm
              _ = (PolygonalArcEndpointGluedVertices pieces)[i] := hglued.symm
              _ = piece.vertices[m + 1] := hmatch.1
          exact (Nat.ne_of_lt (by omega : m < m + 1))
            ((piece.simple_vertices.getElem_inj_iff
              (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 hlocal))
      (adjacent_segment_intersections := hsegmentCerts.1)
      (nonadjacent_segment_disjoint := by
        intro i j hi hj hij
        exact hsegmentCerts.2 hi hj hij)
      (piece_relativeInterior_avoids_endpoints := hpiece_avoids) with
    ⟨Q', hvertices, hsource, htarget, hcarrier, hinterior,
      hpiece_interior, hpiece_segment, _hsegment_piece⟩
  refine ⟨Q', ?_, hsource, htarget, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pieces] using hvertices
  · rw [hcarrier]
    ext z
    simp [pieces, or_assoc]
  · rw [hinterior]
    ext z
    simp [pieces, or_assoc]
  · exact hpiece_interior D.prefixArc (by simp [pieces])
  · exact hpiece_interior bridge (by simp [pieces])
  · exact hpiece_interior D.suffixArc (by simp [pieces])
  · intro z m hm hz
    rcases hpiece_segment bridge (by simp [pieces]) m hm with
      ⟨j, hj, hforward | hreverse⟩
    · refine ⟨j, hj, ?_, 1, one_ne_zero, ?_⟩
      · simpa [hforward.1, hforward.2] using hz
      · simp [hforward.1, hforward.2]
    · refine ⟨j, hj, ?_, -1, neg_ne_zero.mpr one_ne_zero, ?_⟩
      · simpa [hreverse.1, hreverse.2, openSegment_symm] using hz
      · simp [hreverse.1, hreverse.2]
  · intro z i hi hzold hzcarrier hzoutside
    have hz_not_bridge : z ∉ bridge.carrier := by
      intro hzbridge
      by_cases hzendpoint :
          z ∈ ({bridge.source, bridge.target} :
            Set (EuclideanSpace ℝ (Fin 2)))
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzendpoint
        rcases hzendpoint with hzsource | hztarget
        · apply hzoutside
          rw [hzsource, hbridge_source]
          exact Metric.sphere_subset_closedBall D.qminus_mem_sphere
        · apply hzoutside
          rw [hztarget, hbridge_target]
          exact Metric.sphere_subset_closedBall D.qplus_mem_sphere
      · have hzri : z ∈ bridge.relativeInterior := by
          rw [bridge.relativeInterior_eq]
          exact ⟨hzbridge, hzendpoint⟩
        exact hzoutside
          (Metric.ball_subset_closedBall (hbridge_ball hzri))
    have hzpiece : z ∈ D.prefixArc.carrier ∨ z ∈ D.suffixArc.carrier := by
      rw [hcarrier] at hzcarrier
      rcases hzcarrier with ⟨piece, hpiece, hzpiece⟩
      simp [pieces] at hpiece
      rcases hpiece with rfl | rfl | rfl
      · exact Or.inl hzpiece
      · exact False.elim (hz_not_bridge hzpiece)
      · exact Or.inr hzpiece
    rcases hzpiece with hzprefix | hzsuffix
    · rcases D.prefix_segment_transfer z i hi hzold hzprefix hzoutside with
        ⟨m, hm, hzlocal, c, hc, hdir⟩
      rcases hpiece_segment D.prefixArc (by simp [pieces]) m hm with
        ⟨j, hj, hforward | hreverse⟩
      · refine ⟨j, hj, ?_, c, hc, ?_⟩
        · simpa [hforward.1, hforward.2] using hzlocal
        · simpa [hforward.1, hforward.2] using hdir
      · refine ⟨j, hj, ?_, -c, neg_ne_zero.mpr hc, ?_⟩
        · simpa [hreverse.1, hreverse.2, openSegment_symm] using hzlocal
        · rw [hreverse.1, hreverse.2]
          calc
            D.prefixArc.vertices[m] - D.prefixArc.vertices[m + 1] =
                -(D.prefixArc.vertices[m + 1] - D.prefixArc.vertices[m]) := by
              abel
            _ = -(c • (Q.vertices[i + 1] - Q.vertices[i])) :=
              congrArg Neg.neg hdir
            _ = (-c) • (Q.vertices[i + 1] - Q.vertices[i]) := by simp
    · rcases D.suffix_segment_transfer z i hi hzold hzsuffix hzoutside with
        ⟨m, hm, hzlocal, c, hc, hdir⟩
      rcases hpiece_segment D.suffixArc (by simp [pieces]) m hm with
        ⟨j, hj, hforward | hreverse⟩
      · refine ⟨j, hj, ?_, c, hc, ?_⟩
        · simpa [hforward.1, hforward.2] using hzlocal
        · simpa [hforward.1, hforward.2] using hdir
      · refine ⟨j, hj, ?_, -c, neg_ne_zero.mpr hc, ?_⟩
        · simpa [hreverse.1, hreverse.2, openSegment_symm] using hzlocal
        · rw [hreverse.1, hreverse.2]
          calc
            D.suffixArc.vertices[m] - D.suffixArc.vertices[m + 1] =
                -(D.suffixArc.vertices[m + 1] - D.suffixArc.vertices[m]) := by
              abel
            _ = -(c • (Q.vertices[i + 1] - Q.vertices[i])) :=
              congrArg Neg.neg hdir
            _ = (-c) • (Q.vertices[i + 1] - Q.vertices[i]) := by simp
