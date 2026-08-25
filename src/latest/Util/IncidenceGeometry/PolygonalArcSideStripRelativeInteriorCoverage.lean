import Util.IncidenceGeometry.PolygonalArcCollarLocalSideData

open Classical
noncomputable section

lemma PolygonalArcSideStripRelativeInteriorCoverage
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (orientedTubes :
      PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (localSideData :
      PolygonalArcCollarLocalSideData γ controlRadii middleSegments
        forbiddenMargins orientedTubes vertexLocalPieces) :
    γ.relativeInterior ⊆
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length),
          orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube j hj) ∪
        (⋃ i : Fin γ.vertices.length, localSideData.vertexCollar i)) := by
  let sep := orientedTubes.toPolygonalArcCollarSeparatedTubeData
  intro z hzRel
  have hzRel' : z ∈ γ.carrier \ ({γ.source, γ.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
    simpa [γ.relativeInterior_eq] using hzRel
  have hzCarrier : z ∈ γ.carrier := hzRel'.1
  rw [γ.carrier_eq] at hzCarrier
  rcases hzCarrier with ⟨j, hj, hzseg⟩
  rw [segment_eq_image_lineMap] at hzseg
  rcases hzseg with ⟨t, htIcc, rfl⟩
  let a : ℝ :=
    controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  let b : ℝ :=
    1 - controlRadii.radius ⟨j + 1, hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  by_cases ht_lt_a : t < a
  · rcases lt_or_eq_of_le htIcc.1 with ht0 | ht0
    · right
      refine Set.mem_iUnion.2 ⟨⟨j, Nat.lt_of_succ_lt hj⟩, ?_⟩
      exact localSideData.outgoing_germ_subset_vertexCollar j hj
        ⟨t, ⟨ht0, ht_lt_a⟩, rfl⟩
    · subst t
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst j
        have hsource0 : γ.vertices[0] = γ.source := by
          have h0lt : 0 < γ.vertices.length := by
            exact lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) γ.length_ge_two
          have hget : γ.vertices[0]? = some γ.vertices[0] :=
            List.getElem?_eq_getElem h0lt
          rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
          exact Option.some.inj hget.symm
        exfalso
        exact hzRel'.2 (by
          rw [Set.mem_insert_iff, Set.mem_singleton_iff]
          left
          simpa [AffineMap.lineMap_apply_zero] using hsource0)
      · right
        refine Set.mem_iUnion.2 ⟨⟨j, Nat.lt_of_succ_lt hj⟩, ?_⟩
        have hCeq :=
          localSideData.interior_vertexCollar_eq_vertexDisk
            ⟨j, Nat.lt_of_succ_lt hj⟩ hjpos hj
        rw [hCeq, vertexLocalPieces.vertexDisk_eq]
        simp [Metric.mem_ball, AffineMap.lineMap_apply_zero, controlRadii.radius_pos]
  · have ha_le_t : a ≤ t := le_of_not_gt ht_lt_a
    by_cases ht_le_b : t ≤ b
    · left
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      refine Set.mem_iUnion.2 ⟨hj, ?_⟩
      exact sep.middle_subset_tube j hj (by
        rw [middleSegments.middle_eq j hj]
        exact ⟨t, ⟨ha_le_t, ht_le_b⟩, rfl⟩)
    · have hb_lt_t : b < t := lt_of_not_ge ht_le_b
      rcases lt_or_eq_of_le htIcc.2 with ht1 | ht1
      · right
        refine Set.mem_iUnion.2 ⟨⟨j + 1, hj⟩, ?_⟩
        exact localSideData.incoming_germ_subset_vertexCollar j hj
          ⟨t, ⟨hb_lt_t, ht1⟩, rfl⟩
      · subst t
        by_cases hnext : (j + 1) + 1 < γ.vertices.length
        · right
          refine Set.mem_iUnion.2 ⟨⟨j + 1, hj⟩, ?_⟩
          have hCeq :=
            localSideData.interior_vertexCollar_eq_vertexDisk
              ⟨j + 1, hj⟩ (Nat.succ_pos j) hnext
          rw [hCeq, vertexLocalPieces.vertexDisk_eq]
          simp [Metric.mem_ball, AffineMap.lineMap_apply_one, controlRadii.radius_pos]
        · have htarget : γ.vertices[j + 1] = γ.target := by
            let last : ℕ := γ.vertices.length - 1
            have hlast_lt : last < γ.vertices.length := by
              have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
              dsimp [last]
              omega
            have htarget_last : γ.vertices[last] = γ.target := by
              have hlastEq := γ.target_eq_last
              rw [List.getLast?_eq_getElem?] at hlastEq
              rw [List.getElem?_eq_getElem hlast_lt] at hlastEq
              exact Option.some.inj hlastEq
            have hidx : last = j + 1 := by
              dsimp [last]
              omega
            simpa [hidx] using htarget_last
          exfalso
          exact hzRel'.2 (by
            rw [Set.mem_insert_iff, Set.mem_singleton_iff]
            right
            simpa [AffineMap.lineMap_apply_one] using htarget)
