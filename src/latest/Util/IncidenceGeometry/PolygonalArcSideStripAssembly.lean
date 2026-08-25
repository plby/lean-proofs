import Mathlib.Tactic
import Util.IncidenceGeometry.PolygonalArcCollarLocalSideData
import Util.IncidenceGeometry.PolygonalArcMiddleTubeBasicTopology
import Util.IncidenceGeometry.PolygonalArcMiddleTubeWithoutRelativeInterior
import Util.IncidenceGeometry.PolygonalArcSideStripRelativeInteriorCoverage
import Util.IncidenceGeometry.PolygonalArcSideStripSetAlgebra
import Util.IncidenceGeometry.PolygonalSideStrips

open Classical
open Filter
noncomputable section

lemma PolygonalArcSideStripAssembly (γ : PolygonalArc) {η : ℝ}
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
    ∃ S : PolygonalSideStrips γ,
      S.collar =
          ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length),
              orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube j hj) ∪
            (⋃ i : Fin γ.vertices.length, localSideData.vertexCollar i)) ∧
        S.leftStrip =
          ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length),
              orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf j hj) ∪
            (⋃ i : Fin γ.vertices.length, localSideData.leftSidePiece i)) ∧
        S.rightStrip =
          ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length),
              orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf j hj) ∪
            (⋃ i : Fin γ.vertices.length, localSideData.rightSidePiece i)) ∧
        ∀ z ∈ S.collar, ∃ p ∈ γ.carrier, dist z p < η := by
  let sep := orientedTubes.toPolygonalArcCollarSeparatedTubeData
  let C : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.tube j hj) ∪
      (⋃ i : Fin γ.vertices.length, localSideData.vertexCollar i))
  let L : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.leftHalf j hj) ∪
      (⋃ i : Fin γ.vertices.length, localSideData.leftSidePiece i))
  let R : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.rightHalf j hj) ∪
      (⋃ i : Fin γ.vertices.length, localSideData.rightSidePiece i))
  have htop :=
    PolygonalArcMiddleTubeBasicTopology γ controlRadii middleSegments forbiddenMargins
      orientedTubes
  have hset :=
    PolygonalArcSideStripSetAlgebra γ controlRadii middleSegments forbiddenMargins
      orientedTubes vertexLocalPieces localSideData
  have side_connected_chain
      (sidePiece : Fin γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2)))
      (half : (j : ℕ) → j + 1 < γ.vertices.length →
        Set (EuclideanSpace ℝ (Fin 2)))
      (outAttach : (j : ℕ) → j + 1 < γ.vertices.length →
        Set (EuclideanSpace ℝ (Fin 2)))
      (inAttach : (j : ℕ) → j + 1 < γ.vertices.length →
        Set (EuclideanSpace ℝ (Fin 2)))
      (hside_connected : ∀ i, IsConnected (sidePiece i))
      (hhalf_connected : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        IsConnected (half j hj))
      (hout_nonempty : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (outAttach j hj).Nonempty)
      (hin_nonempty : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        (inAttach j hj).Nonempty)
      (hout_side : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        outAttach j hj ⊆ sidePiece ⟨j, Nat.lt_of_succ_lt hj⟩)
      (hout_half : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        outAttach j hj ⊆ half j hj)
      (hin_side : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        inAttach j hj ⊆ sidePiece ⟨j + 1, hj⟩)
      (hin_half : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        inAttach j hj ⊆ half j hj) :
      IsConnected
        ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), half j hj) ∪
          (⋃ i : Fin γ.vertices.length, sidePiece i)) := by
    let pref : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun k =>
      ((⋃ (i : ℕ), ⋃ (hi : i < γ.vertices.length), ⋃ (_ : i ≤ k),
          sidePiece ⟨i, hi⟩) ∪
        (⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), ⋃ (_ : j < k),
          half j hj))
    have hlen2 : 2 ≤ γ.vertices.length := γ.length_ge_two
    have h0 : 0 < γ.vertices.length := by omega
    have hpref_zero : pref 0 = sidePiece ⟨0, h0⟩ := by
      ext z
      constructor
      · intro hz
        dsimp [pref] at hz
        rcases hz with hzV | hzH
        · rcases Set.mem_iUnion.1 hzV with ⟨i, hzi⟩
          rcases Set.mem_iUnion.1 hzi with ⟨hi, hzi'⟩
          rcases Set.mem_iUnion.1 hzi' with ⟨hik, hzPiece⟩
          have hi0 : i = 0 := by omega
          subst i
          simpa using hzPiece
        · rcases Set.mem_iUnion.1 hzH with ⟨j, hzj⟩
          rcases Set.mem_iUnion.1 hzj with ⟨hj, hzj'⟩
          rcases Set.mem_iUnion.1 hzj' with ⟨hjk, _hzHalf⟩
          omega
      · intro hz
        dsimp [pref]
        left
        exact Set.mem_iUnion.2 ⟨0, Set.mem_iUnion.2 ⟨h0,
          Set.mem_iUnion.2 ⟨le_rfl, hz⟩⟩⟩
    have hpref_step :
        ∀ (k : ℕ) (hseg : k + 1 < γ.vertices.length),
          pref (k + 1) =
            (pref k ∪ half k hseg) ∪ sidePiece ⟨k + 1, hseg⟩ := by
      intro k hseg
      ext z
      constructor
      · intro hz
        dsimp [pref] at hz ⊢
        rcases hz with hzV | hzH
        · rcases Set.mem_iUnion.1 hzV with ⟨i, hzi⟩
          rcases Set.mem_iUnion.1 hzi with ⟨hi, hzi'⟩
          rcases Set.mem_iUnion.1 hzi' with ⟨hik, hzPiece⟩
          by_cases hik' : i ≤ k
          · left
            left
            left
            exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi,
              Set.mem_iUnion.2 ⟨hik', hzPiece⟩⟩⟩
          · have hi_eq : i = k + 1 := by omega
            subst i
            right
            simpa using hzPiece
        · rcases Set.mem_iUnion.1 hzH with ⟨j, hzj⟩
          rcases Set.mem_iUnion.1 hzj with ⟨hj, hzj'⟩
          rcases Set.mem_iUnion.1 hzj' with ⟨hjk, hzHalf⟩
          by_cases hjk' : j < k
          · left
            left
            right
            exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj,
              Set.mem_iUnion.2 ⟨hjk', hzHalf⟩⟩⟩
          · have hj_eq : j = k := by omega
            subst j
            left
            right
            simpa using hzHalf
      · intro hz
        dsimp [pref] at hz ⊢
        rcases hz with hzLeft | hzNextPiece
        · rcases hzLeft with hzPrev | hzHalf
          · rcases hzPrev with hzV | hzH
            · rcases Set.mem_iUnion.1 hzV with ⟨i, hzi⟩
              rcases Set.mem_iUnion.1 hzi with ⟨hi, hzi'⟩
              rcases Set.mem_iUnion.1 hzi' with ⟨hik, hzPiece⟩
              left
              exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi,
                Set.mem_iUnion.2 ⟨by omega, hzPiece⟩⟩⟩
            · rcases Set.mem_iUnion.1 hzH with ⟨j, hzj⟩
              rcases Set.mem_iUnion.1 hzj with ⟨hj, hzj'⟩
              rcases Set.mem_iUnion.1 hzj' with ⟨hjk, hzHalf'⟩
              right
              exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj,
                Set.mem_iUnion.2 ⟨by omega, hzHalf'⟩⟩⟩
          · right
            exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hseg,
              Set.mem_iUnion.2 ⟨by omega, hzHalf⟩⟩⟩
        · left
          exact Set.mem_iUnion.2 ⟨k + 1, Set.mem_iUnion.2 ⟨hseg,
            Set.mem_iUnion.2 ⟨le_rfl, hzNextPiece⟩⟩⟩
    have hpref_connected :
        ∀ (k : ℕ), k < γ.vertices.length → IsConnected (pref k) := by
      intro k hk
      induction k with
      | zero =>
          rw [hpref_zero]
          exact hside_connected ⟨0, h0⟩
      | succ k ih =>
          have hk' : k < γ.vertices.length := Nat.lt_of_succ_lt hk
          have hseg : k + 1 < γ.vertices.length := hk
          rw [hpref_step k hseg]
          have hconn_pref : IsConnected (pref k) := ih hk'
          have hconn_half : IsConnected (half k hseg) := hhalf_connected k hseg
          have h_inter_first : (pref k ∩ half k hseg).Nonempty := by
            rcases hout_nonempty k hseg with ⟨x, hx⟩
            refine ⟨x, ?_, hout_half k hseg hx⟩
            dsimp [pref]
            left
            exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨Nat.lt_of_succ_lt hseg,
              Set.mem_iUnion.2 ⟨le_rfl, hout_side k hseg hx⟩⟩⟩
          have hconn_pref_half :
              IsConnected (pref k ∪ half k hseg) :=
            IsConnected.union h_inter_first hconn_pref hconn_half
          have h_inter_second :
              ((pref k ∪ half k hseg) ∩ sidePiece ⟨k + 1, hseg⟩).Nonempty := by
            rcases hin_nonempty k hseg with ⟨x, hx⟩
            refine ⟨x, Or.inr (hin_half k hseg hx), hin_side k hseg hx⟩
          exact IsConnected.union h_inter_second hconn_pref_half
            (hside_connected ⟨k + 1, hseg⟩)
    have hlast : γ.vertices.length - 1 < γ.vertices.length := by omega
    have htarget :
        ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), half j hj) ∪
          (⋃ i : Fin γ.vertices.length, sidePiece i)) =
          pref (γ.vertices.length - 1) := by
      ext z
      constructor
      · intro hz
        dsimp [pref]
        rcases hz with hzHalf | hzPiece
        · right
          rcases Set.mem_iUnion.1 hzHalf with ⟨j, hzj⟩
          rcases Set.mem_iUnion.1 hzj with ⟨hj, hzHalf'⟩
          exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj,
            Set.mem_iUnion.2 ⟨by omega, hzHalf'⟩⟩⟩
        · left
          rcases Set.mem_iUnion.1 hzPiece with ⟨i, hzSide⟩
          exact Set.mem_iUnion.2 ⟨i.1, Set.mem_iUnion.2 ⟨i.2,
            Set.mem_iUnion.2 ⟨by omega, by simpa using hzSide⟩⟩⟩
      · intro hz
        dsimp [pref] at hz
        rcases hz with hzV | hzH
        · right
          rcases Set.mem_iUnion.1 hzV with ⟨i, hzi⟩
          rcases Set.mem_iUnion.1 hzi with ⟨hi, hzi'⟩
          rcases Set.mem_iUnion.1 hzi' with ⟨_hik, hzSide⟩
          exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, by simpa using hzSide⟩
        · left
          rcases Set.mem_iUnion.1 hzH with ⟨j, hzj⟩
          rcases Set.mem_iUnion.1 hzj with ⟨hj, hzj'⟩
          rcases Set.mem_iUnion.1 hzj' with ⟨_hjk, hzHalf⟩
          exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hzHalf⟩⟩
    rw [htarget]
    exact hpref_connected (γ.vertices.length - 1) hlast
  have hleft_out_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        vertexLocalPieces.outgoingLeftAttachment j hj ⊆ sep.leftHalf j hj := by
    intro j hj z hz
    have hz' := hz
    rw [vertexLocalPieces.outgoingLeftAttachment_eq j hj] at hz'
    simpa [sep] using hz'.2
  have hleft_in_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        vertexLocalPieces.incomingLeftAttachment j hj ⊆ sep.leftHalf j hj := by
    intro j hj z hz
    have hz' := hz
    rw [vertexLocalPieces.incomingLeftAttachment_eq j hj] at hz'
    simpa [sep] using hz'.2
  have hright_out_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        vertexLocalPieces.outgoingRightAttachment j hj ⊆ sep.rightHalf j hj := by
    intro j hj z hz
    have hz' := hz
    rw [vertexLocalPieces.outgoingRightAttachment_eq j hj] at hz'
    simpa [sep] using hz'.2
  have hright_in_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        vertexLocalPieces.incomingRightAttachment j hj ⊆ sep.rightHalf j hj := by
    intro j hj z hz
    have hz' := hz
    rw [vertexLocalPieces.incomingRightAttachment_eq j hj] at hz'
    simpa [sep] using hz'.2
  have hleft_connected : IsConnected L := by
    dsimp [L]
    exact side_connected_chain localSideData.leftSidePiece
      (fun j hj => sep.leftHalf j hj)
      vertexLocalPieces.outgoingLeftAttachment
      vertexLocalPieces.incomingLeftAttachment
      localSideData.leftSidePiece_connected
      htop.2.2.2.1
      vertexLocalPieces.outgoingLeftAttachment_nonempty
      vertexLocalPieces.incomingLeftAttachment_nonempty
      localSideData.outgoingLeftAttachment_subset_leftSidePiece
      hleft_out_half
      localSideData.incomingLeftAttachment_subset_leftSidePiece
      hleft_in_half
  have hright_connected : IsConnected R := by
    dsimp [R]
    exact side_connected_chain localSideData.rightSidePiece
      (fun j hj => sep.rightHalf j hj)
      vertexLocalPieces.outgoingRightAttachment
      vertexLocalPieces.incomingRightAttachment
      localSideData.rightSidePiece_connected
      htop.2.2.2.2
      vertexLocalPieces.outgoingRightAttachment_nonempty
      vertexLocalPieces.incomingRightAttachment_nonempty
      localSideData.outgoingRightAttachment_subset_rightSidePiece
      hright_out_half
      localSideData.incomingRightAttachment_subset_rightSidePiece
      hright_in_half
  refine ⟨
    { collar := C
      leftStrip := L
      rightStrip := R
      collar_open := ?_
      left_open := ?_
      right_open := ?_
      relativeInterior_subset_collar := ?_
      left_subset_collar := ?_
      right_subset_collar := ?_
      left_connected := hleft_connected
      right_connected := hright_connected
      left_disjoint_arc := by
        exact hset.1
      right_disjoint_arc := by
        exact hset.2.1
      side_strips_disjoint := by
        exact hset.2.2.1
      relativeInterior_subset_closure_left := by
        have hpiece_subset_L :
            ∀ i : Fin γ.vertices.length, localSideData.leftSidePiece i ⊆ L := by
          intro i z hz
          dsimp [L]
          exact Or.inr (Set.mem_iUnion.2 ⟨i, hz⟩)
        have hhalf_subset_L :
            ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
              sep.leftHalf j hj ⊆ L := by
          intro j hj z hz
          dsimp [L]
          exact Or.inl (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hz⟩⟩)
        have hmiddle_closure :
            ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) {t : ℝ},
              t ∈ Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj) →
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
                  closure L := by
          intro j hj t ht
          let f : ℕ → EuclideanSpace ℝ (Fin 2) := fun n =>
            AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              (sep.halfWidth j hj / ((n : ℝ) + 2)) • sep.normal j hj
          have hscalar :
              Tendsto (fun n : ℕ => sep.halfWidth j hj / ((n : ℝ) + 2))
                atTop (nhds (0 : ℝ)) := by
            have hden :
                Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
              exact tendsto_atTop_add_const_right _ _
                tendsto_natCast_atTop_atTop
            simpa using (tendsto_const_nhds.div_atTop hden :
              Tendsto (fun n : ℕ => sep.halfWidth j hj / ((n : ℝ) + 2))
                atTop (nhds (0 : ℝ)))
          have hf :
              Tendsto f atTop
                (nhds (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)) := by
            have hvec :
                Tendsto
                  (fun n : ℕ =>
                    (sep.halfWidth j hj / ((n : ℝ) + 2)) • sep.normal j hj)
                  atTop (nhds ((0 : ℝ) • sep.normal j hj)) :=
              hscalar.smul_const (sep.normal j hj)
            have hconst :
                Tendsto
                  (fun _ : ℕ =>
                    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
                  atTop
                  (nhds (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)) :=
              tendsto_const_nhds
            have hadd := hconst.add hvec
            simpa [f] using hadd
          have hmem_eventually : ∀ᶠ n in atTop, f n ∈ sep.leftHalf j hj := by
            filter_upwards [eventually_ge_atTop (0 : ℕ)] with n hn
            rw [sep.leftHalf_eq j hj]
            refine ⟨t, ht,
              sep.halfWidth j hj / ((n : ℝ) + 2), ?_, rfl⟩
            have hden_pos : 0 < (n : ℝ) + 2 := by positivity
            have hden_gt_one : 1 < (n : ℝ) + 2 := by
              have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
              linarith
            constructor
            · exact div_pos (sep.halfWidth_pos j hj) hden_pos
            · rw [div_lt_iff₀ hden_pos]
              nlinarith [sep.halfWidth_pos j hj, hden_gt_one]
          exact closure_mono (hhalf_subset_L j hj)
            (mem_closure_of_tendsto hf hmem_eventually)
        intro z hzRel
        have hzRel' :
            z ∈ γ.carrier \ ({γ.source, γ.target} :
              Set (EuclideanSpace ℝ (Fin 2))) := by
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
          · exact closure_mono (hpiece_subset_L ⟨j, Nat.lt_of_succ_lt hj⟩)
              (localSideData.outgoing_germ_subset_closure_leftSidePiece j hj
                ⟨t, ⟨ht0, ht_lt_a⟩, rfl⟩)
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
            · have hlocal :=
                localSideData.interior_vertex_mem_closure_leftSidePiece
                  ⟨j, Nat.lt_of_succ_lt hj⟩ hjpos hj
              exact closure_mono (hpiece_subset_L ⟨j, Nat.lt_of_succ_lt hj⟩)
                (by simpa [AffineMap.lineMap_apply_zero] using hlocal)
        · have ha_le_t : a ≤ t := le_of_not_gt ht_lt_a
          by_cases ht_le_b : t ≤ b
          · have htOpen :
                t ∈ Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj) := by
              constructor
              · have hlt := sep.lowerParam_lt_left_parameter j hj
                exact lt_of_lt_of_le (by simpa [a] using hlt) ha_le_t
              · have hlt := sep.right_parameter_lt_upperParam j hj
                exact lt_of_le_of_lt ht_le_b (by simpa [b] using hlt)
            exact hmiddle_closure j hj htOpen
          · have hb_lt_t : b < t := lt_of_not_ge ht_le_b
            rcases lt_or_eq_of_le htIcc.2 with ht1 | ht1
            · exact closure_mono (hpiece_subset_L ⟨j + 1, hj⟩)
                (localSideData.incoming_germ_subset_closure_leftSidePiece j hj
                  ⟨t, ⟨hb_lt_t, ht1⟩, rfl⟩)
            · subst t
              by_cases hnext : (j + 1) + 1 < γ.vertices.length
              · have hlocal :=
                  localSideData.interior_vertex_mem_closure_leftSidePiece
                    ⟨j + 1, hj⟩ (Nat.succ_pos j) hnext
                exact closure_mono (hpiece_subset_L ⟨j + 1, hj⟩)
                  (by simpa [AffineMap.lineMap_apply_one] using hlocal)
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
      relativeInterior_subset_closure_right := by
        have hpiece_subset_R :
            ∀ i : Fin γ.vertices.length, localSideData.rightSidePiece i ⊆ R := by
          intro i z hz
          dsimp [R]
          exact Or.inr (Set.mem_iUnion.2 ⟨i, hz⟩)
        have hhalf_subset_R :
            ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
              sep.rightHalf j hj ⊆ R := by
          intro j hj z hz
          dsimp [R]
          exact Or.inl (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hz⟩⟩)
        have hmiddle_closure :
            ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) {t : ℝ},
              t ∈ Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj) →
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t ∈
                  closure R := by
          intro j hj t ht
          let f : ℕ → EuclideanSpace ℝ (Fin 2) := fun n =>
            AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              (-(sep.halfWidth j hj / ((n : ℝ) + 2))) • sep.normal j hj
          have hscalar :
              Tendsto (fun n : ℕ => sep.halfWidth j hj / ((n : ℝ) + 2))
                atTop (nhds (0 : ℝ)) := by
            have hden :
                Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
              exact tendsto_atTop_add_const_right _ _
                tendsto_natCast_atTop_atTop
            simpa using (tendsto_const_nhds.div_atTop hden :
              Tendsto (fun n : ℕ => sep.halfWidth j hj / ((n : ℝ) + 2))
                atTop (nhds (0 : ℝ)))
          have hf :
              Tendsto f atTop
                (nhds (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)) := by
            have hneg :
                Tendsto
                  (fun n : ℕ => -(sep.halfWidth j hj / ((n : ℝ) + 2)))
                  atTop (nhds (-(0 : ℝ))) := hscalar.neg
            have hvec :
                Tendsto
                  (fun n : ℕ =>
                    (-(sep.halfWidth j hj / ((n : ℝ) + 2))) •
                      sep.normal j hj)
                  atTop (nhds ((0 : ℝ) • sep.normal j hj)) := by
              simpa using hneg.smul_const (sep.normal j hj)
            have hconst :
                Tendsto
                  (fun _ : ℕ =>
                    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
                  atTop
                  (nhds (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)) :=
              tendsto_const_nhds
            have hadd := hconst.add hvec
            simpa [f] using hadd
          have hmem_eventually : ∀ᶠ n in atTop, f n ∈ sep.rightHalf j hj := by
            filter_upwards [eventually_ge_atTop (0 : ℕ)] with n hn
            rw [sep.rightHalf_eq j hj]
            refine ⟨t, ht,
              -(sep.halfWidth j hj / ((n : ℝ) + 2)), ?_, rfl⟩
            have hden_pos : 0 < (n : ℝ) + 2 := by positivity
            have hden_gt_one : 1 < (n : ℝ) + 2 := by
              have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
              linarith
            have hpos :
                0 < sep.halfWidth j hj / ((n : ℝ) + 2) :=
              div_pos (sep.halfWidth_pos j hj) hden_pos
            have hlt :
                sep.halfWidth j hj / ((n : ℝ) + 2) <
                  sep.halfWidth j hj := by
              rw [div_lt_iff₀ hden_pos]
              nlinarith [sep.halfWidth_pos j hj, hden_gt_one]
            constructor <;> linarith
          exact closure_mono (hhalf_subset_R j hj)
            (mem_closure_of_tendsto hf hmem_eventually)
        intro z hzRel
        have hzRel' :
            z ∈ γ.carrier \ ({γ.source, γ.target} :
              Set (EuclideanSpace ℝ (Fin 2))) := by
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
          · exact closure_mono (hpiece_subset_R ⟨j, Nat.lt_of_succ_lt hj⟩)
              (localSideData.outgoing_germ_subset_closure_rightSidePiece j hj
                ⟨t, ⟨ht0, ht_lt_a⟩, rfl⟩)
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
            · have hlocal :=
                localSideData.interior_vertex_mem_closure_rightSidePiece
                  ⟨j, Nat.lt_of_succ_lt hj⟩ hjpos hj
              exact closure_mono (hpiece_subset_R ⟨j, Nat.lt_of_succ_lt hj⟩)
                (by simpa [AffineMap.lineMap_apply_zero] using hlocal)
        · have ha_le_t : a ≤ t := le_of_not_gt ht_lt_a
          by_cases ht_le_b : t ≤ b
          · have htOpen :
                t ∈ Set.Ioo (sep.lowerParam j hj) (sep.upperParam j hj) := by
              constructor
              · have hlt := sep.lowerParam_lt_left_parameter j hj
                exact lt_of_lt_of_le (by simpa [a] using hlt) ha_le_t
              · have hlt := sep.right_parameter_lt_upperParam j hj
                exact lt_of_le_of_lt ht_le_b (by simpa [b] using hlt)
            exact hmiddle_closure j hj htOpen
          · have hb_lt_t : b < t := lt_of_not_ge ht_le_b
            rcases lt_or_eq_of_le htIcc.2 with ht1 | ht1
            · exact closure_mono (hpiece_subset_R ⟨j + 1, hj⟩)
                (localSideData.incoming_germ_subset_closure_rightSidePiece j hj
                  ⟨t, ⟨hb_lt_t, ht1⟩, rfl⟩)
            · subst t
              by_cases hnext : (j + 1) + 1 < γ.vertices.length
              · have hlocal :=
                  localSideData.interior_vertex_mem_closure_rightSidePiece
                    ⟨j + 1, hj⟩ (Nat.succ_pos j) hnext
                exact closure_mono (hpiece_subset_R ⟨j + 1, hj⟩)
                  (by simpa [AffineMap.lineMap_apply_one] using hlocal)
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
      collar_without_arc := by
        exact hset.2.2.2 },
    ?_, ?_, ?_, ?_⟩
  · dsimp [C]
    exact IsOpen.union
      (isOpen_iUnion fun j => isOpen_iUnion fun hj => htop.1 j hj)
      (isOpen_iUnion fun i => localSideData.vertexCollar_open i)
  · dsimp [L]
    exact IsOpen.union
      (isOpen_iUnion fun j => isOpen_iUnion fun hj => htop.2.1 j hj)
      (isOpen_iUnion fun i => localSideData.leftSidePiece_open i)
  · dsimp [R]
    exact IsOpen.union
      (isOpen_iUnion fun j => isOpen_iUnion fun hj => htop.2.2.1 j hj)
      (isOpen_iUnion fun i => localSideData.rightSidePiece_open i)
  · dsimp [C]
    exact PolygonalArcSideStripRelativeInteriorCoverage γ controlRadii middleSegments
      forbiddenMargins orientedTubes vertexLocalPieces localSideData
  · intro z hz
    dsimp [L, C] at hz ⊢
    rcases hz with hzHalf | hzPiece
    · left
      rcases Set.mem_iUnion.1 hzHalf with ⟨j, hzj⟩
      rcases Set.mem_iUnion.1 hzj with ⟨hj, hzleft⟩
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj,
        sep.leftHalf_subset_tube j hj hzleft⟩⟩
    · right
      rcases Set.mem_iUnion.1 hzPiece with ⟨i, hzi⟩
      exact Set.mem_iUnion.2 ⟨i, localSideData.leftSidePiece_subset_vertexCollar i hzi⟩
  · intro z hz
    dsimp [R, C] at hz ⊢
    rcases hz with hzHalf | hzPiece
    · left
      rcases Set.mem_iUnion.1 hzHalf with ⟨j, hzj⟩
      rcases Set.mem_iUnion.1 hzj with ⟨hj, hzright⟩
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj,
        sep.rightHalf_subset_tube j hj hzright⟩⟩
    · right
      rcases Set.mem_iUnion.1 hzPiece with ⟨i, hzi⟩
      exact Set.mem_iUnion.2 ⟨i, localSideData.rightSidePiece_subset_vertexCollar i hzi⟩
  · rfl
  · rfl
  · rfl
  · intro z hz
    dsimp [C] at hz
    rcases hz with hzTube | hzVertex
    · rcases Set.mem_iUnion.1 hzTube with ⟨j, hzj⟩
      rcases Set.mem_iUnion.1 hzj with ⟨hj, hztube⟩
      exact sep.tube_subset_eta_neighborhood j hj z hztube
    · rcases Set.mem_iUnion.1 hzVertex with ⟨i, hzi⟩
      exact localSideData.vertexCollar_subset_eta_neighborhood i z hzi
