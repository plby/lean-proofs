import Mathlib.Tactic
import Util.IncidenceGeometry.ArcCrossingEarlierPrefix
import Util.IncidenceGeometry.ArcCrossingInitialConeAvoidsBackwardGerm
import Util.IncidenceGeometry.ComplementComponent
import Util.IncidenceGeometry.OpenConnectedComponentPolygonallyConnected
import Util.IncidenceGeometry.PolygonalArcCollarCompatibleOrientedTubeData
import Util.IncidenceGeometry.PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
import Util.IncidenceGeometry.PolygonalArcCollarControlRadiiExistsBelow
import Util.IncidenceGeometry.PolygonalArcCollarLocalSideData
import Util.IncidenceGeometry.PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
import Util.IncidenceGeometry.PolygonalArcCollarMiddleForbiddenMarginsExists
import Util.IncidenceGeometry.PolygonalArcCollarMiddleSegmentDataExists
import Util.IncidenceGeometry.PolygonalArcEndpointIsolation
import Util.IncidenceGeometry.PolygonalArcInitialEndpointCone
import Util.IncidenceGeometry.PolygonalArcInitialEndpointSegmentLength
import Util.IncidenceGeometry.PolygonalArcInitialEndpointLeftCone
import Util.IncidenceGeometry.PolygonalArcReverse
import Util.IncidenceGeometry.PolygonalArcSideStripAssembly
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointLeftCone
import Util.IncidenceGeometry.PolygonallyPathConnected

open Classical
noncomputable section


lemma ArcCrossingCollarBridgeData
    (K Dstar : Set (EuclideanSpace ℝ (Fin 2))) (δ τ : PolygonalArc)
    (j : ℕ) (c d : EuclideanSpace ℝ (Fin 2)) (r₀ rT K₁ η : ℝ)
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hτvertices : τ.vertices = c :: δ.vertices.drop (j + 1))
    (hτsource : τ.source = c)
    (hIso : PolygonalArcEndpointIsolation τ r₀ rT)
    (hK₁pos : 0 < K₁)
    (hnear_germ_ball : segment ℝ d c ⊆ Metric.ball c r₀)
    (hnear_germ_negative : segment ℝ d c ⊆ segment ℝ c δ.vertices[j])
    (hηpos : 0 < η)
    (hηsep :
      ∀ a, a ∈
          (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)) →
        ∀ b, b ∈ τ.carrier → η ≤ dist a b)
    (hcarrier_cover :
      δ.carrier ⊆
        (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d) ∪
          segment ℝ d c ∪ τ.carrier)
    (hDstar_subset : Dstar ⊆ (K ∪ δ.carrier)ᶜ)
    (hDstar_open : IsOpen Dstar)
    (hDstar_connected : IsConnected Dstar)
    (hterminalLeftCone_Dstar :
      PolygonalArcTerminalEndpointLeftCone τ rT K₁ ⊆ Dstar)
    (hterminalRightCone_Dstar :
      PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse τ) rT K₁ ⊆
        Dstar) :
    ∃ (S : PolygonalSideStrips τ) (W : Set (EuclideanSpace ℝ (Fin 2))),
      W = S.leftStrip ∪ S.rightStrip ∪ Dstar ∧
        W ⊆ (K ∪ δ.carrier)ᶜ ∧
          IsOpen W ∧
            IsConnected W ∧
              PolygonallyPathConnected W ∧
                (Dstar ∩ S.leftStrip).Nonempty ∧
                  (Dstar ∩ S.rightStrip).Nonempty ∧
                    S.leftStrip ⊆ W ∧
                      S.rightStrip ⊆ W ∧
                        τ.relativeInterior ⊆ S.collar ∧
                          IsOpen S.collar ∧
                            S.collar \ τ.relativeInterior =
                              S.leftStrip ∪ S.rightStrip := by
  classical
  have hsourceIdx : 0 < τ.vertices.length := by
    have hlen := τ.length_ge_two
    omega
  have hfirst : 0 + 1 < τ.vertices.length := by
    have hlen := τ.length_ge_two
    omega
  have hfirst' : 1 < τ.vertices.length := by
    simpa using hfirst
  let itarget : ℕ := τ.vertices.length - 1
  have htargetIdx : itarget < τ.vertices.length := by
    have hlen := τ.length_ge_two
    dsimp [itarget]
    omega
  let jlast : ℕ := τ.vertices.length - 2
  have hlast : jlast + 1 < τ.vertices.length := by
    have hlen := τ.length_ge_two
    dsimp [jlast]
    omega
  have hlast_succ : jlast + 1 = itarget := by
    have hlen := τ.length_ge_two
    dsimp [jlast, itarget]
    omega
  have hsource_vertex : τ.vertices[0] = τ.source := by
    have hget : τ.vertices[0]? = some τ.vertices[0] :=
      List.getElem?_eq_getElem hsourceIdx
    rw [← List.head?_eq_getElem?, τ.source_eq_head] at hget
    exact Option.some.inj hget.symm
  let K₀ : ℝ := 1
  have hK₀pos : 0 < K₀ := by
    dsimp [K₀]
    norm_num
  obtain ⟨controlRadii, hρ0_lt, hρT_lt, hsourceBalls, htargetBalls⟩ :=
    PolygonalArcCollarControlRadiiExistsBelow τ η r₀ rT hηpos hIso.source_pos
      hIso.target_pos hIso
  obtain ⟨middleSegments⟩ :=
    PolygonalArcCollarMiddleSegmentDataExists τ controlRadii
  obtain ⟨forbiddenMargins⟩ :=
    PolygonalArcCollarMiddleForbiddenMarginsExists τ controlRadii middleSegments
  obtain ⟨compatibleTubes, hKinit_lt, hKterm_lt, htubeSourceDisj,
      _htubeTargetDisj⟩ :=
    PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow τ controlRadii
      middleSegments forbiddenMargins r₀ rT K₀ K₁ hIso hK₀pos hK₁pos
  obtain ⟨vertexLocalPieces, localSideData, _hsourceVertexOmit,
      _htargetVertexOmit, hsourceVertexCone, _htargetVertexCone,
      hvertexSourceDisj, _hvertexTargetDisj, _hsourceLeftCone,
      htargetLeftCone, _hsourceRightCone, htargetRightCone⟩ :=
    PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones τ controlRadii
      middleSegments forbiddenMargins compatibleTubes r₀ rT K₀ K₁
      hIso.source_pos hIso.target_pos hK₀pos hK₁pos hρ0_lt hρT_lt
      hKinit_lt hKterm_lt hsourceBalls htargetBalls
  obtain ⟨S, hcollar_eq, hleft_eq, hright_eq, hnear⟩ :=
    PolygonalArcSideStripAssembly τ controlRadii middleSegments forbiddenMargins
      compatibleTubes.orientedTubes vertexLocalPieces localSideData
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  have hinitialTubeCone :
      sep.tube 0 hfirst ∩ Metric.ball τ.source r₀ ⊆
        PolygonalArcInitialEndpointCone τ r₀ K₀ := by
    rintro z ⟨hzTube, hzBall⟩
    rw [sep.tube_eq 0 hfirst] at hzTube
    rcases hzTube with ⟨t, ht, s, hs, hz_eq⟩
    let dir : EuclideanSpace ℝ (Fin 2) := τ.vertices[1] - τ.source
    let q : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then t else s)
    have hdist_pos : 0 < dist τ.source τ.vertices[1] := by
      have hlen_pos : 0 < PolygonalArcInitialEndpointSegmentLength τ :=
        lt_trans hIso.source_pos hIso.source_lt_initial_length
      simpa [PolygonalArcInitialEndpointSegmentLength] using hlen_pos
    have hdist_eq_normd : dist τ.source τ.vertices[1] = ‖dir‖ := by
      rw [dist_eq_norm]
      dsimp [dir]
      have hneg : τ.source - τ.vertices[1] =
          -(τ.vertices[1] - τ.source) := by
        abel
      rw [hneg, norm_neg]
    have hnormd_pos : 0 < ‖dir‖ := by
      simpa [← hdist_eq_normd] using hdist_pos
    have hnorm_sq :
        ‖t • dir + s • PlanarRot90 dir‖ ^ 2 =
          (t ^ 2 + s ^ 2) * ‖dir‖ ^ 2 := by
      have horth : inner ℝ (t • dir) (s • PlanarRot90 dir) = 0 := by
        rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
        ring
      have hpyth :
          ‖t • dir + s • PlanarRot90 dir‖ ^ 2 =
            ‖t • dir‖ ^ 2 + ‖s • PlanarRot90 dir‖ ^ 2 := by
        simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      rw [hpyth, norm_smul, norm_smul, PlanarRot90Norm]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have hz_chart :
        z = τ.source + t • dir + s • PlanarRot90 dir := by
      rw [hz_eq]
      dsimp [dir]
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn 0 hfirst]
      rw [hsource_vertex]
      apply PiLp.ext
      intro k
      fin_cases k <;>
        simp [PlanarRot90, AffineMap.lineMap_apply_module] <;>
        ring
    have hzBallNorm : ‖z - τ.source‖ < r₀ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzBall
    have hzBallSq : ‖z - τ.source‖ ^ 2 < r₀ ^ 2 := by
      have hsq := hzBallNorm
      rw [← sq_lt_sq₀ (norm_nonneg _) (le_of_lt hIso.source_pos)] at hsq
      exact hsq
    have hsub : z - τ.source = t • dir + s • PlanarRot90 dir := by
      rw [hz_chart]
      abel
    have hdisk : t ^ 2 + s ^ 2 <
        (r₀ / dist τ.source τ.vertices[1]) ^ 2 := by
      have hscale :
          (r₀ / dist τ.source τ.vertices[1]) ^ 2 * ‖dir‖ ^ 2 = r₀ ^ 2 := by
        rw [hdist_eq_normd]
        field_simp [ne_of_gt hnormd_pos]
      rw [hsub, hnorm_sq] at hzBallSq
      rw [← hscale] at hzBallSq
      have hpos_sq : 0 < ‖dir‖ ^ 2 := sq_pos_of_pos hnormd_pos
      nlinarith
    have ht_pos : 0 < t := lt_trans (sep.lowerParam_pos 0 hfirst) ht.1
    have hprod_le :
        compatibleTubes.initialConeBound 0 hfirst *
            sep.lowerParam 0 hfirst ≤
          K₀ * t := by
      exact mul_le_mul (le_of_lt hKinit_lt) (le_of_lt ht.1)
        (le_of_lt (sep.lowerParam_pos 0 hfirst)) (le_of_lt hK₀pos)
    have hwidth_lt_Kt :
        sep.halfWidth 0 hfirst < K₀ * t :=
      lt_of_lt_of_le
        (compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam 0 hfirst)
        hprod_le
    have hs_lower : -K₀ * t < s := by
      linarith [hs.1, hwidth_lt_Kt]
    have hs_upper : s < K₀ * t := lt_trans hs.2 hwidth_lt_Kt
    rw [PolygonalArcInitialEndpointCone]
    refine ⟨q, ?_, ?_⟩
    · dsimp [q]
      exact ⟨by simpa using ht_pos, by simpa using hdisk,
        by simpa using hs_lower, by simpa using hs_upper⟩
    · simpa [q, dir, hsource_vertex] using hz_chart.symm
  have hinitialContain :
      ((S.collar ∩ Metric.ball τ.source r₀) \ τ.relativeInterior ⊆
        PolygonalArcInitialEndpointCone τ r₀ K₀) := by
    rintro z ⟨⟨hzS, hzBall⟩, hzNotRel⟩
    have hzUnion : z ∈
        ((⋃ (j : ℕ), ⋃ (hj : j + 1 < τ.vertices.length), sep.tube j hj) ∪
          (⋃ i : Fin τ.vertices.length, localSideData.vertexCollar i)) := by
      simpa [sep, hcollar_eq] using hzS
    rcases hzUnion with hzTubes | hzVertices
    · rcases Set.mem_iUnion.1 hzTubes with ⟨k, hzk⟩
      rcases Set.mem_iUnion.1 hzk with ⟨hk, hzTube⟩
      by_cases hk0 : k = 0
      · subst k
        exact hinitialTubeCone ⟨by simpa using hzTube, hzBall⟩
      · exact False.elim
          ((Set.disjoint_left.mp (htubeSourceDisj k hk hk0)) hzTube hzBall)
    · rcases Set.mem_iUnion.1 hzVertices with ⟨i, hzVertex⟩
      by_cases hi0 : i.1 = 0
      · have hi_eq : i = ⟨0, hsourceIdx⟩ := Fin.ext hi0
        subst i
        exact hsourceVertexCone ⟨by simpa using hzVertex, hzNotRel⟩
      · exact False.elim
          ((Set.disjoint_left.mp (hvertexSourceDisj i hi0)) hzVertex hzBall)
  have hS_disjoint_far :
      Disjoint S.collar
        (K ∪ (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)) := by
    rw [Set.disjoint_left]
    intro z hzS hzFar
    rcases hnear z hzS with ⟨p, hpτ, hpdist⟩
    have hsep := hηsep z hzFar p hpτ
    linarith
  have hinitConeAvoidBack :
      Disjoint (PolygonalArcInitialEndpointCone τ r₀ K₀)
        (segment ℝ c δ.vertices[j]) :=
    ArcCrossingInitialConeAvoidsBackwardGerm δ τ j c r₀ K₀ hj hcOpen
      hτvertices hτsource
  have side_avoids_near :
      ∀ ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
        z ∈ S.leftStrip ∪ S.rightStrip → z ∉ segment ℝ d c := by
    intro z hzSide hzNear
    have hzS : z ∈ S.collar := by
      rcases hzSide with hzLeft | hzRight
      · exact S.left_subset_collar hzLeft
      · exact S.right_subset_collar hzRight
    have hzBall : z ∈ Metric.ball τ.source r₀ := by
      simpa [hτsource] using hnear_germ_ball hzNear
    have hzNotRel : z ∉ τ.relativeInterior := by
      intro hzRel
      have hzCarrier : z ∈ τ.carrier := by
        have hzRel' :
            z ∈ τ.carrier \ ({τ.source, τ.target} :
              Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [τ.relativeInterior_eq] using hzRel
        exact hzRel'.1
      rcases hzSide with hzLeft | hzRight
      · exact (Set.disjoint_left.mp S.left_disjoint_arc hzLeft) hzCarrier
      · exact (Set.disjoint_left.mp S.right_disjoint_arc hzRight) hzCarrier
    have hzCone : z ∈ PolygonalArcInitialEndpointCone τ r₀ K₀ :=
      hinitialContain ⟨⟨hzS, hzBall⟩, hzNotRel⟩
    exact (Set.disjoint_left.mp hinitConeAvoidBack hzCone)
      (hnear_germ_negative hzNear)
  have left_avoids_forbidden :
      S.leftStrip ⊆ (K ∪ δ.carrier)ᶜ := by
    intro z hzLeft hzForbidden
    rcases hzForbidden with hzK | hzδ
    · exact (Set.disjoint_left.mp hS_disjoint_far (S.left_subset_collar hzLeft))
        (Or.inl hzK)
    · have hzCover := hcarrier_cover hzδ
      rcases hzCover with hzOldNear | hzTail
      · rcases hzOldNear with hzOld | hzNear
        · exact (Set.disjoint_left.mp hS_disjoint_far
            (S.left_subset_collar hzLeft)) (Or.inr hzOld)
        · exact side_avoids_near (Or.inl hzLeft) hzNear
      · exact (Set.disjoint_left.mp S.left_disjoint_arc hzLeft) hzTail
  have right_avoids_forbidden :
      S.rightStrip ⊆ (K ∪ δ.carrier)ᶜ := by
    intro z hzRight hzForbidden
    rcases hzForbidden with hzK | hzδ
    · exact (Set.disjoint_left.mp hS_disjoint_far (S.right_subset_collar hzRight))
        (Or.inl hzK)
    · have hzCover := hcarrier_cover hzδ
      rcases hzCover with hzOldNear | hzTail
      · rcases hzOldNear with hzOld | hzNear
        · exact (Set.disjoint_left.mp hS_disjoint_far
            (S.right_subset_collar hzRight)) (Or.inr hzOld)
        · exact side_avoids_near (Or.inr hzRight) hzNear
      · exact (Set.disjoint_left.mp S.right_disjoint_arc hzRight) hzTail
  have hDleft : (Dstar ∩ S.leftStrip).Nonempty := by
    rcases vertexLocalPieces.incomingLeftAttachment_nonempty jlast hlast with
      ⟨x, hxAttach⟩
    have hxPiece :
        x ∈ localSideData.leftSidePiece ⟨itarget, htargetIdx⟩ := by
      have hx :=
        localSideData.incomingLeftAttachment_subset_leftSidePiece jlast hlast
          hxAttach
      simpa [itarget, hlast_succ] using hx
    have hxLeft : x ∈ S.leftStrip := by
      rw [hleft_eq]
      exact Or.inr (Set.mem_iUnion.2 ⟨⟨itarget, htargetIdx⟩, hxPiece⟩)
    have hxD : x ∈ Dstar := hterminalLeftCone_Dstar (htargetLeftCone hxPiece)
    exact ⟨x, hxD, hxLeft⟩
  have hDright : (Dstar ∩ S.rightStrip).Nonempty := by
    rcases vertexLocalPieces.incomingRightAttachment_nonempty jlast hlast with
      ⟨x, hxAttach⟩
    have hxPiece :
        x ∈ localSideData.rightSidePiece ⟨itarget, htargetIdx⟩ := by
      have hx :=
        localSideData.incomingRightAttachment_subset_rightSidePiece jlast hlast
          hxAttach
      simpa [itarget, hlast_succ] using hx
    have hxRight : x ∈ S.rightStrip := by
      rw [hright_eq]
      exact Or.inr (Set.mem_iUnion.2 ⟨⟨itarget, htargetIdx⟩, hxPiece⟩)
    have hxD : x ∈ Dstar := hterminalRightCone_Dstar (htargetRightCone hxPiece)
    exact ⟨x, hxD, hxRight⟩
  let W : Set (EuclideanSpace ℝ (Fin 2)) := S.leftStrip ∪ S.rightStrip ∪ Dstar
  have hWsubset : W ⊆ (K ∪ δ.carrier)ᶜ := by
    intro z hz
    rcases hz with hzLR | hzD
    · rcases hzLR with hzLeft | hzRight
      · exact left_avoids_forbidden hzLeft
      · exact right_avoids_forbidden hzRight
    · exact hDstar_subset hzD
  have hWopen : IsOpen W := by
    dsimp [W]
    exact (S.left_open.union S.right_open).union hDstar_open
  have hleftD : (S.leftStrip ∩ Dstar).Nonempty := by
    rcases hDleft with ⟨x, hxD, hxLeft⟩
    exact ⟨x, hxLeft, hxD⟩
  have hleftD_connected : IsConnected (S.leftStrip ∪ Dstar) :=
    IsConnected.union hleftD S.left_connected hDstar_connected
  have hmeetRight : ((S.leftStrip ∪ Dstar) ∩ S.rightStrip).Nonempty := by
    rcases hDright with ⟨x, hxD, hxRight⟩
    exact ⟨x, Or.inr hxD, hxRight⟩
  have hconn_alt : IsConnected ((S.leftStrip ∪ Dstar) ∪ S.rightStrip) :=
    IsConnected.union hmeetRight hleftD_connected S.right_connected
  have hWconnected : IsConnected W := by
    simpa [W, Set.union_assoc, Set.union_left_comm, Set.union_comm] using hconn_alt
  have hWnonempty : W.Nonempty := by
    rcases hDleft with ⟨x, hxD, hxLeft⟩
    exact ⟨x, Or.inl (Or.inl hxLeft)⟩
  have hWcomponent : ComplementComponent Wᶜ W := by
    refine ⟨hWnonempty, ?_, hWconnected, ?_⟩
    · intro z hz
      simpa using hz
    · intro C hCnon hCsub _hCconn _hWsub
      intro z hzC
      simpa using hCsub hzC
  have hWpath : PolygonallyPathConnected W :=
    OpenConnectedComponentPolygonallyConnected W W hWopen hWcomponent
  refine ⟨S, W, rfl, hWsubset, hWopen, hWconnected, hWpath, hDleft, hDright,
    ?_, ?_, S.relativeInterior_subset_collar, S.collar_open,
    S.collar_without_arc⟩
  · intro z hz
    exact Or.inl (Or.inl hz)
  · intro z hz
    exact Or.inl (Or.inr hz)

