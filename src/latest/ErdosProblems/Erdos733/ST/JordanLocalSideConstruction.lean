import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve
import ErdosProblems.Erdos733.ST.JordanLocalSideData
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.PositiveSeparation
import ErdosProblems.Erdos733.ST.JordanCurveSimultaneousCollarDataExists

open Classical
noncomputable section

-- [TABLET NODE: JordanLocalSideConstruction]
lemma JordanLocalSideConstruction (J : SimpleClosedPolygonalCurve) :
    Nonempty (JordanLocalSideData J) := by
-- BODY
  classical
  let Edge := {gamma : PolygonalArc // gamma ∈ J.edgeArcs}
  have edge_nonempty : Nonempty Edge := by
    rcases J.edgeArcs_nonempty with ⟨gamma, hgamma⟩
    exact ⟨⟨gamma, hgamma⟩⟩
  letI : Nonempty Edge := edge_nonempty
  let A : JordanCurveSimultaneousCollarData J :=
    Classical.choice (JordanCurveSimultaneousCollarDataExists J)
  let leftBlock : Edge → Set (EuclideanSpace ℝ (Fin 2)) := fun gamma =>
    (A.sideStrips gamma).leftStrip ∪ A.leftVertexSector gamma
  let rightBlock : Edge → Set (EuclideanSpace ℝ (Fin 2)) := fun gamma =>
    (A.sideStrips gamma).rightStrip ∪ A.rightVertexSector gamma
  let leftRegion : Set (EuclideanSpace ℝ (Fin 2)) := ⋃ gamma, leftBlock gamma
  let rightRegion : Set (EuclideanSpace ℝ (Fin 2)) := ⋃ gamma, rightBlock gamma
  have leftBlock_nonempty (gamma : Edge) : (leftBlock gamma).Nonempty := by
    exact (A.sideStrips gamma).left_connected.nonempty.mono (Set.subset_union_left)
  have rightBlock_nonempty (gamma : Edge) : (rightBlock gamma).Nonempty := by
    exact (A.sideStrips gamma).right_connected.nonempty.mono (Set.subset_union_left)
  have leftBlock_open (gamma : Edge) : IsOpen (leftBlock gamma) := by
    exact (A.sideStrips gamma).left_open.union (A.leftVertexSector_open gamma)
  have rightBlock_open (gamma : Edge) : IsOpen (rightBlock gamma) := by
    exact (A.sideStrips gamma).right_open.union (A.rightVertexSector_open gamma)
  have leftBlock_connected (gamma : Edge) : IsConnected (leftBlock gamma) := by
    apply IsConnected.union
      (s := (A.sideStrips gamma).leftStrip)
      (t := A.leftVertexSector gamma)
    · simpa [Set.inter_comm] using A.leftSector_meets_terminalStrip gamma
    · exact (A.sideStrips gamma).left_connected
    · exact A.leftVertexSector_connected gamma
  have rightBlock_connected (gamma : Edge) : IsConnected (rightBlock gamma) := by
    apply IsConnected.union
      (s := (A.sideStrips gamma).rightStrip)
      (t := A.rightVertexSector gamma)
    · simpa [Set.inter_comm] using A.rightSector_meets_terminalStrip gamma
    · exact (A.sideStrips gamma).right_connected
    · exact A.rightVertexSector_connected gamma
  have leftBlock_subset_complement (gamma : Edge) :
      leftBlock gamma ⊆ J.carrierᶜ := by
    rintro z (hz | hz)
    · exact A.leftStrip_subset_curve_complement gamma hz
    · exact A.leftVertexSector_subset_complement gamma hz
  have rightBlock_subset_complement (gamma : Edge) :
      rightBlock gamma ⊆ J.carrierᶜ := by
    rintro z (hz | hz)
    · exact A.rightStrip_subset_curve_complement gamma hz
    · exact A.rightVertexSector_subset_complement gamma hz
  have leftBlock_successor (gamma : Edge) :
      (leftBlock gamma ∩ leftBlock (J.successor gamma)).Nonempty := by
    rcases A.leftSector_meets_successorInitialStrip gamma with ⟨z, hzSector, hzStrip⟩
    exact ⟨z, Or.inr hzSector, Or.inl hzStrip⟩
  have rightBlock_successor (gamma : Edge) :
      (rightBlock gamma ∩ rightBlock (J.successor gamma)).Nonempty := by
    rcases A.rightSector_meets_successorInitialStrip gamma with ⟨z, hzSector, hzStrip⟩
    exact ⟨z, Or.inr hzSector, Or.inl hzStrip⟩
  have leftBlock_reachable (gamma : Edge) : ∀ n : ℕ,
      Relation.ReflTransGen
        (fun gamma delta : Edge => (leftBlock gamma ∩ leftBlock delta).Nonempty)
        gamma ((J.successor^[n]) gamma) := by
    intro n
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact Relation.ReflTransGen.tail ih
          (leftBlock_successor ((J.successor^[n]) gamma))
  have rightBlock_reachable (gamma : Edge) : ∀ n : ℕ,
      Relation.ReflTransGen
        (fun gamma delta : Edge => (rightBlock gamma ∩ rightBlock delta).Nonempty)
        gamma ((J.successor^[n]) gamma) := by
    intro n
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact Relation.ReflTransGen.tail ih
          (rightBlock_successor ((J.successor^[n]) gamma))
  have left_connected : IsConnected leftRegion := by
    apply IsConnected.iUnion_of_reflTransGen leftBlock_connected
    intro gamma delta
    obtain ⟨n, hn⟩ := J.successor_single_cycle gamma delta
    rw [← hn]
    exact leftBlock_reachable gamma n
  have right_connected : IsConnected rightRegion := by
    apply IsConnected.iUnion_of_reflTransGen rightBlock_connected
    intro gamma delta
    obtain ⟨n, hn⟩ := J.successor_single_cycle gamma delta
    rw [← hn]
    exact rightBlock_reachable gamma n
  have leftStrip_subset (gamma : Edge) :
      (A.sideStrips gamma).leftStrip ⊆ leftRegion := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨gamma, Or.inl hz⟩
  have rightStrip_subset (gamma : Edge) :
      (A.sideStrips gamma).rightStrip ⊆ rightRegion := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨gamma, Or.inl hz⟩
  have leftSector_subset (gamma : Edge) :
      A.leftVertexSector gamma ⊆ leftRegion := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨gamma, Or.inr hz⟩
  have rightSector_subset (gamma : Edge) :
      A.rightVertexSector gamma ⊆ rightRegion := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨gamma, Or.inr hz⟩
  have carrier_subset_left_closure : J.carrier ⊆ closure leftRegion := by
    rw [J.carrier_eq]
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨gamma, hzCarrier⟩
    by_cases hzInterior : z ∈ gamma.1.relativeInterior
    · exact closure_mono (leftStrip_subset gamma)
        ((A.sideStrips gamma).relativeInterior_subset_closure_left hzInterior)
    · have hzEnd : z ∈ ({gamma.1.source, gamma.1.target} : Set _) := by
        rw [gamma.1.relativeInterior_eq] at hzInterior
        by_contra hzNotEnd
        exact hzInterior ⟨hzCarrier, hzNotEnd⟩
      rcases hzEnd with hzSource | hzTarget
      · let predecessor : Edge := J.successor.symm gamma
        have predecessor_target : predecessor.1.target = gamma.1.source := by
          dsimp [predecessor]
          simpa using J.adjacent_endpoint (J.successor.symm gamma)
        rw [hzSource, ← predecessor_target]
        exact closure_mono (leftSector_subset predecessor)
          (A.vertex_mem_leftSector_closure predecessor)
      · rw [hzTarget]
        exact closure_mono (leftSector_subset gamma)
          (A.vertex_mem_leftSector_closure gamma)
  have carrier_subset_right_closure : J.carrier ⊆ closure rightRegion := by
    rw [J.carrier_eq]
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨gamma, hzCarrier⟩
    by_cases hzInterior : z ∈ gamma.1.relativeInterior
    · exact closure_mono (rightStrip_subset gamma)
        ((A.sideStrips gamma).relativeInterior_subset_closure_right hzInterior)
    · have hzEnd : z ∈ ({gamma.1.source, gamma.1.target} : Set _) := by
        rw [gamma.1.relativeInterior_eq] at hzInterior
        by_contra hzNotEnd
        exact hzInterior ⟨hzCarrier, hzNotEnd⟩
      rcases hzEnd with hzSource | hzTarget
      · let predecessor : Edge := J.successor.symm gamma
        have predecessor_target : predecessor.1.target = gamma.1.source := by
          dsimp [predecessor]
          simpa using J.adjacent_endpoint (J.successor.symm gamma)
        rw [hzSource, ← predecessor_target]
        exact closure_mono (rightSector_subset predecessor)
          (A.vertex_mem_rightSector_closure predecessor)
      · rw [hzTarget]
        exact closure_mono (rightSector_subset gamma)
          (A.vertex_mem_rightSector_closure gamma)
  let edgeStrips :
      ∀ gamma : Edge,
        {S : PolygonalSideStrips gamma.1 //
          S.leftStrip ⊆ leftRegion ∧ S.rightStrip ⊆ rightRegion} := fun gamma =>
    ⟨A.sideStrips gamma, leftStrip_subset gamma, rightStrip_subset gamma⟩
  have exterior_ray_access :
      ∃ w u : EuclideanSpace ℝ (Fin 2),
        u ≠ 0 ∧ (w ∈ leftRegion ∨ w ∈ rightRegion) ∧
          ∀ t : ℝ, 0 ≤ t → w + t • u ∈ J.carrierᶜ := by
    have edgeCarrier_subset (gamma : Edge) : gamma.1.carrier ⊆ J.carrier := by
      rw [J.carrier_eq]
      exact Set.subset_iUnion (fun delta : Edge => delta.1.carrier) gamma
    let VertexIndex := Sigma fun gamma : Edge => Fin gamma.1.vertices.length
    have vertexIndex_nonempty : Nonempty VertexIndex := by
      rcases J.edgeArcs_nonempty with ⟨gamma, hgamma⟩
      have hlength : 0 < gamma.vertices.length := by
        have hlen := gamma.length_ge_two
        omega
      exact ⟨⟨⟨gamma, hgamma⟩, ⟨0, hlength⟩⟩⟩
    have huniv : (Finset.univ : Finset VertexIndex).Nonempty := by
      letI : Nonempty VertexIndex := vertexIndex_nonempty
      exact Finset.univ_nonempty
    obtain ⟨q, -, hqmax⟩ := Finset.exists_max_image
      (Finset.univ : Finset VertexIndex)
      (fun q => q.1.1.vertices[q.2.1] 0) huniv
    let gamma : Edge := q.1
    let i : Fin gamma.1.vertices.length := q.2
    let v : EuclideanSpace ℝ (Fin 2) := gamma.1.vertices[i.1]
    have vertex_coordinate_le (delta : Edge)
        (k : Fin delta.1.vertices.length) :
        delta.1.vertices[k.1] 0 ≤ v 0 := by
      simpa [gamma, i, v] using hqmax ⟨delta, k⟩ (Finset.mem_univ _)
    have curve_coordinate_le (z : EuclideanSpace ℝ (Fin 2))
        (hz : z ∈ J.carrier) : z 0 ≤ v 0 := by
      rw [J.carrier_eq] at hz
      rcases Set.mem_iUnion.mp hz with ⟨delta, hzdelta⟩
      rw [delta.1.carrier_eq] at hzdelta
      rcases hzdelta with ⟨j, hj, hzseg⟩
      have hleft := vertex_coordinate_le delta
        ⟨j, Nat.lt_of_succ_lt hj⟩
      have hright := vertex_coordinate_le delta ⟨j + 1, hj⟩
      rw [segment_eq_image] at hzseg
      rcases hzseg with ⟨p, hp, rfl⟩
      rcases hp with ⟨hp0, hp1⟩
      change 0 ≤ p at hp0
      change p ≤ 1 at hp1
      change (1 - p) * delta.1.vertices[j] 0 +
        p * delta.1.vertices[j + 1] 0 ≤ v 0
      nlinarith
    let u : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    have u_first : u 0 = 1 := by
      simp [u]
    have u_ne_zero : u ≠ 0 := by
      intro hu
      have hu0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hu
      simp [u] at hu0
    have ray_complement (epsilon : ℝ) (hepsilon : 0 < epsilon) :
        ∀ t : ℝ, 0 ≤ t → v + epsilon • u + t • u ∈ J.carrierᶜ := by
      intro t ht hcarrier
      have hle := curve_coordinate_le _ hcarrier
      have hcoordinate :
          (v + epsilon • u + t • u) 0 = v 0 + epsilon + t := by
        change v 0 + epsilon * u 0 + t * u 0 = v 0 + epsilon + t
        rw [u_first]
        ring
      rw [hcoordinate] at hle
      linarith
    have half_step_mem_ball (center : EuclideanSpace ℝ (Fin 2))
        (r : ℝ) (hr : 0 < r) :
        center + (r / 2) • u ∈ Metric.ball center r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp [u, norm_smul]
      rw [abs_of_pos hr]
      linarith
    by_cases hiSource : i.1 = 0
    · have hsourceIdx : 0 < gamma.1.vertices.length := by
        have hlen := gamma.1.length_ge_two
        omega
      have hsourceVertex : gamma.1.vertices[0] = gamma.1.source := by
        have hget : gamma.1.vertices[0]? = some gamma.1.vertices[0] :=
          List.getElem?_eq_getElem hsourceIdx
        rw [← List.head?_eq_getElem?, gamma.1.source_eq_head] at hget
        exact Option.some.inj hget.symm
      have hvSource : v = gamma.1.source := by
        simpa [v, hiSource] using hsourceVertex
      let predecessor : Edge := J.successor.symm gamma
      have predecessor_target : predecessor.1.target = gamma.1.source := by
        dsimp [predecessor]
        simpa using J.adjacent_endpoint (J.successor.symm gamma)
      have hvPredecessor : v = predecessor.1.target :=
        hvSource.trans predecessor_target.symm
      let r : ℝ := A.vertexRadius predecessor
      have hr : 0 < r := A.vertexRadius_pos predecessor
      let epsilon : ℝ := r / 2
      let w : EuclideanSpace ℝ (Fin 2) := v + epsilon • u
      have hwball : w ∈ Metric.ball predecessor.1.target r := by
        rw [← hvPredecessor]
        exact half_step_mem_ball v r hr
      have hwoff : w ∉ J.carrier := by
        have hw := ray_complement epsilon (half_pos hr) 0 le_rfl
        simpa [w] using hw
      have hwSector :
          w ∈ A.leftVertexSector predecessor ∪
            A.rightVertexSector predecessor := by
        rw [← A.vertexDisk_complement_partition predecessor]
        exact ⟨hwball, hwoff⟩
      refine ⟨w, u, u_ne_zero, ?_, ?_⟩
      · rcases hwSector with hwLeft | hwRight
        · exact Or.inl (leftSector_subset predecessor hwLeft)
        · exact Or.inr (rightSector_subset predecessor hwRight)
      · intro t ht
        simpa [w] using ray_complement epsilon (half_pos hr) t ht
    · by_cases hiTarget : i.1 + 1 = gamma.1.vertices.length
      · have htargetIdx :
            gamma.1.vertices.length - 1 < gamma.1.vertices.length := by
          have hlen := gamma.1.length_ge_two
          omega
        have hiLast : i.1 = gamma.1.vertices.length - 1 := by omega
        have htargetVertex :
            gamma.1.vertices[gamma.1.vertices.length - 1] =
              gamma.1.target := by
          have hget :
              gamma.1.vertices[gamma.1.vertices.length - 1]? =
                some gamma.1.vertices[gamma.1.vertices.length - 1] :=
            List.getElem?_eq_getElem htargetIdx
          rw [← List.getLast?_eq_getElem?, gamma.1.target_eq_last] at hget
          exact Option.some.inj hget.symm
        have hvTarget : v = gamma.1.target := by
          simpa [v, hiLast] using htargetVertex
        let r : ℝ := A.vertexRadius gamma
        have hr : 0 < r := A.vertexRadius_pos gamma
        let epsilon : ℝ := r / 2
        let w : EuclideanSpace ℝ (Fin 2) := v + epsilon • u
        have hwball : w ∈ Metric.ball gamma.1.target r := by
          rw [← hvTarget]
          exact half_step_mem_ball v r hr
        have hwoff : w ∉ J.carrier := by
          have hw := ray_complement epsilon (half_pos hr) 0 le_rfl
          simpa [w] using hw
        have hwSector :
            w ∈ A.leftVertexSector gamma ∪ A.rightVertexSector gamma := by
          rw [← A.vertexDisk_complement_partition gamma]
          exact ⟨hwball, hwoff⟩
        refine ⟨w, u, u_ne_zero, ?_, ?_⟩
        · rcases hwSector with hwLeft | hwRight
          · exact Or.inl (leftSector_subset gamma hwLeft)
          · exact Or.inr (rightSector_subset gamma hwRight)
        · intro t ht
          simpa [w] using ray_complement epsilon (half_pos hr) t ht
      · have hiPos : 0 < i.1 := Nat.pos_of_ne_zero hiSource
        have hiNext : i.1 + 1 < gamma.1.vertices.length := by
          have hiLt := i.2
          omega
        let r : ℝ := (A.controlRadii gamma).radius i
        have hr : 0 < r := (A.controlRadii gamma).radius_pos i
        let epsilon : ℝ := r / 2
        let w : EuclideanSpace ℝ (Fin 2) := v + epsilon • u
        have hwball : w ∈ Metric.ball gamma.1.vertices[i.1] r := by
          change v + (r / 2) • u ∈ Metric.ball v r
          exact half_step_mem_ball v r hr
        have hwVertexDisk :
            w ∈ (A.vertexLocalPieces gamma).vertexDisk i := by
          rw [(A.vertexLocalPieces gamma).vertexDisk_eq i]
          exact hwball
        have hwVertexCollar :
            w ∈ (A.localSideData gamma).vertexCollar i := by
          rw [(A.localSideData gamma).interior_vertexCollar_eq_vertexDisk i
            hiPos hiNext]
          exact hwVertexDisk
        have hwoff : w ∉ J.carrier := by
          have hw := ray_complement epsilon (half_pos hr) 0 le_rfl
          simpa [w] using hw
        have hwoffRelativeInterior : w ∉ gamma.1.relativeInterior := by
          intro hwInterior
          rw [gamma.1.relativeInterior_eq] at hwInterior
          exact hwoff (edgeCarrier_subset gamma hwInterior.1)
        have hwPieces :
            w ∈ (A.localSideData gamma).leftSidePiece i ∪
              (A.localSideData gamma).rightSidePiece i := by
          rw [← (A.localSideData gamma).vertexCollar_without_arc i]
          exact ⟨hwVertexCollar, hwoffRelativeInterior⟩
        refine ⟨w, u, u_ne_zero, ?_, ?_⟩
        · rcases hwPieces with hwLeft | hwRight
          · exact Or.inl (leftStrip_subset gamma
              (A.localLeftPiece_subset_leftStrip gamma i hwLeft))
          · exact Or.inr (rightStrip_subset gamma
              (A.localRightPiece_subset_rightStrip gamma i hwRight))
        · intro t ht
          simpa [w] using ray_complement epsilon (half_pos hr) t ht
  refine ⟨
    { leftRegion := leftRegion
      rightRegion := rightRegion
      left_nonempty := left_connected.nonempty
      right_nonempty := right_connected.nonempty
      left_open := isOpen_iUnion leftBlock_open
      right_open := isOpen_iUnion rightBlock_open
      left_connected := left_connected
      right_connected := right_connected
      left_subset_complement := Set.iUnion_subset leftBlock_subset_complement
      right_subset_complement := Set.iUnion_subset rightBlock_subset_complement
      carrier_subset_left_closure := carrier_subset_left_closure
      carrier_subset_right_closure := carrier_subset_right_closure
      edge_strips := edgeStrips
      left_vertex_sector := ?_
      right_vertex_sector := ?_
      transverse_segment := by
        let gamma : Edge := Classical.choice edge_nonempty
        have hfirst : 0 + 1 < gamma.1.vertices.length := by
          have hlen := gamma.1.length_ge_two
          omega
        let sep :=
          (A.compatibleTubes gamma).orientedTubes.toPolygonalArcCollarSeparatedTubeData
        let d : ℝ := dist gamma.1.vertices[0] gamma.1.vertices[1]
        have hvertices_ne : gamma.1.vertices[0] ≠ gamma.1.vertices[1] := by
          intro h
          have hidx := (gamma.1.simple_vertices.getElem_inj_iff).mp h
          omega
        have hd : 0 < d := by
          exact dist_pos.mpr hvertices_ne
        let beta : ℝ := (A.controlRadii gamma).radius ⟨0, by omega⟩ / d
        have hbeta_pos : 0 < beta := by
          simpa [beta, d] using
            (A.middleSegments gamma).left_parameter_pos 0 hfirst
        have hbeta_lt_one : beta < 1 := by
          have hleft :=
            (A.middleSegments gamma).left_parameter_lt_right_parameter 0 hfirst
          have hright :=
            (A.middleSegments gamma).right_parameter_lt_one 0 hfirst
          simpa [beta, d] using hleft.trans hright
        have hlower_beta : sep.lowerParam 0 hfirst < beta := by
          simpa [sep, beta, d] using
            sep.lowerParam_lt_left_parameter 0 hfirst
        have hbeta_upper : beta < sep.upperParam 0 hfirst := by
          have hleft :=
            (A.middleSegments gamma).left_parameter_lt_right_parameter 0 hfirst
          have hright := sep.right_parameter_lt_upperParam 0 hfirst
          simpa [sep, beta, d] using hleft.trans hright
        have hinfinite :
            ((AffineMap.lineMap gamma.1.vertices[0] gamma.1.vertices[1]) ''
              Set.Ioo (sep.lowerParam 0 hfirst) beta).Infinite := by
          apply Set.Infinite.image
            (AffineMap.lineMap_injective ℝ hvertices_ne).injOn
          exact Set.Ioo_infinite hlower_beta
        obtain ⟨x, ⟨t, ht, htx⟩, hxNotPoint⟩ :=
          hinfinite.exists_notMem_finset A.presentation.points
        have ht_pos : 0 < t := (sep.lowerParam_pos 0 hfirst).trans ht.1
        have ht_one : t < 1 := ht.2.trans hbeta_lt_one
        have ht_upper : t < sep.upperParam 0 hfirst := ht.2.trans hbeta_upper
        have hxFirstOpen :
            x ∈ openSegment ℝ gamma.1.vertices[0] gamma.1.vertices[1] := by
          rw [← htx]
          exact lineMap_mem_openSegment ℝ _ _ ⟨ht_pos, ht_one⟩
        have hxInterior : x ∈ gamma.1.relativeInterior :=
          PolygonalArcOpenSegmentSubsetRelativeInterior gamma.1 0 hfirst hxFirstOpen
        let n := sep.normal 0 hfirst
        have hn_norm : ‖n‖ = d := by
          simpa [n, d] using sep.normal_norm_eq_segment_length 0 hfirst
        have hn_ne : n ≠ 0 := by
          exact norm_pos_iff.mp (hn_norm.trans_gt hd)
        have htd_lt_radius :
            t * d < (A.controlRadii gamma).radius ⟨0, by omega⟩ := by
          exact (lt_div_iff₀ hd).mp (by simpa [beta] using ht.2)
        let clearance : ℝ :=
          ((A.controlRadii gamma).radius ⟨0, by omega⟩ - t * d) / d
        have hclearance : 0 < clearance := by
          exact div_pos (sub_pos.mpr htd_lt_radius) hd
        let h : ℝ := min (sep.halfWidth 0 hfirst) clearance / 2
        have hh_pos : 0 < h := by
          exact half_pos (lt_min (sep.halfWidth_pos 0 hfirst) hclearance)
        have hh_width : h < sep.halfWidth 0 hfirst := by
          have hmin := min_le_left (sep.halfWidth 0 hfirst) clearance
          dsimp [h]
          linarith [sep.halfWidth_pos 0 hfirst]
        have hh_clearance : h < clearance := by
          have hmin := min_le_right (sep.halfWidth 0 hfirst) clearance
          dsimp [h]
          linarith [hclearance]
        let a := x + h • n
        let b := x - h • n
        have offset_mem_ball (r : ℝ) (hr : |r| ≤ h) :
            x + r • n ∈ Metric.ball gamma.1.vertices[0]
              ((A.controlRadii gamma).radius ⟨0, by omega⟩) := by
          rw [Metric.mem_ball]
          calc
            dist (x + r • n) gamma.1.vertices[0] ≤
                dist (x + r • n) x + dist x gamma.1.vertices[0] :=
              dist_triangle _ _ _
            _ = |r| * d + t * d := by
              have hoff : dist (x + r • n) x = |r| * d := by
                rw [dist_eq_norm]
                have : x + r • n - x = r • n := by module
                rw [this, norm_smul, Real.norm_eq_abs, hn_norm]
              have hxsource : dist x gamma.1.vertices[0] = t * d := by
                rw [← htx, dist_eq_norm, AffineMap.lineMap_apply_module']
                have hsub :
                    t • (gamma.1.vertices[1] - gamma.1.vertices[0]) +
                        gamma.1.vertices[0] - gamma.1.vertices[0] =
                      t • (gamma.1.vertices[1] - gamma.1.vertices[0]) := by
                  module
                rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
                simp [d, dist_eq_norm, norm_sub_rev]
              rw [hoff, hxsource]
            _ ≤ h * d + t * d := by gcongr
            _ < (A.controlRadii gamma).radius ⟨0, by omega⟩ := by
              have hmul : h * d < clearance * d :=
                mul_lt_mul_of_pos_right hh_clearance hd
              dsimp [clearance] at hmul
              rw [div_mul_cancel₀ _ (ne_of_gt hd)] at hmul
              linarith
        have pos_offset_left (r : ℝ) (hr0 : 0 < r) (hrh : r ≤ h) :
            x + r • n ∈ (A.sideStrips gamma).leftStrip := by
          apply A.localLeftPiece_subset_leftStrip gamma ⟨0, by omega⟩
          apply
            (A.localSideData gamma).outgoingLeftAttachment_subset_leftSidePiece
              0 hfirst
          rw [(A.vertexLocalPieces gamma).outgoingLeftAttachment_eq 0 hfirst]
          constructor
          · rw [(A.vertexLocalPieces gamma).vertexDisk_eq]
            exact offset_mem_ball r (by rw [abs_of_pos hr0]; exact hrh)
          · rw [sep.leftHalf_eq 0 hfirst]
            refine ⟨t, ⟨ht.1, ht_upper⟩, r,
              ⟨hr0, hrh.trans_lt hh_width⟩, ?_⟩
            simpa [n] using congrArg (fun z => z + r • n) htx.symm
        have neg_offset_right (r : ℝ) (hrh : -h ≤ r) (hr0 : r < 0) :
            x + r • n ∈ (A.sideStrips gamma).rightStrip := by
          apply A.localRightPiece_subset_rightStrip gamma ⟨0, by omega⟩
          apply
            (A.localSideData gamma).outgoingRightAttachment_subset_rightSidePiece
              0 hfirst
          rw [(A.vertexLocalPieces gamma).outgoingRightAttachment_eq 0 hfirst]
          constructor
          · rw [(A.vertexLocalPieces gamma).vertexDisk_eq]
            exact offset_mem_ball r (by rw [abs_of_neg hr0]; linarith)
          · rw [sep.rightHalf_eq 0 hfirst]
            refine ⟨t, ⟨ht.1, ht_upper⟩, r,
              ⟨by linarith [hh_width], hr0⟩, ?_⟩
            simpa [n] using congrArg (fun z => z + r • n) htx.symm
        have haLeftStrip : a ∈ (A.sideStrips gamma).leftStrip := by
          simpa [a] using pos_offset_left h hh_pos le_rfl
        have hbRightStrip : b ∈ (A.sideStrips gamma).rightStrip := by
          have hneg := neg_offset_right (-h) le_rfl (neg_neg_of_pos hh_pos)
          simpa [b, sub_eq_add_neg] using hneg
        have haLeft : a ∈ leftRegion := leftStrip_subset gamma haLeftStrip
        have hbRight : b ∈ rightRegion := rightStrip_subset gamma hbRightStrip
        have hab : a ≠ b := by
          intro hab
          have hsmul : h • n = (-h) • n := by
            apply add_left_cancel (a := x)
            simpa [a, b, sub_eq_add_neg] using hab
          have hscalar : h = -h := smul_left_injective ℝ hn_ne hsmul
          linarith
        have chord_lineMap (q : ℝ) :
            AffineMap.lineMap a b q = x + ((1 - 2 * q) * h) • n := by
          simp only [AffineMap.lineMap_apply_module']
          dsimp [a, b]
          module
        have hxOpenAB : x ∈ openSegment ℝ a b := by
          have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
          have hxEq : AffineMap.lineMap a b (1 / 2 : ℝ) = x := by
            rw [chord_lineMap]
            norm_num
          rw [← hxEq]
          exact lineMap_mem_openSegment ℝ a b hhalf
        have hxGamma : x ∈ gamma.1.carrier := by
          rw [gamma.1.relativeInterior_eq] at hxInterior
          exact hxInterior.1
        have hxJ : x ∈ J.carrier := by
          rw [J.carrier_eq]
          exact Set.mem_iUnion.mpr ⟨gamma, hxGamma⟩
        have chord_curve_unique (z : EuclideanSpace ℝ (Fin 2))
            (hzChord : z ∈ segment ℝ a b) (hzJ : z ∈ J.carrier) : z = x := by
          rw [segment_eq_image_lineMap] at hzChord
          rcases hzChord with ⟨q, hq, rfl⟩
          rw [chord_lineMap] at hzJ ⊢
          let r : ℝ := (1 - 2 * q) * h
          have hrabs : |r| ≤ h := by
            have hfactor : |1 - 2 * q| ≤ 1 := by
              rw [abs_le]
              constructor <;> linarith [hq.1, hq.2]
            dsimp [r]
            rw [abs_mul, abs_of_pos hh_pos]
            nlinarith
          by_cases hrzero : r = 0
          · simp [r, hrzero]
          · rcases lt_or_gt_of_ne hrzero with hrneg | hrpos
            · have hright := neg_offset_right r (abs_le.mp hrabs).1 hrneg
              exfalso
              exact (A.rightStrip_subset_curve_complement gamma hright) (by
                simpa [r] using hzJ)
            · have hleft := pos_offset_left r hrpos (abs_le.mp hrabs).2
              exfalso
              exact (A.leftStrip_subset_curve_complement gamma hleft) (by
                simpa [r] using hzJ)
        have chord_curve_eq : segment ℝ a b ∩ J.carrier = {x} := by
          apply Set.Subset.antisymm
          · intro z hz
            simpa using chord_curve_unique z hz.1 hz.2
          · intro z hz
            have hzx : z = x := by simpa using hz
            subst z
            exact ⟨openSegment_subset_segment ℝ a b hxOpenAB, hxJ⟩
        let K : FinitePolygonalSet := A.presentation
        have hKcarrier : K.carrier = J.carrier := by
          exact A.presentation_carrier_eq
        have hxNotKPoint : x ∉ K.points := by
          simpa [K] using hxNotPoint
        have hxK : x ∈ K.carrier := by
          rw [hKcarrier]
          exact hxJ
        rw [K.carrier_eq] at hxK
        rcases hxK with hxListed | hxSegment
        · exact False.elim (hxNotKPoint hxListed)
        rcases Set.mem_iUnion.mp hxSegment with ⟨s, hxsClosed⟩
        have hsMem : s.1 ∈ K.segments := s.2
        have hsEnds := K.segment_endpoints_listed s.1 hsMem
        have hsLeftNe : s.1.1 ≠ x := by
          intro heq
          apply hxNotKPoint
          simpa [heq] using hsEnds.1
        have hsRightNe : s.1.2 ≠ x := by
          intro heq
          apply hxNotKPoint
          simpa [heq] using hsEnds.2
        have hxOpenS : x ∈ openSegment ℝ s.1.1 s.1.2 :=
          mem_openSegment_of_ne_left_right hsLeftNe hsRightNe hxsClosed
        have listedSegment_subset_carrier
            (u : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
            (hu : u ∈ K.segments) : segment ℝ u.1 u.2 ⊆ K.carrier := by
          rw [K.carrier_eq]
          intro z hz
          exact Or.inr (Set.mem_iUnion.mpr ⟨⟨u, hu⟩, hz⟩)
        have point_avoidance :
            ∀ p : EuclideanSpace ℝ (Fin 2),
              p ∈ K.points → p ∉ segment ℝ a b := by
          intro p hpPoint hpChord
          have hpK : p ∈ K.carrier := by
            rw [K.carrier_eq]
            exact Or.inl hpPoint
          have hpJ : p ∈ J.carrier := by rwa [← hKcarrier]
          have hpx := chord_curve_unique p hpChord hpJ
          subst p
          exact hxNotKPoint hpPoint
        have no_overlap :
            ∀ u : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
              u ∈ K.segments →
                ¬ ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
                  segment ℝ p q ⊆ segment ℝ a b ∩ segment ℝ u.1 u.2 := by
          intro u hu
          rintro ⟨p, q, hpq, hpqSub⟩
          have hpBoth := hpqSub (left_mem_segment ℝ p q)
          have hqBoth := hpqSub (right_mem_segment ℝ p q)
          have hpK := listedSegment_subset_carrier u hu hpBoth.2
          have hqK := listedSegment_subset_carrier u hu hqBoth.2
          have hpJ : p ∈ J.carrier := by rwa [← hKcarrier]
          have hqJ : q ∈ J.carrier := by rwa [← hKcarrier]
          exact hpq ((chord_curve_unique p hpBoth.1 hpJ).trans
            (chord_curve_unique q hqBoth.1 hqJ).symm)
        have parallel_open_overlap
            (u v p : EuclideanSpace ℝ (Fin 2))
            (huv : u ≠ v)
            (hpab : p ∈ openSegment ℝ a b)
            (hpuv : p ∈ openSegment ℝ u v)
            (hparallel : ∃ c : ℝ, v - u = c • (b - a)) :
            ∃ q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
              segment ℝ p q ⊆ segment ℝ a b ∩ segment ℝ u v := by
          rcases hparallel with ⟨c, hc⟩
          have hpabClosed : p ∈ segment ℝ a b :=
            openSegment_subset_segment ℝ a b hpab
          have hpuvClosed : p ∈ segment ℝ u v :=
            openSegment_subset_segment ℝ u v hpuv
          rw [openSegment_eq_image_lineMap] at hpab hpuv
          rcases hpab with ⟨r, hr, hrp⟩
          rcases hpuv with ⟨w, hw, hwp⟩
          let U : Set ℝ := Set.Ioo 0 1 ∩
            (fun q : ℝ => r + c * (q - w)) ⁻¹' Set.Ioo 0 1
          have hUopen : IsOpen U := by
            apply isOpen_Ioo.inter
            apply isOpen_Ioo.preimage
            fun_prop
          have hwU : w ∈ U := by
            refine ⟨hw, ?_⟩
            simpa using hr
          rcases mem_nhds_iff_exists_Ioo_subset.mp (hUopen.mem_nhds hwU) with
            ⟨l, z, hwz, hsub⟩
          obtain ⟨w', hww', hw'z⟩ := exists_between hwz.2
          have hw'U : w' ∈ U := hsub ⟨hwz.1.trans hww', hw'z⟩
          let q : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap u v w'
          have hq_uv : q ∈ openSegment ℝ u v :=
            lineMap_mem_openSegment ℝ u v hw'U.1
          have hq_ab : q ∈ openSegment ℝ a b := by
            have hqeq : AffineMap.lineMap u v w' =
                AffineMap.lineMap a b (r + c * (w' - w)) := by
              have hbase :
                  w • (c • (b - a)) + u = r • (b - a) + a := by
                rw [← hc]
                simpa only [AffineMap.lineMap_apply_module'] using
                  hwp.trans hrp.symm
              have huEq :
                  u = r • (b - a) + a - w • (c • (b - a)) := by
                calc
                  u = (w • (c • (b - a)) + u) -
                      w • (c • (b - a)) := by module
                  _ = (r • (b - a) + a) - w • (c • (b - a)) := by
                    rw [hbase]
              rw [AffineMap.lineMap_apply_module',
                AffineMap.lineMap_apply_module']
              rw [hc, huEq]
              module
            rw [show q = AffineMap.lineMap a b (r + c * (w' - w)) by
              simpa [q] using hqeq]
            exact lineMap_mem_openSegment ℝ a b hw'U.2
          have hpq : p ≠ q := by
            intro hpq
            apply ne_of_lt hww'
            apply AffineMap.lineMap_injective ℝ huv
            rw [hwp]
            simpa [q] using hpq
          exact ⟨q, hpq, fun y hy =>
            ⟨(convex_segment a b).segment_subset hpabClosed
                (openSegment_subset_segment ℝ a b hq_ab) hy,
              (convex_segment u v).segment_subset hpuvClosed
                (openSegment_subset_segment ℝ u v hq_uv) hy⟩⟩
        have transversality :
            ∀ u : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
              u ∈ K.segments →
                ∀ p : EuclideanSpace ℝ (Fin 2),
                  p ∈ openSegment ℝ a b →
                    p ∈ openSegment ℝ u.1 u.2 →
                      ¬ ∃ c : ℝ, u.2 - u.1 = c • (b - a) := by
          intro u hu p hpab hpu hparallel
          rcases parallel_open_overlap u.1 u.2 p
              (K.segment_nondegenerate u hu) hpab hpu hparallel with
            ⟨q, hpq, hpqSub⟩
          exact no_overlap u hu ⟨p, q, hpq, hpqSub⟩
        have intersection_count :
            ∀ u : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
              u ∈ K.segments →
                Set.ncard (openSegment ℝ a b ∩ openSegment ℝ u.1 u.2) =
                  if u = s.1 then 1 else 0 := by
          intro u hu
          by_cases hus : u = s.1
          · subst u
            rw [if_pos rfl]
            have hinter :
                openSegment ℝ a b ∩ openSegment ℝ s.1.1 s.1.2 = {x} := by
              apply Set.Subset.antisymm
              · intro p hp
                have hpK := listedSegment_subset_carrier s.1 hsMem
                  (openSegment_subset_segment ℝ s.1.1 s.1.2 hp.2)
                have hpJ : p ∈ J.carrier := by rwa [← hKcarrier]
                simpa using chord_curve_unique p
                  (openSegment_subset_segment ℝ a b hp.1) hpJ
              · intro p hp
                have hpx : p = x := by simpa using hp
                subst p
                exact ⟨hxOpenAB, hxOpenS⟩
            rw [hinter]
            exact Set.ncard_singleton x
          · rw [if_neg hus]
            have hinter : openSegment ℝ a b ∩ openSegment ℝ u.1 u.2 = ∅ := by
              apply Set.eq_empty_iff_forall_notMem.mpr
              intro p hp
              have hpK := listedSegment_subset_carrier u hu
                (openSegment_subset_segment ℝ u.1 u.2 hp.2)
              have hpJ : p ∈ J.carrier := by rwa [← hKcarrier]
              have hpx := chord_curve_unique p
                (openSegment_subset_segment ℝ a b hp.1) hpJ
              have hxU : x ∈ segment ℝ u.1 u.2 := by
                rw [← hpx]
                exact openSegment_subset_segment ℝ u.1 u.2 hp.2
              exact hxNotKPoint
                (K.segment_intersections_listed s.1 u hsMem hu
                  (fun hsu => hus hsu.symm)
                  x hxsClosed hxU)
            rw [hinter]
            exact Set.ncard_empty (EuclideanSpace ℝ (Fin 2))
        exact ⟨gamma, K, hKcarrier, s.1, hsMem, a, b, x,
          haLeft, hbRight, hab, hxInterior, hxOpenAB, hxOpenS, chord_curve_eq,
          point_avoidance, no_overlap, transversality, intersection_count⟩
      exterior_ray_access := exterior_ray_access }⟩
  · intro gamma
    refine ⟨A.leftVertexSector gamma,
      A.leftVertexSector_nonempty gamma,
      A.leftVertexSector_open gamma,
      A.leftVertexSector_connected gamma,
      A.leftVertexSector_subset_complement gamma,
      leftSector_subset gamma, ?_, ?_,
      A.vertex_mem_leftSector_closure gamma⟩
    · simpa [edgeStrips] using A.leftSector_meets_terminalStrip gamma
    · simpa [edgeStrips] using A.leftSector_meets_successorInitialStrip gamma
  · intro gamma
    refine ⟨A.rightVertexSector gamma,
      A.rightVertexSector_nonempty gamma,
      A.rightVertexSector_open gamma,
      A.rightVertexSector_connected gamma,
      A.rightVertexSector_subset_complement gamma,
      rightSector_subset gamma, ?_, ?_,
      A.vertex_mem_rightSector_closure gamma⟩
    · simpa [edgeStrips] using A.rightSector_meets_terminalStrip gamma
    · simpa [edgeStrips] using A.rightSector_meets_successorInitialStrip gamma
