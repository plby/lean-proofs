import ErdosProblems.Erdos733.ST.PolygonalReplacementCircleOutsideNearSupportingCoordinate
import ErdosProblems.Erdos733.ST.PolygonalReplacementCircularTargetEndpointCenterOrder
import ErdosProblems.Erdos733.ST.PolygonalReplacementCircularTargetRetainedPoint

open Classical
noncomputable section

universe u


-- [TABLET NODE: PolygonalReplacementCircularTargetRetainedHalfspacePoint]
lemma PolygonalReplacementCircularTargetRetainedHalfspacePoint {V : Type u}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (residualPieceData :
      PolygonalReplacementResidualPieceData G D controlDisks boundaryPoints
        edgeEndpoints)
    (i : residualPieceData.pieceIndex)
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)}
    (hcircular :
      0 < r ∧
        Continuous γ ∧ Function.Injective γ ∧
        (∀ t, dist (γ t) c = r) ∧
        γ ⟨0, by simp⟩ = D.edgeSource (residualPieceData.owner i) ∧
        γ ⟨1, by simp⟩ = D.edgeTarget (residualPieceData.owner i) ∧
        D.edgeCarrier (residualPieceData.owner i) = Set.range γ ∧
        D.edgeRelativeInterior (residualPieceData.owner i) =
          Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
            γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)) :
    (∀ (v : V) (ε : ℝ),
        v ∈ (residualPieceData.owner i).1 →
          residualPieceData.target i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
          residualPieceData.target i ∈
            D.edgeCarrier (residualPieceData.owner i) →
          0 < ε →
            ∃ u : Set.Icc (0 : ℝ) 1,
              residualPieceData.sourceParam i ≤ u ∧
                u < residualPieceData.targetParam i ∧
                  residualPieceData.edgeParam (residualPieceData.owner i) u ∈
                    Metric.ball (residualPieceData.target i) ε ∧
                  (controlDisks.vertexRadius v) ^ 2 ≤
                    inner ℝ
                      (residualPieceData.edgeParam (residualPieceData.owner i) u -
                        D.vertexPlacement v)
                      (residualPieceData.target i - D.vertexPlacement v)) ∧
      (∀ (x : {p // p ∈ D.intersectionPoints}) (ε : ℝ),
        x.1 ∈ D.edgeRelativeInterior (residualPieceData.owner i) →
          residualPieceData.target i ∈
            Metric.sphere x.1 (controlDisks.intersectionRadius x) →
          residualPieceData.target i ∈
            D.edgeCarrier (residualPieceData.owner i) →
          0 < ε →
            ∃ u : Set.Icc (0 : ℝ) 1,
              residualPieceData.sourceParam i ≤ u ∧
                u < residualPieceData.targetParam i ∧
                  residualPieceData.edgeParam (residualPieceData.owner i) u ∈
                    Metric.ball (residualPieceData.target i) ε ∧
                  (controlDisks.intersectionRadius x) ^ 2 ≤
                    inner ℝ
                      (residualPieceData.edgeParam (residualPieceData.owner i) u -
                        x.1)
                      (residualPieceData.target i - x.1)) := by
-- BODY
  classical
  let e : G.edgeFinset := residualPieceData.owner i
  let s : EuclideanSpace ℝ (Fin 2) := residualPieceData.target i
  let edgeAtOwner :
      Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) :=
    residualPieceData.edgeParam e
  have retained_point :=
    PolygonalReplacementCircularTargetRetainedPoint G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData i hcircular
  have center_order :=
    PolygonalReplacementCircularTargetEndpointCenterOrder G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData i hcircular
  have build_for_center :
      ∀ (A : EuclideanSpace ℝ (Fin 2)) (R : ℝ),
        0 < R →
          A ∈ Metric.sphere c r →
          s ∈ Metric.sphere A R →
          s ∈ Metric.sphere c r →
          (∀ u : Set.Icc (0 : ℝ) 1,
            (∀ v : V, edgeAtOwner u ∉
              Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v)) →
            (∀ x : {p // p ∈ D.intersectionPoints}, edgeAtOwner u ∉
              Metric.ball x.1 (controlDisks.intersectionRadius x)) →
            edgeAtOwner u ∉ Metric.ball A R) →
          ∀ ε : ℝ, 0 < ε →
            ∃ u : Set.Icc (0 : ℝ) 1,
              residualPieceData.sourceParam i ≤ u ∧
                u < residualPieceData.targetParam i ∧
                  edgeAtOwner u ∈ Metric.ball s ε ∧
                    R ^ 2 ≤ inner ℝ (edgeAtOwner u - A) (s - A) := by
    intro A R hR hAowner hsA hsowner havoid ε hε
    have hs_dist_A : dist s A = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hsA
    obtain ⟨B, hB0⟩ :
        ∃ B : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
          B 0 = (R⁻¹ : ℝ) • (s - A) := by
      let v : Fin 2 → EuclideanSpace ℝ (Fin 2) := fun j =>
        if j = 0 then (R⁻¹ : ℝ) • (s - A) else 0
      have hv_norm : ‖(R⁻¹ : ℝ) • (s - A)‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
        have hnorm : ‖s - A‖ = R := by
          simpa [dist_eq_norm] using hs_dist_A
        rw [hnorm]
        field_simp [hR.ne']
      have hv : Orthonormal ℝ (({0} : Set (Fin 2)).domRestrict v) := by
        rw [orthonormal_iff_ite]
        intro j k
        rcases j with ⟨j, hj⟩
        rcases k with ⟨k, hk⟩
        have hj0 : j = 0 := by simpa using hj
        have hk0 : k = 0 := by simpa using hk
        subst hj0
        subst hk0
        simp [v, hv_norm]
      have hcard :
          Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) =
            Fintype.card (Fin 2) := by
        simp
      rcases Orthonormal.exists_orthonormalBasis_extension_of_card_eq
          (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 2))
          (ι := Fin 2) hcard (s := ({0} : Set (Fin 2))) hv with
        ⟨B, hB⟩
      refine ⟨B, ?_⟩
      simpa [v] using hB 0 (by simp)
    let sourceVec : EuclideanSpace ℝ (Fin 2) := s - A
    let centerVec : EuclideanSpace ℝ (Fin 2) := c - A
    have hsource0 : B.repr sourceVec 0 = R := by
      have hnorm : ‖s - A‖ = R := by
        simpa [dist_eq_norm] using hs_dist_A
      have hinner : inner ℝ (s - A) (s - A) = R ^ 2 := by
        rw [real_inner_self_eq_norm_sq, hnorm]
      dsimp [sourceVec]
      rw [B.repr_apply_apply, hB0, real_inner_smul_left, hinner]
      field_simp [hR.ne']
    have hsource1 : B.repr sourceVec 1 = 0 := by
      have hv_eq : s - A = R • B 0 := by
        rw [hB0]
        simp [smul_smul, hR.ne']
      dsimp [sourceVec]
      rw [B.repr_apply_apply, hv_eq, real_inner_smul_right]
      have horth : inner ℝ (B 1) (B 0) = 0 := by
        simp
      rw [horth]
      ring
    have norm_sq_two (z : EuclideanSpace ℝ (Fin 2)) :
        ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_two]
    have hcenter0 : B.repr centerVec 0 = R / 2 := by
      have hdist_Ac : dist A c = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hAowner
      have hdist_sc : dist s c = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hsowner
      have hnorm_eq : ‖sourceVec - centerVec‖ = ‖centerVec‖ := by
        have h1 : ‖sourceVec - centerVec‖ = dist s c := by
          rw [dist_eq_norm]
          congr 1
          dsimp [sourceVec, centerVec]
          abel
        have h2 : ‖centerVec‖ = dist A c := by
          rw [dist_eq_norm]
          have : centerVec = -(A - c) := by
            dsimp [centerVec]
            abel
          rw [this, norm_neg]
        rw [h1, h2, hdist_sc, hdist_Ac]
      have hnorm_repr :
          ‖B.repr (sourceVec - centerVec)‖ = ‖B.repr centerVec‖ := by
        calc
          ‖B.repr (sourceVec - centerVec)‖ =
              ‖sourceVec - centerVec‖ := by
            simpa using (B.repr.norm_map (sourceVec - centerVec))
          _ = ‖centerVec‖ := hnorm_eq
          _ = ‖B.repr centerVec‖ := by
            simpa using (B.repr.norm_map centerVec).symm
      have hsq : ‖B.repr (sourceVec - centerVec)‖ ^ 2 =
          ‖B.repr centerVec‖ ^ 2 := by rw [hnorm_repr]
      rw [norm_sq_two, norm_sq_two] at hsq
      simp [map_sub, hsource0, hsource1] at hsq
      nlinarith
    obtain ⟨δ, hδpos, hδprop⟩ :=
      PolygonalReplacementCircleOutsideNearSupportingCoordinate (R := R)
        (k := B.repr centerVec 1) hR
    have core_halfspace :
        ∀ q : EuclideanSpace ℝ (Fin 2),
          q ∈ Metric.sphere c r →
            q ∉ Metric.ball A R →
              dist q s < δ →
                R ^ 2 ≤ inner ℝ (q - A) (s - A) := by
      intro q hqowner hqout hnear
      let d : EuclideanSpace ℝ (Fin 2) := q - s
      let x : ℝ := B.repr d 0
      let y : ℝ := B.repr d 1
      have howner_eq :
          R * x + (x ^ 2 + y ^ 2) = 2 * (B.repr centerVec 1) * y := by
        have hdist_Ac : dist A c = r := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hAowner
        have hdist_qc : dist q c = r := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hqowner
        have hnorm_eq : ‖sourceVec + d - centerVec‖ = ‖centerVec‖ := by
          have h1 : ‖sourceVec + d - centerVec‖ = dist q c := by
            rw [dist_eq_norm]
            congr 1
            dsimp [sourceVec, centerVec, d]
            abel
          have h2 : ‖centerVec‖ = dist A c := by
            rw [dist_eq_norm]
            have : centerVec = -(A - c) := by
              dsimp [centerVec]
              abel
            rw [this, norm_neg]
          rw [h1, h2, hdist_qc, hdist_Ac]
        have hnorm_repr :
            ‖B.repr (sourceVec + d - centerVec)‖ =
              ‖B.repr centerVec‖ := by
          calc
            ‖B.repr (sourceVec + d - centerVec)‖ =
                ‖sourceVec + d - centerVec‖ := by
              simpa using (B.repr.norm_map (sourceVec + d - centerVec))
            _ = ‖centerVec‖ := hnorm_eq
            _ = ‖B.repr centerVec‖ := by
              simpa using (B.repr.norm_map centerVec).symm
        have hsq : ‖B.repr (sourceVec + d - centerVec)‖ ^ 2 =
            ‖B.repr centerVec‖ ^ 2 := by rw [hnorm_repr]
        rw [norm_sq_two, norm_sq_two] at hsq
        simp [map_sub, map_add, hsource0, hsource1] at hsq
        change (R + x - B.repr centerVec 0) ^ 2 +
            (y - B.repr centerVec 1) ^ 2 =
            (B.repr centerVec 0) ^ 2 + (B.repr centerVec 1) ^ 2 at hsq
        rw [hcenter0] at hsq
        nlinarith
      have hout : 0 ≤ 2 * R * x + (x ^ 2 + y ^ 2) := by
        have hnotlt : ¬ dist q A < R := by
          simpa [Metric.mem_ball] using hqout
        have hdist_le : R ≤ dist q A := le_of_not_gt hnotlt
        have hnorm_le : R ≤ ‖sourceVec + d‖ := by
          have hqd : ‖sourceVec + d‖ = dist q A := by
            rw [dist_eq_norm]
            congr 1
            dsimp [sourceVec, d]
            abel
          rwa [hqd]
        have hsq_le : R ^ 2 ≤ ‖B.repr (sourceVec + d)‖ ^ 2 := by
          have hnorm_le' : R ≤ ‖B.repr (sourceVec + d)‖ := by
            calc
              R ≤ ‖sourceVec + d‖ := hnorm_le
              _ = ‖B.repr (sourceVec + d)‖ := by
                simpa using (B.repr.norm_map (sourceVec + d)).symm
          exact (sq_le_sq₀ hR.le (norm_nonneg _)).2 hnorm_le'
        rw [norm_sq_two] at hsq_le
        simp [map_add, hsource0, hsource1] at hsq_le
        change R ^ 2 ≤ (R + x) ^ 2 + y ^ 2 at hsq_le
        nlinarith
      have hnear_sq : x ^ 2 + y ^ 2 < δ ^ 2 := by
        have hnorm_lt : ‖d‖ < δ := by
          simpa [d, dist_eq_norm, norm_neg, sub_eq_add_neg, add_comm] using hnear
        have hnorm_lt' : ‖B.repr d‖ < δ := by
          simpa using hnorm_lt
        have hsq_lt : ‖B.repr d‖ ^ 2 < δ ^ 2 :=
          (sq_lt_sq₀ (norm_nonneg _) hδpos.le).2 hnorm_lt'
        rw [norm_sq_two] at hsq_lt
        simpa [x, y] using hsq_lt
      have hx_nonneg : 0 ≤ x := hδprop howner_eq hout hnear_sq
      have hinner_nonneg : 0 ≤ inner ℝ d sourceVec := by
        have hx_eq : x = R⁻¹ * inner ℝ d sourceVec := by
          dsimp [x, sourceVec]
          rw [B.repr_apply_apply, hB0, real_inner_smul_left]
          rw [real_inner_comm (s - A) d]
        have : 0 ≤ R⁻¹ * inner ℝ d sourceVec := by
          simpa [hx_eq] using hx_nonneg
        rw [mul_comm] at this
        exact nonneg_of_mul_nonneg_left this (inv_pos.mpr hR)
      calc
        R ^ 2 = inner ℝ sourceVec sourceVec := by
          have hnorm : ‖s - A‖ = R := by
            simpa [dist_eq_norm] using hs_dist_A
          dsimp [sourceVec]
          rw [real_inner_self_eq_norm_sq, hnorm]
        _ ≤ inner ℝ (q - A) sourceVec := by
          have hqA : q - A = sourceVec + d := by
            simp [sourceVec, d, sub_eq_add_neg, add_left_comm, add_assoc]
          rw [hqA, inner_add_left]
          nlinarith
        _ = inner ℝ (q - A) (s - A) := by
          rfl
    let η : ℝ := min ε δ
    have hηpos : 0 < η := lt_min hε hδpos
    have hη_le_ε : η ≤ ε := min_le_left _ _
    have hη_le_δ : η ≤ δ := min_le_right _ _
    rcases retained_point η hηpos with
      ⟨u, hu_source, hu_target, hb_ballη, _hb_original, hb_owner,
        hb_not_vertex, hb_not_intersection⟩
    let b : EuclideanSpace ℝ (Fin 2) := edgeAtOwner u
    have hb_ballε : b ∈ Metric.ball s ε := by
      rw [Metric.mem_ball] at hb_ballη ⊢
      exact lt_of_lt_of_le (by simpa [b, edgeAtOwner, e, s] using hb_ballη)
        hη_le_ε
    have hb_dist_δ : dist b s < δ := by
      rw [Metric.mem_ball] at hb_ballη
      exact lt_of_lt_of_le (by simpa [b, edgeAtOwner, e, s] using hb_ballη)
        hη_le_δ
    have hb_not_assigned : b ∉ Metric.ball A R := by
      exact havoid u
        (by intro v; simpa [b, edgeAtOwner, e] using hb_not_vertex v)
        (by intro x; simpa [b, edgeAtOwner, e] using hb_not_intersection x)
    have hhalfspace : R ^ 2 ≤ inner ℝ (b - A) (s - A) :=
      core_halfspace b
        (by simpa [b, edgeAtOwner, e] using hb_owner)
        hb_not_assigned hb_dist_δ
    refine ⟨u, ?_, ?_, ?_, ?_⟩
    · exact hu_source
    · exact hu_target
    · simpa [b, edgeAtOwner, e, s] using hb_ballε
    · simpa [b, edgeAtOwner, e, s] using hhalfspace
  constructor
  · intro v ε hv_owner hv_sphere hv_carrier hε
    rcases center_order with hvertex | hintersection
    · rcases hvertex with
        ⟨v₀, hv₀_eq, _htargetParam_eq, _htarget_lt,
          _hone_edge, ht_vertex_sphere, _ht_carrier,
          hcenter_owner, ht_owner⟩
      have hv_eq : v = v₀ := by
        by_contra hne
        have ht_closed_v :
            s ∈ Metric.closedBall (D.vertexPlacement v)
              (controlDisks.vertexRadius v) := by
          rw [Metric.mem_closedBall]
          exact le_of_eq
            (by simpa [s, Metric.mem_sphere, dist_eq_norm] using hv_sphere)
        have ht_closed_v₀ :
            s ∈ Metric.closedBall (D.vertexPlacement v₀)
              (controlDisks.vertexRadius v₀) := by
          rw [Metric.mem_closedBall]
          exact le_of_eq
            (by simpa [s, Metric.mem_sphere, dist_eq_norm] using ht_vertex_sphere)
        have hdisj :
            Disjoint
              (Metric.closedBall (D.vertexPlacement v)
                (controlDisks.vertexRadius v))
              (Metric.closedBall (D.vertexPlacement v₀)
                (controlDisks.vertexRadius v₀)) :=
          controlDisks.vertex_vertex_disjoint (v := v) (w := v₀) hne
        exact (Set.disjoint_left.mp hdisj) ht_closed_v ht_closed_v₀
      subst v
      exact build_for_center (D.vertexPlacement v₀)
        (controlDisks.vertexRadius v₀) (controlDisks.vertexRadius_pos v₀)
        hcenter_owner (by simpa [s] using ht_vertex_sphere)
        (by simpa [s] using ht_owner)
        (fun u hnot_vertex _hnot_intersection => by
          simpa [edgeAtOwner, e] using hnot_vertex v₀)
        ε hε
    · rcases hintersection with
        ⟨x, _hx_rel, _htarget_eq_left, _htargetParam_eq_left,
          _htarget_lt_center, _hcenter_eq, _hcenter_owner,
          _ht_owner, ht_intersection_sphere, _ht_carrier⟩
      exfalso
      have ht_closed_v :
          s ∈ Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v) := by
        rw [Metric.mem_closedBall]
        exact le_of_eq
          (by simpa [s, Metric.mem_sphere, dist_eq_norm] using hv_sphere)
      have ht_closed_x :
          s ∈ Metric.closedBall x.1
            (controlDisks.intersectionRadius x) := by
        rw [Metric.mem_closedBall]
        exact le_of_eq
          (by simpa [s, Metric.mem_sphere, dist_eq_norm] using ht_intersection_sphere)
      have hdisj :
          Disjoint
            (Metric.closedBall (D.vertexPlacement v)
              (controlDisks.vertexRadius v))
            (Metric.closedBall x.1 (controlDisks.intersectionRadius x)) :=
        controlDisks.vertex_intersection_disjoint v x
      exact (Set.disjoint_left.mp hdisj) ht_closed_v ht_closed_x
  · intro x ε hx_rel hx_sphere hx_carrier hε
    rcases center_order with hvertex | hintersection
    · rcases hvertex with
        ⟨v, _hv_eq, _htargetParam_eq, _htarget_lt,
          _hone_edge, ht_vertex_sphere, _ht_carrier,
          _hcenter_owner, _ht_owner⟩
      exfalso
      have ht_closed_v :
          s ∈ Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v) := by
        rw [Metric.mem_closedBall]
        exact le_of_eq
          (by simpa [s, Metric.mem_sphere, dist_eq_norm] using ht_vertex_sphere)
      have ht_closed_x :
          s ∈ Metric.closedBall x.1
            (controlDisks.intersectionRadius x) := by
        rw [Metric.mem_closedBall]
        exact le_of_eq
          (by simpa [s, Metric.mem_sphere, dist_eq_norm] using hx_sphere)
      have hdisj :
          Disjoint
            (Metric.closedBall (D.vertexPlacement v)
              (controlDisks.vertexRadius v))
            (Metric.closedBall x.1 (controlDisks.intersectionRadius x)) :=
        controlDisks.vertex_intersection_disjoint v x
      exact (Set.disjoint_left.mp hdisj) ht_closed_v ht_closed_x
    · rcases hintersection with
        ⟨x₀, hx₀_rel, _htarget_eq_left, _htargetParam_eq_left,
          _htarget_lt_center, _hcenter_eq, hcenter_owner,
          ht_owner, ht_intersection_sphere, _ht_carrier⟩
      have hx_eq : x = x₀ := by
        by_contra hne
        have ht_closed_x :
            s ∈ Metric.closedBall x.1
              (controlDisks.intersectionRadius x) := by
          rw [Metric.mem_closedBall]
          exact le_of_eq
            (by simpa [s, Metric.mem_sphere, dist_eq_norm] using hx_sphere)
        have ht_closed_x₀ :
            s ∈ Metric.closedBall x₀.1
              (controlDisks.intersectionRadius x₀) := by
          rw [Metric.mem_closedBall]
          exact le_of_eq
            (by simpa [s, Metric.mem_sphere, dist_eq_norm] using ht_intersection_sphere)
        have hdisj :
            Disjoint
              (Metric.closedBall x.1 (controlDisks.intersectionRadius x))
              (Metric.closedBall x₀.1 (controlDisks.intersectionRadius x₀)) :=
          controlDisks.intersection_intersection_disjoint (x := x) (y := x₀) hne
        exact (Set.disjoint_left.mp hdisj) ht_closed_x ht_closed_x₀
      subst x
      exact build_for_center x₀.1
        (controlDisks.intersectionRadius x₀)
        (controlDisks.intersectionRadius_pos x₀)
        hcenter_owner (by simpa [s] using ht_intersection_sphere)
        (by simpa [s] using ht_owner)
        (fun u _hnot_vertex hnot_intersection => by
          simpa [edgeAtOwner, e] using hnot_intersection x₀)
        ε hε
