import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Util.IncidenceGeometry.StraightSegmentPolygonalArc
import Util.IncidenceGeometry.PolygonalReplacementTubeChainData

open Classical
noncomputable section

lemma PolygonalReplacementVertexDiskSpokes {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks) :
    ∃ vertex_spoke :
        (v : V) → {e : G.edgeFinset // v ∈ e.1} → PolygonalArc,
      (∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
        (vertex_spoke v e).source = D.vertexPlacement v) ∧
      (∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
        (vertex_spoke v e).source ≠ (vertex_spoke v e).target) ∧
      (∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
        (vertex_spoke v e).target ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
          (vertex_spoke v e).target ∈ D.edgeCarrier e.1) ∧
      (∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
        ∃! i : tubeChains.pieceIndex,
          tubeChains.owner i = e.1 ∧
            (tubeChains.source i = (vertex_spoke v e).target ∨
              tubeChains.target i = (vertex_spoke v e).target)) ∧
      (∀ ⦃v : V⦄ ⦃e : G.edgeFinset⦄
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄
        (hve : v ∈ e.1),
        p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
          p ∈ D.edgeCarrier e →
            (vertex_spoke v ⟨e, hve⟩).target = p) ∧
      (∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
        (vertex_spoke v e).carrier ⊆
          Metric.closedBall (D.vertexPlacement v) (controlDisks.vertexRadius v)) ∧
      (∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
        (vertex_spoke v e).relativeInterior ⊆
          Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v)) ∧
      (∀ v ⦃e f : {e : G.edgeFinset // v ∈ e.1}⦄,
        e ≠ f →
          Disjoint (vertex_spoke v e).relativeInterior
            (vertex_spoke v f).relativeInterior) := by
  classical
  let boundaryPoint :
      (v : V) → {e : G.edgeFinset // v ∈ e.1} →
        EuclideanSpace ℝ (Fin 2) :=
    fun v e => Classical.choose (controlDisks.vertex_boundary_unique e.2)
  have boundaryPoint_spec :
      ∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
        boundaryPoint v e ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
          boundaryPoint v e ∈ D.edgeCarrier e.1 := by
    intro v e
    exact (Classical.choose_spec (controlDisks.vertex_boundary_unique e.2)).1
  have boundaryPoint_unique :
      ∀ v (e : {e : G.edgeFinset // v ∈ e.1})
        (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
          p ∈ D.edgeCarrier e.1 → p = boundaryPoint v e := by
    intro v e p hpSphere hpCarrier
    exact (Classical.choose_spec (controlDisks.vertex_boundary_unique e.2)).2 p
      ⟨hpSphere, hpCarrier⟩
  have boundaryPoint_ne_center :
      ∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
        D.vertexPlacement v ≠ boundaryPoint v e := by
    intro v e h
    have hsphere := (boundaryPoint_spec v e).1
    have hdist : dist (boundaryPoint v e) (D.vertexPlacement v) =
        controlDisks.vertexRadius v := by
      rw [dist_eq_norm]
      simpa only [Metric.mem_sphere, dist_eq_norm] using hsphere
    have hzero : dist (boundaryPoint v e) (D.vertexPlacement v) = 0 := by
      simp [← h]
    have hpos := controlDisks.vertexRadius_pos v
    linarith
  let vertexSpoke :
      (v : V) → {e : G.edgeFinset // v ∈ e.1} → PolygonalArc :=
    fun v e =>
      Classical.choose
        (StraightSegmentPolygonalArc (D.vertexPlacement v) (boundaryPoint v e)
          (boundaryPoint_ne_center v e))
  have vertexSpoke_spec :
      ∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
        (vertexSpoke v e).source = D.vertexPlacement v ∧
          (vertexSpoke v e).target = boundaryPoint v e ∧
            (vertexSpoke v e).carrier =
              segment ℝ (D.vertexPlacement v) (boundaryPoint v e) ∧
              (vertexSpoke v e).relativeInterior =
                openSegment ℝ (D.vertexPlacement v) (boundaryPoint v e) := by
    intro v e
    exact Classical.choose_spec
      (StraightSegmentPolygonalArc (D.vertexPlacement v) (boundaryPoint v e)
        (boundaryPoint_ne_center v e))
  have radial_endpoint_eq :
      ∀ {c a b p : EuclideanSpace ℝ (Fin 2)} {r : ℝ},
        0 < r →
          a ∈ Metric.sphere c r →
            b ∈ Metric.sphere c r →
              p ∈ openSegment ℝ c a →
                p ∈ openSegment ℝ c b → a = b := by
    intro c a b p r hr ha hb hp_a hp_b
    rw [openSegment_eq_image_lineMap] at hp_a hp_b
    rcases hp_a with ⟨s, hs, hps⟩
    rcases hp_b with ⟨t, ht, hpt⟩
    have hdist_a : dist a c = r := by
      rw [dist_eq_norm]
      simpa only [Metric.mem_sphere, dist_eq_norm] using ha
    have hdist_b : dist b c = r := by
      rw [dist_eq_norm]
      simpa only [Metric.mem_sphere, dist_eq_norm] using hb
    have hdist_ca : dist c a = r := by simpa [dist_comm] using hdist_a
    have hdist_cb : dist c b = r := by simpa [dist_comm] using hdist_b
    have hpdist_s : dist p c = s * r := by
      rw [← hps, dist_lineMap_left, hdist_ca]
      rw [Real.norm_of_nonneg hs.1.le]
    have hpdist_t : dist p c = t * r := by
      rw [← hpt, dist_lineMap_left, hdist_cb]
      rw [Real.norm_of_nonneg ht.1.le]
    have hs_eq_t : s = t := by
      have hmul : s * r = t * r := by linarith
      exact mul_right_cancel₀ hr.ne' hmul
    have hs_ne_zero : s ≠ 0 := ne_of_gt hs.1
    have hline : AffineMap.lineMap c a s = AffineMap.lineMap c b s := by
      calc
        AffineMap.lineMap c a s = p := hps
        _ = AffineMap.lineMap c b t := hpt.symm
        _ = AffineMap.lineMap c b s := by rw [hs_eq_t]
    have hvec : s • (a - c) = s • (b - c) := by
      simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc,
        sub_eq_add_neg, smul_add, smul_neg, add_smul] using
        congrArg (fun x => x - c) hline
    have hab_sub : a - c = b - c :=
      smul_right_injective (M := EuclideanSpace ℝ (Fin 2)) hs_ne_zero hvec
    simpa [sub_eq_add_neg, add_assoc] using congrArg (fun x => x + c) hab_sub
  refine ⟨vertexSpoke, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v e
    exact (vertexSpoke_spec v e).1
  · intro v e hst
    have hs := (vertexSpoke_spec v e).1
    have ht := (vertexSpoke_spec v e).2.1
    exact (boundaryPoint_ne_center v e) (by simpa [hs, ht] using hst)
  · intro v e
    have ht := (vertexSpoke_spec v e).2.1
    simpa [ht] using boundaryPoint_spec v e
  · intro v e
    have ht := (vertexSpoke_spec v e).2.1
    simpa [ht] using
      tubeChains.vertex_boundary_attached e.2 (boundaryPoint_spec v e).1
        (boundaryPoint_spec v e).2
  · intro v e p hve hpSphere hpCarrier
    have ht := (vertexSpoke_spec v ⟨e, hve⟩).2.1
    have hp_eq := boundaryPoint_unique v ⟨e, hve⟩ p hpSphere hpCarrier
    simpa [ht] using hp_eq.symm
  · intro v e p hp
    have hcarrier := (vertexSpoke_spec v e).2.2.1
    have hsphere := (boundaryPoint_spec v e).1
    have hdist : dist (D.vertexPlacement v) (boundaryPoint v e) =
        controlDisks.vertexRadius v := by
      have hdist' : dist (boundaryPoint v e) (D.vertexPlacement v) =
          controlDisks.vertexRadius v := by
        rw [dist_eq_norm]
        simpa only [Metric.mem_sphere, dist_eq_norm] using hsphere
      simpa [dist_comm] using hdist'
    have hpseg : p ∈ segment ℝ (D.vertexPlacement v) (boundaryPoint v e) := by
      simpa [hcarrier] using hp
    exact (by
      simpa [hdist] using
        (segment_subset_closedBall_left (D.vertexPlacement v) (boundaryPoint v e) hpseg))
  · intro v e p hp
    have hinterior := (vertexSpoke_spec v e).2.2.2
    have hpopen : p ∈ openSegment ℝ (D.vertexPlacement v) (boundaryPoint v e) := by
      simpa [hinterior] using hp
    have hcenter :
        D.vertexPlacement v ∈
          Metric.closedBall (D.vertexPlacement v) (controlDisks.vertexRadius v) := by
      simp [Metric.mem_closedBall, (controlDisks.vertexRadius_pos v).le]
    have hbclosed :
        boundaryPoint v e ∈
          Metric.closedBall (D.vertexPlacement v) (controlDisks.vertexRadius v) := by
      have hsphere := (boundaryPoint_spec v e).1
      have hdist : dist (boundaryPoint v e) (D.vertexPlacement v) =
          controlDisks.vertexRadius v := by
        rw [dist_eq_norm]
        simpa only [Metric.mem_sphere, dist_eq_norm] using hsphere
      simp [Metric.mem_closedBall, hdist]
    exact
      openSegment_subset_ball_of_ne hcenter hbclosed
        (boundaryPoint_ne_center v e) hpopen
  · intro v e f hef
    rw [Set.disjoint_left]
    intro p hpe hpf
    have he_int := (vertexSpoke_spec v e).2.2.2
    have hf_int := (vertexSpoke_spec v f).2.2.2
    have hp_open_e :
        p ∈ openSegment ℝ (D.vertexPlacement v) (boundaryPoint v e) := by
      simpa [he_int] using hpe
    have hp_open_f :
        p ∈ openSegment ℝ (D.vertexPlacement v) (boundaryPoint v f) := by
      simpa [hf_int] using hpf
    have hb_eq : boundaryPoint v e = boundaryPoint v f :=
      radial_endpoint_eq (controlDisks.vertexRadius_pos v)
        (boundaryPoint_spec v e).1 (boundaryPoint_spec v f).1
        hp_open_e hp_open_f
    have hedge : e.1 = f.1 :=
      controlDisks.vertex_boundary_point_edge_unique e.2 f.2
        (boundaryPoint_spec v e).1 (boundaryPoint_spec v e).2
        (by simpa [hb_eq] using (boundaryPoint_spec v f).2)
    exact hef (Subtype.ext hedge)
