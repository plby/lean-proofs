import Util.IncidenceGeometry.PolygonalReplacementEdgeAssemblyData
import Util.IncidenceGeometry.PolygonalArcReverse
import Util.IncidenceGeometry.PolygonalArcEndpointGluedVertices
import Util.IncidenceGeometry.PolygonalArcEndpointGluedVerticesBasic
import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentOccurrence
import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentCertificates
import Util.IncidenceGeometry.PolygonalArcFromEndpointGluedPieces
import Util.IncidenceGeometry.PolygonalReplacementLocalPieceLists


open Classical
noncomputable section

lemma polygonalArcReverse_segment_to_original
    (Γ : PolygonalArc) (m : ℕ)
    (hm : m + 1 < (PolygonalArcReverse Γ).vertices.length) :
    ∃ k : ℕ, ∃ hk : k + 1 < Γ.vertices.length,
      (PolygonalArcReverse Γ).vertices[m] = Γ.vertices[k + 1] ∧
        (PolygonalArcReverse Γ).vertices[m + 1] = Γ.vertices[k] := by
  let k := Γ.vertices.length - 2 - m
  have hm_orig : m + 1 < Γ.vertices.length := by
    simpa only [PolygonalArcReverse, List.length_reverse] using hm
  have hk : k + 1 < Γ.vertices.length := by
    dsimp [k]
    omega
  refine ⟨k, hk, ?_, ?_⟩
  · dsimp [PolygonalArcReverse]
    have hm_lt : m < Γ.vertices.reverse.length :=
      (by simpa only [List.length_reverse] using
        (Nat.lt_trans (Nat.lt_succ_self m) hm_orig))
    have hidx : Γ.vertices.length - 1 - m = k + 1 := by
      dsimp [k]
      omega
    apply Option.some.inj
    calc
      some Γ.vertices.reverse[m] = Γ.vertices.reverse[m]? :=
        (List.getElem?_eq_getElem hm_lt).symm
      _ = Γ.vertices[k + 1]? := by
        rw [List.getElem?_reverse (by simpa using hm_lt), hidx]
      _ = some Γ.vertices[k + 1] := List.getElem?_eq_getElem hk
  · dsimp [PolygonalArcReverse]
    have hidx : Γ.vertices.length - 1 - (m + 1) = k := by
      dsimp [k]
      omega
    have hm_rev : m + 1 < Γ.vertices.reverse.length := by
      simpa only [PolygonalArcReverse] using hm
    have hk_lt : k < Γ.vertices.length := Nat.lt_of_succ_lt hk
    apply Option.some.inj
    calc
      some Γ.vertices.reverse[m + 1] = Γ.vertices.reverse[m + 1]? :=
        (List.getElem?_eq_getElem hm_rev).symm
      _ = Γ.vertices[k]? := by
        rw [List.getElem?_reverse (by simpa using hm_rev), hidx]
      _ = some Γ.vertices[k] := List.getElem?_eq_getElem hk_lt

lemma polygonalArc_original_segment_to_reverse
    (Γ : PolygonalArc) (m : ℕ) (hm : m + 1 < Γ.vertices.length) :
    ∃ r : ℕ, ∃ hr : r + 1 < (PolygonalArcReverse Γ).vertices.length,
      (PolygonalArcReverse Γ).vertices[r] = Γ.vertices[m + 1] ∧
        (PolygonalArcReverse Γ).vertices[r + 1] = Γ.vertices[m] := by
  let r := Γ.vertices.length - 2 - m
  have hr : r + 1 < (PolygonalArcReverse Γ).vertices.length := by
    simp [PolygonalArcReverse, r, List.length_reverse]
    omega
  refine ⟨r, hr, ?_, ?_⟩
  · dsimp [PolygonalArcReverse]
    have hr_lt : r < Γ.vertices.reverse.length :=
      Nat.lt_trans (Nat.lt_succ_self r) hr
    have hidx : Γ.vertices.length - 1 - r = m + 1 := by
      dsimp [r]
      omega
    apply Option.some.inj
    calc
      some Γ.vertices.reverse[r] = Γ.vertices.reverse[r]? :=
        (List.getElem?_eq_getElem hr_lt).symm
      _ = Γ.vertices[m + 1]? := by
        rw [List.getElem?_reverse (by simpa using hr_lt), hidx]
      _ = some Γ.vertices[m + 1] := List.getElem?_eq_getElem hm
  · dsimp [PolygonalArcReverse]
    have hidx : Γ.vertices.length - 1 - (r + 1) = m := by
      dsimp [r]
      omega
    have hr_rev : r + 1 < Γ.vertices.reverse.length := by
      simpa only [PolygonalArcReverse] using hr
    have hm_lt : m < Γ.vertices.length :=
      Nat.lt_trans (Nat.lt_succ_self m) hm
    apply Option.some.inj
    calc
      some Γ.vertices.reverse[r + 1] = Γ.vertices.reverse[r + 1]? :=
        (List.getElem?_eq_getElem hr_rev).symm
      _ = Γ.vertices[m]? := by
        rw [List.getElem?_reverse (by simpa using hr_rev), hidx]
      _ = some Γ.vertices[m] := List.getElem?_eq_getElem hm_lt

lemma polygonalArcReverse_segment_match_to_original
    (Γ : PolygonalArc) (m : ℕ)
    (hm : m + 1 < (PolygonalArcReverse Γ).vertices.length)
    {a b : EuclideanSpace ℝ (Fin 2)}
    (hmatch :
      ((a = (PolygonalArcReverse Γ).vertices[m] ∧
          b = (PolygonalArcReverse Γ).vertices[m + 1]) ∨
        (a = (PolygonalArcReverse Γ).vertices[m + 1] ∧
          b = (PolygonalArcReverse Γ).vertices[m]))) :
    ∃ k : ℕ, ∃ hk : k + 1 < Γ.vertices.length,
      ((a = Γ.vertices[k] ∧ b = Γ.vertices[k + 1]) ∨
        (a = Γ.vertices[k + 1] ∧ b = Γ.vertices[k])) := by
  rcases polygonalArcReverse_segment_to_original Γ m hm with
    ⟨k, hk, hrev_left, hrev_right⟩
  refine ⟨k, hk, ?_⟩
  rcases hmatch with hmatch | hmatch
  · right
    exact ⟨by rw [hmatch.1, hrev_left], by rw [hmatch.2, hrev_right]⟩
  · left
    exact ⟨by rw [hmatch.1, hrev_right], by rw [hmatch.2, hrev_left]⟩

private lemma vertexSpokeBoundaryPointEqTarget
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) :
    ∀ v (e : {e : G.edgeFinset // v ∈ e.1})
      (p : EuclideanSpace ℝ (Fin 2)),
      p ∈ (localDiskFillings.vertex_spoke v e).carrier →
        p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
          p = (localDiskFillings.vertex_spoke v e).target := by
  intro v e p hpCarrier hpSphere
  by_cases hpTarget : p = (localDiskFillings.vertex_spoke v e).target
  · exact hpTarget
  have hpNotSource : p ≠ (localDiskFillings.vertex_spoke v e).source := by
    intro hpSource
    have hpCenter : p = D.vertexPlacement v := by
      calc
        p = (localDiskFillings.vertex_spoke v e).source := hpSource
        _ = D.vertexPlacement v := localDiskFillings.vertex_spoke_source v e
    have hpDist :
        dist p (D.vertexPlacement v) = controlDisks.vertexRadius v :=
      Metric.mem_sphere.mp hpSphere
    have hzero : (0 : ℝ) = controlDisks.vertexRadius v := by
      simpa [hpCenter] using hpDist
    exact (ne_of_gt (controlDisks.vertexRadius_pos v)) hzero.symm
  have hpRel : p ∈ (localDiskFillings.vertex_spoke v e).relativeInterior := by
    rw [(localDiskFillings.vertex_spoke v e).relativeInterior_eq]
    exact ⟨hpCarrier, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hpNotSource, hpTarget⟩⟩
  have hpBall :
      p ∈ Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v) :=
    localDiskFillings.vertex_spoke_relativeInterior_subset_ball v e hpRel
  have hpDistEq :
      dist p (D.vertexPlacement v) = controlDisks.vertexRadius v :=
    Metric.mem_sphere.mp hpSphere
  have hpDistLt :
      dist p (D.vertexPlacement v) < controlDisks.vertexRadius v := by
    simpa [Metric.mem_ball] using hpBall
  linarith

private lemma intersectionChainBoundaryPointEqEndpoint
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e})
      (p : EuclideanSpace ℝ (Fin 2)),
      p ∈ (localDiskFillings.intersection_chain x e).carrier →
        p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
          p = (localDiskFillings.intersection_chain x e).source ∨
            p = (localDiskFillings.intersection_chain x e).target := by
  intro x e p hpCarrier hpSphere
  by_cases hpSource : p = (localDiskFillings.intersection_chain x e).source
  · exact Or.inl hpSource
  by_cases hpTarget : p = (localDiskFillings.intersection_chain x e).target
  · exact Or.inr hpTarget
  have hpRel :
      p ∈ (localDiskFillings.intersection_chain x e).relativeInterior := by
    rw [(localDiskFillings.intersection_chain x e).relativeInterior_eq]
    exact ⟨hpCarrier, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hpSource, hpTarget⟩⟩
  have hpBall : p ∈ Metric.ball x.1 (controlDisks.intersectionRadius x) :=
    localDiskFillings.intersection_chain_relativeInterior_subset_ball x e hpRel
  have hpDistEq : dist p x.1 = controlDisks.intersectionRadius x :=
    Metric.mem_sphere.mp hpSphere
  have hpDistLt : dist p x.1 < controlDisks.intersectionRadius x := by
    simpa [Metric.mem_ball] using hpBall
  exact False.elim (by linarith)

private lemma vertexSpokeCarrierDisjointVertexSpokeOfNe
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) :
    ∀ ⦃v w : V⦄
      (e : {e : G.edgeFinset // v ∈ e.1})
      (f : {e : G.edgeFinset // w ∈ e.1}),
      v ≠ w →
        Disjoint (localDiskFillings.vertex_spoke v e).carrier
          (localDiskFillings.vertex_spoke w f).carrier := by
  intro v w e f hvw
  rw [Set.disjoint_left]
  intro p hpv hpw
  have hpvClosed :
      p ∈ Metric.closedBall (D.vertexPlacement v)
        (controlDisks.vertexRadius v) :=
    localDiskFillings.vertex_spoke_carrier_subset_closedBall v e hpv
  have hpwClosed :
      p ∈ Metric.closedBall (D.vertexPlacement w)
        (controlDisks.vertexRadius w) :=
    localDiskFillings.vertex_spoke_carrier_subset_closedBall w f hpw
  exact
    (Set.disjoint_left.mp (controlDisks.vertex_vertex_disjoint hvw) hpvClosed)
      hpwClosed

private lemma vertexSpokeCarrierDisjointIntersectionChain
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) :
    ∀ (v : V) (e : {e : G.edgeFinset // v ∈ e.1})
      (x : {p // p ∈ D.intersectionPoints})
      (f : {f : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior f}),
      Disjoint (localDiskFillings.vertex_spoke v e).carrier
        (localDiskFillings.intersection_chain x f).carrier := by
  intro v e x f
  rw [Set.disjoint_left]
  intro p hpv hpx
  have hpvClosed :
      p ∈ Metric.closedBall (D.vertexPlacement v)
        (controlDisks.vertexRadius v) :=
    localDiskFillings.vertex_spoke_carrier_subset_closedBall v e hpv
  have hpxClosed :
      p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) :=
    localDiskFillings.intersection_chain_carrier_subset_closedBall x f hpx
  exact
    (Set.disjoint_left.mp (controlDisks.vertex_intersection_disjoint v x)
      hpvClosed) hpxClosed

private lemma intersectionChainCarrierDisjointIntersectionChainOfNe
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) :
    ∀ (x y : {p // p ∈ D.intersectionPoints})
      (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e})
      (f : {f : G.edgeFinset // y.1 ∈ D.edgeRelativeInterior f}),
      x ≠ y →
        Disjoint (localDiskFillings.intersection_chain x e).carrier
          (localDiskFillings.intersection_chain y f).carrier := by
  intro x y e f hxy
  rw [Set.disjoint_left]
  intro p hpx hpy
  have hpxClosed :
      p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) :=
    localDiskFillings.intersection_chain_carrier_subset_closedBall x e hpx
  have hpyClosed :
      p ∈ Metric.closedBall y.1 (controlDisks.intersectionRadius y) :=
    localDiskFillings.intersection_chain_carrier_subset_closedBall y f hpy
  exact
    (Set.disjoint_left.mp
      (controlDisks.intersection_intersection_disjoint hxy) hpxClosed) hpyClosed

private lemma edgeMemSourceOrTarget
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks) :
    ∀ e v, v ∈ e.1 →
      v = tubeChains.edgeSourceVertex e ∨
        v = tubeChains.edgeTargetVertex e := by
  intro e v hve
  rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hend⟩
  have hvab : v = a ∨ v = b := by
    have hv_mem : v ∈ (Sym2.mk a b : Sym2 V) := by
      simpa [heq] using hve
    simpa using hv_mem
  rcases hend with hend | hend
  · have hsource : tubeChains.edgeSourceVertex e = a := by
      apply D.vertexPlacement_injective
      calc
        D.vertexPlacement (tubeChains.edgeSourceVertex e) = D.edgeSource e :=
          (tubeChains.edgeSource_eq_vertexPlacement e).symm
        _ = D.vertexPlacement a := hend.1
    have htarget : tubeChains.edgeTargetVertex e = b := by
      apply D.vertexPlacement_injective
      calc
        D.vertexPlacement (tubeChains.edgeTargetVertex e) = D.edgeTarget e :=
          (tubeChains.edgeTarget_eq_vertexPlacement e).symm
        _ = D.vertexPlacement b := hend.2
    rcases hvab with rfl | rfl
    · exact Or.inl hsource.symm
    · exact Or.inr htarget.symm
  · have hsource : tubeChains.edgeSourceVertex e = b := by
      apply D.vertexPlacement_injective
      calc
        D.vertexPlacement (tubeChains.edgeSourceVertex e) = D.edgeSource e :=
          (tubeChains.edgeSource_eq_vertexPlacement e).symm
        _ = D.vertexPlacement b := hend.1
    have htarget : tubeChains.edgeTargetVertex e = a := by
      apply D.vertexPlacement_injective
      calc
        D.vertexPlacement (tubeChains.edgeTargetVertex e) = D.edgeTarget e :=
          (tubeChains.edgeTarget_eq_vertexPlacement e).symm
        _ = D.vertexPlacement a := hend.2
    rcases hvab with rfl | rfl
    · exact Or.inr htarget.symm
    · exact Or.inl hsource.symm

private lemma edgeSourceNeTarget
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G) :
    ∀ e, D.edgeSource e ≠ D.edgeTarget e := by
  intro e
  rcases D.edge_is_simple_lineSegment_or_circularArc e with hline | harc
  · exact hline.1
  · rcases harc with
      ⟨c, r, γ, _hr, _hcont, hinj, _hdist, hzero, hone,
        _hcarrier, _hrelativeInterior⟩
    intro hst
    have h01 :
        (⟨(0 : ℝ), by simp⟩ : Set.Icc (0 : ℝ) 1) =
          ⟨(1 : ℝ), by simp⟩ := by
      apply hinj
      rw [hzero, hone]
      exact hst
    have hval := congrArg Subtype.val h01
    norm_num at hval

private lemma edgeSourceVertexNeTargetVertex
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks) :
    ∀ e, tubeChains.edgeSourceVertex e ≠ tubeChains.edgeTargetVertex e := by
  intro e hvertices
  exact edgeSourceNeTarget G D e (by
    rw [tubeChains.edgeSource_eq_vertexPlacement e,
      tubeChains.edgeTarget_eq_vertexPlacement e, hvertices])

private lemma edgeSourceMemSourceBall
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks) :
    ∀ e,
      D.edgeSource e ∈
        Metric.ball (D.vertexPlacement (tubeChains.edgeSourceVertex e))
          (controlDisks.vertexRadius (tubeChains.edgeSourceVertex e)) := by
  intro e
  rw [tubeChains.edgeSource_eq_vertexPlacement e]
  simp [Metric.mem_ball, controlDisks.vertexRadius_pos]

private lemma edgeTargetMemTargetBall
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks) :
    ∀ e,
      D.edgeTarget e ∈
        Metric.ball (D.vertexPlacement (tubeChains.edgeTargetVertex e))
          (controlDisks.vertexRadius (tubeChains.edgeTargetVertex e)) := by
  intro e
  rw [tubeChains.edgeTarget_eq_vertexPlacement e]
  simp [Metric.mem_ball, controlDisks.vertexRadius_pos]

private lemma sourceSpokeCarrierDisjointTubeChainOfNotHead
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (sourceSpokeAttachesFirstTube :
      ∀ e i, (tubeChains.edgePieceOrder e).head? = some i →
        (localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
          ⟨e, tubeChains.edgeSourceVertex_mem e⟩).target =
            (tubeChains.chain i).source)
    (vertexSpokeBoundaryPointEqTarget :
      ∀ v (e : {e : G.edgeFinset // v ∈ e.1})
        (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ (localDiskFillings.vertex_spoke v e).carrier →
          p ∈ Metric.sphere (D.vertexPlacement v)
            (controlDisks.vertexRadius v) →
            p = (localDiskFillings.vertex_spoke v e).target) :
    ∀ e i,
      i ∈ tubeChains.edgePieceOrder e →
        (tubeChains.edgePieceOrder e).head? ≠ some i →
          Disjoint
            (localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
              ⟨e, tubeChains.edgeSourceVertex_mem e⟩).carrier
            (tubeChains.chain i).carrier := by
  intro e i hi_mem hnot_head
  rw [Set.disjoint_left]
  intro p hpSpoke hpTube
  have hpClosed :
      p ∈ Metric.closedBall
        (D.vertexPlacement (tubeChains.edgeSourceVertex e))
        (controlDisks.vertexRadius (tubeChains.edgeSourceVertex e)) :=
    localDiskFillings.vertex_spoke_carrier_subset_closedBall
      (tubeChains.edgeSourceVertex e)
      ⟨e, tubeChains.edgeSourceVertex_mem e⟩ hpSpoke
  have hmeet :=
    tubeChains.chain_carrier_meets_vertex_closedBall_only_endpoint i
      (tubeChains.edgeSourceVertex e) p hpTube hpClosed
  have hpSphere :
      p ∈ Metric.sphere
        (D.vertexPlacement (tubeChains.edgeSourceVertex e))
        (controlDisks.vertexRadius (tubeChains.edgeSourceVertex e)) := by
    rcases hmeet with hsource | htarget
    · simpa [hsource.1] using hsource.2
    · simpa [htarget.1] using htarget.2
  have hpTarget :
      p = (localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
        ⟨e, tubeChains.edgeSourceVertex_mem e⟩).target :=
    vertexSpokeBoundaryPointEqTarget
      (tubeChains.edgeSourceVertex e)
      ⟨e, tubeChains.edgeSourceVertex_mem e⟩ p hpSpoke hpSphere
  have hlen_pos : 0 < (tubeChains.edgePieceOrder e).length :=
    Nat.pos_of_ne_zero (tubeChains.edgePieceOrder_nonempty e)
  let first := (tubeChains.edgePieceOrder e)[0]
  have hhead : (tubeChains.edgePieceOrder e).head? = some first := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen_pos]
  have hfirst_owner : tubeChains.owner first = e :=
    (tubeChains.edgePieceOrder_owner_iff e first).1
      (by
        dsimp [first]
        exact List.getElem_mem hlen_pos)
  have hfirst_attach :
      tubeChains.owner first = e ∧
        (tubeChains.source first =
            (localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
              ⟨e, tubeChains.edgeSourceVertex_mem e⟩).target ∨
          tubeChains.target first =
            (localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
              ⟨e, tubeChains.edgeSourceVertex_mem e⟩).target) := by
    refine ⟨hfirst_owner, Or.inl ?_⟩
    have hattach := sourceSpokeAttachesFirstTube e first hhead
    calc
      tubeChains.source first = (tubeChains.chain first).source :=
        (tubeChains.chain_endpoints first).1.symm
      _ = (localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
            ⟨e, tubeChains.edgeSourceVertex_mem e⟩).target := hattach.symm
  have hi_owner : tubeChains.owner i = e :=
    (tubeChains.edgePieceOrder_owner_iff e i).1 hi_mem
  have hi_attach :
      tubeChains.owner i = e ∧
        (tubeChains.source i =
            (localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
              ⟨e, tubeChains.edgeSourceVertex_mem e⟩).target ∨
          tubeChains.target i =
            (localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
              ⟨e, tubeChains.edgeSourceVertex_mem e⟩).target) := by
    refine ⟨hi_owner, ?_⟩
    rcases hmeet with hsource | htarget
    · left
      calc
        tubeChains.source i = p := hsource.1.symm
        _ = _ := hpTarget
    · right
      calc
        tubeChains.target i = p := htarget.1.symm
        _ = _ := hpTarget
  rcases localDiskFillings.vertex_spoke_attached_to_tube
      (tubeChains.edgeSourceVertex e)
      ⟨e, tubeChains.edgeSourceVertex_mem e⟩ with ⟨a, _ha, hunique⟩
  have hfirst_eq_a : first = a := hunique first hfirst_attach
  have hi_eq_a : i = a := hunique i hi_attach
  have hi_eq_first : i = first := hi_eq_a.trans hfirst_eq_a.symm
  exact hnot_head (by simpa [hi_eq_first] using hhead)

private lemma targetSpokeReverseCarrierDisjointTubeChainOfNotLast
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (terminalTubeIndexGetLast : ∀ e,
      (tubeChains.edgePieceOrder e).getLast? = some (terminalTubeIndex e))
    (terminalTubeIndexMem : ∀ e,
      terminalTubeIndex e ∈ tubeChains.edgePieceOrder e)
    (terminalTubeAttachesTargetSpoke : ∀ e,
      (tubeChains.chain (terminalTubeIndex e)).target =
        (PolygonalArcReverse
          (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
            ⟨e, tubeChains.edgeTargetVertex_mem e⟩)).source)
    (vertexSpokeBoundaryPointEqTarget :
      ∀ v (e : {e : G.edgeFinset // v ∈ e.1})
        (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ (localDiskFillings.vertex_spoke v e).carrier →
          p ∈ Metric.sphere (D.vertexPlacement v)
            (controlDisks.vertexRadius v) →
            p = (localDiskFillings.vertex_spoke v e).target) :
    ∀ e i,
      i ∈ tubeChains.edgePieceOrder e →
        (tubeChains.edgePieceOrder e).getLast? ≠ some i →
          Disjoint
            (PolygonalArcReverse
              (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
                ⟨e, tubeChains.edgeTargetVertex_mem e⟩)).carrier
            (tubeChains.chain i).carrier := by
  intro e i hi_mem hnot_last
  rw [Set.disjoint_left]
  intro p hpSpoke hpTube
  have hpTargetSpoke :
      p ∈ (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
        ⟨e, tubeChains.edgeTargetVertex_mem e⟩).carrier := by
    simpa [PolygonalArcReverse] using hpSpoke
  have hpClosed :
      p ∈ Metric.closedBall
        (D.vertexPlacement (tubeChains.edgeTargetVertex e))
        (controlDisks.vertexRadius (tubeChains.edgeTargetVertex e)) :=
    localDiskFillings.vertex_spoke_carrier_subset_closedBall
      (tubeChains.edgeTargetVertex e)
      ⟨e, tubeChains.edgeTargetVertex_mem e⟩ hpTargetSpoke
  have hmeet :=
    tubeChains.chain_carrier_meets_vertex_closedBall_only_endpoint i
      (tubeChains.edgeTargetVertex e) p hpTube hpClosed
  have hpSphere :
      p ∈ Metric.sphere
        (D.vertexPlacement (tubeChains.edgeTargetVertex e))
        (controlDisks.vertexRadius (tubeChains.edgeTargetVertex e)) := by
    rcases hmeet with hsource | htarget
    · simpa [hsource.1] using hsource.2
    · simpa [htarget.1] using htarget.2
  have hpTarget :
      p = (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
        ⟨e, tubeChains.edgeTargetVertex_mem e⟩).target :=
    vertexSpokeBoundaryPointEqTarget
      (tubeChains.edgeTargetVertex e)
      ⟨e, tubeChains.edgeTargetVertex_mem e⟩ p hpTargetSpoke hpSphere
  have hlast := terminalTubeIndexGetLast e
  have hterminal_owner : tubeChains.owner (terminalTubeIndex e) = e :=
    (tubeChains.edgePieceOrder_owner_iff e (terminalTubeIndex e)).1
      (terminalTubeIndexMem e)
  have hterminal_attach :
      tubeChains.owner (terminalTubeIndex e) = e ∧
        (tubeChains.source (terminalTubeIndex e) =
            (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
              ⟨e, tubeChains.edgeTargetVertex_mem e⟩).target ∨
          tubeChains.target (terminalTubeIndex e) =
            (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
              ⟨e, tubeChains.edgeTargetVertex_mem e⟩).target) := by
    refine ⟨hterminal_owner, Or.inr ?_⟩
    calc
      tubeChains.target (terminalTubeIndex e) =
          (tubeChains.chain (terminalTubeIndex e)).target :=
        (tubeChains.chain_endpoints (terminalTubeIndex e)).2.symm
      _ = (PolygonalArcReverse
            (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
              ⟨e, tubeChains.edgeTargetVertex_mem e⟩)).source :=
        terminalTubeAttachesTargetSpoke e
      _ = (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
            ⟨e, tubeChains.edgeTargetVertex_mem e⟩).target := by
        rfl
  have hi_owner : tubeChains.owner i = e :=
    (tubeChains.edgePieceOrder_owner_iff e i).1 hi_mem
  have hi_attach :
      tubeChains.owner i = e ∧
        (tubeChains.source i =
            (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
              ⟨e, tubeChains.edgeTargetVertex_mem e⟩).target ∨
          tubeChains.target i =
            (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
              ⟨e, tubeChains.edgeTargetVertex_mem e⟩).target) := by
    refine ⟨hi_owner, ?_⟩
    rcases hmeet with hsource | htarget
    · left
      calc
        tubeChains.source i = p := hsource.1.symm
        _ = _ := hpTarget
    · right
      calc
        tubeChains.target i = p := htarget.1.symm
        _ = _ := hpTarget
  rcases localDiskFillings.vertex_spoke_attached_to_tube
      (tubeChains.edgeTargetVertex e)
      ⟨e, tubeChains.edgeTargetVertex_mem e⟩ with ⟨a, _ha, hunique⟩
  have hterminal_eq_a : terminalTubeIndex e = a :=
    hunique (terminalTubeIndex e) hterminal_attach
  have hi_eq_a : i = a := hunique i hi_attach
  have hi_eq_terminal : i = terminalTubeIndex e :=
    hi_eq_a.trans hterminal_eq_a.symm
  exact hnot_last (by simpa [hi_eq_terminal] using hlast)

private lemma tubeChainCarrierDisjointGapConnectorOfNotBoundary
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (gapConnectorEqOrReverse : ∀ e n,
      ∃ (x : {p // p ∈ D.intersectionPoints})
        (hxe : x.1 ∈ D.edgeRelativeInterior e),
        gapConnector e n =
            localDiskFillings.intersection_chain x ⟨e, hxe⟩ ∨
          gapConnector e n = PolygonalArcReverse
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩))
    (gapConnectorSource : ∀ e n,
      (gapConnector e n).source =
        tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]))
    (gapConnectorTarget : ∀ e n,
      (gapConnector e n).target =
        tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1])) :
    ∀ e (q : Fin ((tubeChains.edgePieceOrder e).length - 1)) i,
      i ∈ tubeChains.edgePieceOrder e →
        i ≠ (tubeChains.edgePieceOrder e)[q.1] →
          i ≠ (tubeChains.edgePieceOrder e)[q.1 + 1] →
            Disjoint (tubeChains.chain i).carrier
              (gapConnector e q).carrier := by
  intro e q i hi_mem hne_left hne_right
  rw [Set.disjoint_left]
  intro p hpTube hpGap
  have hq : q.1 + 1 < (tubeChains.edgePieceOrder e).length := by
    have hq' : q.1 < (tubeChains.edgePieceOrder e).length - 1 := q.2
    omega
  rcases gapConnectorEqOrReverse e q with ⟨x, hx_edge, hconnector⟩
  let connector := localDiskFillings.intersection_chain x ⟨e, hx_edge⟩
  have hpOrig : p ∈ connector.carrier := by
    rcases hconnector with hconnector | hconnector
    · simpa [connector, hconnector] using hpGap
    · simpa [connector, hconnector, PolygonalArcReverse] using hpGap
  have hpClosed :
      p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) :=
    localDiskFillings.intersection_chain_carrier_subset_closedBall x
      ⟨e, hx_edge⟩ hpOrig
  have hmeet :=
    tubeChains.chain_carrier_meets_intersection_closedBall_only_endpoint
      i x p hpTube hpClosed
  have hpSphere :
      p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
    rcases hmeet with hsource | htarget
    · simpa [hsource.1] using hsource.2
    · simpa [htarget.1] using htarget.2
  have hpEndpoint :=
    intersectionChainBoundaryPointEqEndpoint G D controlDisks tubeChains
      localDiskFillings x ⟨e, hx_edge⟩ p hpOrig hpSphere
  have hpGapEndpoint :
      p = (gapConnector e q).source ∨ p = (gapConnector e q).target := by
    rcases hconnector with hconnector | hconnector
    · simpa [connector, hconnector] using hpEndpoint
    · rcases hpEndpoint with hpSource | hpTarget
      · right
        simpa [connector, hconnector, PolygonalArcReverse] using hpSource
      · left
        simpa [connector, hconnector, PolygonalArcReverse] using hpTarget
  have hi_owner : tubeChains.owner i = e :=
    (tubeChains.edgePieceOrder_owner_iff e i).1 hi_mem
  have hi_attach :
      tubeChains.owner i = e ∧
        (tubeChains.source i = p ∨ tubeChains.target i = p) := by
    refine ⟨hi_owner, ?_⟩
    rcases hmeet with hsource | htarget
    · exact Or.inl hsource.1.symm
    · exact Or.inr htarget.1.symm
  rcases hpGapEndpoint with hpLeft | hpRight
  · have hp_left :
        p = tubeChains.target ((tubeChains.edgePieceOrder e)[q.1]) :=
      hpLeft.trans (gapConnectorSource e q)
    have hpEdge : p ∈ D.edgeCarrier e := by
      rw [hp_left]
      exact (Classical.choose_spec
        (tubeChains.edgePieceOrder_consecutive_intersection e q.1 hq)).2.2.1
    rcases tubeChains.intersection_boundary_attached
        (x := x) (e := e) (p := p) hx_edge hpSphere hpEdge with
      ⟨a, _ha, hunique⟩
    have hleft_mem :
        (tubeChains.edgePieceOrder e)[q.1] ∈ tubeChains.edgePieceOrder e :=
      List.getElem_mem (by omega)
    have hleft_owner :
        tubeChains.owner ((tubeChains.edgePieceOrder e)[q.1]) = e :=
      (tubeChains.edgePieceOrder_owner_iff e _).1 hleft_mem
    have hleft_attach :
        tubeChains.owner ((tubeChains.edgePieceOrder e)[q.1]) = e ∧
          (tubeChains.source ((tubeChains.edgePieceOrder e)[q.1]) = p ∨
            tubeChains.target ((tubeChains.edgePieceOrder e)[q.1]) = p) :=
      ⟨hleft_owner, Or.inr hp_left.symm⟩
    have hi_eq_a : i = a := hunique i hi_attach
    have hleft_eq_a : (tubeChains.edgePieceOrder e)[q.1] = a :=
      hunique ((tubeChains.edgePieceOrder e)[q.1]) hleft_attach
    exact hne_left (hi_eq_a.trans hleft_eq_a.symm)
  · have hp_right :
        p = tubeChains.source ((tubeChains.edgePieceOrder e)[q.1 + 1]) :=
      hpRight.trans (gapConnectorTarget e q)
    have hpEdge : p ∈ D.edgeCarrier e := by
      rw [hp_right]
      exact (Classical.choose_spec
        (tubeChains.edgePieceOrder_consecutive_intersection e q.1 hq)).2.2.2.2.1
    rcases tubeChains.intersection_boundary_attached
        (x := x) (e := e) (p := p) hx_edge hpSphere hpEdge with
      ⟨a, _ha, hunique⟩
    have hright_mem :
        (tubeChains.edgePieceOrder e)[q.1 + 1] ∈
          tubeChains.edgePieceOrder e :=
      List.getElem_mem hq
    have hright_owner :
        tubeChains.owner ((tubeChains.edgePieceOrder e)[q.1 + 1]) = e :=
      (tubeChains.edgePieceOrder_owner_iff e _).1 hright_mem
    have hright_attach :
        tubeChains.owner ((tubeChains.edgePieceOrder e)[q.1 + 1]) = e ∧
          (tubeChains.source ((tubeChains.edgePieceOrder e)[q.1 + 1]) = p ∨
            tubeChains.target ((tubeChains.edgePieceOrder e)[q.1 + 1]) = p) :=
      ⟨hright_owner, Or.inl hp_right.symm⟩
    have hi_eq_a : i = a := hunique i hi_attach
    have hright_eq_a : (tubeChains.edgePieceOrder e)[q.1 + 1] = a :=
      hunique ((tubeChains.edgePieceOrder e)[q.1 + 1]) hright_attach
    exact hne_right (hi_eq_a.trans hright_eq_a.symm)

private lemma gapConnectorCarrierDisjointGapConnectorOfNe
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (gapCenter :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) →
          {p // p ∈ D.intersectionPoints})
    (gapCenterEdge : ∀ e q,
      (gapCenter e q).1 ∈ D.edgeRelativeInterior e)
    (gapCenterInjective : ∀ e q r, gapCenter e q = gapCenter e r → q = r)
    (gapConnectorEqOrReverse : ∀ e q,
      gapConnector e q =
          localDiskFillings.intersection_chain (gapCenter e q)
            ⟨e, gapCenterEdge e q⟩ ∨
        gapConnector e q = PolygonalArcReverse
          (localDiskFillings.intersection_chain (gapCenter e q)
            ⟨e, gapCenterEdge e q⟩)) :
    ∀ e (q r : Fin ((tubeChains.edgePieceOrder e).length - 1)),
      q ≠ r → Disjoint (gapConnector e q).carrier (gapConnector e r).carrier := by
  intro e q r hqr
  have hcenter_ne : gapCenter e q ≠ gapCenter e r := by
    intro hcenter
    exact hqr (gapCenterInjective e q r hcenter)
  have hdisjoint :=
    intersectionChainCarrierDisjointIntersectionChainOfNe G D controlDisks
      tubeChains localDiskFillings (gapCenter e q) (gapCenter e r)
      ⟨e, gapCenterEdge e q⟩ ⟨e, gapCenterEdge e r⟩ hcenter_ne
  rcases gapConnectorEqOrReverse e q with hqeq | hqeq <;>
    rcases gapConnectorEqOrReverse e r with hreq | hreq
  · simpa [hqeq, hreq] using hdisjoint
  · simpa [hqeq, hreq, PolygonalArcReverse] using hdisjoint
  · simpa [hqeq, hreq, PolygonalArcReverse] using hdisjoint
  · simpa [hqeq, hreq, PolygonalArcReverse] using hdisjoint

private lemma gapCenterInjective
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (gapCenter :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) →
          {p // p ∈ D.intersectionPoints})
    (gapCenter_spec : ∀ e n,
      (gapCenter e n).1 ∈ D.edgeRelativeInterior e ∧
        tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ∈
            Metric.sphere (gapCenter e n).1
              (controlDisks.intersectionRadius (gapCenter e n)) ∧
          tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ∈
              D.edgeCarrier e ∧
            tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) ∈
                Metric.sphere (gapCenter e n).1
                  (controlDisks.intersectionRadius (gapCenter e n)) ∧
              tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) ∈
                  D.edgeCarrier e ∧
                tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ≠
                  tubeChains.source
                    ((tubeChains.edgePieceOrder e)[n.1 + 1])) :
    ∀ e (q r : Fin ((tubeChains.edgePieceOrder e).length - 1)),
      gapCenter e q = gapCenter e r → q = r := by
  intro e q r hcenter
  let L := tubeChains.edgePieceOrder e
  have hq : q.1 + 1 < L.length := by
    have hq' : q.1 < L.length - 1 := by simpa [L] using q.2
    omega
  have hr : r.1 + 1 < L.length := by
    have hr' : r.1 < L.length - 1 := by simpa [L] using r.2
    omega
  have hq0 : q.1 < L.length := by omega
  have hr0 : r.1 < L.length := by omega
  have hqspec := gapCenter_spec e q
  have hrspec := gapCenter_spec e r
  have hboundary_q :
      ∀ p,
        p ∈ Metric.sphere (gapCenter e q).1
            (controlDisks.intersectionRadius (gapCenter e q)) →
          p ∈ D.edgeCarrier e →
            p = tubeChains.target L[q.1] ∨
              p = tubeChains.source L[q.1 + 1] := by
    intro p hpSphere hpEdge
    rcases
      controlDisks.intersection_boundary_two_points
        (x := gapCenter e q) (e := e) hqspec.1 with
      ⟨a, b, hab, haSphere, haEdge, hbSphere, hbEdge, h_all⟩
    have htarget_ab :
        tubeChains.target L[q.1] = a ∨
          tubeChains.target L[q.1] = b := by
      exact h_all (tubeChains.target L[q.1])
        (by simpa [L] using hqspec.2.1)
        (by simpa [L] using hqspec.2.2.1)
    have hsource_ab :
        tubeChains.source L[q.1 + 1] = a ∨
          tubeChains.source L[q.1 + 1] = b := by
      exact h_all (tubeChains.source L[q.1 + 1])
        (by simpa [L] using hqspec.2.2.2.1)
        (by simpa [L] using hqspec.2.2.2.2.1)
    have hp_ab : p = a ∨ p = b := h_all p hpSphere hpEdge
    rcases htarget_ab with hta | htb <;>
      rcases hsource_ab with hsa | hsb <;>
      rcases hp_ab with hpa | hpb
    · exact False.elim (hqspec.2.2.2.2.2 (by rw [hta, hsa]))
    · exact False.elim (hqspec.2.2.2.2.2 (by rw [hta, hsa]))
    · exact Or.inl (by rw [hpa, ← hta])
    · exact Or.inr (by rw [hpb, ← hsb])
    · exact Or.inr (by rw [hpa, ← hsa])
    · exact Or.inl (by rw [hpb, ← htb])
    · exact False.elim (hqspec.2.2.2.2.2 (by rw [htb, hsb]))
    · exact False.elim (hqspec.2.2.2.2.2 (by rw [htb, hsb]))
  have endpoint_unique :
      ∀ p
        (hpSphere :
          p ∈ Metric.sphere (gapCenter e q).1
            (controlDisks.intersectionRadius (gapCenter e q)))
        (hpEdge : p ∈ D.edgeCarrier e)
        (i j : tubeChains.pieceIndex),
        tubeChains.owner i = e →
          (tubeChains.source i = p ∨ tubeChains.target i = p) →
            tubeChains.owner j = e →
              (tubeChains.source j = p ∨ tubeChains.target j = p) →
                i = j := by
    intro p hpSphere hpEdge i j hi_owner hi_endpoint hj_owner hj_endpoint
    rcases
      tubeChains.intersection_boundary_attached
        (x := gapCenter e q) (e := e) (p := p)
        hqspec.1 hpSphere hpEdge with
      ⟨a, _ha, hunique⟩
    have hi_eq_a : i = a := hunique i ⟨hi_owner, hi_endpoint⟩
    have hj_eq_a : j = a := hunique j ⟨hj_owner, hj_endpoint⟩
    exact hi_eq_a.trans hj_eq_a.symm
  have howner_q :
      tubeChains.owner L[q.1] = e :=
    (tubeChains.edgePieceOrder_owner_iff e L[q.1]).1
      (by
        dsimp [L]
        exact List.getElem_mem hq0)
  have howner_q1 :
      tubeChains.owner L[q.1 + 1] = e :=
    (tubeChains.edgePieceOrder_owner_iff e L[q.1 + 1]).1
      (by
        dsimp [L]
        exact List.getElem_mem hq)
  have howner_r :
      tubeChains.owner L[r.1] = e :=
    (tubeChains.edgePieceOrder_owner_iff e L[r.1]).1
      (by
        dsimp [L]
        exact List.getElem_mem hr0)
  have howner_r1 :
      tubeChains.owner L[r.1 + 1] = e :=
    (tubeChains.edgePieceOrder_owner_iff e L[r.1 + 1]).1
      (by
        dsimp [L]
        exact List.getElem_mem hr)
  have hr_target_boundary :
      tubeChains.target L[r.1] = tubeChains.target L[q.1] ∨
        tubeChains.target L[r.1] = tubeChains.source L[q.1 + 1] := by
    have hsphere :
        tubeChains.target L[r.1] ∈
          Metric.sphere (gapCenter e q).1
            (controlDisks.intersectionRadius (gapCenter e q)) := by
      simpa [L, ← hcenter] using hrspec.2.1
    have hedge : tubeChains.target L[r.1] ∈ D.edgeCarrier e := by
      simpa [L] using hrspec.2.2.1
    exact hboundary_q (tubeChains.target L[r.1]) hsphere hedge
  have hr_source_boundary :
      tubeChains.source L[r.1 + 1] = tubeChains.target L[q.1] ∨
        tubeChains.source L[r.1 + 1] = tubeChains.source L[q.1 + 1] := by
    have hsphere :
        tubeChains.source L[r.1 + 1] ∈
          Metric.sphere (gapCenter e q).1
            (controlDisks.intersectionRadius (gapCenter e q)) := by
      simpa [L, ← hcenter] using hrspec.2.2.2.1
    have hedge : tubeChains.source L[r.1 + 1] ∈ D.edgeCarrier e := by
      simpa [L] using hrspec.2.2.2.2.1
    exact hboundary_q (tubeChains.source L[r.1 + 1]) hsphere hedge
  have nodupL : L.Nodup := by
    simpa [L] using tubeChains.edgePieceOrder_nodup e
  rcases hr_target_boundary with hrt_left | hrt_right
  · have hpiece_eq : L[r.1] = L[q.1] := by
      exact endpoint_unique (tubeChains.target L[q.1])
        (by simpa [L] using hqspec.2.1)
        (by simpa [L] using hqspec.2.2.1)
        L[r.1] L[q.1] howner_r
        (Or.inr hrt_left) howner_q (Or.inr rfl)
    have hidx : r.1 = q.1 :=
      (nodupL.getElem_inj_iff (i := r.1) (j := q.1)
        (hi := hr0) (hj := hq0)).1 hpiece_eq
    exact Fin.ext hidx.symm
  · have hpiece_r_q1 : L[r.1] = L[q.1 + 1] := by
      exact endpoint_unique (tubeChains.source L[q.1 + 1])
        (by simpa [L] using hqspec.2.2.2.1)
        (by simpa [L] using hqspec.2.2.2.2.1)
        L[r.1] L[q.1 + 1] howner_r
        (Or.inr hrt_right) howner_q1 (Or.inl rfl)
    have hr_eq_q1 : r.1 = q.1 + 1 :=
      (nodupL.getElem_inj_iff (i := r.1) (j := q.1 + 1)
        (hi := hr0) (hj := hq)).1 hpiece_r_q1
    rcases hr_source_boundary with hrs_left | hrs_right
    · have hpiece_r1_q : L[r.1 + 1] = L[q.1] := by
        exact endpoint_unique (tubeChains.target L[q.1])
          (by simpa [L] using hqspec.2.1)
          (by simpa [L] using hqspec.2.2.1)
          L[r.1 + 1] L[q.1] howner_r1
          (Or.inl hrs_left) howner_q (Or.inr rfl)
      have hr1_eq_q : r.1 + 1 = q.1 :=
        (nodupL.getElem_inj_iff (i := r.1 + 1) (j := q.1)
          (hi := hr) (hj := hq0)).1 hpiece_r1_q
      omega
    · have hpiece_r1_q1 : L[r.1 + 1] = L[q.1 + 1] := by
        exact endpoint_unique (tubeChains.source L[q.1 + 1])
          (by simpa [L] using hqspec.2.2.2.1)
          (by simpa [L] using hqspec.2.2.2.2.1)
          L[r.1 + 1] L[q.1 + 1] howner_r1
          (Or.inl hrs_right) howner_q1 (Or.inl rfl)
      have hr1_eq_q1 : r.1 + 1 = q.1 + 1 :=
        (nodupL.getElem_inj_iff (i := r.1 + 1) (j := q.1 + 1)
          (hi := hr) (hj := hq)).1 hpiece_r1_q1
      exact Fin.ext (by omega)

private lemma gapConnectorEqOrReverseGapCenter
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (gapCenter :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) →
          {p // p ∈ D.intersectionPoints})
    (gapCenterEdge : ∀ e q,
      (gapCenter e q).1 ∈ D.edgeRelativeInterior e)
    (gapConnector_def : ∀ e q,
      let connector := localDiskFillings.intersection_chain (gapCenter e q)
        ⟨e, gapCenterEdge e q⟩
      gapConnector e q =
        if connector.source =
            tubeChains.target ((tubeChains.edgePieceOrder e)[q.1]) then
          connector
        else PolygonalArcReverse connector) :
    ∀ e q,
      gapConnector e q =
          localDiskFillings.intersection_chain (gapCenter e q)
            ⟨e, gapCenterEdge e q⟩ ∨
        gapConnector e q = PolygonalArcReverse
          (localDiskFillings.intersection_chain (gapCenter e q)
            ⟨e, gapCenterEdge e q⟩) := by
  intro e q
  rw [gapConnector_def e q]
  by_cases hsrc :
      (localDiskFillings.intersection_chain (gapCenter e q)
        ⟨e, gapCenterEdge e q⟩).source =
          tubeChains.target ((tubeChains.edgePieceOrder e)[q.1])
  · exact Or.inl (if_pos hsrc)
  · exact Or.inr (if_neg hsrc)

private lemma finiteAlternatingBlockIsChain
    (R : PolygonalArc → PolygonalArc → Prop) :
    ∀ (K : ℕ) (chain : Fin (K + 1) → PolygonalArc)
      (gap : Fin K → PolygonalArc),
      (∀ n : Fin K, R (chain (Fin.castSucc n)) (gap n)) →
      (∀ n : Fin K, R (gap n) (chain n.succ)) →
      List.IsChain R
        (((List.finRange K).map
          (fun n => [chain (Fin.castSucc n), gap n])).flatten ++
          [chain (Fin.last K)]) := by
  intro K chain gap hchain_gap hgap_chain
  induction K with
  | zero =>
      simp
  | succ K ih =>
      rw [List.finRange_succ]
      simp only [List.map_cons, List.flatten_cons, List.append_assoc]
      change List.IsChain R
        (chain (Fin.castSucc 0) :: gap 0 ::
          ((List.map (fun n => [chain n.castSucc, gap n])
            (List.map Fin.succ (List.finRange K))).flatten ++
            [chain (Fin.last (K + 1))]))
      rw [List.isChain_cons_cons]
      constructor
      · exact hchain_gap 0
      · refine List.IsChain.cons ?_ ?_
        · have ih' := ih (fun n => chain n.succ) (fun n => gap n.succ)
            (by
              intro n
              simpa using hchain_gap n.succ)
            (by
              intro n
              simpa using hgap_chain n.succ)
          have hlast : (Fin.last K).succ = Fin.last (K + 1) := by
            apply Fin.ext
            rfl
          have ih'' : List.IsChain R
              (((List.map (fun n => [chain n.castSucc, gap n])
                (List.map Fin.succ (List.finRange K))).flatten ++
                [chain (Fin.last K).succ])) := by
            simpa [List.map_map, Function.comp_def, Fin.succ,
              Fin.castSucc, List.append_assoc] using ih'
          simpa only [hlast] using ih''
        · intro y hy
          have hy' : y = chain (Fin.succ 0) := by
            cases K with
            | zero =>
                symm
                simpa [Fin.succ, Fin.last] using hy
            | succ K =>
                symm
                have hy0 :
                    chain (Fin.castSucc (Fin.succ (0 : Fin (K + 1)))) = y := by
                  simpa [List.finRange_succ, List.map_map,
                    Function.comp_def] using hy
                have hidx :
                    Fin.castSucc (Fin.succ (0 : Fin (K + 1))) =
                      Fin.succ (0 : Fin (K + 2)) := by
                  apply Fin.ext
                  rfl
                simpa only [hidx] using hy0
          subst y
          exact hgap_chain 0

private lemma finiteAlternatingBlockLength :
    ∀ (K : ℕ) (chain : Fin (K + 1) → PolygonalArc)
      (gap : Fin K → PolygonalArc),
      ((((List.finRange K).map
          (fun q => [chain q.castSucc, gap q])).flatten ++
        [chain (Fin.last K)]).length = 2 * K + 1) := by
  intro K chain gap
  have hmap :
      List.map (List.length ∘ fun q => [chain q.castSucc, gap q])
          (List.finRange K) = List.replicate K 2 := by
    simp [Function.comp_def]
  simp [List.length_flatten, hmap, List.sum_replicate]
  omega

private lemma finiteAlternatingBlockGetChain :
    ∀ (K : ℕ) (chain : Fin (K + 1) → PolygonalArc)
      (gap : Fin K → PolygonalArc) (q : Fin K),
      ((((List.finRange K).map
          (fun q => [chain q.castSucc, gap q])).flatten ++
        [chain (Fin.last K)])[2 * q.1]? =
        some (chain q.castSucc)) := by
  intro K
  induction K with
  | zero =>
      intro chain gap q
      exact Fin.elim0 q
  | succ K ih =>
      intro chain gap q
      rw [List.finRange_succ]
      cases q using Fin.cases with
      | zero =>
          simp
      | succ q =>
          have ihq := ih (fun r : Fin (K + 1) => chain r.succ)
            (fun r : Fin K => gap r.succ) q
          have hlast : (Fin.last K).succ = Fin.last (K + 1) := by
            apply Fin.ext
            rfl
          rw [hlast] at ihq
          simp only [List.map_cons, List.flatten_cons, List.cons_append]
          simp [Fin.succ]
          simpa [List.finRange_succ, List.map_map, Function.comp_def,
            Fin.succ, Nat.mul_add] using ihq

private lemma finiteAlternatingBlockGetGap :
    ∀ (K : ℕ) (chain : Fin (K + 1) → PolygonalArc)
      (gap : Fin K → PolygonalArc) (q : Fin K),
      ((((List.finRange K).map
          (fun q => [chain q.castSucc, gap q])).flatten ++
        [chain (Fin.last K)])[2 * q.1 + 1]? =
        some (gap q)) := by
  intro K
  induction K with
  | zero =>
      intro chain gap q
      exact Fin.elim0 q
  | succ K ih =>
      intro chain gap q
      rw [List.finRange_succ]
      cases q using Fin.cases with
      | zero =>
          simp
      | succ q =>
          have ihq := ih (fun r : Fin (K + 1) => chain r.succ)
            (fun r : Fin K => gap r.succ) q
          have hlast : (Fin.last K).succ = Fin.last (K + 1) := by
            apply Fin.ext
            rfl
          rw [hlast] at ihq
          simp only [List.map_cons, List.flatten_cons, List.cons_append]
          simp [Fin.succ]
          simpa [List.finRange_succ, List.map_map, Function.comp_def,
            Fin.succ, Nat.mul_add] using ihq

private lemma finiteAlternatingBlockGetLast :
    ∀ (K : ℕ) (chain : Fin (K + 1) → PolygonalArc)
      (gap : Fin K → PolygonalArc),
      ((((List.finRange K).map
          (fun q => [chain q.castSucc, gap q])).flatten ++
        [chain (Fin.last K)])[2 * K]? =
        some (chain (Fin.last K))) := by
  intro K
  induction K with
  | zero =>
      intro chain gap
      simp
  | succ K ih =>
      intro chain gap
      have ih' := ih (fun r : Fin (K + 1) => chain r.succ)
        (fun r : Fin K => gap r.succ)
      rw [List.finRange_succ]
      simp only [List.map_cons, List.flatten_cons, List.cons_append]
      simp [Fin.last, Fin.succ, Nat.mul_add]
      simpa [List.finRange_succ, List.map_map, Function.comp_def,
        Fin.last, Fin.succ, Nat.mul_add] using ih'

private def tubeGapBlockForAttach
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (e : G.edgeFinset)
    (n : Fin ((tubeChains.edgePieceOrder e).length - 1)) :
    List PolygonalArc := by
  have hn : n.1 < (tubeChains.edgePieceOrder e).length := by omega
  exact [tubeChains.chain ((tubeChains.edgePieceOrder e)[n.1]), gapConnector e n]

private def orderedPiecesForAttach
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (e : G.edgeFinset) : List PolygonalArc :=
  ([sourceSpoke e] ++
      ((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
        (fun n => tubeGapBlockForAttach G D controlDisks tubeChains
          gapConnector e n)).flatten ++
      [tubeChains.chain (terminalTubeIndex e)]) ++
    [targetSpokeReverse e]

private lemma orderedPiecesForAttachLength
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc) :
    ∀ e,
      (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e).length =
        2 * (tubeChains.edgePieceOrder e).length + 1 := by
  intro e
  have hlen_pos : 0 < (tubeChains.edgePieceOrder e).length :=
    Nat.pos_of_ne_zero (tubeChains.edgePieceOrder_nonempty e)
  have hmap :
      List.map
          (List.length ∘ fun n =>
            tubeGapBlockForAttach G D controlDisks tubeChains gapConnector e n)
          (List.finRange ((tubeChains.edgePieceOrder e).length - 1)) =
        List.replicate ((tubeChains.edgePieceOrder e).length - 1) 2 := by
    simp [Function.comp_def, tubeGapBlockForAttach]
  simp [orderedPiecesForAttach, List.length_flatten, hmap,
    List.sum_replicate]
  omega

private lemma orderedPiecesForAttachGetSource
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc) :
    ∀ e,
      (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e)[0]? =
        some (sourceSpoke e) := by
  intro e
  simp [orderedPiecesForAttach]

private lemma orderedPiecesForAttachGetTarget
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc) :
    ∀ e,
      (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e)[
          2 * (tubeChains.edgePieceOrder e).length]? =
        some (targetSpokeReverse e) := by
  intro e
  have hlast :
      (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e).getLast? =
        some (targetSpokeReverse e) := by
    simpa [orderedPiecesForAttach] using
      (List.getLast?_append_of_ne_nil
        ([sourceSpoke e] ++
          ((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
            (fun n => tubeGapBlockForAttach G D controlDisks tubeChains
              gapConnector e n)).flatten ++
          [tubeChains.chain (terminalTubeIndex e)])
        (l₂ := [targetSpokeReverse e]) (by simp))
  rw [List.getLast?_eq_getElem?] at hlast
  have hidx :
      (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e).length - 1 =
        2 * (tubeChains.edgePieceOrder e).length := by
    rw [orderedPiecesForAttachLength G D controlDisks tubeChains sourceSpoke
      targetSpokeReverse terminalTubeIndex gapConnector e]
    omega
  rw [hidx] at hlast
  exact hlast

private lemma orderedPiecesForAttachGetOfBlock
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc) :
    ∀ (e : G.edgeFinset) (n : ℕ) (Γ : PolygonalArc),
      (((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
          (fun q => tubeGapBlockForAttach G D controlDisks tubeChains
            gapConnector e q)).flatten ++
        [tubeChains.chain (terminalTubeIndex e)])[n]? = some Γ →
      (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e)[1 + n]? = some Γ := by
  intro e n Γ h
  let block : List PolygonalArc :=
    ((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
      (fun q => tubeGapBlockForAttach G D controlDisks tubeChains
        gapConnector e q)).flatten ++
      [tubeChains.chain (terminalTubeIndex e)]
  have hn : n < block.length := by
    dsimp [block]
    rcases List.getElem?_eq_some_iff.mp h with ⟨hn, _⟩
    exact hn
  have hshape :
      orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
          targetSpokeReverse terminalTubeIndex gapConnector e =
        sourceSpoke e :: (block ++ [targetSpokeReverse e]) := by
    simp [orderedPiecesForAttach, block, List.append_assoc]
  rw [hshape, show 1 + n = n + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_left hn]
  simpa [block] using h

private lemma orderedPiecesForAttachGetTube
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (terminalTubeIndex_getLast : ∀ e,
      (tubeChains.edgePieceOrder e).getLast? = some (terminalTubeIndex e)) :
    ∀ (e : G.edgeFinset) q
      (hq : q < (tubeChains.edgePieceOrder e).length),
      (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e)[1 + 2 * q]? =
        some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q])) := by
  intro e q hq
  let L := tubeChains.edgePieceOrder e
  let K := L.length - 1
  have hL_nonzero : L.length ≠ 0 := by
    dsimp [L]
    exact tubeChains.edgePieceOrder_nonempty e
  have hK_last : K < L.length := by
    dsimp [K]
    omega
  have hlast_get? : L[K]? = some (terminalTubeIndex e) := by
    have hlast := terminalTubeIndex_getLast e
    rw [List.getLast?_eq_getElem?] at hlast
    simpa [L, K] using hlast
  have hlast_eq : L.get ⟨K, hK_last⟩ = terminalTubeIndex e := by
    have hget := hlast_get?
    rw [List.getElem?_eq_getElem hK_last] at hget
    exact Option.some.inj hget
  let chainAt : Fin (K + 1) → PolygonalArc := fun r =>
    tubeChains.chain (L.get ⟨r.1, by
      have hr : r.1 < K + 1 := r.2
      dsimp [K] at hr ⊢
      omega⟩)
  let blockList : List PolygonalArc :=
    ((List.finRange K).map
      (fun r => [chainAt (Fin.castSucc r), gapConnector e r])).flatten ++
      [chainAt (Fin.last K)]
  have hblockList_eq :
      blockList =
        ((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
          (fun r => tubeGapBlockForAttach G D controlDisks tubeChains
            gapConnector e r)).flatten ++
          [tubeChains.chain (terminalTubeIndex e)] := by
    have hterminal_index :
        ∀ h : L.length - 1 < L.length,
          L.get ⟨L.length - 1, h⟩ = terminalTubeIndex e := by
      intro h
      have hfin :
          (⟨L.length - 1, h⟩ : Fin L.length) = ⟨K, hK_last⟩ := by
        apply Fin.ext
        simp [K]
      simpa [hfin] using hlast_eq
    have hterminal_chain :
        ∀ h : L.length - 1 < L.length,
          tubeChains.chain (L.get ⟨L.length - 1, h⟩) =
            tubeChains.chain (terminalTubeIndex e) := by
      intro h
      exact congrArg tubeChains.chain (hterminal_index h)
    simp [blockList, tubeGapBlockForAttach, chainAt, L, K]
    simpa [L] using
      hterminal_chain (by simpa [L, K] using hK_last)
  by_cases hqK : q < K
  · let qFin : Fin K := ⟨q, hqK⟩
    have hget := finiteAlternatingBlockGetChain K chainAt
      (fun r : Fin K => gapConnector e r) qFin
    have hgetBlockList :
        blockList[2 * q]? = some (chainAt qFin.castSucc) := by
      simpa [blockList, qFin] using hget
    rw [hblockList_eq] at hgetBlockList
    have hblock :
        (((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
            (fun r => tubeGapBlockForAttach G D controlDisks tubeChains
              gapConnector e r)).flatten ++
          [tubeChains.chain (terminalTubeIndex e)])[2 * q]? =
          some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q])) := by
      simpa [qFin, chainAt, L, K] using hgetBlockList
    simpa using orderedPiecesForAttachGetOfBlock G D controlDisks tubeChains
      sourceSpoke targetSpokeReverse terminalTubeIndex gapConnector e (2 * q)
      (tubeChains.chain ((tubeChains.edgePieceOrder e)[q])) hblock
  · have hqL : q < L.length := by
      simpa [L] using hq
    have hqeq : q = K := by
      dsimp [K] at hqK ⊢
      omega
    subst q
    have hget := finiteAlternatingBlockGetLast K chainAt
      (fun r : Fin K => gapConnector e r)
    have hgetBlockList :
        blockList[2 * K]? = some (chainAt (Fin.last K)) := by
      simpa [blockList] using hget
    rw [hblockList_eq] at hgetBlockList
    have hblock :
        (((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
            (fun r => tubeGapBlockForAttach G D controlDisks tubeChains
              gapConnector e r)).flatten ++
          [tubeChains.chain (terminalTubeIndex e)])[2 * K]? =
          some (tubeChains.chain ((tubeChains.edgePieceOrder e)[K])) := by
      simpa [chainAt, L, K] using hgetBlockList
    simpa using orderedPiecesForAttachGetOfBlock G D controlDisks tubeChains
      sourceSpoke targetSpokeReverse terminalTubeIndex gapConnector e (2 * K)
      (tubeChains.chain ((tubeChains.edgePieceOrder e)[K])) hblock

private lemma orderedPiecesForAttachGetGap
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (terminalTubeIndex_getLast : ∀ e,
      (tubeChains.edgePieceOrder e).getLast? = some (terminalTubeIndex e)) :
    ∀ (e : G.edgeFinset) q
      (hq : q + 1 < (tubeChains.edgePieceOrder e).length),
      (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e)[2 + 2 * q]? =
        some (gapConnector e ⟨q, by omega⟩) := by
  intro e q hq
  let L := tubeChains.edgePieceOrder e
  let K := L.length - 1
  have hL_nonzero : L.length ≠ 0 := by
    dsimp [L]
    exact tubeChains.edgePieceOrder_nonempty e
  have hK_last : K < L.length := by
    dsimp [K]
    omega
  have hlast_get? : L[K]? = some (terminalTubeIndex e) := by
    have hlast := terminalTubeIndex_getLast e
    rw [List.getLast?_eq_getElem?] at hlast
    simpa [L, K] using hlast
  have hlast_eq : L.get ⟨K, hK_last⟩ = terminalTubeIndex e := by
    have hget := hlast_get?
    rw [List.getElem?_eq_getElem hK_last] at hget
    exact Option.some.inj hget
  let chainAt : Fin (K + 1) → PolygonalArc := fun r =>
    tubeChains.chain (L.get ⟨r.1, by
      have hr : r.1 < K + 1 := r.2
      dsimp [K] at hr ⊢
      omega⟩)
  let blockList : List PolygonalArc :=
    ((List.finRange K).map
      (fun r => [chainAt (Fin.castSucc r), gapConnector e r])).flatten ++
      [chainAt (Fin.last K)]
  have hblockList_eq :
      blockList =
        ((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
          (fun r => tubeGapBlockForAttach G D controlDisks tubeChains
            gapConnector e r)).flatten ++
          [tubeChains.chain (terminalTubeIndex e)] := by
    have hterminal_index :
        ∀ h : L.length - 1 < L.length,
          L.get ⟨L.length - 1, h⟩ = terminalTubeIndex e := by
      intro h
      have hfin :
          (⟨L.length - 1, h⟩ : Fin L.length) = ⟨K, hK_last⟩ := by
        apply Fin.ext
        simp [K]
      simpa [hfin] using hlast_eq
    have hterminal_chain :
        ∀ h : L.length - 1 < L.length,
          tubeChains.chain (L.get ⟨L.length - 1, h⟩) =
            tubeChains.chain (terminalTubeIndex e) := by
      intro h
      exact congrArg tubeChains.chain (hterminal_index h)
    simp [blockList, tubeGapBlockForAttach, chainAt, L, K]
    simpa [L] using
      hterminal_chain (by simpa [L, K] using hK_last)
  have hqK : q < K := by
    dsimp [K, L]
    omega
  let qFin : Fin K := ⟨q, hqK⟩
  have hget := finiteAlternatingBlockGetGap K chainAt
    (fun r : Fin K => gapConnector e r) qFin
  have hgetBlockList :
      blockList[2 * q + 1]? = some (gapConnector e qFin) := by
    simpa [blockList, qFin] using hget
  rw [hblockList_eq] at hgetBlockList
  have hblock :
      (((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
          (fun r => tubeGapBlockForAttach G D controlDisks tubeChains
            gapConnector e r)).flatten ++
        [tubeChains.chain (terminalTubeIndex e)])[2 * q + 1]? =
        some (gapConnector e ⟨q, by omega⟩) := by
    simpa [qFin, L, K] using hgetBlockList
  have hres := orderedPiecesForAttachGetOfBlock G D controlDisks tubeChains
    sourceSpoke targetSpokeReverse terminalTubeIndex gapConnector e (2 * q + 1)
    (gapConnector e ⟨q, by omega⟩) hblock
  have hidx : 1 + (1 + 2 * q) = 2 + 2 * q := by omega
  simpa [hidx, qFin, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hres

private lemma orderedPiecesForAttachGetTerminal
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (terminalTubeIndex_getLast : ∀ e,
      (tubeChains.edgePieceOrder e).getLast? = some (terminalTubeIndex e)) :
    ∀ e,
      (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e)[
          2 * (tubeChains.edgePieceOrder e).length - 1]? =
        some (tubeChains.chain (terminalTubeIndex e)) := by
  intro e
  let L := tubeChains.edgePieceOrder e
  have hL_nonzero : L.length ≠ 0 := by
    dsimp [L]
    exact tubeChains.edgePieceOrder_nonempty e
  have hlast_get? : L[L.length - 1]? = some (terminalTubeIndex e) := by
    have hlast := terminalTubeIndex_getLast e
    rw [List.getLast?_eq_getElem?] at hlast
    simpa [L] using hlast
  have hlast_lt : L.length - 1 < L.length := by omega
  have hlast_eq :
      L.get ⟨L.length - 1, hlast_lt⟩ = terminalTubeIndex e := by
    have hget := hlast_get?
    rw [List.getElem?_eq_getElem hlast_lt] at hget
    exact Option.some.inj hget
  have htube := orderedPiecesForAttachGetTube G D controlDisks tubeChains
    sourceSpoke targetSpokeReverse terminalTubeIndex gapConnector
    terminalTubeIndex_getLast e (L.length - 1) (by simpa [L] using hlast_lt)
  have hidx :
      1 + 2 * (L.length - 1) =
        2 * (tubeChains.edgePieceOrder e).length - 1 := by
    have hpos : 0 < L.length := Nat.pos_of_ne_zero hL_nonzero
    dsimp [L] at hpos ⊢
    omega
  have hchain :
      tubeChains.chain ((tubeChains.edgePieceOrder e)[L.length - 1]) =
        tubeChains.chain (terminalTubeIndex e) := by
    dsimp [L] at hlast_eq ⊢
    exact congrArg tubeChains.chain hlast_eq
  simpa [hidx, hchain, L] using htube

private lemma orderedPiecesForAttachGetClassify
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (terminalTubeIndex_getLast : ∀ e,
      (tubeChains.edgePieceOrder e).getLast? = some (terminalTubeIndex e)) :
    ∀ e m
      (hm : m <
        (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
          targetSpokeReverse terminalTubeIndex gapConnector e).length),
      (m = 0 ∧
          (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
            targetSpokeReverse terminalTubeIndex gapConnector e)[m]? =
            some (sourceSpoke e)) ∨
        (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
          m = 1 + 2 * q ∧
            (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
              targetSpokeReverse terminalTubeIndex gapConnector e)[m]? =
              some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q]))) ∨
        (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
          m = 2 + 2 * q ∧
            (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
              targetSpokeReverse terminalTubeIndex gapConnector e)[m]? =
              some (gapConnector e ⟨q, by omega⟩)) ∨
        (m = 2 * (tubeChains.edgePieceOrder e).length - 1 ∧
          (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
            targetSpokeReverse terminalTubeIndex gapConnector e)[m]? =
            some (tubeChains.chain (terminalTubeIndex e))) ∨
        (m = 2 * (tubeChains.edgePieceOrder e).length ∧
          (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
            targetSpokeReverse terminalTubeIndex gapConnector e)[m]? =
            some (targetSpokeReverse e)) := by
  intro e m hm
  let len := (tubeChains.edgePieceOrder e).length
  have hlen_pos : 0 < len := by
    dsimp [len]
    exact Nat.pos_of_ne_zero (tubeChains.edgePieceOrder_nonempty e)
  have hm_len : m < 2 * len + 1 := by
    rw [orderedPiecesForAttachLength G D controlDisks tubeChains sourceSpoke
      targetSpokeReverse terminalTubeIndex gapConnector e] at hm
    simpa [len] using hm
  by_cases hm0 : m = 0
  · left
    refine ⟨hm0, ?_⟩
    simpa [hm0] using orderedPiecesForAttachGetSource G D controlDisks
      tubeChains sourceSpoke targetSpokeReverse terminalTubeIndex gapConnector e
  by_cases hmtarget : m = 2 * len
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by
        simpa [len] using hmtarget, by
        simpa [hmtarget, len] using orderedPiecesForAttachGetTarget G D
          controlDisks tubeChains sourceSpoke targetSpokeReverse
          terminalTubeIndex gapConnector e⟩)))
  by_cases hmterminal : m = 2 * len - 1
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by
        simpa [len] using hmterminal, by
        simpa [hmterminal, len] using orderedPiecesForAttachGetTerminal G D
          controlDisks tubeChains sourceSpoke targetSpokeReverse
          terminalTubeIndex gapConnector terminalTubeIndex_getLast e⟩)))
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hm_before_terminal : m < 2 * len - 1 := by omega
  let t := m - 1
  have ht_bound : t < 2 * (len - 1) := by
    dsimp [t]
    omega
  rcases Nat.even_or_odd' t with ⟨q, ht | ht⟩
  · have hq : q + 1 < len := by omega
    have hm_eq : m = 1 + 2 * q := by
      dsimp [t] at ht
      omega
    exact Or.inr (Or.inl ⟨q, by
      simpa [len] using hq, hm_eq, by
        have hget := orderedPiecesForAttachGetTube G D controlDisks
          tubeChains sourceSpoke targetSpokeReverse terminalTubeIndex gapConnector
          terminalTubeIndex_getLast e q (by
            simpa [len] using (show q < len by omega))
        simpa [hm_eq] using hget⟩)
  · have hq : q + 1 < len := by omega
    have hm_eq : m = 2 + 2 * q := by
      dsimp [t] at ht
      omega
    exact Or.inr (Or.inr (Or.inl ⟨q, by
      simpa [len] using hq, hm_eq, by
        have hget := orderedPiecesForAttachGetGap G D controlDisks tubeChains
          sourceSpoke targetSpokeReverse terminalTubeIndex gapConnector
          terminalTubeIndex_getLast e q (by simpa [len] using hq)
        simpa [hm_eq] using hget⟩))

private lemma orderedPiecesForAttachNonSuccessiveDisjoint
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (sourceSpoke_def : ∀ e, sourceSpoke e =
      localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
        ⟨e, tubeChains.edgeSourceVertex_mem e⟩)
    (targetSpokeReverse_def : ∀ e, targetSpokeReverse e =
      PolygonalArcReverse
        (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
          ⟨e, tubeChains.edgeTargetVertex_mem e⟩))
    (terminalTubeIndex_getLast : ∀ e,
      (tubeChains.edgePieceOrder e).getLast? = some (terminalTubeIndex e))
    (terminalTubeIndex_mem : ∀ e,
      terminalTubeIndex e ∈ tubeChains.edgePieceOrder e)
    (gapConnector_eq_or_reverse : ∀ e n,
      ∃ (x : {p // p ∈ D.intersectionPoints})
        (hxe : x.1 ∈ D.edgeRelativeInterior e),
        gapConnector e n =
            localDiskFillings.intersection_chain x ⟨e, hxe⟩ ∨
          gapConnector e n = PolygonalArcReverse
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩))
    (sourceSpoke_carrier_disjoint_tube_chain_of_not_head : ∀ e i,
      i ∈ tubeChains.edgePieceOrder e →
        (tubeChains.edgePieceOrder e).head? ≠ some i →
          Disjoint (sourceSpoke e).carrier (tubeChains.chain i).carrier)
    (targetSpokeReverse_carrier_disjoint_tube_chain_of_not_last : ∀ e i,
      i ∈ tubeChains.edgePieceOrder e →
        (tubeChains.edgePieceOrder e).getLast? ≠ some i →
          Disjoint (targetSpokeReverse e).carrier (tubeChains.chain i).carrier)
    (tube_chain_carrier_disjoint_gapConnector_of_not_boundary :
      ∀ e (q : Fin ((tubeChains.edgePieceOrder e).length - 1)) i,
        i ∈ tubeChains.edgePieceOrder e →
          i ≠ (tubeChains.edgePieceOrder e)[q.1] →
            i ≠ (tubeChains.edgePieceOrder e)[q.1 + 1] →
              Disjoint (tubeChains.chain i).carrier (gapConnector e q).carrier)
    (gapConnector_carrier_disjoint_gapConnector_of_ne :
      ∀ e (q r : Fin ((tubeChains.edgePieceOrder e).length - 1)),
        q ≠ r → Disjoint (gapConnector e q).carrier (gapConnector e r).carrier)
    (orderedPieces_get?_classify :
      ∀ e m (hm : m < (orderedPieces e).length),
        (m = 0 ∧ (orderedPieces e)[m]? = some (sourceSpoke e)) ∨
          (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
            m = 1 + 2 * q ∧
              (orderedPieces e)[m]? =
                some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q]))) ∨
          (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
            m = 2 + 2 * q ∧
              (orderedPieces e)[m]? =
                some (gapConnector e ⟨q, by omega⟩)) ∨
          (m = 2 * (tubeChains.edgePieceOrder e).length - 1 ∧
            (orderedPieces e)[m]? =
              some (tubeChains.chain (terminalTubeIndex e))) ∨
          (m = 2 * (tubeChains.edgePieceOrder e).length ∧
            (orderedPieces e)[m]? = some (targetSpokeReverse e))) :
    ∀ e m n (hm : m < (orderedPieces e).length)
      (hn : n < (orderedPieces e).length),
      m + 1 < n ∨ n + 1 < m →
        Disjoint ((orderedPieces e)[m]).carrier
          ((orderedPieces e)[n]).carrier := by
  intro e m n hm hn hmn
  have prove_forward :
      ∀ m n (hm : m < (orderedPieces e).length)
        (hn : n < (orderedPieces e).length),
        m + 1 < n →
          Disjoint ((orderedPieces e)[m]).carrier
            ((orderedPieces e)[n]).carrier := by
    intro m n hm hn hmn
    let L := tubeChains.edgePieceOrder e
    have hlen_pos : 0 < L.length := by
      dsimp [L]
      exact Nat.pos_of_ne_zero (tubeChains.edgePieceOrder_nonempty e)
    have hnodup : L.Nodup := by
      dsimp [L]
      exact tubeChains.edgePieceOrder_nodup e
    have get_eq_of_get? :
        ∀ {k : ℕ} {Γ : PolygonalArc} (hk : k < (orderedPieces e).length),
          (orderedPieces e)[k]? = some Γ → (orderedPieces e)[k] = Γ := by
      intro k Γ hk hget
      rw [List.getElem?_eq_getElem hk] at hget
      exact Option.some.inj hget
    have head_eq : L.head? = some L[0] := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen_pos]
    have last_eq : L.getLast? = some L[L.length - 1] := by
      rw [List.getLast?_eq_getElem?]
      rw [List.getElem?_eq_getElem (by omega : L.length - 1 < L.length)]
    have not_head_of_pos :
        ∀ {q : ℕ} (hq : q < L.length), 0 < q → L.head? ≠ some L[q] := by
      intro q hq hqpos hhead
      rw [head_eq] at hhead
      have hidx : (0 : ℕ) = q :=
        (hnodup.getElem_inj_iff (i := 0) (j := q)
          (hi := hlen_pos) (hj := hq)).1 (Option.some.inj hhead)
      omega
    have not_last_of_not_terminal :
        ∀ {q : ℕ} (hq : q < L.length), q ≠ L.length - 1 →
          L.getLast? ≠ some L[q] := by
      intro q hq hqne hlast
      rw [last_eq] at hlast
      have hidx : L.length - 1 = q :=
        (hnodup.getElem_inj_iff (i := L.length - 1) (j := q)
          (hi := by omega) (hj := hq)).1 (Option.some.inj hlast)
      exact hqne hidx.symm
    have terminal_ne_get_of_not_terminal :
        ∀ {q : ℕ} (hq : q < L.length), q ≠ L.length - 1 →
          terminalTubeIndex e ≠ L[q] := by
      intro q hq hqne heq
      exact (not_last_of_not_terminal hq hqne) (by
        simpa [L, heq] using terminalTubeIndex_getLast e)
    have chain_ne_of_index_ne :
        ∀ {q r : ℕ} (hq : q < L.length) (hr : r < L.length),
          q ≠ r → L[q] ≠ L[r] := by
      intro q r hq hr hqr heq
      have hidx : q = r :=
        (hnodup.getElem_inj_iff (i := q) (j := r)
          (hi := hq) (hj := hr)).1 heq
      exact hqr hidx
    rcases orderedPieces_get?_classify e m hm with
      ⟨hm_source, hm_get⟩ |
      ⟨q, hq, hm_tube, hm_get⟩ |
      ⟨q, hq, hm_gap, hm_get⟩ |
      ⟨hm_terminal, hm_get⟩ |
      ⟨hm_target, hm_get⟩
    · have hm_piece : (orderedPieces e)[m] = sourceSpoke e :=
        get_eq_of_get? (k := m) (Γ := sourceSpoke e) hm hm_get
      rcases orderedPieces_get?_classify e n hn with
        ⟨hn_source, hn_get⟩ |
        ⟨r, hr, hn_tube, hn_get⟩ |
        ⟨r, hr, hn_gap, hn_get⟩ |
        ⟨hn_terminal, hn_get⟩ |
        ⟨hn_target, hn_get⟩
      · omega
      · have hn_piece : (orderedPieces e)[n] = tubeChains.chain L[r] := by
          exact get_eq_of_get? (k := n) (Γ := tubeChains.chain L[r])
            hn (by simpa [L] using hn_get)
        have hr_pos : 0 < r := by omega
        have hr_lt : r < L.length := by
          dsimp [L]
          omega
        have hmem : L[r] ∈ tubeChains.edgePieceOrder e := by
          dsimp [L]
          exact List.getElem_mem hr_lt
        have hnot_head :
            (tubeChains.edgePieceOrder e).head? ≠ some L[r] := by
          dsimp [L]
          exact not_head_of_pos hr_lt hr_pos
        rw [hm_piece, hn_piece]
        exact sourceSpoke_carrier_disjoint_tube_chain_of_not_head e L[r]
          hmem hnot_head
      · have hn_piece :
            (orderedPieces e)[n] = gapConnector e ⟨r, by omega⟩ :=
          get_eq_of_get? (k := n) (Γ := gapConnector e ⟨r, by omega⟩) hn hn_get
        rcases gapConnector_eq_or_reverse e ⟨r, by omega⟩ with
          ⟨x, hxe, hgap | hgap⟩
        · rw [hm_piece, hn_piece, hgap, sourceSpoke_def e]
          exact vertexSpokeCarrierDisjointIntersectionChain G D controlDisks
            tubeChains localDiskFillings (tubeChains.edgeSourceVertex e)
            ⟨e, tubeChains.edgeSourceVertex_mem e⟩ x ⟨e, hxe⟩
        · rw [hm_piece, hn_piece, hgap, sourceSpoke_def e]
          simpa [PolygonalArcReverse] using
            vertexSpokeCarrierDisjointIntersectionChain G D controlDisks
              tubeChains localDiskFillings (tubeChains.edgeSourceVertex e)
              ⟨e, tubeChains.edgeSourceVertex_mem e⟩ x ⟨e, hxe⟩
      · have hn_piece :
            (orderedPieces e)[n] = tubeChains.chain (terminalTubeIndex e) :=
          get_eq_of_get? (k := n) (Γ := tubeChains.chain (terminalTubeIndex e))
            hn hn_get
        have hlen_gt_one : 1 < L.length := by
          change 1 < (tubeChains.edgePieceOrder e).length
          omega
        have hnot_head :
            (tubeChains.edgePieceOrder e).head? ≠ some (terminalTubeIndex e) := by
          intro hhead
          have hlast_terminal : L.getLast? = some (terminalTubeIndex e) := by
            simpa [L] using terminalTubeIndex_getLast e
          have hidx : (0 : ℕ) = L.length - 1 := by
            rw [head_eq] at hhead
            rw [last_eq] at hlast_terminal
            have heq : L[0] = L[L.length - 1] :=
              (Option.some.inj hhead).trans (Option.some.inj hlast_terminal).symm
            exact (hnodup.getElem_inj_iff (i := 0) (j := L.length - 1)
              (hi := hlen_pos) (hj := by omega)).1 heq
          omega
        rw [hm_piece, hn_piece]
        exact sourceSpoke_carrier_disjoint_tube_chain_of_not_head e
          (terminalTubeIndex e) (terminalTubeIndex_mem e) hnot_head
      · have hn_piece : (orderedPieces e)[n] = targetSpokeReverse e :=
          get_eq_of_get? (k := n) (Γ := targetSpokeReverse e) hn hn_get
        rw [hm_piece, hn_piece, sourceSpoke_def e, targetSpokeReverse_def e]
        simpa [PolygonalArcReverse] using
          vertexSpokeCarrierDisjointVertexSpokeOfNe G D controlDisks tubeChains
            localDiskFillings ⟨e, tubeChains.edgeSourceVertex_mem e⟩
            ⟨e, tubeChains.edgeTargetVertex_mem e⟩
            (edgeSourceVertexNeTargetVertex G D controlDisks tubeChains e)
    · have hm_piece : (orderedPieces e)[m] = tubeChains.chain L[q] := by
        exact get_eq_of_get? (k := m) (Γ := tubeChains.chain L[q])
          hm (by simpa [L] using hm_get)
      have hq_lt : q < L.length := by
        dsimp [L]
        omega
      rcases orderedPieces_get?_classify e n hn with
        ⟨hn_source, hn_get⟩ |
        ⟨r, hr, hn_tube, hn_get⟩ |
        ⟨r, hr, hn_gap, hn_get⟩ |
        ⟨hn_terminal, hn_get⟩ |
        ⟨hn_target, hn_get⟩
      · omega
      · have hn_piece : (orderedPieces e)[n] = tubeChains.chain L[r] := by
          exact get_eq_of_get? (k := n) (Γ := tubeChains.chain L[r])
            hn (by simpa [L] using hn_get)
        have hr_lt : r < L.length := by
          dsimp [L]
          omega
        have hne : L[q] ≠ L[r] :=
          chain_ne_of_index_ne hq_lt hr_lt (by omega)
        rw [hm_piece, hn_piece]
        exact tubeChains.chain_carriers_pairwise_disjoint hne
      · have hn_piece :
            (orderedPieces e)[n] = gapConnector e ⟨r, by omega⟩ :=
          get_eq_of_get? (k := n) (Γ := gapConnector e ⟨r, by omega⟩) hn hn_get
        have hq_not_left : L[q] ≠ L[r] :=
          chain_ne_of_index_ne hq_lt (by dsimp [L]; omega) (by omega)
        have hq_not_right : L[q] ≠ L[r + 1] :=
          chain_ne_of_index_ne hq_lt (by dsimp [L]; omega) (by omega)
        have hmem : L[q] ∈ tubeChains.edgePieceOrder e := by
          dsimp [L]
          exact List.getElem_mem hq_lt
        rw [hm_piece, hn_piece]
        exact tube_chain_carrier_disjoint_gapConnector_of_not_boundary e
          ⟨r, by omega⟩ L[q] hmem hq_not_left hq_not_right
      · have hn_piece :
            (orderedPieces e)[n] = tubeChains.chain (terminalTubeIndex e) :=
          get_eq_of_get? (k := n) (Γ := tubeChains.chain (terminalTubeIndex e))
            hn hn_get
        have hq_not_terminal : q ≠ L.length - 1 := by
          change q ≠ (tubeChains.edgePieceOrder e).length - 1
          omega
        have hne : L[q] ≠ terminalTubeIndex e := by
          intro heq
          exact terminal_ne_get_of_not_terminal hq_lt hq_not_terminal heq.symm
        rw [hm_piece, hn_piece]
        exact tubeChains.chain_carriers_pairwise_disjoint hne
      · have hn_piece : (orderedPieces e)[n] = targetSpokeReverse e :=
          get_eq_of_get? (k := n) (Γ := targetSpokeReverse e) hn hn_get
        have hnot_last :
            (tubeChains.edgePieceOrder e).getLast? ≠ some L[q] := by
          dsimp [L]
          exact not_last_of_not_terminal hq_lt (by
            change q ≠ (tubeChains.edgePieceOrder e).length - 1
            omega)
        have hmem : L[q] ∈ tubeChains.edgePieceOrder e := by
          dsimp [L]
          exact List.getElem_mem hq_lt
        rw [hm_piece, hn_piece]
        exact (targetSpokeReverse_carrier_disjoint_tube_chain_of_not_last
          e L[q] hmem hnot_last).symm
    · have hm_piece :
          (orderedPieces e)[m] = gapConnector e ⟨q, by omega⟩ :=
        get_eq_of_get? (k := m) (Γ := gapConnector e ⟨q, by omega⟩) hm hm_get
      rcases orderedPieces_get?_classify e n hn with
        ⟨hn_source, hn_get⟩ |
        ⟨r, hr, hn_tube, hn_get⟩ |
        ⟨r, hr, hn_gap, hn_get⟩ |
        ⟨hn_terminal, hn_get⟩ |
        ⟨hn_target, hn_get⟩
      · omega
      · have hn_piece : (orderedPieces e)[n] = tubeChains.chain L[r] := by
          exact get_eq_of_get? (k := n) (Γ := tubeChains.chain L[r])
            hn (by simpa [L] using hn_get)
        have hr_lt : r < L.length := by
          dsimp [L]
          omega
        have hr_not_left : L[r] ≠ L[q] :=
          chain_ne_of_index_ne hr_lt (by dsimp [L]; omega) (by omega)
        have hr_not_right : L[r] ≠ L[q + 1] :=
          chain_ne_of_index_ne hr_lt (by dsimp [L]; omega) (by omega)
        have hmem : L[r] ∈ tubeChains.edgePieceOrder e := by
          dsimp [L]
          exact List.getElem_mem hr_lt
        rw [hm_piece, hn_piece]
        exact (tube_chain_carrier_disjoint_gapConnector_of_not_boundary e
          ⟨q, by omega⟩ L[r] hmem hr_not_left hr_not_right).symm
      · have hn_piece :
            (orderedPieces e)[n] = gapConnector e ⟨r, by omega⟩ :=
          get_eq_of_get? (k := n) (Γ := gapConnector e ⟨r, by omega⟩) hn hn_get
        have hqr : (⟨q, by omega⟩ :
            Fin ((tubeChains.edgePieceOrder e).length - 1)) ≠
              ⟨r, by omega⟩ := by
          intro hfin
          have hidx := congrArg Fin.val hfin
          have hidx' : q = r := by simpa using hidx
          omega
        rw [hm_piece, hn_piece]
        exact gapConnector_carrier_disjoint_gapConnector_of_ne e
          ⟨q, by omega⟩ ⟨r, by omega⟩ hqr
      · have hn_piece :
            (orderedPieces e)[n] = tubeChains.chain (terminalTubeIndex e) :=
          get_eq_of_get? (k := n) (Γ := tubeChains.chain (terminalTubeIndex e))
            hn hn_get
        have hterminal_not_left : terminalTubeIndex e ≠ L[q] :=
          terminal_ne_get_of_not_terminal (q := q) (by dsimp [L]; omega) (by
            change q ≠ (tubeChains.edgePieceOrder e).length - 1
            omega)
        have hterminal_not_right : terminalTubeIndex e ≠ L[q + 1] :=
          terminal_ne_get_of_not_terminal (q := q + 1) (by dsimp [L]; omega) (by
            change q + 1 ≠ (tubeChains.edgePieceOrder e).length - 1
            omega)
        rw [hm_piece, hn_piece]
        exact (tube_chain_carrier_disjoint_gapConnector_of_not_boundary e
          ⟨q, by omega⟩ (terminalTubeIndex e) (terminalTubeIndex_mem e)
          hterminal_not_left hterminal_not_right).symm
      · have hn_piece : (orderedPieces e)[n] = targetSpokeReverse e :=
          get_eq_of_get? (k := n) (Γ := targetSpokeReverse e) hn hn_get
        rcases gapConnector_eq_or_reverse e ⟨q, by omega⟩ with
          ⟨x, hxe, hgap | hgap⟩
        · rw [hm_piece, hn_piece, hgap, targetSpokeReverse_def e]
          simpa [PolygonalArcReverse] using
            (vertexSpokeCarrierDisjointIntersectionChain G D controlDisks
              tubeChains localDiskFillings (tubeChains.edgeTargetVertex e)
              ⟨e, tubeChains.edgeTargetVertex_mem e⟩ x ⟨e, hxe⟩).symm
        · rw [hm_piece, hn_piece, hgap, targetSpokeReverse_def e]
          simpa [PolygonalArcReverse] using
            (vertexSpokeCarrierDisjointIntersectionChain G D controlDisks
              tubeChains localDiskFillings (tubeChains.edgeTargetVertex e)
              ⟨e, tubeChains.edgeTargetVertex_mem e⟩ x ⟨e, hxe⟩).symm
    · rcases orderedPieces_get?_classify e n hn with
        ⟨hn_source, hn_get⟩ |
        ⟨r, hr, hn_tube, hn_get⟩ |
        ⟨r, hr, hn_gap, hn_get⟩ |
        ⟨hn_terminal, hn_get⟩ |
        ⟨hn_target, hn_get⟩ <;> omega
    · rcases orderedPieces_get?_classify e n hn with
        ⟨hn_source, hn_get⟩ |
        ⟨r, hr, hn_tube, hn_get⟩ |
        ⟨r, hr, hn_gap, hn_get⟩ |
        ⟨hn_terminal, hn_get⟩ |
        ⟨hn_target, hn_get⟩ <;> omega
  rcases hmn with hmn | hnm
  · exact prove_forward m n hm hn hmn
  · exact (prove_forward n m hn hm hnm).symm

private lemma polygonalArcSourceMemCarrier (Γ : PolygonalArc) :
    Γ.source ∈ Γ.carrier := by
  rw [Γ.carrier_eq]
  refine ⟨0, ?_, ?_⟩
  · have hlen := Γ.length_ge_two
    omega
  · have h0 : 0 < Γ.vertices.length := by
      have hlen := Γ.length_ge_two
      omega
    have hsource : Γ.vertices[0] = Γ.source := by
      have hhead := Γ.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem h0] at hhead
      exact Option.some.inj hhead
    have h1 : 0 + 1 < Γ.vertices.length := by
      have hlen := Γ.length_ge_two
      omega
    have hseg :
        Γ.source ∈
          segment ℝ (Γ.vertices[0]'h0) (Γ.vertices[0 + 1]'h1) := by
      simpa [hsource] using
        (left_mem_segment ℝ (Γ.vertices[0]'h0) (Γ.vertices[0 + 1]'h1))
    exact hseg

private lemma getElemEqOfGetElem?
    {α : Type*} {L : List α} {k : ℕ} {Γ : α}
    (hk : k < L.length) (hget : L[k]? = some Γ) : L[k] = Γ := by
  rw [List.getElem?_eq_getElem hk] at hget
  exact Option.some.inj hget

private lemma polygonalArcTargetMemCarrier (Γ : PolygonalArc) :
    Γ.target ∈ Γ.carrier := by
  let k := Γ.vertices.length - 2
  have hk : k + 1 < Γ.vertices.length := by
    dsimp [k]
    have hlen := Γ.length_ge_two
    omega
  rw [Γ.carrier_eq]
  refine ⟨k, hk, ?_⟩
  have hlast_lt : Γ.vertices.length - 1 < Γ.vertices.length := by
    have hlen := Γ.length_ge_two
    omega
  have htarget_last : Γ.vertices[Γ.vertices.length - 1] = Γ.target := by
    have hlast := Γ.target_eq_last
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getElem?_eq_getElem hlast_lt] at hlast
    exact Option.some.inj hlast
  have hk1 : k + 1 = Γ.vertices.length - 1 := by
    dsimp [k]
    omega
  have hk_lt : k < Γ.vertices.length := by omega
  have hlast_get : Γ.vertices[k + 1]'hk = Γ.target := by
    have hidx :
        (⟨k + 1, hk⟩ : Fin Γ.vertices.length) =
          ⟨Γ.vertices.length - 1, hlast_lt⟩ := by
      apply Fin.ext
      exact hk1
    calc
      Γ.vertices[k + 1]'hk =
          Γ.vertices[Γ.vertices.length - 1]'hlast_lt := by
        simpa using
          congrArg (fun q : Fin Γ.vertices.length => Γ.vertices[q]) hidx
      _ = Γ.target := htarget_last
  have hseg :
      Γ.target ∈ segment ℝ (Γ.vertices[k]'hk_lt) (Γ.vertices[k + 1]'hk) := by
    simpa [hlast_get] using
      (right_mem_segment ℝ (Γ.vertices[k]'hk_lt) (Γ.vertices[k + 1]'hk))
  simpa using hseg

private lemma sourceSpokeTubeInterSubset
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (sourceSpoke : G.edgeFinset → PolygonalArc)
    (sourceSpoke_def : ∀ e, sourceSpoke e =
      localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
        ⟨e, tubeChains.edgeSourceVertex_mem e⟩)
    (vertex_spoke_boundary_point_eq_target :
      ∀ v (e : {e : G.edgeFinset // v ∈ e.1})
        (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ (localDiskFillings.vertex_spoke v e).carrier →
          p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
            p = (localDiskFillings.vertex_spoke v e).target)
    (e : G.edgeFinset) :
    ∀ i,
      (sourceSpoke e).carrier ∩ (tubeChains.chain i).carrier ⊆
        ({(sourceSpoke e).target} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro i p hp
  have hpClosed :
      p ∈ Metric.closedBall
        (D.vertexPlacement (tubeChains.edgeSourceVertex e))
        (controlDisks.vertexRadius (tubeChains.edgeSourceVertex e)) :=
    localDiskFillings.vertex_spoke_carrier_subset_closedBall
      (tubeChains.edgeSourceVertex e)
      ⟨e, tubeChains.edgeSourceVertex_mem e⟩ (by
        simpa [sourceSpoke_def e] using hp.1)
  have hmeet :=
    tubeChains.chain_carrier_meets_vertex_closedBall_only_endpoint
      i (tubeChains.edgeSourceVertex e) p hp.2 hpClosed
  have hpSphere :
      p ∈ Metric.sphere
        (D.vertexPlacement (tubeChains.edgeSourceVertex e))
        (controlDisks.vertexRadius (tubeChains.edgeSourceVertex e)) := by
    rcases hmeet with hsource | htarget
    · simpa [hsource.1] using hsource.2
    · simpa [htarget.1] using htarget.2
  have hpTarget : p = (sourceSpoke e).target := by
    simpa [sourceSpoke_def e] using
      vertex_spoke_boundary_point_eq_target
        (tubeChains.edgeSourceVertex e)
        ⟨e, tubeChains.edgeSourceVertex_mem e⟩ p (by
          simpa [sourceSpoke_def e] using hp.1) hpSphere
  simpa [Set.mem_singleton_iff] using hpTarget

private lemma tubeTargetSpokeInterSubset
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (targetSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (targetSpoke_def : ∀ e, targetSpoke e =
      localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
        ⟨e, tubeChains.edgeTargetVertex_mem e⟩)
    (targetSpokeReverse_def : ∀ e,
      targetSpokeReverse e = PolygonalArcReverse (targetSpoke e))
    (vertex_spoke_boundary_point_eq_target :
      ∀ v (e : {e : G.edgeFinset // v ∈ e.1})
        (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ (localDiskFillings.vertex_spoke v e).carrier →
          p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
            p = (localDiskFillings.vertex_spoke v e).target)
    (e : G.edgeFinset) :
    ∀ i,
      (tubeChains.chain i).carrier ∩ (targetSpokeReverse e).carrier ⊆
        ({(targetSpokeReverse e).source} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro i p hp
  have hpTargetSpoke : p ∈ (targetSpoke e).carrier := by
    simpa [targetSpokeReverse_def e, targetSpoke_def e,
      PolygonalArcReverse] using hp.2
  have hpTargetSpokeLocal :
      p ∈
        (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
          ⟨e, tubeChains.edgeTargetVertex_mem e⟩).carrier := by
    simpa [targetSpoke_def e] using hpTargetSpoke
  have hpClosed :
      p ∈ Metric.closedBall
        (D.vertexPlacement (tubeChains.edgeTargetVertex e))
        (controlDisks.vertexRadius (tubeChains.edgeTargetVertex e)) :=
    localDiskFillings.vertex_spoke_carrier_subset_closedBall
      (tubeChains.edgeTargetVertex e)
      ⟨e, tubeChains.edgeTargetVertex_mem e⟩ hpTargetSpokeLocal
  have hmeet :=
    tubeChains.chain_carrier_meets_vertex_closedBall_only_endpoint
      i (tubeChains.edgeTargetVertex e) p hp.1 hpClosed
  have hpSphere :
      p ∈ Metric.sphere
        (D.vertexPlacement (tubeChains.edgeTargetVertex e))
        (controlDisks.vertexRadius (tubeChains.edgeTargetVertex e)) := by
    rcases hmeet with hsource | htarget
    · simpa [hsource.1] using hsource.2
    · simpa [htarget.1] using htarget.2
  have hpTarget : p = (targetSpoke e).target := by
    simpa [targetSpoke_def e] using
      vertex_spoke_boundary_point_eq_target
        (tubeChains.edgeTargetVertex e)
        ⟨e, tubeChains.edgeTargetVertex_mem e⟩ p hpTargetSpokeLocal hpSphere
  have hpRev : p = (targetSpokeReverse e).source := by
    simpa [targetSpokeReverse_def e, targetSpoke_def e,
      PolygonalArcReverse] using hpTarget
  simpa [Set.mem_singleton_iff] using hpRev

private lemma gapConnectorCarrierSubsetClosedBall
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (gapCenter :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) →
          {p // p ∈ D.intersectionPoints})
    (gapCenter_mem : ∀ e q,
      (gapCenter e q).1 ∈ D.edgeRelativeInterior e)
    (gapConnector_eq_or_reverse_gapCenter :
      ∀ e (q : Fin ((tubeChains.edgePieceOrder e).length - 1)),
        gapConnector e q =
            localDiskFillings.intersection_chain (gapCenter e q)
              ⟨e, gapCenter_mem e q⟩ ∨
          gapConnector e q = PolygonalArcReverse
            (localDiskFillings.intersection_chain (gapCenter e q)
              ⟨e, gapCenter_mem e q⟩))
    (e : G.edgeFinset) :
    ∀ q,
      (gapConnector e q).carrier ⊆
        Metric.closedBall (gapCenter e q).1
          (controlDisks.intersectionRadius (gapCenter e q)) := by
  intro q p hp
  rcases gapConnector_eq_or_reverse_gapCenter e q with hgap | hgap
  · have hpOrig :
        p ∈
          (localDiskFillings.intersection_chain (gapCenter e q)
            ⟨e, gapCenter_mem e q⟩).carrier := by
      simpa [hgap] using hp
    exact
      localDiskFillings.intersection_chain_carrier_subset_closedBall
        (gapCenter e q) ⟨e, gapCenter_mem e q⟩ hpOrig
  · have hpOrig :
        p ∈
          (localDiskFillings.intersection_chain (gapCenter e q)
            ⟨e, gapCenter_mem e q⟩).carrier := by
      simpa [hgap, PolygonalArcReverse] using hp
    exact
      localDiskFillings.intersection_chain_carrier_subset_closedBall
        (gapCenter e q) ⟨e, gapCenter_mem e q⟩ hpOrig

private lemma tubeGapInterSubsetLeft
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (gapCenter :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) →
          {p // p ∈ D.intersectionPoints})
    (orderedPieces_length : ∀ e, (orderedPieces e).length =
      2 * (tubeChains.edgePieceOrder e).length + 1)
    (orderedPieces_get?_tube : ∀ (e : G.edgeFinset) q
      (hq : q < (tubeChains.edgePieceOrder e).length),
      (orderedPieces e)[1 + 2 * q]? =
        some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q])))
    (orderedPieces_get?_gap : ∀ (e : G.edgeFinset) q
      (hq : q + 1 < (tubeChains.edgePieceOrder e).length),
      (orderedPieces e)[2 + 2 * q]? =
        some (gapConnector e ⟨q, by omega⟩))
    (orderedPieces_successive_attach :
      ∀ e n (hn : n + 1 < (orderedPieces e).length),
        ((orderedPieces e)[n]).target = ((orderedPieces e)[n + 1]).source)
    (orderedPieces_non_successive_disjoint :
      ∀ e m n (hm : m < (orderedPieces e).length)
        (hn : n < (orderedPieces e).length),
        m + 1 < n ∨ n + 1 < m →
          Disjoint ((orderedPieces e)[m]).carrier
            ((orderedPieces e)[n]).carrier)
    (e : G.edgeFinset)
    (gapConnector_carrier_subset_closedBall :
      ∀ q,
        (gapConnector e q).carrier ⊆
          Metric.closedBall (gapCenter e q).1
            (controlDisks.intersectionRadius (gapCenter e q))) :
    ∀ q,
      (tubeChains.chain ((tubeChains.edgePieceOrder e)[q.1])).carrier ∩
          (gapConnector e q).carrier ⊆
        ({(tubeChains.chain ((tubeChains.edgePieceOrder e)[q.1])).target} :
          Set (EuclideanSpace ℝ (Fin 2))) := by
  intro q p hp
  have hclosed := gapConnector_carrier_subset_closedBall q hp.2
  have hmeet :=
    tubeChains.chain_carrier_meets_intersection_closedBall_only_endpoint
      ((tubeChains.edgePieceOrder e)[q.1]) (gapCenter e q) p hp.1 hclosed
  rcases hmeet with hsource | htarget
  · let tubePos := 1 + 2 * q.1
    let gapPos := 2 + 2 * q.1
    let prevPos := 2 * q.1
    have htube_get :=
      orderedPieces_get?_tube e q.1 (by
        have hq : q.1 < (tubeChains.edgePieceOrder e).length - 1 := q.2
        omega)
    have hgap_get :=
      orderedPieces_get?_gap e q.1 (by
        have hq : q.1 < (tubeChains.edgePieceOrder e).length - 1 := q.2
        omega)
    have htube_lt : tubePos < (orderedPieces e).length := by
      rw [orderedPieces_length e]
      dsimp [tubePos]
      omega
    have hgap_lt : gapPos < (orderedPieces e).length := by
      rw [orderedPieces_length e]
      dsimp [gapPos]
      omega
    have hprev_lt : prevPos < (orderedPieces e).length := by
      rw [orderedPieces_length e]
      dsimp [prevPos]
      omega
    have htube_piece :
        (orderedPieces e)[tubePos] =
          tubeChains.chain ((tubeChains.edgePieceOrder e)[q.1]) := by
      exact getElemEqOfGetElem? htube_lt (by simpa [tubePos] using htube_get)
    have hgap_piece : (orderedPieces e)[gapPos] = gapConnector e q := by
      exact getElemEqOfGetElem? hgap_lt (by simpa [gapPos] using hgap_get)
    have hprev_succ : prevPos + 1 = tubePos := by
      dsimp [prevPos, tubePos]
      omega
    have hprev_attach :
        ((orderedPieces e)[prevPos]).target =
          ((orderedPieces e)[tubePos]).source := by
      simpa [hprev_succ] using
        orderedPieces_successive_attach e prevPos (by
          simpa [hprev_succ] using htube_lt)
    have hp_tube_source :
        p = (tubeChains.chain ((tubeChains.edgePieceOrder e)[q.1])).source := by
      calc
        p = tubeChains.source ((tubeChains.edgePieceOrder e)[q.1]) := hsource.1
        _ = (tubeChains.chain
              ((tubeChains.edgePieceOrder e)[q.1])).source :=
          (tubeChains.chain_endpoints
            ((tubeChains.edgePieceOrder e)[q.1])).1.symm
    have hp_prev : p ∈ ((orderedPieces e)[prevPos]).carrier := by
      have hprev_target : ((orderedPieces e)[prevPos]).target = p := by
        calc
          ((orderedPieces e)[prevPos]).target =
              ((orderedPieces e)[tubePos]).source := hprev_attach
          _ = (tubeChains.chain
                ((tubeChains.edgePieceOrder e)[q.1])).source := by
            rw [htube_piece]
          _ = p := hp_tube_source.symm
      simpa [hprev_target] using
        polygonalArcTargetMemCarrier ((orderedPieces e)[prevPos])
    have hp_gap : p ∈ ((orderedPieces e)[gapPos]).carrier := by
      simpa [hgap_piece] using hp.2
    have hdis :=
      orderedPieces_non_successive_disjoint e prevPos gapPos hprev_lt hgap_lt
        (Or.inl (by
          dsimp [prevPos, gapPos]
          omega))
    exact False.elim ((Set.disjoint_left.mp hdis hp_prev) hp_gap)
  · have hp_tube_target :
        p = (tubeChains.chain ((tubeChains.edgePieceOrder e)[q.1])).target := by
      calc
        p = tubeChains.target ((tubeChains.edgePieceOrder e)[q.1]) := htarget.1
        _ = (tubeChains.chain
              ((tubeChains.edgePieceOrder e)[q.1])).target :=
          (tubeChains.chain_endpoints
            ((tubeChains.edgePieceOrder e)[q.1])).2.symm
    simpa [Set.mem_singleton_iff] using hp_tube_target

private lemma gapTubeInterSubsetRight
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (gapCenter :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) →
          {p // p ∈ D.intersectionPoints})
    (gapConnector_target : ∀ e n,
      (gapConnector e n).target =
        tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]))
    (orderedPieces_length : ∀ e, (orderedPieces e).length =
      2 * (tubeChains.edgePieceOrder e).length + 1)
    (orderedPieces_get?_tube : ∀ (e : G.edgeFinset) q
      (hq : q < (tubeChains.edgePieceOrder e).length),
      (orderedPieces e)[1 + 2 * q]? =
        some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q])))
    (orderedPieces_get?_gap : ∀ (e : G.edgeFinset) q
      (hq : q + 1 < (tubeChains.edgePieceOrder e).length),
      (orderedPieces e)[2 + 2 * q]? =
        some (gapConnector e ⟨q, by omega⟩))
    (orderedPieces_successive_attach :
      ∀ e n (hn : n + 1 < (orderedPieces e).length),
        ((orderedPieces e)[n]).target = ((orderedPieces e)[n + 1]).source)
    (orderedPieces_non_successive_disjoint :
      ∀ e m n (hm : m < (orderedPieces e).length)
        (hn : n < (orderedPieces e).length),
        m + 1 < n ∨ n + 1 < m →
          Disjoint ((orderedPieces e)[m]).carrier
            ((orderedPieces e)[n]).carrier)
    (e : G.edgeFinset)
    (gapConnector_carrier_subset_closedBall :
      ∀ q,
        (gapConnector e q).carrier ⊆
          Metric.closedBall (gapCenter e q).1
            (controlDisks.intersectionRadius (gapCenter e q))) :
    ∀ q,
      (gapConnector e q).carrier ∩
          (tubeChains.chain ((tubeChains.edgePieceOrder e)[q.1 + 1])).carrier ⊆
        ({(gapConnector e q).target} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro q p hp
  have hclosed := gapConnector_carrier_subset_closedBall q hp.1
  have hmeet :=
    tubeChains.chain_carrier_meets_intersection_closedBall_only_endpoint
      ((tubeChains.edgePieceOrder e)[q.1 + 1]) (gapCenter e q) p hp.2 hclosed
  rcases hmeet with hsource | htarget
  · have hp_tube_source :
        p = (tubeChains.chain
          ((tubeChains.edgePieceOrder e)[q.1 + 1])).source := by
      calc
        p = tubeChains.source
              ((tubeChains.edgePieceOrder e)[q.1 + 1]) := hsource.1
        _ = (tubeChains.chain
              ((tubeChains.edgePieceOrder e)[q.1 + 1])).source :=
          (tubeChains.chain_endpoints
            ((tubeChains.edgePieceOrder e)[q.1 + 1])).1.symm
    have hgap_target :
        (gapConnector e q).target =
          (tubeChains.chain
            ((tubeChains.edgePieceOrder e)[q.1 + 1])).source := by
      calc
        (gapConnector e q).target =
            tubeChains.source ((tubeChains.edgePieceOrder e)[q.1 + 1]) :=
          gapConnector_target e q
        _ = (tubeChains.chain
              ((tubeChains.edgePieceOrder e)[q.1 + 1])).source :=
          (tubeChains.chain_endpoints
            ((tubeChains.edgePieceOrder e)[q.1 + 1])).1.symm
    have hp_eq : p = (gapConnector e q).target :=
      hp_tube_source.trans hgap_target.symm
    simpa [Set.mem_singleton_iff] using hp_eq
  · let gapPos := 2 + 2 * q.1
    let tubePos := 1 + 2 * (q.1 + 1)
    let nextPos := tubePos + 1
    have htube_get :=
      orderedPieces_get?_tube e (q.1 + 1) (by
        have hq : q.1 < (tubeChains.edgePieceOrder e).length - 1 := q.2
        omega)
    have hgap_get :=
      orderedPieces_get?_gap e q.1 (by
        have hq : q.1 < (tubeChains.edgePieceOrder e).length - 1 := q.2
        omega)
    have hgap_lt : gapPos < (orderedPieces e).length := by
      rw [orderedPieces_length e]
      dsimp [gapPos]
      omega
    have htube_lt : tubePos < (orderedPieces e).length := by
      rw [orderedPieces_length e]
      dsimp [tubePos]
      omega
    have hnext_lt : nextPos < (orderedPieces e).length := by
      rw [orderedPieces_length e]
      dsimp [nextPos, tubePos]
      omega
    have hgap_piece : (orderedPieces e)[gapPos] = gapConnector e q := by
      exact getElemEqOfGetElem? hgap_lt (by simpa [gapPos] using hgap_get)
    have htube_piece :
        (orderedPieces e)[tubePos] =
          tubeChains.chain ((tubeChains.edgePieceOrder e)[q.1 + 1]) := by
      exact getElemEqOfGetElem? htube_lt (by
        have hidx : 1 + 2 * (q.1 + 1) = tubePos := by
          dsimp [tubePos]
        simpa [hidx] using htube_get)
    have htube_attach :
        ((orderedPieces e)[tubePos]).target =
          ((orderedPieces e)[nextPos]).source := by
      exact orderedPieces_successive_attach e tubePos (by
        simpa [nextPos] using hnext_lt)
    have hp_tube_target :
        p = (tubeChains.chain
          ((tubeChains.edgePieceOrder e)[q.1 + 1])).target := by
      calc
        p = tubeChains.target
              ((tubeChains.edgePieceOrder e)[q.1 + 1]) := htarget.1
        _ = (tubeChains.chain
              ((tubeChains.edgePieceOrder e)[q.1 + 1])).target :=
          (tubeChains.chain_endpoints
            ((tubeChains.edgePieceOrder e)[q.1 + 1])).2.symm
    have hp_next : p ∈ ((orderedPieces e)[nextPos]).carrier := by
      have hnext_source : ((orderedPieces e)[nextPos]).source = p := by
        calc
          ((orderedPieces e)[nextPos]).source =
              ((orderedPieces e)[tubePos]).target := htube_attach.symm
          _ = (tubeChains.chain
                ((tubeChains.edgePieceOrder e)[q.1 + 1])).target := by
            rw [htube_piece]
          _ = p := hp_tube_target.symm
      simpa [hnext_source] using
        polygonalArcSourceMemCarrier ((orderedPieces e)[nextPos])
    have hp_gap : p ∈ ((orderedPieces e)[gapPos]).carrier := by
      simpa [hgap_piece] using hp.1
    have hdis :=
      orderedPieces_non_successive_disjoint e gapPos nextPos hgap_lt hnext_lt
        (Or.inl (by
          dsimp [gapPos, nextPos, tubePos]
          omega))
    exact False.elim ((Set.disjoint_left.mp hdis hp_gap) hp_next)

private lemma orderedPiecesSuccessiveCarrierIntersectionsSubset
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (terminalTubeIndex_getLast : ∀ e,
      (tubeChains.edgePieceOrder e).getLast? = some (terminalTubeIndex e))
    (terminalTube_attaches_targetSpoke : ∀ e,
      (tubeChains.chain (terminalTubeIndex e)).target =
        (targetSpokeReverse e).source)
    (orderedPieces_length : ∀ e, (orderedPieces e).length =
      2 * (tubeChains.edgePieceOrder e).length + 1)
    (orderedPieces_get?_classify :
      ∀ e m (hm : m < (orderedPieces e).length),
        (m = 0 ∧ (orderedPieces e)[m]? = some (sourceSpoke e)) ∨
          (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
            m = 1 + 2 * q ∧
              (orderedPieces e)[m]? =
                some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q]))) ∨
          (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
            m = 2 + 2 * q ∧
              (orderedPieces e)[m]? =
                some (gapConnector e ⟨q, by omega⟩)) ∨
          (m = 2 * (tubeChains.edgePieceOrder e).length - 1 ∧
            (orderedPieces e)[m]? =
              some (tubeChains.chain (terminalTubeIndex e))) ∨
          (m = 2 * (tubeChains.edgePieceOrder e).length ∧
            (orderedPieces e)[m]? = some (targetSpokeReverse e)))
    (e : G.edgeFinset)
    (sourceSpoke_tube_inter_subset : ∀ i,
      (sourceSpoke e).carrier ∩ (tubeChains.chain i).carrier ⊆
        ({(sourceSpoke e).target} : Set (EuclideanSpace ℝ (Fin 2))))
    (tube_targetSpoke_inter_subset : ∀ i,
      (tubeChains.chain i).carrier ∩ (targetSpokeReverse e).carrier ⊆
        ({(targetSpokeReverse e).source} : Set (EuclideanSpace ℝ (Fin 2))))
    (tube_gap_inter_subset_left : ∀ q,
      (tubeChains.chain ((tubeChains.edgePieceOrder e)[q.1])).carrier ∩
          (gapConnector e q).carrier ⊆
        ({(tubeChains.chain ((tubeChains.edgePieceOrder e)[q.1])).target} :
          Set (EuclideanSpace ℝ (Fin 2))))
    (gap_tube_inter_subset_right : ∀ q,
      (gapConnector e q).carrier ∩
          (tubeChains.chain ((tubeChains.edgePieceOrder e)[q.1 + 1])).carrier ⊆
        ({(gapConnector e q).target} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∀ n (hn : n + 1 < (orderedPieces e).length),
      (orderedPieces e)[n].carrier ∩ (orderedPieces e)[n + 1].carrier ⊆
        ({(orderedPieces e)[n].target} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro n hn p hp
  simp only [Set.mem_singleton_iff]
  let L := tubeChains.edgePieceOrder e
  have hlen_pos : 0 < L.length := by
    dsimp [L]
    exact Nat.pos_of_ne_zero (tubeChains.edgePieceOrder_nonempty e)
  have hn_left : n < (orderedPieces e).length := by omega
  have get_eq_of_get? :
      ∀ {k : ℕ} {Γ : PolygonalArc}
        (hk : k < (orderedPieces e).length),
        (orderedPieces e)[k]? = some Γ →
          (orderedPieces e)[k] = Γ := by
    intro k Γ hk hget
    exact getElemEqOfGetElem? hk hget
  rcases orderedPieces_get?_classify e n hn_left with
    ⟨hn_source, hn_get⟩ |
    ⟨q, hq, hn_tube, hn_get⟩ |
    ⟨q, hq, hn_gap, hn_get⟩ |
    ⟨hn_terminal, hn_get⟩ |
    ⟨hn_target, hn_get⟩
  · have hn_piece : (orderedPieces e)[n] = sourceSpoke e :=
      get_eq_of_get? (k := n) (Γ := sourceSpoke e) hn_left hn_get
    rcases orderedPieces_get?_classify e (n + 1) hn with
      ⟨hn1_source, hn1_get⟩ |
      ⟨r, hr, hn1_tube, hn1_get⟩ |
      ⟨r, hr, hn1_gap, hn1_get⟩ |
      ⟨hn1_terminal, hn1_get⟩ |
      ⟨hn1_target, hn1_get⟩
    · omega
    · have hn1_piece :
          (orderedPieces e)[n + 1] =
            tubeChains.chain L[r] := by
        exact get_eq_of_get? (k := n + 1) (Γ := tubeChains.chain L[r])
          hn (by simpa [L] using hn1_get)
      have hp' :
          p ∈ (sourceSpoke e).carrier ∩
            (tubeChains.chain L[r]).carrier := by
        simpa [hn_piece, hn1_piece] using hp
      have hp_eq_mem := sourceSpoke_tube_inter_subset L[r] hp'
      have hp_eq : p = (sourceSpoke e).target := by
        simpa using hp_eq_mem
      simpa [hn_piece] using hp_eq
    · omega
    · have hn1_piece :
          (orderedPieces e)[n + 1] =
            tubeChains.chain (terminalTubeIndex e) :=
        get_eq_of_get? (k := n + 1)
          (Γ := tubeChains.chain (terminalTubeIndex e)) hn hn1_get
      have hp' :
          p ∈ (sourceSpoke e).carrier ∩
            (tubeChains.chain (terminalTubeIndex e)).carrier := by
        simpa [hn_piece, hn1_piece] using hp
      have hp_eq_mem :=
        sourceSpoke_tube_inter_subset (terminalTubeIndex e) hp'
      have hp_eq : p = (sourceSpoke e).target := by
        simpa using hp_eq_mem
      simpa [hn_piece] using hp_eq
    · omega
  · have hn_piece :
        (orderedPieces e)[n] = tubeChains.chain L[q] := by
      exact get_eq_of_get? (k := n) (Γ := tubeChains.chain L[q])
        hn_left (by simpa [L] using hn_get)
    rcases orderedPieces_get?_classify e (n + 1) hn with
      ⟨hn1_source, hn1_get⟩ |
      ⟨r, hr, hn1_tube, hn1_get⟩ |
      ⟨r, hr, hn1_gap, hn1_get⟩ |
      ⟨hn1_terminal, hn1_get⟩ |
      ⟨hn1_target, hn1_get⟩
    · omega
    · omega
    · have hrq : r = q := by omega
      subst r
      let qFin : Fin ((tubeChains.edgePieceOrder e).length - 1) :=
        ⟨q, by omega⟩
      have hn1_piece :
          (orderedPieces e)[n + 1] = gapConnector e qFin :=
        get_eq_of_get? (k := n + 1) (Γ := gapConnector e qFin)
          hn (by simpa [qFin] using hn1_get)
      have hp' :
          p ∈ (tubeChains.chain L[q]).carrier ∩
            (gapConnector e qFin).carrier := by
        simpa [hn_piece, hn1_piece, L, qFin] using hp
      have hp_eq_mem := tube_gap_inter_subset_left qFin hp'
      have hp_eq : p = (tubeChains.chain L[q]).target := by
        simpa [L, qFin] using hp_eq_mem
      simpa [hn_piece] using hp_eq
    · omega
    · omega
  · have hn_piece :
        (orderedPieces e)[n] =
          gapConnector e ⟨q, by omega⟩ :=
      get_eq_of_get? (k := n)
        (Γ := gapConnector e ⟨q, by omega⟩) hn_left hn_get
    rcases orderedPieces_get?_classify e (n + 1) hn with
      ⟨hn1_source, hn1_get⟩ |
      ⟨r, hr, hn1_tube, hn1_get⟩ |
      ⟨r, hr, hn1_gap, hn1_get⟩ |
      ⟨hn1_terminal, hn1_get⟩ |
      ⟨hn1_target, hn1_get⟩
    · omega
    · have hrq : r = q + 1 := by omega
      subst r
      let qFin : Fin ((tubeChains.edgePieceOrder e).length - 1) :=
        ⟨q, by omega⟩
      have hn1_piece :
          (orderedPieces e)[n + 1] =
            tubeChains.chain L[q + 1] := by
        exact get_eq_of_get? (k := n + 1)
          (Γ := tubeChains.chain L[q + 1]) hn
          (by simpa [L] using hn1_get)
      have hp' :
          p ∈ (gapConnector e qFin).carrier ∩
            (tubeChains.chain L[q + 1]).carrier := by
        simpa [hn_piece, hn1_piece, L, qFin] using hp
      have hp_eq_mem := gap_tube_inter_subset_right qFin hp'
      have hp_eq : p = (gapConnector e qFin).target := by
        simpa [qFin] using hp_eq_mem
      simpa [hn_piece, qFin] using hp_eq
    · omega
    · have hq1_last :
          q + 1 = (tubeChains.edgePieceOrder e).length - 1 := by
        omega
      have hterminal_eq :
          terminalTubeIndex e = L[q + 1] := by
        have hlast := terminalTubeIndex_getLast e
        have hlast_get :
            L.getLast? = some L[L.length - 1] := by
          rw [List.getLast?_eq_getElem?]
          rw [List.getElem?_eq_getElem (by omega :
            L.length - 1 < L.length)]
        have hterm_eq_last : terminalTubeIndex e = L[L.length - 1] := by
          rw [show L.getLast? = some (terminalTubeIndex e) by
            simpa [L] using hlast] at hlast_get
          exact Option.some.inj hlast_get
        simpa [L, hq1_last] using hterm_eq_last
      let qFin : Fin ((tubeChains.edgePieceOrder e).length - 1) :=
        ⟨q, by omega⟩
      have hn1_piece :
          (orderedPieces e)[n + 1] =
            tubeChains.chain (terminalTubeIndex e) :=
        get_eq_of_get? (k := n + 1)
          (Γ := tubeChains.chain (terminalTubeIndex e)) hn hn1_get
      have hp' :
          p ∈ (gapConnector e qFin).carrier ∩
            (tubeChains.chain L[q + 1]).carrier := by
        simpa [hn_piece, hn1_piece, hterminal_eq, L, qFin] using hp
      have hp_eq_mem := gap_tube_inter_subset_right qFin hp'
      have hp_eq : p = (gapConnector e qFin).target := by
        simpa [qFin] using hp_eq_mem
      simpa [hn_piece, qFin] using hp_eq
    · omega
  · have hn_piece :
        (orderedPieces e)[n] =
          tubeChains.chain (terminalTubeIndex e) :=
      get_eq_of_get? (k := n)
        (Γ := tubeChains.chain (terminalTubeIndex e)) hn_left hn_get
    rcases orderedPieces_get?_classify e (n + 1) hn with
      ⟨hn1_source, hn1_get⟩ |
      ⟨r, hr, hn1_tube, hn1_get⟩ |
      ⟨r, hr, hn1_gap, hn1_get⟩ |
      ⟨hn1_terminal, hn1_get⟩ |
      ⟨hn1_target, hn1_get⟩
    · omega
    · omega
    · omega
    · omega
    · have hn1_piece :
          (orderedPieces e)[n + 1] = targetSpokeReverse e :=
        get_eq_of_get? (k := n + 1) (Γ := targetSpokeReverse e)
          hn hn1_get
      have hp' :
          p ∈ (tubeChains.chain (terminalTubeIndex e)).carrier ∩
            (targetSpokeReverse e).carrier := by
        simpa [hn_piece, hn1_piece] using hp
      have hp_rev_mem :=
        tube_targetSpoke_inter_subset (terminalTubeIndex e) hp'
      have hp_rev :
          p = (targetSpokeReverse e).source := by
        simpa using hp_rev_mem
      have hp_eq :
          p = (tubeChains.chain (terminalTubeIndex e)).target := by
        exact hp_rev.trans (terminalTube_attaches_targetSpoke e).symm
      simpa [hn_piece] using hp_eq
  · rw [orderedPieces_length e] at hn
    omega

private lemma orderedPieceRelativeInteriorAvoidsEdgeEndpoints
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (orderedPiece_is_local : ∀ e Γ, Γ ∈ orderedPieces e →
      (∃ (v : V) (hve : v ∈ e.1),
        Γ.carrier =
            (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier ∧
          Γ.relativeInterior =
            (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior) ∨
      (∃ i : tubeChains.pieceIndex,
        tubeChains.owner i = e ∧
          Γ.carrier = (tubeChains.chain i).carrier ∧
            Γ.relativeInterior = (tubeChains.chain i).relativeInterior) ∨
      (∃ (x : {p // p ∈ D.intersectionPoints})
          (hxe : x.1 ∈ D.edgeRelativeInterior e),
        Γ.carrier =
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩).carrier ∧
          Γ.relativeInterior =
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩).relativeInterior))
    (edge_mem_source_or_target : ∀ e v, v ∈ e.1 →
      v = tubeChains.edgeSourceVertex e ∨ v = tubeChains.edgeTargetVertex e)
    (edgeSourceVertex_ne_targetVertex : ∀ e,
      tubeChains.edgeSourceVertex e ≠ tubeChains.edgeTargetVertex e)
    (edgeSource_mem_source_ball : ∀ e,
      D.edgeSource e ∈
        Metric.ball (D.vertexPlacement (tubeChains.edgeSourceVertex e))
          (controlDisks.vertexRadius (tubeChains.edgeSourceVertex e)))
    (edgeTarget_mem_target_ball : ∀ e,
      D.edgeTarget e ∈
        Metric.ball (D.vertexPlacement (tubeChains.edgeTargetVertex e))
          (controlDisks.vertexRadius (tubeChains.edgeTargetVertex e))) :
    ∀ e piece, piece ∈ orderedPieces e →
      Disjoint piece.relativeInterior
        ({D.edgeSource e, D.edgeTarget e} :
          Set (EuclideanSpace ℝ (Fin 2))) := by
  intro e
  intro piece hpiece
  rw [Set.disjoint_left]
  intro p hp hpEndpoint
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpEndpoint
  rcases orderedPiece_is_local e piece hpiece with hvertex | htube |
    hintersection
  · rcases hvertex with ⟨v, hve, _hcarrier, hrelativeInterior⟩
    have hpSpoke :
        p ∈
          (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior := by
      simpa [hrelativeInterior] using hp
    have hpSpoke_not_endpoints :
        p ∉
          ({(localDiskFillings.vertex_spoke v ⟨e, hve⟩).source,
              (localDiskFillings.vertex_spoke v ⟨e, hve⟩).target} :
            Set (EuclideanSpace ℝ (Fin 2))) := by
      have hp' := hpSpoke
      rw [(localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior_eq] at hp'
      exact hp'.2
    rcases hpEndpoint with hpSource | hpTarget
    · rcases edge_mem_source_or_target e v hve with hvsource | hvtarget
      · subst v
        have hspoke_source :
            (localDiskFillings.vertex_spoke
                (tubeChains.edgeSourceVertex e)
                ⟨e, tubeChains.edgeSourceVertex_mem e⟩).source =
              D.edgeSource e := by
          calc
            (localDiskFillings.vertex_spoke
                (tubeChains.edgeSourceVertex e)
                ⟨e, tubeChains.edgeSourceVertex_mem e⟩).source =
                D.vertexPlacement (tubeChains.edgeSourceVertex e) :=
              localDiskFillings.vertex_spoke_source
                (tubeChains.edgeSourceVertex e)
                ⟨e, tubeChains.edgeSourceVertex_mem e⟩
            _ = D.edgeSource e :=
              (tubeChains.edgeSource_eq_vertexPlacement e).symm
        exact hpSpoke_not_endpoints (by
          simp [hpSource, hspoke_source])
      · subst v
        have hpClosedSource :
            p ∈
              Metric.closedBall
                (D.vertexPlacement (tubeChains.edgeSourceVertex e))
                (controlDisks.vertexRadius
                  (tubeChains.edgeSourceVertex e)) := by
          rw [hpSource]
          exact Metric.ball_subset_closedBall
            (edgeSource_mem_source_ball e)
        have hpClosedTarget :
            p ∈
              Metric.closedBall
                (D.vertexPlacement (tubeChains.edgeTargetVertex e))
                (controlDisks.vertexRadius
                  (tubeChains.edgeTargetVertex e)) :=
          Metric.ball_subset_closedBall
            (localDiskFillings.vertex_spoke_relativeInterior_subset_ball
              (tubeChains.edgeTargetVertex e)
              ⟨e, tubeChains.edgeTargetVertex_mem e⟩ hpSpoke)
        exact
          (Set.disjoint_left.mp
            (controlDisks.vertex_vertex_disjoint
              (edgeSourceVertex_ne_targetVertex e))
            hpClosedSource) hpClosedTarget
    · rcases edge_mem_source_or_target e v hve with hvsource | hvtarget
      · subst v
        have hpClosedTarget :
            p ∈
              Metric.closedBall
                (D.vertexPlacement (tubeChains.edgeTargetVertex e))
                (controlDisks.vertexRadius
                  (tubeChains.edgeTargetVertex e)) := by
          rw [hpTarget]
          exact Metric.ball_subset_closedBall
            (edgeTarget_mem_target_ball e)
        have hpClosedSource :
            p ∈
              Metric.closedBall
                (D.vertexPlacement (tubeChains.edgeSourceVertex e))
                (controlDisks.vertexRadius
                  (tubeChains.edgeSourceVertex e)) :=
          Metric.ball_subset_closedBall
            (localDiskFillings.vertex_spoke_relativeInterior_subset_ball
              (tubeChains.edgeSourceVertex e)
              ⟨e, tubeChains.edgeSourceVertex_mem e⟩ hpSpoke)
        exact
          (Set.disjoint_left.mp
            (controlDisks.vertex_vertex_disjoint
              (edgeSourceVertex_ne_targetVertex e))
            hpClosedSource) hpClosedTarget
      · subst v
        have hspoke_source :
            (localDiskFillings.vertex_spoke
                (tubeChains.edgeTargetVertex e)
                ⟨e, tubeChains.edgeTargetVertex_mem e⟩).source =
              D.edgeTarget e := by
          calc
            (localDiskFillings.vertex_spoke
                (tubeChains.edgeTargetVertex e)
                ⟨e, tubeChains.edgeTargetVertex_mem e⟩).source =
                D.vertexPlacement (tubeChains.edgeTargetVertex e) :=
              localDiskFillings.vertex_spoke_source
                (tubeChains.edgeTargetVertex e)
                ⟨e, tubeChains.edgeTargetVertex_mem e⟩
            _ = D.edgeTarget e :=
              (tubeChains.edgeTarget_eq_vertexPlacement e).symm
        exact hpSpoke_not_endpoints (by
          simp [hpTarget, hspoke_source])
  · rcases htube with ⟨i, _howner, _hcarrier, hrelativeInterior⟩
    have hpChain : p ∈ (tubeChains.chain i).relativeInterior := by
      simpa [hrelativeInterior] using hp
    rcases hpEndpoint with hpSource | hpTarget
    · have hpSourceBall :
          p ∈
            Metric.ball
              (D.vertexPlacement (tubeChains.edgeSourceVertex e))
              (controlDisks.vertexRadius
                (tubeChains.edgeSourceVertex e)) := by
        rw [hpSource]
        exact edgeSource_mem_source_ball e
      exact
        (Set.disjoint_left.mp
          (tubeChains.chain_relativeInterior_avoids_vertex_disk_interiors
            i (tubeChains.edgeSourceVertex e))
          hpChain) hpSourceBall
    · have hpTargetBall :
          p ∈
            Metric.ball
              (D.vertexPlacement (tubeChains.edgeTargetVertex e))
              (controlDisks.vertexRadius
                (tubeChains.edgeTargetVertex e)) := by
        rw [hpTarget]
        exact edgeTarget_mem_target_ball e
      exact
        (Set.disjoint_left.mp
          (tubeChains.chain_relativeInterior_avoids_vertex_disk_interiors
            i (tubeChains.edgeTargetVertex e))
          hpChain) hpTargetBall
  · rcases hintersection with
      ⟨x, hxe, _hcarrier, hrelativeInterior⟩
    have hpChain :
        p ∈
          (localDiskFillings.intersection_chain x ⟨e, hxe⟩).relativeInterior := by
      simpa [hrelativeInterior] using hp
    have hpClosedX :
        p ∈ Metric.closedBall x.1
          (controlDisks.intersectionRadius x) :=
      Metric.ball_subset_closedBall
        (localDiskFillings.intersection_chain_relativeInterior_subset_ball
          x ⟨e, hxe⟩ hpChain)
    rcases hpEndpoint with hpSource | hpTarget
    · have hpClosedSource :
          p ∈
            Metric.closedBall
              (D.vertexPlacement (tubeChains.edgeSourceVertex e))
              (controlDisks.vertexRadius
                (tubeChains.edgeSourceVertex e)) := by
        rw [hpSource]
        exact Metric.ball_subset_closedBall
          (edgeSource_mem_source_ball e)
      exact
        (Set.disjoint_left.mp
          (controlDisks.vertex_intersection_disjoint
            (tubeChains.edgeSourceVertex e) x)
          hpClosedSource) hpClosedX
    · have hpClosedTarget :
          p ∈
            Metric.closedBall
              (D.vertexPlacement (tubeChains.edgeTargetVertex e))
              (controlDisks.vertexRadius
                (tubeChains.edgeTargetVertex e)) := by
        rw [hpTarget]
        exact Metric.ball_subset_closedBall
          (edgeTarget_mem_target_ball e)
      exact
        (Set.disjoint_left.mp
          (controlDisks.vertex_intersection_disjoint
            (tubeChains.edgeTargetVertex e) x)
                  hpClosedTarget) hpClosedX

private lemma endpointGluedVerticesAdjacentDistinct
    (pieces : List PolygonalArc)
    (successive_attach :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).target = (pieces[n + 1]).source) :
    ∀ i (hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length),
      (PolygonalArcEndpointGluedVertices pieces)[i] ≠
        (PolygonalArcEndpointGluedVertices pieces)[i + 1] := by
  intro i hi
  have htransfer :=
    PolygonalArcEndpointGluedSegmentTransfer pieces successive_attach
  rcases htransfer.2 i hi with
    ⟨piece, _hpiece, m, hm, hmatch | hmatch⟩
  · have hpiece_ne : piece.vertices[m] ≠ piece.vertices[m + 1] := by
      intro heq
      have hm_left : m < piece.vertices.length := by omega
      have hm_right : m + 1 < piece.vertices.length := by omega
      have hidx : m = m + 1 :=
        (piece.simple_vertices.getElem_inj_iff
          (i := m) (j := m + 1)
          (hi := hm_left) (hj := hm_right)).1 heq
      omega
    intro hglued
    exact hpiece_ne (by
      calc
        piece.vertices[m] =
            (PolygonalArcEndpointGluedVertices pieces)[i] := hmatch.1.symm
        _ = (PolygonalArcEndpointGluedVertices pieces)[i + 1] := hglued
        _ = piece.vertices[m + 1] := hmatch.2)
  · have hpiece_ne : piece.vertices[m] ≠ piece.vertices[m + 1] := by
      intro heq
      have hm_left : m < piece.vertices.length := by omega
      have hm_right : m + 1 < piece.vertices.length := by omega
      have hidx : m = m + 1 :=
        (piece.simple_vertices.getElem_inj_iff
          (i := m) (j := m + 1)
          (hi := hm_left) (hj := hm_right)).1 heq
      omega
    intro hglued
    exact hpiece_ne (by
      calc
        piece.vertices[m] =
            (PolygonalArcEndpointGluedVertices pieces)[i + 1] := hmatch.2.symm
        _ = (PolygonalArcEndpointGluedVertices pieces)[i] := hglued.symm
        _ = piece.vertices[m + 1] := hmatch.1)

private lemma assembleEndpointGluedPieces
    (pieces : List PolygonalArc)
    (source target : EuclideanSpace ℝ (Fin 2))
    (hpieces : pieces ≠ [])
    (first_source : ∀ Γ, pieces.head? = some Γ → Γ.source = source)
    (last_target : ∀ Γ, pieces.getLast? = some Γ → Γ.target = target)
    (successive_attach :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).target = (pieces[n + 1]).source)
    (adjacent_segment_intersections :
      ∀ i
        (hi : (i + 1) + 1 <
          (PolygonalArcEndpointGluedVertices pieces).length),
        (segment ℝ (PolygonalArcEndpointGluedVertices pieces)[i]
              (PolygonalArcEndpointGluedVertices pieces)[i + 1] ∩
            segment ℝ (PolygonalArcEndpointGluedVertices pieces)[i + 1]
              (PolygonalArcEndpointGluedVertices pieces)[(i + 1) + 1]) =
          {(PolygonalArcEndpointGluedVertices pieces)[i + 1]})
    (nonadjacent_segment_disjoint :
      ∀ ⦃i j : ℕ⦄,
        (hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length) →
        (hj : j + 1 < (PolygonalArcEndpointGluedVertices pieces).length) →
        i + 1 < j →
        Disjoint
          (segment ℝ (PolygonalArcEndpointGluedVertices pieces)[i]
            (PolygonalArcEndpointGluedVertices pieces)[i + 1])
          (segment ℝ (PolygonalArcEndpointGluedVertices pieces)[j]
            (PolygonalArcEndpointGluedVertices pieces)[j + 1]))
    (piece_relativeInterior_avoids_endpoints :
      ∀ Γ, Γ ∈ pieces →
        Disjoint Γ.relativeInterior
          ({source, target} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ Γ : PolygonalArc,
      Γ.source = source ∧
        Γ.target = target ∧
          Γ.carrier =
            {p | ∃ piece : PolygonalArc,
              piece ∈ pieces ∧ p ∈ piece.carrier} ∧
            Γ.relativeInterior =
              {p | ∃ piece : PolygonalArc,
                piece ∈ pieces ∧ p ∈ piece.carrier} \
                ({source, target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
              (∀ piece, piece ∈ pieces →
                piece.relativeInterior ⊆ Γ.relativeInterior) ∧
                (∀ piece, piece ∈ pieces →
                  ∀ m (hm : m + 1 < piece.vertices.length),
                    ∃ i : ℕ, ∃ hi : i + 1 < Γ.vertices.length,
                      ((Γ.vertices[i] = piece.vertices[m] ∧
                          Γ.vertices[i + 1] = piece.vertices[m + 1]) ∨
                        (Γ.vertices[i] = piece.vertices[m + 1] ∧
                          Γ.vertices[i + 1] = piece.vertices[m]))) ∧
                  (∀ i (hi : i + 1 < Γ.vertices.length),
                    ∃ piece : PolygonalArc, piece ∈ pieces ∧
                      ∃ m : ℕ, ∃ hm : m + 1 < piece.vertices.length,
                        ((Γ.vertices[i] = piece.vertices[m] ∧
                            Γ.vertices[i + 1] = piece.vertices[m + 1]) ∨
                          (Γ.vertices[i] = piece.vertices[m + 1] ∧
                            Γ.vertices[i + 1] = piece.vertices[m]))) := by
  rcases PolygonalArcFromEndpointGluedPieces
      (pieces := pieces) (source := source) (target := target)
      hpieces first_source last_target successive_attach
      (endpointGluedVerticesAdjacentDistinct pieces successive_attach)
      adjacent_segment_intersections nonadjacent_segment_disjoint
      piece_relativeInterior_avoids_endpoints with
    ⟨Γ, _hvertices, hsource, htarget, hcarrier, hrelativeInterior,
      hpiece_subset, hpiece_lift, hsegment_localized⟩
  exact ⟨Γ, hsource, htarget, hcarrier, hrelativeInterior,
    hpiece_subset, hpiece_lift, hsegment_localized⟩

private structure OrderedPiecesAssemblyFacts
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (sourceSpoke targetSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (gapCenter :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) →
          {p // p ∈ D.intersectionPoints}) where
  sourceSpoke_def : ∀ e, sourceSpoke e =
    localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
      ⟨e, tubeChains.edgeSourceVertex_mem e⟩
  targetSpoke_def : ∀ e, targetSpoke e =
    localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
      ⟨e, tubeChains.edgeTargetVertex_mem e⟩
  targetSpokeReverse_def : ∀ e,
    targetSpokeReverse e = PolygonalArcReverse (targetSpoke e)
  gapCenter_spec : ∀ e n,
    (gapCenter e n).1 ∈ D.edgeRelativeInterior e ∧
      tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ∈
          Metric.sphere (gapCenter e n).1
            (controlDisks.intersectionRadius (gapCenter e n)) ∧
        tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ∈
            D.edgeCarrier e ∧
          tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) ∈
              Metric.sphere (gapCenter e n).1
                (controlDisks.intersectionRadius (gapCenter e n)) ∧
            tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) ∈
                D.edgeCarrier e ∧
              tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ≠
                tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1])
  orderedPieces_nonempty : ∀ e, (orderedPieces e).length ≠ 0
  orderedPieces_head_source : ∀ e Γ,
    (orderedPieces e).head? = some Γ → Γ.source = D.edgeSource e
  orderedPieces_last_target : ∀ e Γ,
    (orderedPieces e).getLast? = some Γ → Γ.target = D.edgeTarget e
  orderedPiece_is_local : ∀ e Γ, Γ ∈ orderedPieces e →
    (∃ (v : V) (hve : v ∈ e.1),
      Γ.carrier =
          (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier ∧
        Γ.relativeInterior =
          (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior) ∨
    (∃ i : tubeChains.pieceIndex,
      tubeChains.owner i = e ∧
        Γ.carrier = (tubeChains.chain i).carrier ∧
          Γ.relativeInterior = (tubeChains.chain i).relativeInterior) ∨
    (∃ (x : {p // p ∈ D.intersectionPoints})
        (hxe : x.1 ∈ D.edgeRelativeInterior e),
      Γ.carrier =
          (localDiskFillings.intersection_chain x ⟨e, hxe⟩).carrier ∧
        Γ.relativeInterior =
          (localDiskFillings.intersection_chain x ⟨e, hxe⟩).relativeInterior)
  edge_mem_source_or_target : ∀ e v, v ∈ e.1 →
    v = tubeChains.edgeSourceVertex e ∨ v = tubeChains.edgeTargetVertex e
  edgeSourceVertex_ne_targetVertex : ∀ e,
    tubeChains.edgeSourceVertex e ≠ tubeChains.edgeTargetVertex e
  edgeSource_mem_source_ball : ∀ e,
    D.edgeSource e ∈
      Metric.ball (D.vertexPlacement (tubeChains.edgeSourceVertex e))
        (controlDisks.vertexRadius (tubeChains.edgeSourceVertex e))
  edgeTarget_mem_target_ball : ∀ e,
    D.edgeTarget e ∈
      Metric.ball (D.vertexPlacement (tubeChains.edgeTargetVertex e))
        (controlDisks.vertexRadius (tubeChains.edgeTargetVertex e))
  vertex_spoke_boundary_point_eq_target :
    ∀ v (e : {e : G.edgeFinset // v ∈ e.1})
      (p : EuclideanSpace ℝ (Fin 2)),
      p ∈ (localDiskFillings.vertex_spoke v e).carrier →
        p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
          p = (localDiskFillings.vertex_spoke v e).target
  gapConnector_target : ∀ e n,
    (gapConnector e n).target =
      tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1])
  terminalTube_attaches_targetSpoke : ∀ e,
    (tubeChains.chain (terminalTubeIndex e)).target =
      (targetSpokeReverse e).source
  terminalTubeIndex_getLast : ∀ e,
    (tubeChains.edgePieceOrder e).getLast? = some (terminalTubeIndex e)
  gapConnector_eq_or_reverse_gapCenter :
    ∀ e (q : Fin ((tubeChains.edgePieceOrder e).length - 1)),
      gapConnector e q =
          localDiskFillings.intersection_chain (gapCenter e q)
            ⟨e, (gapCenter_spec e q).1⟩ ∨
        gapConnector e q = PolygonalArcReverse
          (localDiskFillings.intersection_chain (gapCenter e q)
            ⟨e, (gapCenter_spec e q).1⟩)
  orderedPieces_length : ∀ e, (orderedPieces e).length =
    2 * (tubeChains.edgePieceOrder e).length + 1
  orderedPieces_get?_tube : ∀ (e : G.edgeFinset) q
    (hq : q < (tubeChains.edgePieceOrder e).length),
    (orderedPieces e)[1 + 2 * q]? =
      some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q]))
  orderedPieces_get?_gap : ∀ (e : G.edgeFinset) q
    (hq : q + 1 < (tubeChains.edgePieceOrder e).length),
    (orderedPieces e)[2 + 2 * q]? =
      some (gapConnector e ⟨q, by omega⟩)
  orderedPieces_get?_classify :
    ∀ e m (hm : m < (orderedPieces e).length),
      (m = 0 ∧ (orderedPieces e)[m]? = some (sourceSpoke e)) ∨
        (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
          m = 1 + 2 * q ∧
            (orderedPieces e)[m]? =
              some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q]))) ∨
        (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
          m = 2 + 2 * q ∧
            (orderedPieces e)[m]? = some (gapConnector e ⟨q, by omega⟩)) ∨
        (m = 2 * (tubeChains.edgePieceOrder e).length - 1 ∧
          (orderedPieces e)[m]? =
            some (tubeChains.chain (terminalTubeIndex e))) ∨
        (m = 2 * (tubeChains.edgePieceOrder e).length ∧
          (orderedPieces e)[m]? = some (targetSpokeReverse e))
  orderedPieces_successive_attach_local :
    ∀ e n (hn : n + 1 < (orderedPieces e).length),
      ((orderedPieces e)[n]).target = ((orderedPieces e)[n + 1]).source
  orderedPieces_non_successive_disjoint_local :
    ∀ e m n (hm : m < (orderedPieces e).length)
      (hn : n < (orderedPieces e).length),
      m + 1 < n ∨ n + 1 < m →
        Disjoint ((orderedPieces e)[m]).carrier
          ((orderedPieces e)[n]).carrier

private def mkOrderedPiecesAssemblyFacts
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (gapCenter :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) →
          {p // p ∈ D.intersectionPoints})
    (gapCenter_spec : ∀ e n,
      (gapCenter e n).1 ∈ D.edgeRelativeInterior e ∧
        tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ∈
            Metric.sphere (gapCenter e n).1
              (controlDisks.intersectionRadius (gapCenter e n)) ∧
          tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ∈
              D.edgeCarrier e ∧
            tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) ∈
                Metric.sphere (gapCenter e n).1
                  (controlDisks.intersectionRadius (gapCenter e n)) ∧
              tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) ∈
                  D.edgeCarrier e ∧
                tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ≠
                  tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]))
    (orderedPieces_nonempty : ∀ e, (orderedPieces e).length ≠ 0)
    (orderedPieces_head_source : ∀ e Γ,
      (orderedPieces e).head? = some Γ → Γ.source = D.edgeSource e)
    (orderedPieces_last_target : ∀ e Γ,
      (orderedPieces e).getLast? = some Γ → Γ.target = D.edgeTarget e)
    (orderedPiece_is_local : ∀ e Γ, Γ ∈ orderedPieces e →
      (∃ (v : V) (hve : v ∈ e.1),
        Γ.carrier =
            (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier ∧
          Γ.relativeInterior =
            (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior) ∨
      (∃ i : tubeChains.pieceIndex,
        tubeChains.owner i = e ∧
          Γ.carrier = (tubeChains.chain i).carrier ∧
            Γ.relativeInterior = (tubeChains.chain i).relativeInterior) ∨
      (∃ (x : {p // p ∈ D.intersectionPoints})
          (hxe : x.1 ∈ D.edgeRelativeInterior e),
        Γ.carrier =
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩).carrier ∧
          Γ.relativeInterior =
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩).relativeInterior))
    (edge_mem_source_or_target : ∀ e v, v ∈ e.1 →
      v = tubeChains.edgeSourceVertex e ∨ v = tubeChains.edgeTargetVertex e)
    (edgeSourceVertex_ne_targetVertex : ∀ e,
      tubeChains.edgeSourceVertex e ≠ tubeChains.edgeTargetVertex e)
    (edgeSource_mem_source_ball : ∀ e,
      D.edgeSource e ∈
        Metric.ball (D.vertexPlacement (tubeChains.edgeSourceVertex e))
          (controlDisks.vertexRadius (tubeChains.edgeSourceVertex e)))
    (edgeTarget_mem_target_ball : ∀ e,
      D.edgeTarget e ∈
        Metric.ball (D.vertexPlacement (tubeChains.edgeTargetVertex e))
          (controlDisks.vertexRadius (tubeChains.edgeTargetVertex e)))
    (vertex_spoke_boundary_point_eq_target :
      ∀ v (e : {e : G.edgeFinset // v ∈ e.1})
        (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ (localDiskFillings.vertex_spoke v e).carrier →
          p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
            p = (localDiskFillings.vertex_spoke v e).target)
    (gapConnector_target : ∀ e n,
      (gapConnector e n).target =
        tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]))
    (terminalTube_attaches_targetSpoke : ∀ e,
      (tubeChains.chain (terminalTubeIndex e)).target =
        (PolygonalArcReverse
          (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
            ⟨e, tubeChains.edgeTargetVertex_mem e⟩)).source)
    (terminalTubeIndex_getLast : ∀ e,
      (tubeChains.edgePieceOrder e).getLast? = some (terminalTubeIndex e))
    (gapConnector_eq_or_reverse_gapCenter :
      ∀ e (q : Fin ((tubeChains.edgePieceOrder e).length - 1)),
        gapConnector e q =
            localDiskFillings.intersection_chain (gapCenter e q)
              ⟨e, (gapCenter_spec e q).1⟩ ∨
          gapConnector e q = PolygonalArcReverse
            (localDiskFillings.intersection_chain (gapCenter e q)
              ⟨e, (gapCenter_spec e q).1⟩))
    (orderedPieces_length : ∀ e, (orderedPieces e).length =
      2 * (tubeChains.edgePieceOrder e).length + 1)
    (orderedPieces_get?_tube : ∀ (e : G.edgeFinset) q
      (hq : q < (tubeChains.edgePieceOrder e).length),
      (orderedPieces e)[1 + 2 * q]? =
        some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q])))
    (orderedPieces_get?_gap : ∀ (e : G.edgeFinset) q
      (hq : q + 1 < (tubeChains.edgePieceOrder e).length),
      (orderedPieces e)[2 + 2 * q]? =
        some (gapConnector e ⟨q, by omega⟩))
    (orderedPieces_get?_classify :
      ∀ e m (hm : m < (orderedPieces e).length),
        (m = 0 ∧ (orderedPieces e)[m]? = some
          (localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
            ⟨e, tubeChains.edgeSourceVertex_mem e⟩)) ∨
          (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
            m = 1 + 2 * q ∧
              (orderedPieces e)[m]? =
                some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q]))) ∨
          (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
            m = 2 + 2 * q ∧
              (orderedPieces e)[m]? = some (gapConnector e ⟨q, by omega⟩)) ∨
          (m = 2 * (tubeChains.edgePieceOrder e).length - 1 ∧
            (orderedPieces e)[m]? =
              some (tubeChains.chain (terminalTubeIndex e))) ∨
          (m = 2 * (tubeChains.edgePieceOrder e).length ∧
            (orderedPieces e)[m]? = some (PolygonalArcReverse
              (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
                ⟨e, tubeChains.edgeTargetVertex_mem e⟩))))
    (orderedPieces_successive_attach_local :
      ∀ e n (hn : n + 1 < (orderedPieces e).length),
        ((orderedPieces e)[n]).target = ((orderedPieces e)[n + 1]).source)
    (orderedPieces_non_successive_disjoint_local :
      ∀ e m n (hm : m < (orderedPieces e).length)
        (hn : n < (orderedPieces e).length),
        m + 1 < n ∨ n + 1 < m →
          Disjoint ((orderedPieces e)[m]).carrier
            ((orderedPieces e)[n]).carrier) :
    OrderedPiecesAssemblyFacts G D controlDisks tubeChains localDiskFillings
      (fun e => localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
        ⟨e, tubeChains.edgeSourceVertex_mem e⟩)
      (fun e => localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
        ⟨e, tubeChains.edgeTargetVertex_mem e⟩)
      (fun e => PolygonalArcReverse
        (localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
          ⟨e, tubeChains.edgeTargetVertex_mem e⟩))
      orderedPieces terminalTubeIndex gapConnector gapCenter :=
  { sourceSpoke_def := by intro e; rfl
    targetSpoke_def := by intro e; rfl
    targetSpokeReverse_def := by intro e; rfl
    gapCenter_spec := gapCenter_spec
    orderedPieces_nonempty := orderedPieces_nonempty
    orderedPieces_head_source := orderedPieces_head_source
    orderedPieces_last_target := orderedPieces_last_target
    orderedPiece_is_local := orderedPiece_is_local
    edge_mem_source_or_target := edge_mem_source_or_target
    edgeSourceVertex_ne_targetVertex := edgeSourceVertex_ne_targetVertex
    edgeSource_mem_source_ball := edgeSource_mem_source_ball
    edgeTarget_mem_target_ball := edgeTarget_mem_target_ball
    vertex_spoke_boundary_point_eq_target := vertex_spoke_boundary_point_eq_target
    gapConnector_target := gapConnector_target
    terminalTube_attaches_targetSpoke := terminalTube_attaches_targetSpoke
    terminalTubeIndex_getLast := terminalTubeIndex_getLast
    gapConnector_eq_or_reverse_gapCenter := gapConnector_eq_or_reverse_gapCenter
    orderedPieces_length := orderedPieces_length
    orderedPieces_get?_tube := orderedPieces_get?_tube
    orderedPieces_get?_gap := orderedPieces_get?_gap
    orderedPieces_get?_classify := orderedPieces_get?_classify
    orderedPieces_successive_attach_local := orderedPieces_successive_attach_local
    orderedPieces_non_successive_disjoint_local :=
      orderedPieces_non_successive_disjoint_local }

private lemma assembleOrderedPieces
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (sourceSpoke targetSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (gapCenter :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) →
          {p // p ∈ D.intersectionPoints})
    (facts :
      OrderedPiecesAssemblyFacts G D controlDisks tubeChains localDiskFillings
        sourceSpoke targetSpoke targetSpokeReverse orderedPieces
        terminalTubeIndex gapConnector gapCenter) :
    ∀ e, ∃ Γ : PolygonalArc,
      Γ.source = D.edgeSource e ∧
        Γ.target = D.edgeTarget e ∧
          Γ.carrier =
            {p | ∃ piece : PolygonalArc,
              piece ∈ orderedPieces e ∧ p ∈ piece.carrier} ∧
            Γ.relativeInterior =
              {p | ∃ piece : PolygonalArc,
                piece ∈ orderedPieces e ∧ p ∈ piece.carrier} \
                ({D.edgeSource e, D.edgeTarget e} :
                  Set (EuclideanSpace ℝ (Fin 2))) ∧
              (∀ piece, piece ∈ orderedPieces e →
                piece.relativeInterior ⊆ Γ.relativeInterior) ∧
                (∀ piece, piece ∈ orderedPieces e →
                  ∀ m (hm : m + 1 < piece.vertices.length),
                    ∃ i : ℕ, ∃ hi : i + 1 < Γ.vertices.length,
                      ((Γ.vertices[i] = piece.vertices[m] ∧
                          Γ.vertices[i + 1] = piece.vertices[m + 1]) ∨
                        (Γ.vertices[i] = piece.vertices[m + 1] ∧
                          Γ.vertices[i + 1] = piece.vertices[m]))) ∧
                  (∀ i (hi : i + 1 < Γ.vertices.length),
                    ∃ piece : PolygonalArc, piece ∈ orderedPieces e ∧
                      ∃ m : ℕ, ∃ hm : m + 1 < piece.vertices.length,
                        ((Γ.vertices[i] = piece.vertices[m] ∧
                            Γ.vertices[i + 1] = piece.vertices[m + 1]) ∨
                          (Γ.vertices[i] = piece.vertices[m + 1] ∧
                            Γ.vertices[i + 1] = piece.vertices[m]))) := by
    have sourceSpoke_def := facts.sourceSpoke_def
    have targetSpoke_def := facts.targetSpoke_def
    have targetSpokeReverse_def := facts.targetSpokeReverse_def
    have gapCenter_spec := facts.gapCenter_spec
    have orderedPieces_nonempty := facts.orderedPieces_nonempty
    have orderedPieces_head_source := facts.orderedPieces_head_source
    have orderedPieces_last_target := facts.orderedPieces_last_target
    have orderedPiece_is_local := facts.orderedPiece_is_local
    have edge_mem_source_or_target := facts.edge_mem_source_or_target
    have edgeSourceVertex_ne_targetVertex :=
      facts.edgeSourceVertex_ne_targetVertex
    have edgeSource_mem_source_ball := facts.edgeSource_mem_source_ball
    have edgeTarget_mem_target_ball := facts.edgeTarget_mem_target_ball
    have vertex_spoke_boundary_point_eq_target :=
      facts.vertex_spoke_boundary_point_eq_target
    have gapConnector_target := facts.gapConnector_target
    have terminalTube_attaches_targetSpoke :=
      facts.terminalTube_attaches_targetSpoke
    have terminalTubeIndex_getLast := facts.terminalTubeIndex_getLast
    have gapConnector_eq_or_reverse_gapCenter :=
      facts.gapConnector_eq_or_reverse_gapCenter
    have orderedPieces_length := facts.orderedPieces_length
    have orderedPieces_get?_tube := facts.orderedPieces_get?_tube
    have orderedPieces_get?_gap := facts.orderedPieces_get?_gap
    have orderedPieces_get?_classify := facts.orderedPieces_get?_classify
    have orderedPieces_successive_attach_local :=
      facts.orderedPieces_successive_attach_local
    have orderedPieces_non_successive_disjoint_local :=
      facts.orderedPieces_non_successive_disjoint_local
    intro e
    have sourceSpoke_tube_inter_subset :
        ∀ i,
          (sourceSpoke e).carrier ∩ (tubeChains.chain i).carrier ⊆
            ({(sourceSpoke e).target} : Set (EuclideanSpace ℝ (Fin 2))) :=
      sourceSpokeTubeInterSubset G D controlDisks tubeChains localDiskFillings
        sourceSpoke sourceSpoke_def vertex_spoke_boundary_point_eq_target e
    have tube_targetSpoke_inter_subset :
        ∀ i,
          (tubeChains.chain i).carrier ∩ (targetSpokeReverse e).carrier ⊆
            ({(targetSpokeReverse e).source} :
              Set (EuclideanSpace ℝ (Fin 2))) :=
      tubeTargetSpokeInterSubset G D controlDisks tubeChains localDiskFillings
        targetSpoke targetSpokeReverse targetSpoke_def targetSpokeReverse_def
        vertex_spoke_boundary_point_eq_target e
    have gapConnector_carrier_subset_closedBall :
        ∀ q,
          (gapConnector e q).carrier ⊆
            Metric.closedBall (gapCenter e q).1
              (controlDisks.intersectionRadius (gapCenter e q)) := by
      let gapCenter_mem : ∀ e q,
          (gapCenter e q).1 ∈ D.edgeRelativeInterior e :=
        fun e q => (gapCenter_spec e q).1
      exact
        gapConnectorCarrierSubsetClosedBall G D controlDisks tubeChains
          localDiskFillings gapConnector gapCenter gapCenter_mem (by
            intro e q
            simpa [gapCenter_mem] using
              gapConnector_eq_or_reverse_gapCenter e q) e
    have tube_gap_inter_subset_left :
        ∀ q,
          (tubeChains.chain ((tubeChains.edgePieceOrder e)[q.1])).carrier ∩
              (gapConnector e q).carrier ⊆
            ({(tubeChains.chain
                ((tubeChains.edgePieceOrder e)[q.1])).target} :
              Set (EuclideanSpace ℝ (Fin 2))) :=
      tubeGapInterSubsetLeft G D controlDisks tubeChains orderedPieces
        gapConnector gapCenter orderedPieces_length orderedPieces_get?_tube
        orderedPieces_get?_gap orderedPieces_successive_attach_local
        orderedPieces_non_successive_disjoint_local e
        gapConnector_carrier_subset_closedBall
    have gap_tube_inter_subset_right :
        ∀ q,
          (gapConnector e q).carrier ∩
              (tubeChains.chain
                ((tubeChains.edgePieceOrder e)[q.1 + 1])).carrier ⊆
            ({(gapConnector e q).target} : Set (EuclideanSpace ℝ (Fin 2))) :=
      gapTubeInterSubsetRight G D controlDisks tubeChains orderedPieces
        gapConnector gapCenter gapConnector_target orderedPieces_length
        orderedPieces_get?_tube orderedPieces_get?_gap
        orderedPieces_successive_attach_local
        orderedPieces_non_successive_disjoint_local e
        gapConnector_carrier_subset_closedBall
    have orderedPieces_successive_carrier_intersections_subset :
        ∀ n (hn : n + 1 < (orderedPieces e).length),
          (orderedPieces e)[n].carrier ∩ (orderedPieces e)[n + 1].carrier ⊆
            ({(orderedPieces e)[n].target} :
              Set (EuclideanSpace ℝ (Fin 2))) :=
      orderedPiecesSuccessiveCarrierIntersectionsSubset G D controlDisks
        tubeChains sourceSpoke targetSpokeReverse orderedPieces terminalTubeIndex
        gapConnector terminalTubeIndex_getLast terminalTube_attaches_targetSpoke
        orderedPieces_length orderedPieces_get?_classify e
        sourceSpoke_tube_inter_subset tube_targetSpoke_inter_subset
        tube_gap_inter_subset_left gap_tube_inter_subset_right
    have hsegmentCerts :
        (∀ i
          (hi : (i + 1) + 1 <
            (PolygonalArcEndpointGluedVertices (orderedPieces e)).length),
          (segment ℝ (PolygonalArcEndpointGluedVertices (orderedPieces e))[i]
                (PolygonalArcEndpointGluedVertices (orderedPieces e))[i + 1] ∩
              segment ℝ
                (PolygonalArcEndpointGluedVertices (orderedPieces e))[i + 1]
                (PolygonalArcEndpointGluedVertices (orderedPieces e))[(i + 1) + 1]) =
            {(PolygonalArcEndpointGluedVertices (orderedPieces e))[i + 1]}) ∧
        (∀ ⦃i j : ℕ⦄,
          (hi : i + 1 <
            (PolygonalArcEndpointGluedVertices (orderedPieces e)).length) →
          (hj : j + 1 <
            (PolygonalArcEndpointGluedVertices (orderedPieces e)).length) →
          i + 1 < j →
          Disjoint
            (segment ℝ (PolygonalArcEndpointGluedVertices (orderedPieces e))[i]
              (PolygonalArcEndpointGluedVertices (orderedPieces e))[i + 1])
            (segment ℝ (PolygonalArcEndpointGluedVertices (orderedPieces e))[j]
              (PolygonalArcEndpointGluedVertices (orderedPieces e))[j + 1])) := by
      exact
        PolygonalArcEndpointGluedSegmentCertificates
          (pieces := orderedPieces e)
          (successive_attach := by
            intro n hn
            exact orderedPieces_successive_attach_local e n hn)
          (successive_carrier_intersections_subset := by
            intro n hn
            exact orderedPieces_successive_carrier_intersections_subset n hn)
          (non_successive_carrier_disjoint := by
            intro k l hk hl hkl
            exact orderedPieces_non_successive_disjoint_local e k l hk hl hkl)
    exact
      assembleEndpointGluedPieces (orderedPieces e) (D.edgeSource e)
        (D.edgeTarget e) (by
          intro hnil
          exact orderedPieces_nonempty e (by simp [hnil]))
        (orderedPieces_head_source e) (orderedPieces_last_target e)
        (orderedPieces_successive_attach_local e) hsegmentCerts.1 hsegmentCerts.2
        (orderedPieceRelativeInteriorAvoidsEdgeEndpoints G D controlDisks
          tubeChains localDiskFillings orderedPieces orderedPiece_is_local
          edge_mem_source_or_target edgeSourceVertex_ne_targetVertex
          edgeSource_mem_source_ball edgeTarget_mem_target_ball e)


private lemma orderedPiecesSuccessiveAttachLocal
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (sourceSpoke targetSpokeReverse : G.edgeFinset → PolygonalArc)
    (terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex)
    (gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc)
    (terminalTubeIndex_getLast : ∀ e,
      (tubeChains.edgePieceOrder e).getLast? = some (terminalTubeIndex e))
    (sourceSpoke_attaches_first_tube : ∀ e i,
      (tubeChains.edgePieceOrder e).head? = some i →
        (sourceSpoke e).target = (tubeChains.chain i).source)
    (gapConnector_source : ∀ e n,
      (gapConnector e n).source =
        tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]))
    (gapConnector_target : ∀ e n,
      (gapConnector e n).target =
        tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]))
    (terminalTube_attaches_targetSpoke : ∀ e,
      (tubeChains.chain (terminalTubeIndex e)).target =
        (targetSpokeReverse e).source) :
    ∀ e n
      (hn : n + 1 <
        (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
          targetSpokeReverse terminalTubeIndex gapConnector e).length),
      ((orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e)[n]).target =
      ((orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e)[n + 1]).source := by
  intro e n hn
  let R : PolygonalArc → PolygonalArc → Prop :=
    fun Γ Δ => Γ.target = Δ.source
  have finBlockHead_of_eq_zero :
      ∀ (K : ℕ) (hK : K = 0)
        (chain : Fin (K + 1) → PolygonalArc)
        (gap : Fin K → PolygonalArc),
        (((List.finRange K).map
          (fun q => [chain (Fin.castSucc q), gap q])).flatten ++
          [chain (Fin.last K)]).head? =
            some (chain (Fin.last K)) := by
    intro K hK chain gap
    subst K
    simp
  have finBlockHead_of_pos :
      ∀ (K : ℕ) (hK : 0 < K)
        (chain : Fin (K + 1) → PolygonalArc)
        (gap : Fin K → PolygonalArc),
        (((List.finRange K).map
          (fun q => [chain (Fin.castSucc q), gap q])).flatten ++
          [chain (Fin.last K)]).head? =
            some (chain 0) := by
    intro K hK chain gap
    cases K with
    | zero => omega
    | succ K =>
        simp [List.finRange_succ]
  let L := tubeChains.edgePieceOrder e
  let K := L.length - 1
  have hL_nonzero : L.length ≠ 0 := by
    dsimp [L]
    exact tubeChains.edgePieceOrder_nonempty e
  have hK_last : K < L.length := by
    dsimp [K]
    omega
  have hlast_get? : L[K]? = some (terminalTubeIndex e) := by
    have hlast := terminalTubeIndex_getLast e
    rw [List.getLast?_eq_getElem?] at hlast
    simpa [L, K] using hlast
  have hlast_eq : L.get ⟨K, hK_last⟩ = terminalTubeIndex e := by
    have hget := hlast_get?
    rw [List.getElem?_eq_getElem hK_last] at hget
    exact Option.some.inj hget
  let chainAt : Fin (K + 1) → PolygonalArc := fun q =>
    tubeChains.chain (L.get ⟨q.1, by
      have hq : q.1 < K + 1 := q.2
      dsimp [K] at hq ⊢
      omega⟩)
  have hlast_chainAt :
      chainAt (Fin.last K) =
        tubeChains.chain (terminalTubeIndex e) := by
    dsimp [chainAt]
    simpa using congrArg tubeChains.chain hlast_eq
  let blockList : List PolygonalArc :=
    ((List.finRange K).map
      (fun q => [chainAt (Fin.castSucc q), gapConnector e q])).flatten ++
      [chainAt (Fin.last K)]
  have hblocks : List.IsChain R blockList := by
    exact
      finiteAlternatingBlockIsChain R K chainAt
        (fun q : Fin K => gapConnector e q)
        (by
          intro q
          dsimp [R, chainAt]
          calc
            (tubeChains.chain
                (L.get ⟨(Fin.castSucc q).1, by
                  have hq : (Fin.castSucc q).1 < K + 1 :=
                    (Fin.castSucc q).2
                  dsimp [K] at hq ⊢
                  omega⟩)).target =
                tubeChains.target
                  (L.get ⟨(Fin.castSucc q).1, by
                    have hq : (Fin.castSucc q).1 < K + 1 :=
                      (Fin.castSucc q).2
                    dsimp [K] at hq ⊢
                    omega⟩) :=
              (tubeChains.chain_endpoints
                (L.get ⟨(Fin.castSucc q).1, by
                  have hq : (Fin.castSucc q).1 < K + 1 :=
                    (Fin.castSucc q).2
                  dsimp [K] at hq ⊢
                  omega⟩)).2
            _ = (gapConnector e q).source := by
              simpa [L] using (gapConnector_source e q).symm)
        (by
          intro q
          dsimp [R, chainAt]
          calc
            (gapConnector e q).target =
                tubeChains.source (L.get ⟨q.1 + 1, by
                  have hq : q.1 < K := q.2
                  dsimp [K] at hq ⊢
                  omega⟩) := by
              simpa [L] using gapConnector_target e q
            _ =
                (tubeChains.chain
                  (L.get ⟨(q.succ).1, by
                    have hq : (q.succ).1 < K + 1 := q.succ.2
                    dsimp [K] at hq ⊢
                    omega⟩)).source := by
              simpa using
                (tubeChains.chain_endpoints
                  (L.get ⟨(q.succ).1, by
                    have hq : (q.succ).1 < K + 1 := q.succ.2
                    dsimp [K] at hq ⊢
                    omega⟩)).1.symm)
  have hsource_head :
      ∀ y ∈ blockList.head?, R (sourceSpoke e) y := by
    intro y hy
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · have hblock_head :
          blockList.head? = some (chainAt (Fin.last K)) := by
        simpa [blockList] using
          finBlockHead_of_eq_zero K hK0 chainAt
            (fun q : Fin K => gapConnector e q)
      have hy_chain : chainAt (Fin.last K) = y := by
        rw [hblock_head] at hy
        simpa using hy
      rw [← hy_chain]
      have h0 : 0 < L.length := by omega
      have hhead0 : L.head? = some L[0] := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
      have hlast0 : L[0] = terminalTubeIndex e := by
        have hidx : (0 : ℕ) = K := hK0.symm
        simpa [hidx] using hlast_eq
      have hterm_head : L.head? = some (terminalTubeIndex e) := by
        simpa [hlast0] using hhead0
      have hattach :=
        sourceSpoke_attaches_first_tube e (terminalTubeIndex e) hterm_head
      simpa [R, hlast_chainAt] using hattach
    · have hblock_head0 : blockList.head? = some (chainAt 0) := by
        simpa [blockList] using
          finBlockHead_of_pos K hKpos chainAt
            (fun q : Fin K => gapConnector e q)
      have h0 : 0 < L.length := by omega
      have hhead0 : L.head? = some L[0] := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
      have hchain0 : chainAt 0 = tubeChains.chain L[0] := by
        dsimp [chainAt]
        rfl
      have hy_chain : chainAt 0 = y := by
        rw [hblock_head0] at hy
        simpa using hy
      rw [← hy_chain]
      have hattach := sourceSpoke_attaches_first_tube e L[0] hhead0
      simpa [R, hchain0] using hattach
  have hwithSource :
      List.IsChain R (sourceSpoke e :: blockList) :=
    hblocks.cons hsource_head
  have htoTarget :
      ∀ x ∈ (sourceSpoke e :: blockList).getLast?,
        ∀ y ∈ [targetSpokeReverse e].head?, R x y := by
    intro x hx y hy
    have hy' : y = targetSpokeReverse e := by
      simpa using hy.symm
    have hx' : x = tubeChains.chain (terminalTubeIndex e) := by
      have hblock_getLast :
          blockList.getLast? = some (chainAt (Fin.last K)) := by
        dsimp [blockList]
        rw [List.getLast?_append_of_ne_nil
          ((List.map (fun q => [chainAt q.castSucc, gapConnector e q])
            (List.finRange K)).flatten) (by simp)]
        simp
      have hxlast :
          (sourceSpoke e :: blockList).getLast? =
            some (chainAt (Fin.last K)) := by
        rw [List.getLast?_cons, hblock_getLast]
        simp
      rw [hxlast] at hx
      have hx_chain : x = chainAt (Fin.last K) := Option.some.inj hx.symm
      simpa [hlast_chainAt] using hx_chain
    subst x
    subst y
    exact terminalTube_attaches_targetSpoke e
  have hchain :
      List.IsChain R
        (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
          targetSpokeReverse terminalTubeIndex gapConnector e) := by
    have hfull :=
      hwithSource.append (List.IsChain.singleton (targetSpokeReverse e)) htoTarget
    have hterminal_index :
        ∀ h : L.length - 1 < L.length,
          L.get ⟨L.length - 1, h⟩ = terminalTubeIndex e := by
      intro h
      have hfin :
          (⟨L.length - 1, h⟩ : Fin L.length) = ⟨K, hK_last⟩ := by
        apply Fin.ext
        simp [K]
      simpa [hfin] using hlast_eq
    have hterminal_chain :
        ∀ h : L.length - 1 < L.length,
          tubeChains.chain (L.get ⟨L.length - 1, h⟩) =
            tubeChains.chain (terminalTubeIndex e) := by
      intro h
      exact congrArg tubeChains.chain (hterminal_index h)
    have hblockList_eq :
        blockList =
          ((List.finRange
              ((tubeChains.edgePieceOrder e).length - 1)).map
            (fun q => tubeGapBlockForAttach G D controlDisks tubeChains
              gapConnector e q)).flatten ++
            [tubeChains.chain (terminalTubeIndex e)] := by
      simp [blockList, tubeGapBlockForAttach, chainAt, L, K]
      simpa [L] using hterminal_chain (by simpa [L, K] using hK_last)
    simpa [orderedPiecesForAttach, hblockList_eq, R] using hfull
  have hF := List.isChain_iff_forall₂.mp hchain
  have hdrop : n <
      (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e).dropLast.length := by
    simp [List.length_dropLast]
    omega
  have htail : n <
      (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e).tail.length := by
    simp [List.length_tail]
    omega
  have hrel := hF.get hdrop htail
  simpa [List.getElem_dropLast, List.getElem_tail] using hrel

private def chooseFamilyWitness
    {ι α : Type*} {P : ι → α → Prop}
    (exists_witness : ∀ i, ∃ x, P i x) : ι → α :=
  fun i => Classical.choose (exists_witness i)

private lemma chooseFamilyWitness_spec
    {ι α : Type*} {P : ι → α → Prop}
    (exists_witness : ∀ i, ∃ x, P i x) :
    ∀ i, P i (chooseFamilyWitness exists_witness i) := by
  intro i
  exact Classical.choose_spec (exists_witness i)

private def EdgeArcAssemblySpec
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (e : G.edgeFinset) (Γ : PolygonalArc) : Prop :=
  Γ.source = D.edgeSource e ∧
    Γ.target = D.edgeTarget e ∧
      Γ.carrier =
        {p | ∃ piece : PolygonalArc,
          piece ∈ orderedPieces e ∧ p ∈ piece.carrier} ∧
        Γ.relativeInterior =
          {p | ∃ piece : PolygonalArc,
            piece ∈ orderedPieces e ∧ p ∈ piece.carrier} \
            ({D.edgeSource e, D.edgeTarget e} :
              Set (EuclideanSpace ℝ (Fin 2))) ∧
          (∀ piece, piece ∈ orderedPieces e →
            piece.relativeInterior ⊆ Γ.relativeInterior) ∧
            (∀ piece, piece ∈ orderedPieces e →
              ∀ m (hm : m + 1 < piece.vertices.length),
                ∃ i : ℕ, ∃ hi : i + 1 < Γ.vertices.length,
                  ((Γ.vertices[i] = piece.vertices[m] ∧
                      Γ.vertices[i + 1] = piece.vertices[m + 1]) ∨
                    (Γ.vertices[i] = piece.vertices[m + 1] ∧
                      Γ.vertices[i + 1] = piece.vertices[m]))) ∧
              (∀ i (hi : i + 1 < Γ.vertices.length),
                ∃ piece : PolygonalArc, piece ∈ orderedPieces e ∧
                  ∃ m : ℕ, ∃ hm : m + 1 < piece.vertices.length,
                    ((Γ.vertices[i] = piece.vertices[m] ∧
                        Γ.vertices[i + 1] = piece.vertices[m + 1]) ∨
                      (Γ.vertices[i] = piece.vertices[m + 1] ∧
                        Γ.vertices[i + 1] = piece.vertices[m])))

private lemma selectedEdgeArcRelativeInteriorLocalized
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (edgeArc : G.edgeFinset → PolygonalArc)
    (edgeArc_spec : ∀ e,
      EdgeArcAssemblySpec G D orderedPieces e (edgeArc e))
    (orderedPiece_is_local : ∀ e Γ, Γ ∈ orderedPieces e →
      (∃ (v : V) (hve : v ∈ e.1),
        Γ.carrier =
            (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier ∧
          Γ.relativeInterior =
            (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior) ∨
      (∃ i : tubeChains.pieceIndex,
        tubeChains.owner i = e ∧
          Γ.carrier = (tubeChains.chain i).carrier ∧
            Γ.relativeInterior = (tubeChains.chain i).relativeInterior) ∨
      (∃ (x : {p // p ∈ D.intersectionPoints})
          (hxe : x.1 ∈ D.edgeRelativeInterior e),
        Γ.carrier =
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩).carrier ∧
          Γ.relativeInterior =
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩).relativeInterior)) :
    ∀ ⦃e : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ (edgeArc e).relativeInterior →
        (∃ (v : V) (hve : v ∈ e.1),
          p ∈ (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier) ∨
        (∃ i : tubeChains.pieceIndex,
          tubeChains.owner i = e ∧ p ∈ (tubeChains.chain i).carrier) ∨
        (∃ (x : {q // q ∈ D.intersectionPoints})
            (hxe : x.1 ∈ D.edgeRelativeInterior e),
          p ∈ (localDiskFillings.intersection_chain x ⟨e, hxe⟩).carrier) := by
  intro e p hp
  rw [(edgeArc_spec e).2.2.2.1] at hp
  rcases hp.1 with ⟨piece, hpiece, hp_piece⟩
  rcases orderedPiece_is_local e piece hpiece with hvertex | htube |
    hintersection
  · left
    rcases hvertex with ⟨v, hve, hcarrier, _hrelativeInterior⟩
    exact ⟨v, hve, by simpa [hcarrier] using hp_piece⟩
  · right
    left
    rcases htube with ⟨i, howner, hcarrier, _hrelativeInterior⟩
    exact ⟨i, howner, by simpa [hcarrier] using hp_piece⟩
  · right
    right
    rcases hintersection with ⟨x, hxe, hcarrier, _hrelativeInterior⟩
    exact ⟨x, hxe, by simpa [hcarrier] using hp_piece⟩

private lemma selectedEdgeArcRelativeInteriorNotEndpoints
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (edgeArc : G.edgeFinset → PolygonalArc)
    (edgeArc_spec : ∀ e,
      EdgeArcAssemblySpec G D orderedPieces e (edgeArc e)) :
    ∀ ⦃e : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ (edgeArc e).relativeInterior →
        p ≠ D.edgeSource e ∧ p ≠ D.edgeTarget e := by
  intro e p hp
  have hp' := hp
  rw [(edgeArc_spec e).2.2.2.1] at hp'
  exact ⟨by
    intro h
    exact hp'.2 (by simp [h]), by
    intro h
    exact hp'.2 (by simp [h])⟩

private structure SelectedEdgeArcPrepared
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (orderedPieces : G.edgeFinset → List PolygonalArc) where
  edgeArc : G.edgeFinset → PolygonalArc
  spec : ∀ e, EdgeArcAssemblySpec G D orderedPieces e (edgeArc e)
  relativeInterior_localized :
    ∀ ⦃e : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ (edgeArc e).relativeInterior →
        (∃ (v : V) (hve : v ∈ e.1),
          p ∈ (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier) ∨
        (∃ i : tubeChains.pieceIndex,
          tubeChains.owner i = e ∧ p ∈ (tubeChains.chain i).carrier) ∨
        (∃ (x : {q // q ∈ D.intersectionPoints})
            (hxe : x.1 ∈ D.edgeRelativeInterior e),
          p ∈ (localDiskFillings.intersection_chain x ⟨e, hxe⟩).carrier)
  relativeInterior_not_endpoints :
    ∀ ⦃e : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ (edgeArc e).relativeInterior →
        p ≠ D.edgeSource e ∧ p ≠ D.edgeTarget e

private noncomputable def prepareSelectedEdgeArcs
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (orderedPieces : G.edgeFinset → List PolygonalArc)
    (assembled : ∀ e, ∃ Γ : PolygonalArc,
      EdgeArcAssemblySpec G D orderedPieces e Γ)
    (orderedPiece_is_local : ∀ e Γ, Γ ∈ orderedPieces e →
      (∃ (v : V) (hve : v ∈ e.1),
        Γ.carrier =
            (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier ∧
          Γ.relativeInterior =
            (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior) ∨
      (∃ i : tubeChains.pieceIndex,
        tubeChains.owner i = e ∧
          Γ.carrier = (tubeChains.chain i).carrier ∧
            Γ.relativeInterior = (tubeChains.chain i).relativeInterior) ∨
      (∃ (x : {p // p ∈ D.intersectionPoints})
          (hxe : x.1 ∈ D.edgeRelativeInterior e),
        Γ.carrier =
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩).carrier ∧
          Γ.relativeInterior =
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩).relativeInterior)) :
    SelectedEdgeArcPrepared G D controlDisks tubeChains localDiskFillings
      orderedPieces := by
  let edgeArc : G.edgeFinset → PolygonalArc :=
    chooseFamilyWitness assembled
  have edgeArc_spec : ∀ e,
      EdgeArcAssemblySpec G D orderedPieces e (edgeArc e) :=
    chooseFamilyWitness_spec assembled
  refine
    { edgeArc := edgeArc
      spec := edgeArc_spec
      relativeInterior_localized :=
        selectedEdgeArcRelativeInteriorLocalized G D controlDisks tubeChains
          localDiskFillings orderedPieces edgeArc edgeArc_spec
          orderedPiece_is_local
      relativeInterior_not_endpoints :=
        selectedEdgeArcRelativeInteriorNotEndpoints G D orderedPieces edgeArc
          edgeArc_spec }

private structure EdgeAssemblyCorePrepared
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) where
  sourceSpoke : G.edgeFinset → PolygonalArc
  targetSpoke : G.edgeFinset → PolygonalArc
  targetSpokeReverse : G.edgeFinset → PolygonalArc
  terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex
  gapConnector :
    (e : G.edgeFinset) →
      Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc
  gapCenter :
    (e : G.edgeFinset) →
      Fin ((tubeChains.edgePieceOrder e).length - 1) →
        {p // p ∈ D.intersectionPoints}
  tubeGapBlock :
    (e : G.edgeFinset) →
      Fin ((tubeChains.edgePieceOrder e).length - 1) → List PolygonalArc
  orderedPieces : G.edgeFinset → List PolygonalArc
  sourceSpoke_def : ∀ e, sourceSpoke e =
    localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
      ⟨e, tubeChains.edgeSourceVertex_mem e⟩
  targetSpoke_def : ∀ e, targetSpoke e =
    localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
      ⟨e, tubeChains.edgeTargetVertex_mem e⟩
  targetSpokeReverse_def : ∀ e,
    targetSpokeReverse e = PolygonalArcReverse (targetSpoke e)
  tubeGapBlock_def : ∀ e n,
    tubeGapBlock e n =
      [tubeChains.chain ((tubeChains.edgePieceOrder e)[n.1]),
        gapConnector e n]
  gapConnector_source : ∀ e n,
    (gapConnector e n).source =
      tubeChains.target ((tubeChains.edgePieceOrder e)[n.1])
  gapConnector_target : ∀ e n,
    (gapConnector e n).target =
      tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1])
  orderedPieces_def : ∀ e,
    orderedPieces e =
      orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e
  terminalTubeIndex_getLast : ∀ e,
    (tubeChains.edgePieceOrder e).getLast? = some (terminalTubeIndex e)
  terminalTubeIndex_mem : ∀ e,
    terminalTubeIndex e ∈ tubeChains.edgePieceOrder e
  gapCenter_spec : ∀ e n,
    (gapCenter e n).1 ∈ D.edgeRelativeInterior e ∧
      tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ∈
          Metric.sphere (gapCenter e n).1
            (controlDisks.intersectionRadius (gapCenter e n)) ∧
        tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ∈
            D.edgeCarrier e ∧
          tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) ∈
              Metric.sphere (gapCenter e n).1
                (controlDisks.intersectionRadius (gapCenter e n)) ∧
            tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) ∈
                D.edgeCarrier e ∧
              tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ≠
                tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1])
  gapConnector_def : ∀ e q,
    let connector :=
      localDiskFillings.intersection_chain (gapCenter e q)
        ⟨e, (gapCenter_spec e q).1⟩
    gapConnector e q =
      if connector.source =
          tubeChains.target ((tubeChains.edgePieceOrder e)[q.1]) then
        connector
      else PolygonalArcReverse connector
  orderedPieces_nonempty : ∀ e, (orderedPieces e).length ≠ 0
  orderedPieces_head_source : ∀ e Γ,
    (orderedPieces e).head? = some Γ → Γ.source = D.edgeSource e
  orderedPieces_last_target : ∀ e Γ,
    (orderedPieces e).getLast? = some Γ → Γ.target = D.edgeTarget e
  orderedPiece_is_local : ∀ e Γ, Γ ∈ orderedPieces e →
    (∃ (v : V) (hve : v ∈ e.1),
      Γ.carrier =
          (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier ∧
        Γ.relativeInterior =
          (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior) ∨
    (∃ i : tubeChains.pieceIndex,
      tubeChains.owner i = e ∧
        Γ.carrier = (tubeChains.chain i).carrier ∧
          Γ.relativeInterior = (tubeChains.chain i).relativeInterior) ∨
    (∃ (x : {p // p ∈ D.intersectionPoints})
        (hxe : x.1 ∈ D.edgeRelativeInterior e),
      Γ.carrier =
          (localDiskFillings.intersection_chain x ⟨e, hxe⟩).carrier ∧
        Γ.relativeInterior =
          (localDiskFillings.intersection_chain x ⟨e, hxe⟩).relativeInterior)
  vertex_spoke_in_orderedPieces :
    ∀ e v (hve : v ∈ e.1),
      ∃ Γ : PolygonalArc,
        Γ ∈ orderedPieces e ∧
          Γ.carrier =
              (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier ∧
            Γ.relativeInterior =
              (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior
  tube_chain_in_orderedPieces :
    ∀ i,
      ∃ Γ : PolygonalArc,
        Γ ∈ orderedPieces (tubeChains.owner i) ∧
          Γ.carrier = (tubeChains.chain i).carrier ∧
            Γ.relativeInterior = (tubeChains.chain i).relativeInterior
  intersection_chain_in_orderedPieces :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      ∃ Γ : PolygonalArc,
        Γ ∈ orderedPieces e.1 ∧
          Γ.carrier = (localDiskFillings.intersection_chain x e).carrier ∧
            Γ.relativeInterior =
              (localDiskFillings.intersection_chain x e).relativeInterior
  intersection_chain_or_reverse_in_orderedPieces :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      ∃ Γ : PolygonalArc,
        Γ ∈ orderedPieces e.1 ∧
          (Γ = localDiskFillings.intersection_chain x e ∨
            Γ = PolygonalArcReverse
              (localDiskFillings.intersection_chain x e))
  gapConnector_eq_or_reverse :
    ∀ e n,
      ∃ (x : {p // p ∈ D.intersectionPoints})
        (hxe : x.1 ∈ D.edgeRelativeInterior e),
        gapConnector e n =
            localDiskFillings.intersection_chain x ⟨e, hxe⟩ ∨
          gapConnector e n = PolygonalArcReverse
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩)

private structure EdgeAssemblyEarlyPrepared
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) where
  sourceSpoke : G.edgeFinset → PolygonalArc
  targetSpoke : G.edgeFinset → PolygonalArc
  targetSpokeReverse : G.edgeFinset → PolygonalArc
  orderedPieces : G.edgeFinset → List PolygonalArc
  terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex
  gapConnector :
    (e : G.edgeFinset) →
      Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc
  gapCenter :
    (e : G.edgeFinset) →
      Fin ((tubeChains.edgePieceOrder e).length - 1) →
        {p // p ∈ D.intersectionPoints}
  orderedPieces_def : ∀ e,
    orderedPieces e =
      orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
        targetSpokeReverse terminalTubeIndex gapConnector e
  assemblyFacts :
    OrderedPiecesAssemblyFacts G D controlDisks tubeChains localDiskFillings
      sourceSpoke targetSpoke targetSpokeReverse orderedPieces terminalTubeIndex
      gapConnector gapCenter
  selectedEdgeArcs :
    SelectedEdgeArcPrepared G D controlDisks tubeChains localDiskFillings
      orderedPieces
  terminalTubeIndex_mem : ∀ e,
    terminalTubeIndex e ∈ tubeChains.edgePieceOrder e
  vertex_spoke_in_orderedPieces :
    ∀ e v (hve : v ∈ e.1),
      ∃ Γ : PolygonalArc,
        Γ ∈ orderedPieces e ∧
          Γ.carrier =
              (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier ∧
            Γ.relativeInterior =
              (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior
  tube_chain_in_orderedPieces :
    ∀ i,
      ∃ Γ : PolygonalArc,
        Γ ∈ orderedPieces (tubeChains.owner i) ∧
          Γ.carrier = (tubeChains.chain i).carrier ∧
            Γ.relativeInterior = (tubeChains.chain i).relativeInterior
  intersection_chain_in_orderedPieces :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      ∃ Γ : PolygonalArc,
        Γ ∈ orderedPieces e.1 ∧
          Γ.carrier = (localDiskFillings.intersection_chain x e).carrier ∧
            Γ.relativeInterior =
              (localDiskFillings.intersection_chain x e).relativeInterior
  intersection_chain_or_reverse_in_orderedPieces :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      ∃ Γ : PolygonalArc,
        Γ ∈ orderedPieces e.1 ∧
          (Γ = localDiskFillings.intersection_chain x e ∨
            Γ = PolygonalArcReverse
              (localDiskFillings.intersection_chain x e))
  gapConnector_eq_or_reverse :
    ∀ e n,
      ∃ (x : {p // p ∈ D.intersectionPoints})
        (hxe : x.1 ∈ D.edgeRelativeInterior e),
        gapConnector e n =
            localDiskFillings.intersection_chain x ⟨e, hxe⟩ ∨
          gapConnector e n = PolygonalArcReverse
            (localDiskFillings.intersection_chain x ⟨e, hxe⟩)

private noncomputable def polygonalReplacementEdgeAssemblies_prepareCore
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) :
    EdgeAssemblyCorePrepared G D controlDisks tubeChains
      localDiskFillings := by
  classical
  let sourceSpoke : G.edgeFinset → PolygonalArc := fun e =>
    localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
      ⟨e, tubeChains.edgeSourceVertex_mem e⟩
  let targetSpoke : G.edgeFinset → PolygonalArc := fun e =>
    localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
      ⟨e, tubeChains.edgeTargetVertex_mem e⟩
  let targetSpokeReverse : G.edgeFinset → PolygonalArc := fun e =>
    PolygonalArcReverse (targetSpoke e)
  let terminalTubeIndex : G.edgeFinset → tubeChains.pieceIndex := fun e =>
    Classical.choose (show
        ∃ i : tubeChains.pieceIndex,
          (tubeChains.edgePieceOrder e).getLast? = some i from by
      rcases List.eq_nil_or_concat (tubeChains.edgePieceOrder e) with hnil |
          ⟨init, i, hconcat⟩
      · have hlen : (tubeChains.edgePieceOrder e).length = 0 := by
          simp [hnil]
        exact False.elim (tubeChains.edgePieceOrder_nonempty e hlen)
      · refine ⟨i, ?_⟩
        simpa [hconcat] using (List.getLast?_concat init i))
  have terminalTubeIndex_getLast :
      ∀ e, (tubeChains.edgePieceOrder e).getLast? =
        some (terminalTubeIndex e) := by
    intro e
    dsimp [terminalTubeIndex]
    exact Classical.choose_spec (show
        ∃ i : tubeChains.pieceIndex,
          (tubeChains.edgePieceOrder e).getLast? = some i from by
      rcases List.eq_nil_or_concat (tubeChains.edgePieceOrder e) with hnil |
          ⟨init, i, hconcat⟩
      · have hlen : (tubeChains.edgePieceOrder e).length = 0 := by
          simp [hnil]
        exact False.elim (tubeChains.edgePieceOrder_nonempty e hlen)
      · refine ⟨i, ?_⟩
        simpa [hconcat] using (List.getLast?_concat init i))
  have terminalTubeIndex_mem :
      ∀ e, terminalTubeIndex e ∈ tubeChains.edgePieceOrder e := by
    intro e
    rcases (List.getLast?_eq_some_iff.mp
      (terminalTubeIndex_getLast e)) with ⟨init, hinit⟩
    rw [hinit]
    simp
  let gapConnector :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → PolygonalArc :=
    fun e n =>
      have hn : n.1 + 1 < (tubeChains.edgePieceOrder e).length := by
        have hnlt : n.1 < (tubeChains.edgePieceOrder e).length - 1 := n.2
        omega
      let gapData := tubeChains.edgePieceOrder_consecutive_intersection e n.1 hn
      let x : {p // p ∈ D.intersectionPoints} := Classical.choose gapData
      have hx_edge : x.1 ∈ D.edgeRelativeInterior e :=
        (Classical.choose_spec gapData).1
      let connector := localDiskFillings.intersection_chain x ⟨e, hx_edge⟩
      if connector.source = tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) then
        connector
      else
        PolygonalArcReverse connector
  let gapCenter :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) →
          {p // p ∈ D.intersectionPoints} :=
    fun e n =>
      have hn : n.1 + 1 < (tubeChains.edgePieceOrder e).length := by
        have hnlt : n.1 < (tubeChains.edgePieceOrder e).length - 1 := n.2
        omega
      Classical.choose
        (tubeChains.edgePieceOrder_consecutive_intersection e n.1 hn)
  have gapCenter_spec :
      ∀ e n,
        (gapCenter e n).1 ∈ D.edgeRelativeInterior e ∧
          tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ∈
              Metric.sphere (gapCenter e n).1
                (controlDisks.intersectionRadius (gapCenter e n)) ∧
            tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ∈
                D.edgeCarrier e ∧
              tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) ∈
                  Metric.sphere (gapCenter e n).1
                    (controlDisks.intersectionRadius (gapCenter e n)) ∧
                tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) ∈
                    D.edgeCarrier e ∧
                  tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) ≠
                    tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) := by
    intro e n
    dsimp [gapCenter]
    exact Classical.choose_spec
      (tubeChains.edgePieceOrder_consecutive_intersection e n.1 (by
        have hnlt : n.1 < (tubeChains.edgePieceOrder e).length - 1 := n.2
        omega))
  let tubeGapBlock :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → List PolygonalArc :=
    fun e n =>
      have hn : n.1 + 1 < (tubeChains.edgePieceOrder e).length := by
        have hnlt : n.1 < (tubeChains.edgePieceOrder e).length - 1 := n.2
        omega
      [tubeChains.chain ((tubeChains.edgePieceOrder e)[n.1]), gapConnector e n]
  let orderedPieces : G.edgeFinset → List PolygonalArc := fun e =>
    ([sourceSpoke e] ++
        ((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
          (fun n => tubeGapBlock e n)).flatten ++
        [tubeChains.chain (terminalTubeIndex e)]) ++
      [targetSpokeReverse e]
  have sourceSpoke_source :
      ∀ e, (sourceSpoke e).source = D.edgeSource e := by
    intro e
    dsimp [sourceSpoke]
    rw [localDiskFillings.vertex_spoke_source]
    exact (tubeChains.edgeSource_eq_vertexPlacement e).symm
  have targetSpokeReverse_target :
      ∀ e, (targetSpokeReverse e).target = D.edgeTarget e := by
    intro e
    dsimp [targetSpokeReverse, targetSpoke, PolygonalArcReverse]
    rw [localDiskFillings.vertex_spoke_source]
    exact (tubeChains.edgeTarget_eq_vertexPlacement e).symm
  have orderedPieces_nonempty : ∀ e, (orderedPieces e).length ≠ 0 := by
    intro e
    simp [orderedPieces]
  have orderedPieces_head_source :
      ∀ e Γ, (orderedPieces e).head? = some Γ → Γ.source = D.edgeSource e := by
    intro e Γ hhead
    have hfirst : (orderedPieces e).head? = some (sourceSpoke e) := by
      simp [orderedPieces]
    rw [hfirst] at hhead
    have hΓ : sourceSpoke e = Γ := Option.some.inj hhead
    rw [← hΓ]
    exact sourceSpoke_source e
  have orderedPieces_last_target :
      ∀ e Γ, (orderedPieces e).getLast? = some Γ →
        Γ.target = D.edgeTarget e := by
    intro e Γ hlast
    have hlast' :
        (orderedPieces e).getLast? = some (targetSpokeReverse e) := by
      simpa [orderedPieces] using
        (List.getLast?_append_of_ne_nil
          ([sourceSpoke e] ++
            ((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
              (fun n => tubeGapBlock e n)).flatten ++
            [tubeChains.chain (terminalTubeIndex e)])
          (l₂ := [targetSpokeReverse e]) (by simp))
    rw [hlast'] at hlast
    have hΓ : targetSpokeReverse e = Γ := Option.some.inj hlast
    rw [← hΓ]
    exact targetSpokeReverse_target e
  have orderedPiece_is_local :
    ∀ e Γ, Γ ∈ orderedPieces e →
      (∃ (v : V) (hve : v ∈ e.1),
        Γ.carrier =
            (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier ∧
          Γ.relativeInterior =
            (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior) ∨
      (∃ i : tubeChains.pieceIndex,
        tubeChains.owner i = e ∧
          Γ.carrier = (tubeChains.chain i).carrier ∧
            Γ.relativeInterior = (tubeChains.chain i).relativeInterior) ∨
    (∃ (x : {p // p ∈ D.intersectionPoints})
        (hxe : x.1 ∈ D.edgeRelativeInterior e),
      Γ.carrier =
          (localDiskFillings.intersection_chain x ⟨e, hxe⟩).carrier ∧
        Γ.relativeInterior =
          (localDiskFillings.intersection_chain x ⟨e, hxe⟩).relativeInterior) := by
    intro e Γ hΓ
    simp only [orderedPieces, List.mem_append, List.mem_singleton,
      List.mem_flatten, List.mem_map] at hΓ
    rcases hΓ with ((hΓ | hΓ) | hΓ) | hΓ
    · subst Γ
      left
      exact ⟨tubeChains.edgeSourceVertex e,
        tubeChains.edgeSourceVertex_mem e, rfl, rfl⟩
    · rcases hΓ with ⟨l, ⟨n, _hnmem, hl⟩, hΓl⟩
      subst l
      simp only [tubeGapBlock, List.mem_cons, List.mem_singleton] at hΓl
      rcases hΓl with hΓchain | hΓgap
      · subst Γ
        right
        left
        have hnlt : n.1 < (tubeChains.edgePieceOrder e).length := by
          have hnsub : n.1 < (tubeChains.edgePieceOrder e).length - 1 := n.2
          omega
        exact ⟨(tubeChains.edgePieceOrder e)[n.1],
          (tubeChains.edgePieceOrder_owner_iff e _).1
            (List.getElem_mem hnlt), rfl, rfl⟩
      · rcases hΓgap with hΓgap | hΓnil
        · subst Γ
          right
          right
          have hn : n.1 + 1 < (tubeChains.edgePieceOrder e).length := by
            have hnsub : n.1 < (tubeChains.edgePieceOrder e).length - 1 := n.2
            omega
          let gapData :=
            tubeChains.edgePieceOrder_consecutive_intersection e n.1 hn
          let x : {p // p ∈ D.intersectionPoints} :=
            Classical.choose gapData
          have hx_edge : x.1 ∈ D.edgeRelativeInterior e :=
            (Classical.choose_spec gapData).1
          refine ⟨x, hx_edge, ?_, ?_⟩
          · dsimp [gapConnector]
            by_cases hsrc :
                (localDiskFillings.intersection_chain x ⟨e, hx_edge⟩).source =
                  tubeChains.target ((tubeChains.edgePieceOrder e)[n.1])
            · simp [gapData, x, hx_edge, hsrc]
            · simp [gapData, x, hx_edge, hsrc, PolygonalArcReverse]
          · dsimp [gapConnector]
            by_cases hsrc :
                (localDiskFillings.intersection_chain x ⟨e, hx_edge⟩).source =
                  tubeChains.target ((tubeChains.edgePieceOrder e)[n.1])
            · simp [gapData, x, hx_edge, hsrc]
            · simp [gapData, x, hx_edge, hsrc, PolygonalArcReverse]
        · cases hΓnil
    · subst Γ
      right
      left
      exact ⟨terminalTubeIndex e,
        (tubeChains.edgePieceOrder_owner_iff e _).1
          (terminalTubeIndex_mem e), rfl, rfl⟩
    · subst Γ
      left
      refine ⟨tubeChains.edgeTargetVertex e,
        tubeChains.edgeTargetVertex_mem e, ?_, ?_⟩
      · simp [targetSpokeReverse, targetSpoke, PolygonalArcReverse]
      · simp [targetSpokeReverse, targetSpoke, PolygonalArcReverse]
  have edge_mem_source_or_target :
      ∀ e v, v ∈ e.1 →
        v = tubeChains.edgeSourceVertex e ∨
          v = tubeChains.edgeTargetVertex e := by
    exact edgeMemSourceOrTarget G D controlDisks tubeChains
  have edgeSource_ne_target :
      ∀ e, D.edgeSource e ≠ D.edgeTarget e := by
    exact edgeSourceNeTarget G D
  have edgeSourceVertex_ne_targetVertex :
      ∀ e, tubeChains.edgeSourceVertex e ≠ tubeChains.edgeTargetVertex e := by
    exact edgeSourceVertexNeTargetVertex G D controlDisks tubeChains
  have edgeSource_mem_source_ball :
      ∀ e,
        D.edgeSource e ∈
          Metric.ball (D.vertexPlacement (tubeChains.edgeSourceVertex e))
            (controlDisks.vertexRadius (tubeChains.edgeSourceVertex e)) := by
    exact edgeSourceMemSourceBall G D controlDisks tubeChains
  have edgeTarget_mem_target_ball :
      ∀ e,
        D.edgeTarget e ∈
          Metric.ball (D.vertexPlacement (tubeChains.edgeTargetVertex e))
            (controlDisks.vertexRadius (tubeChains.edgeTargetVertex e)) := by
    exact edgeTargetMemTargetBall G D controlDisks tubeChains
  have vertex_spoke_boundary_point_eq_target :
      ∀ v (e : {e : G.edgeFinset // v ∈ e.1})
        (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ (localDiskFillings.vertex_spoke v e).carrier →
          p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
            p = (localDiskFillings.vertex_spoke v e).target := by
    exact vertexSpokeBoundaryPointEqTarget G D controlDisks tubeChains
      localDiskFillings
  have intersection_chain_boundary_point_eq_endpoint :
      ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e})
        (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ (localDiskFillings.intersection_chain x e).carrier →
          p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
            p = (localDiskFillings.intersection_chain x e).source ∨
              p = (localDiskFillings.intersection_chain x e).target := by
    exact intersectionChainBoundaryPointEqEndpoint G D controlDisks tubeChains
      localDiskFillings
  have vertex_spoke_carrier_disjoint_vertex_spoke_of_ne :
      ∀ ⦃v w : V⦄
        (e : {e : G.edgeFinset // v ∈ e.1})
        (f : {e : G.edgeFinset // w ∈ e.1}),
        v ≠ w →
          Disjoint (localDiskFillings.vertex_spoke v e).carrier
            (localDiskFillings.vertex_spoke w f).carrier := by
    exact vertexSpokeCarrierDisjointVertexSpokeOfNe G D controlDisks tubeChains
      localDiskFillings
  have vertex_spoke_carrier_disjoint_intersection_chain :
      ∀ (v : V) (e : {e : G.edgeFinset // v ∈ e.1})
        (x : {p // p ∈ D.intersectionPoints})
        (f : {f : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior f}),
        Disjoint (localDiskFillings.vertex_spoke v e).carrier
          (localDiskFillings.intersection_chain x f).carrier := by
    exact vertexSpokeCarrierDisjointIntersectionChain G D controlDisks tubeChains
      localDiskFillings
  have intersection_chain_carrier_disjoint_intersection_chain_of_ne :
      ∀ ⦃x y : {p // p ∈ D.intersectionPoints}⦄
        (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e})
        (f : {f : G.edgeFinset // y.1 ∈ D.edgeRelativeInterior f}),
        x ≠ y →
          Disjoint (localDiskFillings.intersection_chain x e).carrier
            (localDiskFillings.intersection_chain y f).carrier := by
    exact intersectionChainCarrierDisjointIntersectionChainOfNe G D controlDisks
      tubeChains localDiskFillings
  have vertex_spoke_in_orderedPieces :
      ∀ e v (hve : v ∈ e.1),
        ∃ Γ : PolygonalArc,
          Γ ∈ orderedPieces e ∧
            Γ.carrier =
                (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier ∧
              Γ.relativeInterior =
                (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior := by
    intro e v hve
    rcases edge_mem_source_or_target e v hve with hvsource | hvtarget
    · subst v
      refine ⟨sourceSpoke e, ?_, ?_, ?_⟩
      · simp [orderedPieces]
      · simp [sourceSpoke]
      · simp [sourceSpoke]
    · subst v
      refine ⟨targetSpokeReverse e, ?_, ?_, ?_⟩
      · simp [orderedPieces]
      · simp [targetSpokeReverse, targetSpoke, PolygonalArcReverse]
      · simp [targetSpokeReverse, targetSpoke, PolygonalArcReverse]
  have tube_chain_in_orderedPieces :
      ∀ i,
        ∃ Γ : PolygonalArc,
          Γ ∈ orderedPieces (tubeChains.owner i) ∧
            Γ.carrier = (tubeChains.chain i).carrier ∧
              Γ.relativeInterior = (tubeChains.chain i).relativeInterior := by
    intro i
    let e := tubeChains.owner i
    have hi_mem : i ∈ tubeChains.edgePieceOrder e :=
      (tubeChains.edgePieceOrder_owner_iff e i).2 rfl
    rcases List.getElem_of_mem hi_mem with ⟨k, hk, hki⟩
    refine ⟨tubeChains.chain i, ?_, rfl, rfl⟩
    by_cases hlast : k + 1 = (tubeChains.edgePieceOrder e).length
    · have hidx : (tubeChains.edgePieceOrder e).length - 1 = k := by
        omega
      have hlast_i : (tubeChains.edgePieceOrder e).getLast? = some i := by
        rw [List.getLast?_eq_getElem?]
        have hkopt :
            (tubeChains.edgePieceOrder e)[k]? = some i := by
          rw [List.getElem?_eq_getElem hk, hki]
        simpa [hidx] using hkopt
      have hterm : terminalTubeIndex e = i := by
        have hterminal := terminalTubeIndex_getLast e
        rw [hlast_i] at hterminal
        exact Option.some.inj hterminal.symm
      have hmem_terminal :
          tubeChains.chain (terminalTubeIndex e) ∈ orderedPieces e := by
        simp [orderedPieces]
      simpa [e, hterm] using hmem_terminal
    · have hk_nonterminal :
          k < (tubeChains.edgePieceOrder e).length - 1 := by
        omega
      let n : Fin ((tubeChains.edgePieceOrder e).length - 1) :=
        ⟨k, hk_nonterminal⟩
      have hmem_gap :
          tubeChains.chain ((tubeChains.edgePieceOrder e)[n.1]) ∈
            orderedPieces e := by
        simp only [orderedPieces, tubeGapBlock, List.mem_append,
          List.mem_flatten, List.mem_map, List.mem_cons, List.not_mem_nil]
        left
        left
        right
        refine ⟨[tubeChains.chain ((tubeChains.edgePieceOrder e)[n.1]),
          gapConnector e n], ?_, ?_⟩
        · exact ⟨n, List.mem_finRange n, rfl⟩
        · simp
      simpa [e, n, hki] using hmem_gap
  have intersection_chain_in_orderedPieces :
      ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        ∃ Γ : PolygonalArc,
          Γ ∈ orderedPieces e.1 ∧
            Γ.carrier = (localDiskFillings.intersection_chain x e).carrier ∧
              Γ.relativeInterior =
                (localDiskFillings.intersection_chain x e).relativeInterior := by
    intro x e
    rcases e with ⟨e0, hxe⟩
    rcases tubeChains.edgePieceOrder_intersection_between x e0 hxe with
      ⟨n, hn, htarget_sphere, _htarget_edge, _hsource_sphere,
        _hsource_edge, _hne⟩
    let nFin : Fin ((tubeChains.edgePieceOrder e0).length - 1) :=
      ⟨n, by omega⟩
    have hnGap : nFin.1 + 1 < (tubeChains.edgePieceOrder e0).length := by
      have hnlt : nFin.1 < (tubeChains.edgePieceOrder e0).length - 1 :=
        nFin.2
      omega
    let gapData :=
      tubeChains.edgePieceOrder_consecutive_intersection e0 nFin.1 hnGap
    let xgap : {p // p ∈ D.intersectionPoints} := Classical.choose gapData
    have hxgap_spec := Classical.choose_spec gapData
    have hxgap_edge : xgap.1 ∈ D.edgeRelativeInterior e0 :=
      hxgap_spec.1
    have htarget_sphere_gap :
        tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) ∈
          Metric.sphere xgap.1 (controlDisks.intersectionRadius xgap) :=
      hxgap_spec.2.1
    have htarget_sphere_x :
        tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) ∈
          Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
      simpa [nFin] using htarget_sphere
    have hxgap_eq : xgap = x := by
      by_contra hxne
      have hclosed_gap :
          tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) ∈
            Metric.closedBall xgap.1 (controlDisks.intersectionRadius xgap) :=
        Metric.sphere_subset_closedBall htarget_sphere_gap
      have hclosed_x :
          tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) ∈
            Metric.closedBall x.1 (controlDisks.intersectionRadius x) :=
        Metric.sphere_subset_closedBall htarget_sphere_x
      exact
        (Set.disjoint_left.mp
          (controlDisks.intersection_intersection_disjoint hxne)
          hclosed_gap) hclosed_x
    have hchain_eq :
        localDiskFillings.intersection_chain xgap ⟨e0, hxgap_edge⟩ =
          localDiskFillings.intersection_chain x ⟨e0, hxe⟩ := by
      subst x
      congr
    have hmem_gap : gapConnector e0 nFin ∈ orderedPieces e0 := by
      simp only [orderedPieces, tubeGapBlock, List.mem_append,
        List.mem_flatten, List.mem_map, List.mem_cons, List.not_mem_nil]
      left
      left
      right
      refine ⟨[tubeChains.chain ((tubeChains.edgePieceOrder e0)[nFin.1]),
        gapConnector e0 nFin], ?_, ?_⟩
      · exact ⟨nFin, List.mem_finRange nFin, rfl⟩
      · simp
    refine ⟨gapConnector e0 nFin, hmem_gap, ?_, ?_⟩
    · dsimp [gapConnector]
      by_cases hsrc :
          (localDiskFillings.intersection_chain xgap ⟨e0, hxgap_edge⟩).source =
            tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1])
      · have hsrc_x :
            (localDiskFillings.intersection_chain x ⟨e0, hxe⟩).source =
              tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) := by
          simpa [hchain_eq] using hsrc
        simp [gapData, xgap, hxgap_edge, hsrc, hsrc_x, hchain_eq]
      · have hsrc_x :
            (localDiskFillings.intersection_chain x ⟨e0, hxe⟩).source ≠
              tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) := by
          intro h
          exact hsrc (by simpa [hchain_eq] using h)
        simp [gapData, xgap, hxgap_edge, hsrc, hsrc_x, hchain_eq,
          PolygonalArcReverse]
    · dsimp [gapConnector]
      by_cases hsrc :
          (localDiskFillings.intersection_chain xgap ⟨e0, hxgap_edge⟩).source =
            tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1])
      · have hsrc_x :
            (localDiskFillings.intersection_chain x ⟨e0, hxe⟩).source =
              tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) := by
          simpa [hchain_eq] using hsrc
        simp [gapData, xgap, hxgap_edge, hsrc, hsrc_x, hchain_eq]
      · have hsrc_x :
            (localDiskFillings.intersection_chain x ⟨e0, hxe⟩).source ≠
              tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) := by
          intro h
          exact hsrc (by simpa [hchain_eq] using h)
        simp [gapData, xgap, hxgap_edge, hsrc, hsrc_x, hchain_eq,
          PolygonalArcReverse]
  have intersection_chain_or_reverse_in_orderedPieces :
      ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        ∃ Γ : PolygonalArc,
          Γ ∈ orderedPieces e.1 ∧
            (Γ = localDiskFillings.intersection_chain x e ∨
              Γ = PolygonalArcReverse
                (localDiskFillings.intersection_chain x e)) := by
    intro x e
    rcases e with ⟨e0, hxe⟩
    rcases tubeChains.edgePieceOrder_intersection_between x e0 hxe with
      ⟨n, hn, htarget_sphere, _htarget_edge, _hsource_sphere,
        _hsource_edge, _hne⟩
    let nFin : Fin ((tubeChains.edgePieceOrder e0).length - 1) :=
      ⟨n, by omega⟩
    have hnGap : nFin.1 + 1 < (tubeChains.edgePieceOrder e0).length := by
      have hnlt : nFin.1 < (tubeChains.edgePieceOrder e0).length - 1 :=
        nFin.2
      omega
    let gapData :=
      tubeChains.edgePieceOrder_consecutive_intersection e0 nFin.1 hnGap
    let xgap : {p // p ∈ D.intersectionPoints} := Classical.choose gapData
    have hxgap_spec := Classical.choose_spec gapData
    have hxgap_edge : xgap.1 ∈ D.edgeRelativeInterior e0 :=
      hxgap_spec.1
    have htarget_sphere_gap :
        tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) ∈
          Metric.sphere xgap.1 (controlDisks.intersectionRadius xgap) :=
      hxgap_spec.2.1
    have htarget_sphere_x :
        tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) ∈
          Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
      simpa [nFin] using htarget_sphere
    have hxgap_eq : xgap = x := by
      by_contra hxne
      have hclosed_gap :
          tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) ∈
            Metric.closedBall xgap.1 (controlDisks.intersectionRadius xgap) :=
        Metric.sphere_subset_closedBall htarget_sphere_gap
      have hclosed_x :
          tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) ∈
            Metric.closedBall x.1 (controlDisks.intersectionRadius x) :=
        Metric.sphere_subset_closedBall htarget_sphere_x
      exact
        (Set.disjoint_left.mp
          (controlDisks.intersection_intersection_disjoint hxne)
          hclosed_gap) hclosed_x
    have hchain_eq :
        localDiskFillings.intersection_chain xgap ⟨e0, hxgap_edge⟩ =
          localDiskFillings.intersection_chain x ⟨e0, hxe⟩ := by
      subst x
      congr
    have hmem_gap : gapConnector e0 nFin ∈ orderedPieces e0 := by
      simp only [orderedPieces, tubeGapBlock, List.mem_append,
        List.mem_flatten, List.mem_map, List.mem_cons, List.not_mem_nil]
      left
      left
      right
      refine ⟨[tubeChains.chain ((tubeChains.edgePieceOrder e0)[nFin.1]),
        gapConnector e0 nFin], ?_, ?_⟩
      · exact ⟨nFin, List.mem_finRange nFin, rfl⟩
      · simp
    refine ⟨gapConnector e0 nFin, hmem_gap, ?_⟩
    dsimp [gapConnector]
    by_cases hsrc :
        (localDiskFillings.intersection_chain xgap ⟨e0, hxgap_edge⟩).source =
          tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1])
    · left
      have hsrc_x :
          (localDiskFillings.intersection_chain x ⟨e0, hxe⟩).source =
            tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) := by
        simpa [hchain_eq] using hsrc
      simp [gapData, xgap, hxgap_edge, hsrc, hsrc_x, hchain_eq]
    · right
      have hsrc_x :
          (localDiskFillings.intersection_chain x ⟨e0, hxe⟩).source ≠
            tubeChains.target ((tubeChains.edgePieceOrder e0)[nFin.1]) := by
        intro h
        exact hsrc (by simpa [hchain_eq] using h)
      simp [gapData, xgap, hxgap_edge, hsrc, hsrc_x, hchain_eq,
        PolygonalArcReverse]
  have gapConnector_eq_or_reverse :
      ∀ e n,
        ∃ (x : {p // p ∈ D.intersectionPoints})
          (hxe : x.1 ∈ D.edgeRelativeInterior e),
          gapConnector e n =
              localDiskFillings.intersection_chain x ⟨e, hxe⟩ ∨
            gapConnector e n =
              PolygonalArcReverse
                (localDiskFillings.intersection_chain x ⟨e, hxe⟩) := by
    intro e n
    have hn : n.1 + 1 < (tubeChains.edgePieceOrder e).length := by
      have hnlt : n.1 < (tubeChains.edgePieceOrder e).length - 1 := n.2
      omega
    let gapData := tubeChains.edgePieceOrder_consecutive_intersection e n.1 hn
    let x : {p // p ∈ D.intersectionPoints} := Classical.choose gapData
    have hx_edge : x.1 ∈ D.edgeRelativeInterior e :=
      (Classical.choose_spec gapData).1
    refine ⟨x, hx_edge, ?_⟩
    dsimp [gapConnector]
    by_cases hsrc :
        (localDiskFillings.intersection_chain x ⟨e, hx_edge⟩).source =
          tubeChains.target ((tubeChains.edgePieceOrder e)[n.1])
    · left
      simp [gapData, x, hx_edge, hsrc]
    · right
      simp [gapData, x, hx_edge, hsrc, PolygonalArcReverse]
  have gapConnector_source_core :
      ∀ e n,
        (gapConnector e n).source =
          tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) := by
    intro e n
    have hn : n.1 + 1 < (tubeChains.edgePieceOrder e).length := by
      have hnlt : n.1 < (tubeChains.edgePieceOrder e).length - 1 := n.2
      omega
    let gapData := tubeChains.edgePieceOrder_consecutive_intersection e n.1 hn
    let x : {p // p ∈ D.intersectionPoints} := Classical.choose gapData
    rcases Classical.choose_spec gapData with
      ⟨hx_edge, htarget_sphere, htarget_edge, _hsource_sphere,
        _hsource_edge, _hne⟩
    let connector := localDiskFillings.intersection_chain x ⟨e, hx_edge⟩
    let boundaryTarget : EuclideanSpace ℝ (Fin 2) :=
      tubeChains.target ((tubeChains.edgePieceOrder e)[n.1])
    have hcovered :=
      localDiskFillings.intersection_boundary_covered hx_edge htarget_sphere
        htarget_edge
    dsimp [gapConnector]
    by_cases hsrc : connector.source = boundaryTarget
    · simp [gapData, x, connector, boundaryTarget, hx_edge, hsrc]
    · rcases hcovered with hcovered | hcovered
      · exact False.elim (hsrc hcovered)
      · simp [gapData, x, connector, boundaryTarget, hx_edge, hsrc, hcovered,
          PolygonalArcReverse]
  have gapConnector_target_core :
      ∀ e n,
        (gapConnector e n).target =
          tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) := by
    intro e n
    have hn : n.1 + 1 < (tubeChains.edgePieceOrder e).length := by
      have hnlt : n.1 < (tubeChains.edgePieceOrder e).length - 1 := n.2
      omega
    let gapData := tubeChains.edgePieceOrder_consecutive_intersection e n.1 hn
    let x : {p // p ∈ D.intersectionPoints} := Classical.choose gapData
    rcases Classical.choose_spec gapData with
      ⟨hx_edge, htarget_sphere, htarget_edge, hsource_sphere,
        hsource_edge, hne⟩
    let connector := localDiskFillings.intersection_chain x ⟨e, hx_edge⟩
    have hcovered_target :=
      localDiskFillings.intersection_boundary_covered hx_edge htarget_sphere
        htarget_edge
    have hcovered_source :=
      localDiskFillings.intersection_boundary_covered hx_edge hsource_sphere
        hsource_edge
    dsimp [gapConnector]
    by_cases hsrc :
        connector.source =
          tubeChains.target ((tubeChains.edgePieceOrder e)[n.1])
    · have htarget :
          connector.target =
            tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) := by
        rcases hcovered_source with hsource | htarget
        · exact False.elim (hne (by rw [← hsrc, hsource]))
        · exact htarget
      rw [if_pos]
      · exact htarget
      · exact hsrc
    · have htarget_current :
          connector.target =
            tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) := by
        rcases hcovered_target with hsource | htarget
        · exact False.elim (hsrc hsource)
        · exact htarget
      have hsource :
          connector.source =
            tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) := by
        rcases hcovered_source with hsource | htarget
        · exact hsource
        · exact False.elim (hne (by rw [← htarget_current, htarget]))
      rw [if_neg]
      · exact hsource
      · exact hsrc
  exact
    { sourceSpoke := sourceSpoke
      targetSpoke := targetSpoke
      targetSpokeReverse := targetSpokeReverse
      terminalTubeIndex := terminalTubeIndex
      gapConnector := gapConnector
      gapCenter := gapCenter
      tubeGapBlock := tubeGapBlock
      orderedPieces := orderedPieces
      sourceSpoke_def := by intro e; rfl
      targetSpoke_def := by intro e; rfl
      targetSpokeReverse_def := by intro e; rfl
      tubeGapBlock_def := by intro e n; rfl
      gapConnector_source := gapConnector_source_core
      gapConnector_target := gapConnector_target_core
      orderedPieces_def := by intro e; rfl
      terminalTubeIndex_getLast := terminalTubeIndex_getLast
      terminalTubeIndex_mem := terminalTubeIndex_mem
      gapCenter_spec := gapCenter_spec
      gapConnector_def := by
        intro e q
        dsimp [gapConnector, gapCenter]
      orderedPieces_nonempty := orderedPieces_nonempty
      orderedPieces_head_source := orderedPieces_head_source
      orderedPieces_last_target := orderedPieces_last_target
      orderedPiece_is_local := orderedPiece_is_local
      vertex_spoke_in_orderedPieces := vertex_spoke_in_orderedPieces
      tube_chain_in_orderedPieces := tube_chain_in_orderedPieces
      intersection_chain_in_orderedPieces :=
        intersection_chain_in_orderedPieces
      intersection_chain_or_reverse_in_orderedPieces :=
        intersection_chain_or_reverse_in_orderedPieces
      gapConnector_eq_or_reverse := gapConnector_eq_or_reverse }

private noncomputable def polygonalReplacementEdgeAssemblies_prepareEarly
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (core :
      EdgeAssemblyCorePrepared G D controlDisks tubeChains
        localDiskFillings) :
    EdgeAssemblyEarlyPrepared G D controlDisks tubeChains
      localDiskFillings := by
  classical
  let sourceSpoke : G.edgeFinset → PolygonalArc := fun e =>
    localDiskFillings.vertex_spoke (tubeChains.edgeSourceVertex e)
      ⟨e, tubeChains.edgeSourceVertex_mem e⟩
  let targetSpoke : G.edgeFinset → PolygonalArc := fun e =>
    localDiskFillings.vertex_spoke (tubeChains.edgeTargetVertex e)
      ⟨e, tubeChains.edgeTargetVertex_mem e⟩
  let targetSpokeReverse : G.edgeFinset → PolygonalArc := fun e =>
    PolygonalArcReverse (targetSpoke e)
  have sourceSpoke_eq : core.sourceSpoke = sourceSpoke := by
    funext e
    exact core.sourceSpoke_def e
  have targetSpoke_eq : core.targetSpoke = targetSpoke := by
    funext e
    exact core.targetSpoke_def e
  have targetSpokeReverse_eq :
      core.targetSpokeReverse = targetSpokeReverse := by
    funext e
    rw [core.targetSpokeReverse_def e, targetSpoke_eq]
  let terminalTubeIndex := core.terminalTubeIndex
  let gapConnector := core.gapConnector
  let gapCenter := core.gapCenter
  let tubeGapBlock :
      (e : G.edgeFinset) →
        Fin ((tubeChains.edgePieceOrder e).length - 1) → List PolygonalArc :=
    fun e q =>
      tubeGapBlockForAttach G D controlDisks tubeChains gapConnector e q
  let orderedPieces := core.orderedPieces
  have orderedPieces_def : ∀ e,
      orderedPieces e =
        orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
          targetSpokeReverse terminalTubeIndex gapConnector e := by
    intro e
    rw [← sourceSpoke_eq, ← targetSpokeReverse_eq]
    exact core.orderedPieces_def e
  have terminalTubeIndex_getLast := core.terminalTubeIndex_getLast
  have terminalTubeIndex_mem := core.terminalTubeIndex_mem
  have gapCenter_spec := core.gapCenter_spec
  have orderedPieces_nonempty := core.orderedPieces_nonempty
  have orderedPieces_head_source := core.orderedPieces_head_source
  have orderedPieces_last_target := core.orderedPieces_last_target
  have orderedPiece_is_local := core.orderedPiece_is_local
  have edge_mem_source_or_target :=
    edgeMemSourceOrTarget G D controlDisks tubeChains
  have edgeSourceVertex_ne_targetVertex :=
    edgeSourceVertexNeTargetVertex G D controlDisks tubeChains
  have edgeSource_mem_source_ball :=
    edgeSourceMemSourceBall G D controlDisks tubeChains
  have edgeTarget_mem_target_ball :=
    edgeTargetMemTargetBall G D controlDisks tubeChains
  have vertex_spoke_boundary_point_eq_target :=
    vertexSpokeBoundaryPointEqTarget G D controlDisks tubeChains
      localDiskFillings
  have vertex_spoke_in_orderedPieces := core.vertex_spoke_in_orderedPieces
  have tube_chain_in_orderedPieces := core.tube_chain_in_orderedPieces
  have intersection_chain_in_orderedPieces :=
    core.intersection_chain_in_orderedPieces
  have intersection_chain_or_reverse_in_orderedPieces :=
    core.intersection_chain_or_reverse_in_orderedPieces
  have gapConnector_eq_or_reverse := core.gapConnector_eq_or_reverse
  have sourceSpoke_attaches_first_tube :
      ∀ e i, (tubeChains.edgePieceOrder e).head? = some i →
        (sourceSpoke e).target = (tubeChains.chain i).source := by
    intro e i hhead
    have hboundary :=
      tubeChains.edgePieceOrder_first_source_boundary e i hhead
    have hspoke :
        (sourceSpoke e).target = tubeChains.source i := by
      dsimp [sourceSpoke]
      exact localDiskFillings.vertex_boundary_covered
        (tubeChains.edgeSourceVertex_mem e) hboundary.1 hboundary.2
    calc
      (sourceSpoke e).target = tubeChains.source i := hspoke
      _ = (tubeChains.chain i).source := (tubeChains.chain_endpoints i).1.symm
  have gapConnector_source :
      ∀ e n,
        (gapConnector e n).source =
          tubeChains.target ((tubeChains.edgePieceOrder e)[n.1]) := by
    exact core.gapConnector_source
  have gapConnector_target :
      ∀ e n,
        (gapConnector e n).target =
          tubeChains.source ((tubeChains.edgePieceOrder e)[n.1 + 1]) := by
    exact core.gapConnector_target
  have terminalTube_attaches_targetSpoke :
      ∀ e,
        (tubeChains.chain (terminalTubeIndex e)).target =
          (targetSpokeReverse e).source := by
    intro e
    have hboundary :=
      tubeChains.edgePieceOrder_last_target_boundary e (terminalTubeIndex e)
        (terminalTubeIndex_getLast e)
    have hspoke :
        (targetSpoke e).target = tubeChains.target (terminalTubeIndex e) := by
      dsimp [targetSpoke]
      exact localDiskFillings.vertex_boundary_covered
        (tubeChains.edgeTargetVertex_mem e) hboundary.1 hboundary.2
    calc
      (tubeChains.chain (terminalTubeIndex e)).target =
          tubeChains.target (terminalTubeIndex e) :=
        (tubeChains.chain_endpoints (terminalTubeIndex e)).2
      _ = (targetSpokeReverse e).source := by
        dsimp [targetSpokeReverse, PolygonalArcReverse]
        exact hspoke.symm
  have sourceSpoke_carrier_disjoint_tube_chain_of_not_head :
      ∀ e i,
        i ∈ tubeChains.edgePieceOrder e →
          (tubeChains.edgePieceOrder e).head? ≠ some i →
            Disjoint (sourceSpoke e).carrier (tubeChains.chain i).carrier := by
    simpa only [sourceSpoke] using
      (sourceSpokeCarrierDisjointTubeChainOfNotHead G D controlDisks tubeChains
        localDiskFillings sourceSpoke_attaches_first_tube
        vertex_spoke_boundary_point_eq_target)
  have targetSpokeReverse_carrier_disjoint_tube_chain_of_not_last :
      ∀ e i,
        i ∈ tubeChains.edgePieceOrder e →
          (tubeChains.edgePieceOrder e).getLast? ≠ some i →
            Disjoint (targetSpokeReverse e).carrier (tubeChains.chain i).carrier := by
    simpa only [targetSpokeReverse, targetSpoke] using
      (targetSpokeReverseCarrierDisjointTubeChainOfNotLast G D controlDisks
        tubeChains localDiskFillings terminalTubeIndex terminalTubeIndex_getLast
        terminalTubeIndex_mem terminalTube_attaches_targetSpoke
        vertex_spoke_boundary_point_eq_target)
  have tube_chain_carrier_disjoint_gapConnector_of_not_boundary :
      ∀ e (q : Fin ((tubeChains.edgePieceOrder e).length - 1)) i,
        i ∈ tubeChains.edgePieceOrder e →
          i ≠ (tubeChains.edgePieceOrder e)[q.1] →
            i ≠ (tubeChains.edgePieceOrder e)[q.1 + 1] →
              Disjoint (tubeChains.chain i).carrier
                (gapConnector e q).carrier :=
    tubeChainCarrierDisjointGapConnectorOfNotBoundary G D controlDisks
      tubeChains localDiskFillings gapConnector gapConnector_eq_or_reverse
      gapConnector_source gapConnector_target
  have gapCenter_injective :
      ∀ e (q r : Fin ((tubeChains.edgePieceOrder e).length - 1)),
        gapCenter e q = gapCenter e r → q = r :=
    gapCenterInjective G D controlDisks tubeChains gapCenter gapCenter_spec
  have gapConnector_eq_or_reverse_gapCenter :
      ∀ e (q : Fin ((tubeChains.edgePieceOrder e).length - 1)),
        gapConnector e q =
            localDiskFillings.intersection_chain (gapCenter e q)
              ⟨e, (gapCenter_spec e q).1⟩ ∨
          gapConnector e q =
            PolygonalArcReverse
              (localDiskFillings.intersection_chain (gapCenter e q)
                ⟨e, (gapCenter_spec e q).1⟩) := by
    exact gapConnectorEqOrReverseGapCenter G D controlDisks tubeChains
      localDiskFillings gapConnector gapCenter
      (fun e q => (gapCenter_spec e q).1) core.gapConnector_def
  have gapConnector_carrier_disjoint_gapConnector_of_ne :
      ∀ e (q r : Fin ((tubeChains.edgePieceOrder e).length - 1)),
        q ≠ r →
          Disjoint (gapConnector e q).carrier (gapConnector e r).carrier := by
    exact gapConnectorCarrierDisjointGapConnectorOfNe G D controlDisks
      tubeChains localDiskFillings gapConnector gapCenter
      (fun e q => (gapCenter_spec e q).1) gapCenter_injective
      gapConnector_eq_or_reverse_gapCenter
  have orderedPieces_successive_attach_local :
      ∀ e n (hn : n + 1 < (orderedPieces e).length),
        ((orderedPieces e)[n]).target = ((orderedPieces e)[n + 1]).source := by
    intro e n hn
    have hn' : n + 1 <
        (orderedPiecesForAttach G D controlDisks tubeChains sourceSpoke
          targetSpokeReverse terminalTubeIndex gapConnector e).length := by
      simpa only [orderedPieces_def e] using hn
    have hraw := orderedPiecesSuccessiveAttachLocal G D controlDisks tubeChains
      sourceSpoke targetSpokeReverse terminalTubeIndex gapConnector
      terminalTubeIndex_getLast sourceSpoke_attaches_first_tube
      gapConnector_source gapConnector_target terminalTube_attaches_targetSpoke
      e n hn'
    simpa only [orderedPieces_def e] using hraw
  have finBlock_length :
      ∀ (K : ℕ) (chain : Fin (K + 1) → PolygonalArc)
        (gap : Fin K → PolygonalArc),
        ((((List.finRange K).map
            (fun q => [chain q.castSucc, gap q])).flatten ++
          [chain (Fin.last K)]).length = 2 * K + 1) :=
    finiteAlternatingBlockLength
  have finBlock_get?_chain :
      ∀ (K : ℕ) (chain : Fin (K + 1) → PolygonalArc)
        (gap : Fin K → PolygonalArc) (q : Fin K),
        ((((List.finRange K).map
            (fun q => [chain q.castSucc, gap q])).flatten ++
          [chain (Fin.last K)])[2 * q.1]? =
          some (chain q.castSucc)) :=
    finiteAlternatingBlockGetChain
  have finBlock_get?_gap :
      ∀ (K : ℕ) (chain : Fin (K + 1) → PolygonalArc)
        (gap : Fin K → PolygonalArc) (q : Fin K),
        ((((List.finRange K).map
            (fun q => [chain q.castSucc, gap q])).flatten ++
          [chain (Fin.last K)])[2 * q.1 + 1]? =
          some (gap q)) :=
    finiteAlternatingBlockGetGap
  have finBlock_get?_last :
      ∀ (K : ℕ) (chain : Fin (K + 1) → PolygonalArc)
        (gap : Fin K → PolygonalArc),
        ((((List.finRange K).map
            (fun q => [chain q.castSucc, gap q])).flatten ++
          [chain (Fin.last K)])[2 * K]? =
          some (chain (Fin.last K))) :=
    finiteAlternatingBlockGetLast
  have orderedPieces_length :
      ∀ e, (orderedPieces e).length =
        2 * (tubeChains.edgePieceOrder e).length + 1 := by
    intro e
    rw [orderedPieces_def e]
    exact orderedPiecesForAttachLength G D controlDisks tubeChains sourceSpoke
      targetSpokeReverse terminalTubeIndex gapConnector e
  have orderedPieces_get?_source :
      ∀ e, (orderedPieces e)[0]? = some (sourceSpoke e) := by
    intro e
    rw [orderedPieces_def e]
    exact orderedPiecesForAttachGetSource G D controlDisks tubeChains sourceSpoke
      targetSpokeReverse terminalTubeIndex gapConnector e
  have orderedPieces_get?_target :
      ∀ e, (orderedPieces e)[2 * (tubeChains.edgePieceOrder e).length]? =
        some (targetSpokeReverse e) := by
    intro e
    rw [orderedPieces_def e]
    exact orderedPiecesForAttachGetTarget G D controlDisks tubeChains sourceSpoke
      targetSpokeReverse terminalTubeIndex gapConnector e
  have orderedPieces_get?_of_block :
      ∀ (e : G.edgeFinset) (n : ℕ) (Γ : PolygonalArc),
        (((List.finRange ((tubeChains.edgePieceOrder e).length - 1)).map
            (fun q => tubeGapBlock e q)).flatten ++
          [tubeChains.chain (terminalTubeIndex e)])[n]? = some Γ →
        (orderedPieces e)[1 + n]? = some Γ := by
    intro e n Γ hΓ
    rw [orderedPieces_def e]
    exact orderedPiecesForAttachGetOfBlock G D controlDisks tubeChains sourceSpoke
      targetSpokeReverse terminalTubeIndex gapConnector e n Γ (by
        simpa [tubeGapBlock, tubeGapBlockForAttach] using hΓ)
  have orderedPieces_get?_tube :
      ∀ (e : G.edgeFinset) q
        (hq : q < (tubeChains.edgePieceOrder e).length),
        (orderedPieces e)[1 + 2 * q]? =
          some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q])) := by
    intro e q hq
    rw [orderedPieces_def e]
    exact orderedPiecesForAttachGetTube G D controlDisks tubeChains sourceSpoke
      targetSpokeReverse terminalTubeIndex gapConnector terminalTubeIndex_getLast
      e q hq
  have orderedPieces_get?_gap :
      ∀ (e : G.edgeFinset) q
        (hq : q + 1 < (tubeChains.edgePieceOrder e).length),
        (orderedPieces e)[2 + 2 * q]? =
          some (gapConnector e ⟨q, by omega⟩) := by
    intro e q hq
    rw [orderedPieces_def e]
    exact orderedPiecesForAttachGetGap G D controlDisks tubeChains sourceSpoke
      targetSpokeReverse terminalTubeIndex gapConnector terminalTubeIndex_getLast
      e q hq
  have orderedPieces_get?_terminal :
      ∀ e, (orderedPieces e)[2 * (tubeChains.edgePieceOrder e).length - 1]? =
        some (tubeChains.chain (terminalTubeIndex e)) := by
    intro e
    rw [orderedPieces_def e]
    exact orderedPiecesForAttachGetTerminal G D controlDisks tubeChains sourceSpoke
      targetSpokeReverse terminalTubeIndex gapConnector terminalTubeIndex_getLast e
  have orderedPieces_get?_classify :
      ∀ e m (hm : m < (orderedPieces e).length),
        (m = 0 ∧ (orderedPieces e)[m]? = some (sourceSpoke e)) ∨
          (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
            m = 1 + 2 * q ∧
              (orderedPieces e)[m]? =
                some (tubeChains.chain ((tubeChains.edgePieceOrder e)[q]))) ∨
          (∃ q, ∃ hq : q + 1 < (tubeChains.edgePieceOrder e).length,
            m = 2 + 2 * q ∧
              (orderedPieces e)[m]? =
                some (gapConnector e ⟨q, by omega⟩)) ∨
          (m = 2 * (tubeChains.edgePieceOrder e).length - 1 ∧
            (orderedPieces e)[m]? =
              some (tubeChains.chain (terminalTubeIndex e))) ∨
          (m = 2 * (tubeChains.edgePieceOrder e).length ∧
            (orderedPieces e)[m]? = some (targetSpokeReverse e)) := by
    intro e m hm
    rw [orderedPieces_def e] at hm ⊢
    exact orderedPiecesForAttachGetClassify G D controlDisks tubeChains sourceSpoke
      targetSpokeReverse terminalTubeIndex gapConnector terminalTubeIndex_getLast
      e m hm
  have orderedPieces_non_successive_disjoint_local :=
    orderedPiecesForAttachNonSuccessiveDisjoint G D controlDisks tubeChains
      localDiskFillings sourceSpoke targetSpokeReverse orderedPieces
      terminalTubeIndex gapConnector
      (by intro e; rfl)
      (by intro e; rfl)
      terminalTubeIndex_getLast terminalTubeIndex_mem gapConnector_eq_or_reverse
      sourceSpoke_carrier_disjoint_tube_chain_of_not_head
      targetSpokeReverse_carrier_disjoint_tube_chain_of_not_last
      tube_chain_carrier_disjoint_gapConnector_of_not_boundary
      gapConnector_carrier_disjoint_gapConnector_of_ne
      orderedPieces_get?_classify
  let concatenatedVertices : G.edgeFinset → List (EuclideanSpace ℝ (Fin 2)) :=
    fun e => PolygonalArcEndpointGluedVertices (orderedPieces e)
  let assemblyFacts :=
    mkOrderedPiecesAssemblyFacts G D controlDisks tubeChains localDiskFillings
      orderedPieces terminalTubeIndex gapConnector gapCenter gapCenter_spec
      orderedPieces_nonempty orderedPieces_head_source orderedPieces_last_target
      orderedPiece_is_local edge_mem_source_or_target
      edgeSourceVertex_ne_targetVertex edgeSource_mem_source_ball
      edgeTarget_mem_target_ball vertex_spoke_boundary_point_eq_target
      gapConnector_target terminalTube_attaches_targetSpoke
      terminalTubeIndex_getLast gapConnector_eq_or_reverse_gapCenter
      orderedPieces_length orderedPieces_get?_tube orderedPieces_get?_gap
      orderedPieces_get?_classify orderedPieces_successive_attach_local
      orderedPieces_non_successive_disjoint_local
  have assembled :=
    assembleOrderedPieces G D controlDisks tubeChains localDiskFillings
      sourceSpoke targetSpoke targetSpokeReverse orderedPieces terminalTubeIndex
      gapConnector gapCenter assemblyFacts
  let selectedEdgeArcs :=
    prepareSelectedEdgeArcs G D controlDisks tubeChains localDiskFillings
      orderedPieces assembled orderedPiece_is_local
  exact
    { sourceSpoke := sourceSpoke
      targetSpoke := targetSpoke
      targetSpokeReverse := targetSpokeReverse
      orderedPieces := orderedPieces
      terminalTubeIndex := terminalTubeIndex
      gapConnector := gapConnector
      gapCenter := gapCenter
      orderedPieces_def := orderedPieces_def
      assemblyFacts := assemblyFacts
      selectedEdgeArcs := selectedEdgeArcs
      terminalTubeIndex_mem := terminalTubeIndex_mem
      vertex_spoke_in_orderedPieces := vertex_spoke_in_orderedPieces
      tube_chain_in_orderedPieces := tube_chain_in_orderedPieces
      intersection_chain_in_orderedPieces :=
        intersection_chain_in_orderedPieces
      intersection_chain_or_reverse_in_orderedPieces :=
        intersection_chain_or_reverse_in_orderedPieces
      gapConnector_eq_or_reverse := gapConnector_eq_or_reverse }

private noncomputable def polygonalReplacementEdgeAssemblies_finish
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (prepared :
      EdgeAssemblyEarlyPrepared G D controlDisks tubeChains
        localDiskFillings) :
    PolygonalReplacementEdgeAssemblyData G D controlDisks tubeChains
      localDiskFillings := by
  classical
  let sourceSpoke := prepared.sourceSpoke
  let targetSpoke := prepared.targetSpoke
  let targetSpokeReverse := prepared.targetSpokeReverse
  let orderedPieces := prepared.orderedPieces
  let terminalTubeIndex := prepared.terminalTubeIndex
  let gapConnector := prepared.gapConnector
  let gapCenter := prepared.gapCenter
  have orderedPieces_def := prepared.orderedPieces_def
  have assemblyFacts := prepared.assemblyFacts
  have orderedPieces_nonempty := assemblyFacts.orderedPieces_nonempty
  have orderedPieces_head_source := assemblyFacts.orderedPieces_head_source
  have orderedPieces_last_target := assemblyFacts.orderedPieces_last_target
  have orderedPiece_is_local := assemblyFacts.orderedPiece_is_local
  have edge_mem_source_or_target := assemblyFacts.edge_mem_source_or_target
  have vertex_spoke_boundary_point_eq_target :=
    assemblyFacts.vertex_spoke_boundary_point_eq_target
  have orderedPieces_successive_attach_local :=
    assemblyFacts.orderedPieces_successive_attach_local
  have orderedPieces_non_successive_disjoint_local :=
    assemblyFacts.orderedPieces_non_successive_disjoint_local
  have terminalTubeIndex_mem := prepared.terminalTubeIndex_mem
  have vertex_spoke_in_orderedPieces :=
    prepared.vertex_spoke_in_orderedPieces
  have tube_chain_in_orderedPieces := prepared.tube_chain_in_orderedPieces
  have intersection_chain_in_orderedPieces :=
    prepared.intersection_chain_in_orderedPieces
  have intersection_chain_or_reverse_in_orderedPieces :=
    prepared.intersection_chain_or_reverse_in_orderedPieces
  have gapConnector_eq_or_reverse := prepared.gapConnector_eq_or_reverse
  have intersection_chain_boundary_point_eq_endpoint :=
    intersectionChainBoundaryPointEqEndpoint G D controlDisks tubeChains
      localDiskFillings
  have vertex_spoke_carrier_disjoint_vertex_spoke_of_ne :=
    vertexSpokeCarrierDisjointVertexSpokeOfNe G D controlDisks tubeChains
      localDiskFillings
  have vertex_spoke_carrier_disjoint_intersection_chain :=
    vertexSpokeCarrierDisjointIntersectionChain G D controlDisks tubeChains
      localDiskFillings
  have intersection_chain_carrier_disjoint_intersection_chain_of_ne :=
    intersectionChainCarrierDisjointIntersectionChainOfNe G D controlDisks
      tubeChains localDiskFillings
  let selectedEdgeArcs := prepared.selectedEdgeArcs
  let edgeArc : G.edgeFinset → PolygonalArc := selectedEdgeArcs.edgeArc
  have edgeArc_spec := selectedEdgeArcs.spec
  have edgeArc_relativeInterior_localized_local :=
    selectedEdgeArcs.relativeInterior_localized
  have edgeArc_relativeInterior_not_endpoints :=
    selectedEdgeArcs.relativeInterior_not_endpoints
  have vertexPlacement_eq_edge_endpoint :
      ∀ e v, v ∈ e.1 →
        D.vertexPlacement v = D.edgeSource e ∨
          D.vertexPlacement v = D.edgeTarget e := by
    intro e v hve
    rcases edge_mem_source_or_target e v hve with hv | hv
    · left
      rw [hv]
      exact (tubeChains.edgeSource_eq_vertexPlacement e).symm
    · right
      rw [hv]
      exact (tubeChains.edgeTarget_eq_vertexPlacement e).symm
  have tube_source_mem_owner_carrier :
      ∀ i, tubeChains.source i ∈ D.edgeCarrier (tubeChains.owner i) := by
    intro i
    rcases tubeChains.source_on_control_boundary i with hvertex |
      hintersection
    · rcases hvertex with ⟨_v, _hv, _hsphere, hcarrier⟩
      exact hcarrier
    · rcases hintersection with ⟨_x, _hx, _hsphere, hcarrier⟩
      exact hcarrier
  have tube_target_mem_owner_carrier :
      ∀ i, tubeChains.target i ∈ D.edgeCarrier (tubeChains.owner i) := by
    intro i
    rcases tubeChains.target_on_control_boundary i with hvertex |
      hintersection
    · rcases hvertex with ⟨_v, _hv, _hsphere, hcarrier⟩
      exact hcarrier
    · rcases hintersection with ⟨_x, _hx, _hsphere, hcarrier⟩
      exact hcarrier
  have vertex_spoke_carrier_disjoint_tube_chain_of_owner_ne :
      ∀ (v : V) (e : {e : G.edgeFinset // v ∈ e.1})
        (i : tubeChains.pieceIndex),
        e.1 ≠ tubeChains.owner i →
          Disjoint (localDiskFillings.vertex_spoke v e).carrier
            (tubeChains.chain i).carrier := by
    intro v e i howner_ne
    rw [Set.disjoint_left]
    intro p hpv hpi
    have hpvClosed :
        p ∈ Metric.closedBall (D.vertexPlacement v)
          (controlDisks.vertexRadius v) :=
      localDiskFillings.vertex_spoke_carrier_subset_closedBall v e hpv
    have hmeet :=
      tubeChains.chain_carrier_meets_vertex_closedBall_only_endpoint i v p
        hpi hpvClosed
    have hpSphere :
        p ∈ Metric.sphere (D.vertexPlacement v)
          (controlDisks.vertexRadius v) := by
      rcases hmeet with hsource | htarget
      · simpa [hsource.1] using hsource.2
      · simpa [htarget.1] using htarget.2
    have hpvTarget :
        p = (localDiskFillings.vertex_spoke v e).target :=
      vertex_spoke_boundary_point_eq_target v e p hpv hpSphere
    have hpvEdgeCarrier : p ∈ D.edgeCarrier e.1 := by
      rw [hpvTarget]
      exact (localDiskFillings.vertex_spoke_target_boundary v e).2
    have hpOwnerCarrier :
        p ∈ D.edgeCarrier (tubeChains.owner i) := by
      rcases hmeet with hsource | htarget
      · rw [hsource.1]
        exact tube_source_mem_owner_carrier i
      · rw [htarget.1]
        exact tube_target_mem_owner_carrier i
    have hvOwner : v ∈ (tubeChains.owner i).1 :=
      controlDisks.vertex_disk_meets_only_incident_edges
        (p := p) (e := tubeChains.owner i)
        (Metric.sphere_subset_closedBall hpSphere) hpOwnerCarrier
    have hedge_eq :
        e.1 = tubeChains.owner i :=
      controlDisks.vertex_boundary_point_edge_unique
        (v := v) (e₁ := e.1) (e₂ := tubeChains.owner i) (p := p)
        e.2 hvOwner hpSphere hpvEdgeCarrier hpOwnerCarrier
    exact howner_ne hedge_eq
  have tube_chain_carrier_disjoint_intersection_chain_of_owner_ne :
      ∀ (i : tubeChains.pieceIndex)
        (x : {q // q ∈ D.intersectionPoints})
        (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        tubeChains.owner i ≠ e.1 →
          Disjoint (tubeChains.chain i).carrier
            (localDiskFillings.intersection_chain x e).carrier := by
    intro i x e howner_ne
    rw [Set.disjoint_left]
    intro p hpi hpx
    have hpxClosed :
        p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) :=
      localDiskFillings.intersection_chain_carrier_subset_closedBall x e hpx
    have hmeet :=
      tubeChains.chain_carrier_meets_intersection_closedBall_only_endpoint
        i x p hpi hpxClosed
    have hpSphere :
        p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
      rcases hmeet with hsource | htarget
      · simpa [hsource.1] using hsource.2
      · simpa [htarget.1] using htarget.2
    have hpOwnerCarrier :
        p ∈ D.edgeCarrier (tubeChains.owner i) := by
      rcases hmeet with hsource | htarget
      · rw [hsource.1]
        exact tube_source_mem_owner_carrier i
      · rw [htarget.1]
        exact tube_target_mem_owner_carrier i
    have hxOwner : x.1 ∈ D.edgeRelativeInterior (tubeChains.owner i) :=
      controlDisks.intersection_disk_meets_only_passing_edges
        (x := x) (e := tubeChains.owner i) (p := p)
        (Metric.sphere_subset_closedBall hpSphere) hpOwnerCarrier
    have hendpoint :=
      intersection_chain_boundary_point_eq_endpoint x e p hpx hpSphere
    have hpxEdgeCarrier : p ∈ D.edgeCarrier e.1 := by
      rcases hendpoint with hsource | htarget
      · rw [hsource]
        exact (localDiskFillings.intersection_chain_source_boundary x e).2
      · rw [htarget]
        exact (localDiskFillings.intersection_chain_target_boundary x e).2
    have hedge_eq :
        tubeChains.owner i = e.1 :=
      controlDisks.intersection_boundary_point_edge_unique
        (x := x) (e₁ := tubeChains.owner i) (e₂ := e.1) (p := p)
        hxOwner e.2 hpSphere hpOwnerCarrier hpxEdgeCarrier
    exact howner_ne hedge_eq
  exact
    { orderedPieces := orderedPieces
      orderedPieces_nonempty := orderedPieces_nonempty
      orderedPieces_head_source := by
        intro e Γ hhead
        exact orderedPieces_head_source e Γ hhead
      orderedPieces_last_target := by
        intro e Γ hlast
        exact orderedPieces_last_target e Γ hlast
      orderedPieces_successive_attach := by
        intro e n hn
        exact orderedPieces_successive_attach_local e n hn
      orderedPieces_non_successive_disjoint := by
        intro e m n hm hn hmn
        exact orderedPieces_non_successive_disjoint_local e m n hm hn hmn
      orderedPiece_is_local := orderedPiece_is_local
      vertex_spoke_in_orderedPieces := vertex_spoke_in_orderedPieces
      tube_chain_in_orderedPieces := tube_chain_in_orderedPieces
      intersection_chain_in_orderedPieces := intersection_chain_in_orderedPieces
      edgeArc := edgeArc
      edgeArc_source := fun e => (edgeArc_spec e).1
      edgeArc_target := fun e => (edgeArc_spec e).2.1
      edgeArc_carrier_eq := fun e => (edgeArc_spec e).2.2.1
      edgeArc_relativeInterior_eq := by
        intro e
        rw [(edgeArc_spec e).2.2.2.1]
        ext p
        constructor
        · intro hp
          exact ⟨hp.1, by
            constructor
            · intro h
              exact hp.2 (by simp [h])
            · intro h
              exact hp.2 (by simp [h])⟩
        · intro hp
          exact ⟨hp.1, by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            intro h
            rcases h with h | h
            · exact hp.2.1 h
            · exact hp.2.2 h⟩
      orderedPiece_carrier_subset_edgeArc := by
        intro e piece hpiece p hp
        rw [(edgeArc_spec e).2.2.1]
        exact ⟨piece, hpiece, hp⟩
      vertex_spoke_relativeInterior_subset_edgeArc := by
        intro e v hve p hp
        rcases vertex_spoke_in_orderedPieces e v hve with
          ⟨piece, hpiece, _hcarrier, hrelativeInterior⟩
        have hp_piece : p ∈ piece.relativeInterior := by
          simpa [hrelativeInterior] using hp
        exact (edgeArc_spec e).2.2.2.2.1 piece hpiece hp_piece
      tube_chain_relativeInterior_subset_edgeArc := by
        intro i p hp
        rcases tube_chain_in_orderedPieces i with
          ⟨piece, hpiece, _hcarrier, hrelativeInterior⟩
        have hp_piece : p ∈ piece.relativeInterior := by
          simpa [hrelativeInterior] using hp
        exact (edgeArc_spec (tubeChains.owner i)).2.2.2.2.1 piece hpiece
          hp_piece
      intersection_chain_relativeInterior_subset_edgeArc := by
        intro x e p hp
        rcases intersection_chain_in_orderedPieces x e with
          ⟨piece, hpiece, _hcarrier, hrelativeInterior⟩
        have hp_piece : p ∈ piece.relativeInterior := by
          simpa [hrelativeInterior] using hp
        exact (edgeArc_spec e.1).2.2.2.2.1 piece hpiece hp_piece
      edgeArc_relativeInterior_localized := by
        intro e p hp
        exact edgeArc_relativeInterior_localized_local hp
      intersection_chain_segment_lift := by
        intro x e m hm
        rcases edgeArc_spec e.1 with
          ⟨_hsource, _htarget, _hcarrier, _hrelativeInterior,
            _hpiece_subset, hpiece_lift, _hsegment_localized⟩
        rcases intersection_chain_or_reverse_in_orderedPieces x e with
          ⟨piece, hpiece, hpiece_eq | hpiece_eq⟩
        · subst piece
          exact hpiece_lift (localDiskFillings.intersection_chain x e)
            hpiece m hm
        · subst piece
          rcases polygonalArc_original_segment_to_reverse
              (localDiskFillings.intersection_chain x e) m hm with
            ⟨r, hr, hrev_left, hrev_right⟩
          rcases hpiece_lift
              (PolygonalArcReverse
                (localDiskFillings.intersection_chain x e))
              hpiece r hr with
            ⟨i, hi, hmatch | hmatch⟩
          · refine ⟨i, hi, Or.inr ?_⟩
            exact ⟨by rw [hmatch.1, hrev_left],
              by rw [hmatch.2, hrev_right]⟩
          · refine ⟨i, hi, Or.inl ?_⟩
            exact ⟨by rw [hmatch.1, hrev_right],
              by rw [hmatch.2, hrev_left]⟩
      edgeArc_segment_localized := by
        intro e i hi
        rcases edgeArc_spec e with
          ⟨_hsource, _htarget, _hcarrier, _hrelativeInterior,
            _hpiece_subset, _hpiece_lift, hsegment_localized⟩
        rcases hsegment_localized i hi with
          ⟨piece, hpiece, m, hm, hmatch⟩
        rw [orderedPieces_def e] at hpiece
        simp only [orderedPiecesForAttach, tubeGapBlockForAttach,
          List.mem_append, List.mem_singleton, List.mem_flatten,
          List.mem_map] at hpiece
        rcases hpiece with ((hpiece | hpiece) | hpiece) | hpiece
        · subst piece
          left
          refine ⟨tubeChains.edgeSourceVertex e,
            tubeChains.edgeSourceVertex_mem e, m, ?_, ?_⟩
          · simpa [sourceSpoke, assemblyFacts.sourceSpoke_def e] using hm
          · simpa [sourceSpoke, assemblyFacts.sourceSpoke_def e] using hmatch
        · rcases hpiece with ⟨l, ⟨n, _hnmem, hl⟩, hpiece_l⟩
          subst l
          simp only [tubeGapBlockForAttach, List.mem_cons,
            List.mem_singleton] at hpiece_l
          rcases hpiece_l with hpiece_chain | hpiece_gap
          · subst piece
            right
            left
            have hnlt : n.1 < (tubeChains.edgePieceOrder e).length := by
              have hnsub : n.1 < (tubeChains.edgePieceOrder e).length - 1 :=
                n.2
              omega
            refine ⟨(tubeChains.edgePieceOrder e)[n.1], ?_, m, hm, hmatch⟩
            exact (tubeChains.edgePieceOrder_owner_iff e _).1
              (List.getElem_mem hnlt)
          · rcases hpiece_gap with hpiece_gap | hpiece_nil
            · subst piece
              rcases gapConnector_eq_or_reverse e n with
                ⟨x, hx_edge, hgap_eq | hgap_eq⟩
              · right
                right
                refine ⟨x, hx_edge, m, ?_, ?_⟩
                · simpa [hgap_eq] using hm
                · simpa [hgap_eq] using hmatch
              · rcases polygonalArcReverse_segment_match_to_original
                    (localDiskFillings.intersection_chain x ⟨e, hx_edge⟩) m
                    (by simpa [hgap_eq] using hm)
                    (by simpa [hgap_eq] using hmatch) with
                  ⟨k, hk, hmatch_original⟩
                right
                right
                exact ⟨x, hx_edge, k, hk, hmatch_original⟩
            · cases hpiece_nil
        · subst piece
          right
          left
          exact ⟨terminalTubeIndex e,
            (tubeChains.edgePieceOrder_owner_iff e _).1
              (terminalTubeIndex_mem e), m, hm, hmatch⟩
        · subst piece
          left
          rcases polygonalArcReverse_segment_match_to_original (targetSpoke e) m
              (by simpa [targetSpokeReverse,
                assemblyFacts.targetSpokeReverse_def e] using hm)
              (by simpa [targetSpokeReverse,
                assemblyFacts.targetSpokeReverse_def e] using hmatch) with
            ⟨k, hk, hmatch_original⟩
          refine ⟨tubeChains.edgeTargetVertex e,
            tubeChains.edgeTargetVertex_mem e, k, ?_, ?_⟩
          · simpa [targetSpoke, assemblyFacts.targetSpoke_def e] using hk
          · simpa [targetSpoke, assemblyFacts.targetSpoke_def e] using
              hmatch_original
      distinct_edge_relativeInteriors_localized := by
        intro e f p hef hpe hpf
        have vertex_spoke_rel_of_same_vertex_other_edge
            (v : V) (e f : G.edgeFinset) (hve : v ∈ e.1)
            (hvf : v ∈ f.1) (hef' : e ≠ f)
            (hpArc : p ∈ (edgeArc e).relativeInterior)
            (hpE :
              p ∈ (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier)
            (hpF :
              p ∈ (localDiskFillings.vertex_spoke v ⟨f, hvf⟩).carrier) :
            p ∈
              (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior := by
          rw [(localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior_eq]
          refine ⟨hpE, ?_⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          constructor
          · intro hpSource
            have hpVertex : p = D.vertexPlacement v := by
              rw [hpSource]
              exact localDiskFillings.vertex_spoke_source v ⟨e, hve⟩
            rcases vertexPlacement_eq_edge_endpoint e v hve with hendpoint |
              hendpoint
            · exact (edgeArc_relativeInterior_not_endpoints hpArc).1
                (by rw [hpVertex, hendpoint])
            · exact (edgeArc_relativeInterior_not_endpoints hpArc).2
                (by rw [hpVertex, hendpoint])
          · intro hpTarget
            have hpSphere :
                p ∈ Metric.sphere (D.vertexPlacement v)
                  (controlDisks.vertexRadius v) := by
              rw [hpTarget]
              exact
                (localDiskFillings.vertex_spoke_target_boundary v
                  ⟨e, hve⟩).1
            have hpFTarget :
                p =
                  (localDiskFillings.vertex_spoke v ⟨f, hvf⟩).target :=
              vertex_spoke_boundary_point_eq_target v ⟨f, hvf⟩ p hpF
                hpSphere
            have hpECarrier : p ∈ D.edgeCarrier e := by
              rw [hpTarget]
              exact
                (localDiskFillings.vertex_spoke_target_boundary v
                  ⟨e, hve⟩).2
            have hpFCarrier : p ∈ D.edgeCarrier f := by
              rw [hpFTarget]
              exact
                (localDiskFillings.vertex_spoke_target_boundary v
                  ⟨f, hvf⟩).2
            have hedge_eq :
                e = f :=
              controlDisks.vertex_boundary_point_edge_unique
                (v := v) (e₁ := e) (e₂ := f) (p := p)
                hve hvf hpSphere hpECarrier hpFCarrier
            exact hef' hedge_eq
        have intersection_chain_rel_of_same_center_other_edge
            (x : {q // q ∈ D.intersectionPoints}) (e f : G.edgeFinset)
            (hxe : x.1 ∈ D.edgeRelativeInterior e)
            (hxf : x.1 ∈ D.edgeRelativeInterior f) (hef' : e ≠ f)
            (hpE :
              p ∈
                (localDiskFillings.intersection_chain x
                  ⟨e, hxe⟩).carrier)
            (hpF :
              p ∈
                (localDiskFillings.intersection_chain x
                  ⟨f, hxf⟩).carrier) :
            p ∈
              (localDiskFillings.intersection_chain x
                ⟨e, hxe⟩).relativeInterior := by
          rw [(localDiskFillings.intersection_chain x
            ⟨e, hxe⟩).relativeInterior_eq]
          refine ⟨hpE, ?_⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          constructor
          · intro hpSource
            have hpSphere :
                p ∈ Metric.sphere x.1
                  (controlDisks.intersectionRadius x) := by
              rw [hpSource]
              exact
                (localDiskFillings.intersection_chain_source_boundary x
                  ⟨e, hxe⟩).1
            have hpFEndpoint :=
              intersection_chain_boundary_point_eq_endpoint x ⟨f, hxf⟩ p
                hpF hpSphere
            have hpECarrier : p ∈ D.edgeCarrier e := by
              rw [hpSource]
              exact
                (localDiskFillings.intersection_chain_source_boundary x
                  ⟨e, hxe⟩).2
            have hpFCarrier : p ∈ D.edgeCarrier f := by
              rcases hpFEndpoint with hpFSource | hpFTarget
              · rw [hpFSource]
                exact
                  (localDiskFillings.intersection_chain_source_boundary x
                    ⟨f, hxf⟩).2
              · rw [hpFTarget]
                exact
                  (localDiskFillings.intersection_chain_target_boundary x
                    ⟨f, hxf⟩).2
            have hedge_eq :
                e = f :=
              controlDisks.intersection_boundary_point_edge_unique
                (x := x) (e₁ := e) (e₂ := f) (p := p)
                hxe hxf hpSphere hpECarrier hpFCarrier
            exact hef' hedge_eq
          · intro hpTarget
            have hpSphere :
                p ∈ Metric.sphere x.1
                  (controlDisks.intersectionRadius x) := by
              rw [hpTarget]
              exact
                (localDiskFillings.intersection_chain_target_boundary x
                  ⟨e, hxe⟩).1
            have hpFEndpoint :=
              intersection_chain_boundary_point_eq_endpoint x ⟨f, hxf⟩ p
                hpF hpSphere
            have hpECarrier : p ∈ D.edgeCarrier e := by
              rw [hpTarget]
              exact
                (localDiskFillings.intersection_chain_target_boundary x
                  ⟨e, hxe⟩).2
            have hpFCarrier : p ∈ D.edgeCarrier f := by
              rcases hpFEndpoint with hpFSource | hpFTarget
              · rw [hpFSource]
                exact
                  (localDiskFillings.intersection_chain_source_boundary x
                    ⟨f, hxf⟩).2
              · rw [hpFTarget]
                exact
                  (localDiskFillings.intersection_chain_target_boundary x
                    ⟨f, hxf⟩).2
            have hedge_eq :
                e = f :=
              controlDisks.intersection_boundary_point_edge_unique
                (x := x) (e₁ := e) (e₂ := f) (p := p)
                hxe hxf hpSphere hpECarrier hpFCarrier
            exact hef' hedge_eq
        have hloc_e := edgeArc_relativeInterior_localized_local hpe
        have hloc_f := edgeArc_relativeInterior_localized_local hpf
        rcases hloc_e with hvertex_e | htube_e | hintersection_e
        · rcases hvertex_e with ⟨v, hve, hpv⟩
          rcases hloc_f with hvertex_f | htube_f | hintersection_f
          · rcases hvertex_f with ⟨w, hwf, hpw⟩
            by_cases hvw : v = w
            · subst w
              have hpvRel :=
                vertex_spoke_rel_of_same_vertex_other_edge v e f hve hwf
                  hef hpe hpv hpw
              have hpwRel :=
                vertex_spoke_rel_of_same_vertex_other_edge v f e hwf hve
                  hef.symm hpf hpw hpv
              have hsub_ne :
                  (⟨e, hve⟩ :
                    {e : G.edgeFinset // v ∈ e.1}) ≠ ⟨f, hwf⟩ := by
                intro h
                exact hef (congrArg Subtype.val h)
              exact False.elim
                ((Set.disjoint_left.mp
                  (localDiskFillings.vertex_spokes_same_vertex_disjoint v
                    hsub_ne) hpvRel) hpwRel)
            · exact False.elim
                ((Set.disjoint_left.mp
                  (vertex_spoke_carrier_disjoint_vertex_spoke_of_ne
                    ⟨e, hve⟩ ⟨f, hwf⟩ hvw) hpv) hpw)
          · rcases htube_f with ⟨i, howner, hpi⟩
            have howner_ne : e ≠ tubeChains.owner i := by
              rw [howner]
              exact hef
            exact False.elim
              ((Set.disjoint_left.mp
                (vertex_spoke_carrier_disjoint_tube_chain_of_owner_ne v
                  ⟨e, hve⟩ i howner_ne) hpv) hpi)
          · rcases hintersection_f with ⟨x, hxf, hpx⟩
            exact False.elim
              ((Set.disjoint_left.mp
                (vertex_spoke_carrier_disjoint_intersection_chain v
                  ⟨e, hve⟩ x ⟨f, hxf⟩) hpv) hpx)
        · rcases htube_e with ⟨i, howner_i, hpi⟩
          rcases hloc_f with hvertex_f | htube_f | hintersection_f
          · rcases hvertex_f with ⟨v, hvf, hpv⟩
            have howner_ne : f ≠ tubeChains.owner i := by
              rw [howner_i]
              exact hef.symm
            exact False.elim
              ((Set.disjoint_left.mp
                (vertex_spoke_carrier_disjoint_tube_chain_of_owner_ne v
                  ⟨f, hvf⟩ i howner_ne) hpv) hpi)
          · rcases htube_f with ⟨j, howner_j, hpj⟩
            by_cases hij : i = j
            · subst j
              have hef_eq : e = f := by
                rw [← howner_i, ← howner_j]
              exact False.elim (hef hef_eq)
            · exact False.elim
                ((Set.disjoint_left.mp
                  (tubeChains.chain_carriers_pairwise_disjoint hij) hpi)
                  hpj)
          · rcases hintersection_f with ⟨x, hxf, hpx⟩
            have howner_ne : tubeChains.owner i ≠ f := by
              rw [howner_i]
              exact hef
            exact False.elim
              ((Set.disjoint_left.mp
                (tube_chain_carrier_disjoint_intersection_chain_of_owner_ne
                  i x ⟨f, hxf⟩ howner_ne) hpi) hpx)
        · rcases hintersection_e with ⟨x, hxe, hpx⟩
          rcases hloc_f with hvertex_f | htube_f | hintersection_f
          · rcases hvertex_f with ⟨v, hvf, hpv⟩
            exact False.elim
              ((Set.disjoint_left.mp
                (vertex_spoke_carrier_disjoint_intersection_chain v
                  ⟨f, hvf⟩ x ⟨e, hxe⟩) hpv) hpx)
          · rcases htube_f with ⟨i, howner_i, hpi⟩
            have howner_ne : tubeChains.owner i ≠ e := by
              rw [howner_i]
              exact hef.symm
            exact False.elim
              ((Set.disjoint_left.mp
                (tube_chain_carrier_disjoint_intersection_chain_of_owner_ne
                  i x ⟨e, hxe⟩ howner_ne) hpi) hpx)
          · rcases hintersection_f with ⟨y, hyf, hpy⟩
            by_cases hxy : x = y
            · subst y
              refine ⟨x, hxe, hyf, ?_, ?_⟩
              · exact
                  intersection_chain_rel_of_same_center_other_edge x e f
                    hxe hyf hef hpx hpy
              · exact
                  intersection_chain_rel_of_same_center_other_edge x f e
                    hyf hxe hef.symm hpy hpx
            · exact False.elim
                ((Set.disjoint_left.mp
                  (intersection_chain_carrier_disjoint_intersection_chain_of_ne
                    (x := x) (y := y)
                    (⟨e, hxe⟩ :
                      {g : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior g})
                    (⟨f, hyf⟩ :
                      {g : G.edgeFinset // y.1 ∈ D.edgeRelativeInterior g})
                    hxy) hpx) hpy) }

lemma PolygonalReplacementEdgeAssemblies {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) :
    Nonempty
      (PolygonalReplacementEdgeAssemblyData G D controlDisks tubeChains
        localDiskFillings) := by
  let core :=
    polygonalReplacementEdgeAssemblies_prepareCore G D controlDisks tubeChains
      localDiskFillings
  let prepared :=
    polygonalReplacementEdgeAssemblies_prepareEarly G D controlDisks tubeChains
      localDiskFillings core
  exact ⟨polygonalReplacementEdgeAssemblies_finish G D controlDisks tubeChains
    localDiskFillings prepared⟩
