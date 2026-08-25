import Util.IncidenceGeometry.PolygonalReplacementLocalDiskFillingData

open Classical
noncomputable section

lemma PolygonalReplacementLocalPieceLists {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) :
    ∃ localPieces : G.edgeFinset → List PolygonalArc,
      (∀ e, (localPieces e).length ≠ 0) ∧
      (∀ e Γ, Γ ∈ localPieces e →
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
              (localDiskFillings.intersection_chain x ⟨e, hxe⟩).relativeInterior)) ∧
      (∀ e v (hve : v ∈ e.1),
        ∃ Γ : PolygonalArc,
          Γ ∈ localPieces e ∧
            Γ.carrier =
                (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier ∧
              Γ.relativeInterior =
                (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior) ∧
      (∀ i,
        ∃ Γ : PolygonalArc,
          Γ ∈ localPieces (tubeChains.owner i) ∧
            Γ.carrier = (tubeChains.chain i).carrier ∧
              Γ.relativeInterior = (tubeChains.chain i).relativeInterior) ∧
      (∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        ∃ Γ : PolygonalArc,
          Γ ∈ localPieces e.1 ∧
            Γ.carrier = (localDiskFillings.intersection_chain x e).carrier ∧
              Γ.relativeInterior =
                (localDiskFillings.intersection_chain x e).relativeInterior) := by
  classical
  let vertexPieces : G.edgeFinset → List PolygonalArc := fun e =>
    ((Finset.univ.filter (fun v : V => v ∈ e.1)).attach.toList.map
      (fun vh =>
        localDiskFillings.vertex_spoke vh.1
          ⟨e, (Finset.mem_filter.mp vh.2).2⟩))
  let tubePieces : G.edgeFinset → List PolygonalArc := fun e =>
    (tubeChains.edgePieceOrder e).map (fun i => tubeChains.chain i)
  let intersectionPieces : G.edgeFinset → List PolygonalArc := fun e =>
    ((D.intersectionPoints.filter
        (fun p : EuclideanSpace ℝ (Fin 2) =>
          p ∈ D.edgeRelativeInterior e)).attach.toList.map
      (fun xh =>
        localDiskFillings.intersection_chain
          ⟨xh.1, (Finset.mem_filter.mp xh.2).1⟩
          ⟨e, (Finset.mem_filter.mp xh.2).2⟩))
  let localPieces : G.edgeFinset → List PolygonalArc := fun e =>
    vertexPieces e ++ tubePieces e ++ intersectionPieces e
  refine ⟨localPieces, ?_, ?_, ?_, ?_, ?_⟩
  · intro e hzero
    have htube_nonempty : (tubePieces e).length ≠ 0 := by
      dsimp [tubePieces]
      simpa using tubeChains.edgePieceOrder_nonempty e
    have : (tubePieces e).length = 0 := by
      have hsum :
          (vertexPieces e).length + (tubePieces e).length +
            (intersectionPieces e).length = 0 := by
        simpa [localPieces, List.length_append, Nat.add_assoc] using hzero
      omega
    exact htube_nonempty this
  · intro e Γ hΓ
    dsimp [localPieces] at hΓ
    rw [List.mem_append, List.mem_append] at hΓ
    rcases hΓ with (hΓv | hΓt) | hΓx
    · left
      dsimp [vertexPieces] at hΓv
      rw [List.mem_map] at hΓv
      rcases hΓv with ⟨vh, _hvh_mem, rfl⟩
      refine ⟨vh.1, (Finset.mem_filter.mp vh.2).2, rfl, rfl⟩
    · right
      left
      dsimp [tubePieces] at hΓt
      rw [List.mem_map] at hΓt
      rcases hΓt with ⟨i, hi_mem, rfl⟩
      refine ⟨i, ?_, rfl, rfl⟩
      exact (tubeChains.edgePieceOrder_owner_iff e i).1 hi_mem
    · right
      right
      dsimp [intersectionPieces] at hΓx
      rw [List.mem_map] at hΓx
      rcases hΓx with ⟨xh, _hxh_mem, rfl⟩
      refine ⟨⟨xh.1, (Finset.mem_filter.mp xh.2).1⟩,
        (Finset.mem_filter.mp xh.2).2, rfl, rfl⟩
  · intro e v hve
    refine ⟨localDiskFillings.vertex_spoke v ⟨e, hve⟩, ?_, rfl, rfl⟩
    dsimp [localPieces]
    rw [List.mem_append, List.mem_append]
    left
    left
    dsimp [vertexPieces]
    rw [List.mem_map]
    refine ⟨⟨v, ?_⟩, ?_, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hve⟩
    · simp
  · intro i
    refine ⟨tubeChains.chain i, ?_, rfl, rfl⟩
    dsimp [localPieces]
    rw [List.mem_append, List.mem_append]
    left
    right
    dsimp [tubePieces]
    rw [List.mem_map]
    refine ⟨i, ?_, rfl⟩
    exact (tubeChains.edgePieceOrder_owner_iff (tubeChains.owner i) i).2 rfl
  · intro x e
    refine ⟨localDiskFillings.intersection_chain x e, ?_, rfl, rfl⟩
    dsimp [localPieces]
    rw [List.mem_append, List.mem_append]
    right
    dsimp [intersectionPieces]
    rw [List.mem_map]
    refine ⟨⟨x.1, ?_⟩, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨x.2, e.2⟩
    · simp
    · rfl
