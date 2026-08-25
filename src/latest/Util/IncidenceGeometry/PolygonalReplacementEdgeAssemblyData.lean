import Util.IncidenceGeometry.PolygonalReplacementLocalDiskFillingData

open Classical
noncomputable section

structure PolygonalReplacementEdgeAssemblyData {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) where
  orderedPieces : G.edgeFinset → List PolygonalArc
  orderedPieces_nonempty : ∀ e, (orderedPieces e).length ≠ 0
  orderedPieces_head_source :
    ∀ e Γ, (orderedPieces e).head? = some Γ → Γ.source = D.edgeSource e
  orderedPieces_last_target :
    ∀ e Γ, (orderedPieces e).getLast? = some Γ → Γ.target = D.edgeTarget e
  orderedPieces_successive_attach :
    ∀ e n (hn : n + 1 < (orderedPieces e).length),
      ((orderedPieces e)[n]).target = ((orderedPieces e)[n + 1]).source
  orderedPieces_non_successive_disjoint :
    ∀ e m n (hm : m < (orderedPieces e).length)
      (hn : n < (orderedPieces e).length),
      m + 1 < n ∨ n + 1 < m →
        Disjoint ((orderedPieces e)[m]).carrier ((orderedPieces e)[n]).carrier
  orderedPiece_is_local :
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
  edgeArc : G.edgeFinset → PolygonalArc
  edgeArc_source : ∀ e, (edgeArc e).source = D.edgeSource e
  edgeArc_target : ∀ e, (edgeArc e).target = D.edgeTarget e
  edgeArc_carrier_eq :
    ∀ e,
      (edgeArc e).carrier =
        {p | ∃ Γ : PolygonalArc, Γ ∈ orderedPieces e ∧ p ∈ Γ.carrier}
  edgeArc_relativeInterior_eq :
    ∀ e,
      (edgeArc e).relativeInterior =
        {p |
          (∃ Γ : PolygonalArc, Γ ∈ orderedPieces e ∧ p ∈ Γ.carrier) ∧
            p ≠ D.edgeSource e ∧ p ≠ D.edgeTarget e}
  orderedPiece_carrier_subset_edgeArc :
    ∀ e Γ, Γ ∈ orderedPieces e → Γ.carrier ⊆ (edgeArc e).carrier
  vertex_spoke_relativeInterior_subset_edgeArc :
    ∀ e v (hve : v ∈ e.1),
      (localDiskFillings.vertex_spoke v ⟨e, hve⟩).relativeInterior ⊆
        (edgeArc e).relativeInterior
  tube_chain_relativeInterior_subset_edgeArc :
    ∀ i,
      (tubeChains.chain i).relativeInterior ⊆
        (edgeArc (tubeChains.owner i)).relativeInterior
  intersection_chain_relativeInterior_subset_edgeArc :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      (localDiskFillings.intersection_chain x e).relativeInterior ⊆
        (edgeArc e.1).relativeInterior
  edgeArc_relativeInterior_localized :
    ∀ ⦃e : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      p ∈ (edgeArc e).relativeInterior →
        (∃ (v : V) (hve : v ∈ e.1),
          p ∈ (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier) ∨
        (∃ i : tubeChains.pieceIndex,
          tubeChains.owner i = e ∧ p ∈ (tubeChains.chain i).carrier) ∨
        (∃ (x : {q // q ∈ D.intersectionPoints})
            (hxe : x.1 ∈ D.edgeRelativeInterior e),
          p ∈ (localDiskFillings.intersection_chain x ⟨e, hxe⟩).carrier)
  intersection_chain_segment_lift :
    ∀ (x : {q // q ∈ D.intersectionPoints})
      (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}) m
      (hm :
        m + 1 <
          (localDiskFillings.intersection_chain x e).vertices.length),
      ∃ i : ℕ, ∃ hi : i + 1 < (edgeArc e.1).vertices.length,
        (((edgeArc e.1).vertices[i] =
              (localDiskFillings.intersection_chain x e).vertices[m] ∧
            (edgeArc e.1).vertices[i + 1] =
              (localDiskFillings.intersection_chain x e).vertices[m + 1]) ∨
          ((edgeArc e.1).vertices[i] =
              (localDiskFillings.intersection_chain x e).vertices[m + 1] ∧
            (edgeArc e.1).vertices[i + 1] =
              (localDiskFillings.intersection_chain x e).vertices[m]))
  edgeArc_segment_localized :
    ∀ e i (hi : i + 1 < (edgeArc e).vertices.length),
      (∃ (v : V) (hve : v ∈ e.1) (m : ℕ)
          (hm :
            m + 1 <
              (localDiskFillings.vertex_spoke v ⟨e, hve⟩).vertices.length),
          (((edgeArc e).vertices[i] =
                (localDiskFillings.vertex_spoke v ⟨e, hve⟩).vertices[m] ∧
              (edgeArc e).vertices[i + 1] =
                (localDiskFillings.vertex_spoke v ⟨e, hve⟩).vertices[m + 1]) ∨
            ((edgeArc e).vertices[i] =
                (localDiskFillings.vertex_spoke v ⟨e, hve⟩).vertices[m + 1] ∧
              (edgeArc e).vertices[i + 1] =
                (localDiskFillings.vertex_spoke v ⟨e, hve⟩).vertices[m]))) ∨
      (∃ k : tubeChains.pieceIndex,
        tubeChains.owner k = e ∧
          ∃ (m : ℕ) (hm : m + 1 < (tubeChains.chain k).vertices.length),
            (((edgeArc e).vertices[i] = (tubeChains.chain k).vertices[m] ∧
                (edgeArc e).vertices[i + 1] =
                  (tubeChains.chain k).vertices[m + 1]) ∨
              ((edgeArc e).vertices[i] =
                  (tubeChains.chain k).vertices[m + 1] ∧
                (edgeArc e).vertices[i + 1] =
                  (tubeChains.chain k).vertices[m]))) ∨
      (∃ (x : {q // q ∈ D.intersectionPoints})
          (hxe : x.1 ∈ D.edgeRelativeInterior e) (m : ℕ)
          (hm :
            m + 1 <
              (localDiskFillings.intersection_chain x ⟨e, hxe⟩).vertices.length),
          (((edgeArc e).vertices[i] =
                (localDiskFillings.intersection_chain x ⟨e, hxe⟩).vertices[m] ∧
              (edgeArc e).vertices[i + 1] =
                (localDiskFillings.intersection_chain x ⟨e, hxe⟩).vertices[m + 1]) ∨
            ((edgeArc e).vertices[i] =
                (localDiskFillings.intersection_chain x ⟨e, hxe⟩).vertices[m + 1] ∧
              (edgeArc e).vertices[i + 1] =
                (localDiskFillings.intersection_chain x ⟨e, hxe⟩).vertices[m])))
  distinct_edge_relativeInteriors_localized :
    ∀ ⦃e f : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e ≠ f →
        p ∈ (edgeArc e).relativeInterior →
          p ∈ (edgeArc f).relativeInterior →
            ∃ (x : {q // q ∈ D.intersectionPoints})
              (hxe : x.1 ∈ D.edgeRelativeInterior e)
              (hxf : x.1 ∈ D.edgeRelativeInterior f),
              p ∈
                  (localDiskFillings.intersection_chain x ⟨e, hxe⟩).relativeInterior ∧
                p ∈
                  (localDiskFillings.intersection_chain x ⟨f, hxf⟩).relativeInterior
