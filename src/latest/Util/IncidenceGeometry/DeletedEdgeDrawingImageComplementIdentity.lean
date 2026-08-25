import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.PolygonalArc
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

lemma DeletedEdgeDrawingImageComplementIdentity {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (e : G.edgeFinset) (Ddel : OrdinaryPolygonalDrawing (G.deleteEdges {e.1}))
    (hvertex : Ddel.vertexPlacement = D.vertexPlacement)
    (hedges :
      ∀ ed : (G.deleteEdges {e.1}).edgeFinset,
        ∃ eG : G.edgeFinset, eG.1 = ed.1 ∧ eG.1 ≠ e.1 ∧
          Ddel.edgeArc ed = D.edgeArc eG) :
    (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ =
      (OrdinaryDrawingImage G D)ᶜ ∪ (D.edgeArc e).relativeInterior := by
  have hImageSubset :
      OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel ⊆ OrdinaryDrawingImage G D := by
    intro x hx
    rw [OrdinaryDrawingImage] at hx ⊢
    rcases hx with hxv | hxe
    · left
      rcases hxv with ⟨v, hvx⟩
      exact ⟨v, by simpa [hvertex] using hvx⟩
    · right
      rcases Set.mem_iUnion.mp hxe with ⟨ed, hxed⟩
      rcases hedges ed with ⟨eG, _heq, _hne, hArc⟩
      exact Set.mem_iUnion.mpr ⟨eG, by simpa [hArc] using hxed⟩
  have hEndpointOfCarrierNotInterior :
      ∀ (γ : PolygonalArc) {x : EuclideanSpace ℝ (Fin 2)},
        x ∈ γ.carrier → x ∉ γ.relativeInterior → x = γ.source ∨ x = γ.target := by
    intro γ x hxCarrier hxNotInterior
    have hxNotDiff :
        x ∉ γ.carrier \ ({γ.source, γ.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
      simpa [γ.relativeInterior_eq] using hxNotInterior
    have hxEndpoint : x ∈ ({γ.source, γ.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
      by_contra hxNotEndpoint
      exact hxNotDiff ⟨hxCarrier, hxNotEndpoint⟩
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hxEndpoint
  have hOldCarrierEndpointVertex :
      ∀ (f : G.edgeFinset) {x : EuclideanSpace ℝ (Fin 2)},
        x ∈ (D.edgeArc f).carrier →
          x ∉ (D.edgeArc f).relativeInterior → x ∈ Set.range D.vertexPlacement := by
    intro f x hxCarrier hxNotInterior
    have hxEndpoint := hEndpointOfCarrierNotInterior (D.edgeArc f) hxCarrier hxNotInterior
    rcases D.edgeArc_endpoints f with ⟨u, v, _hAdj, _heq, hdir | hdir⟩
    · rcases hdir with ⟨hsource, htarget⟩
      rcases hxEndpoint with rfl | rfl
      · exact ⟨u, hsource.symm⟩
      · exact ⟨v, htarget.symm⟩
    · rcases hdir with ⟨hsource, htarget⟩
      rcases hxEndpoint with rfl | rfl
      · exact ⟨v, hsource.symm⟩
      · exact ⟨u, htarget.symm⟩
  have hDeletedInteriorNewCompl :
      (D.edgeArc e).relativeInterior ⊆
        (OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel)ᶜ := by
    intro x hxInterior hxNew
    rw [OrdinaryDrawingImage] at hxNew
    rcases hxNew with hxv | hxed
    · rcases hxv with ⟨v, hvx⟩
      have hOldVertex : D.vertexPlacement v = x := by
        simpa [hvertex] using hvx
      exact D.no_vertex_in_edge_interior v e (by simpa [hOldVertex] using hxInterior)
    · rcases Set.mem_iUnion.mp hxed with ⟨ed, hxEdCarrier⟩
      rcases hedges ed with ⟨eG, _heq, hne, hArc⟩
      have hxOldCarrier : x ∈ (D.edgeArc eG).carrier := by
        simpa [hArc] using hxEdCarrier
      by_cases hxOldInterior : x ∈ (D.edgeArc eG).relativeInterior
      · have he_ne : e ≠ eG := by
          intro h
          exact hne (congrArg Subtype.val h).symm
        have hxCross : x ∈ D.crossingSet := by
          exact (D.crossingSet_spec x).2 ⟨e, eG, he_ne, hxInterior, hxOldInterior⟩
        have hCrossEmpty : D.crossingSet = ∅ := Finset.card_eq_zero.mp hD
        simpa [hCrossEmpty] using hxCross
      · rcases hOldCarrierEndpointVertex eG hxOldCarrier hxOldInterior with ⟨v, hvx⟩
        exact D.no_vertex_in_edge_interior v e (by simpa [hvx] using hxInterior)
  have hOldOutsideInteriorSubsetNew :
      OrdinaryDrawingImage G D \ (D.edgeArc e).relativeInterior ⊆
        OrdinaryDrawingImage (G.deleteEdges {e.1}) Ddel := by
    intro x hx
    rcases hx with ⟨hxOld, hxNotInterior⟩
    rw [OrdinaryDrawingImage] at hxOld ⊢
    rcases hxOld with hxv | hxf
    · left
      rcases hxv with ⟨v, hvx⟩
      exact ⟨v, by simpa [hvertex] using hvx⟩
    · rcases Set.mem_iUnion.mp hxf with ⟨f, hxFCarrier⟩
      by_cases hfdel : f.1 = e.1
      · have hf_eq : f = e := Subtype.ext hfdel
        have hxNotFInterior : x ∉ (D.edgeArc f).relativeInterior := by
          simpa [hf_eq] using hxNotInterior
        rcases hOldCarrierEndpointVertex f hxFCarrier hxNotFInterior with ⟨v, hvx⟩
        left
        exact ⟨v, by simpa [hvertex] using hvx⟩
      · let ed : (G.deleteEdges {e.1}).edgeFinset :=
          ⟨f.1, by
            apply SimpleGraph.mem_edgeFinset.mpr
            rw [SimpleGraph.edgeSet_deleteEdges]
            exact ⟨SimpleGraph.mem_edgeFinset.mp f.2, by simpa using hfdel⟩⟩
        right
        refine Set.mem_iUnion.mpr ⟨ed, ?_⟩
        rcases hedges ed with ⟨eG, heq, _hne, hArc⟩
        have heG_eq_f : eG = f := Subtype.ext heq
        have hArcEq : Ddel.edgeArc ed = D.edgeArc f := by
          simpa [heG_eq_f] using hArc
        simpa [hArcEq] using hxFCarrier
  ext x
  constructor
  · intro hxNewCompl
    by_cases hxOld : x ∈ OrdinaryDrawingImage G D
    · right
      by_contra hxNotInterior
      exact hxNewCompl (hOldOutsideInteriorSubsetNew ⟨hxOld, hxNotInterior⟩)
    · left
      exact hxOld
  · intro hx
    rcases hx with hxOldCompl | hxInterior
    · intro hxNew
      exact hxOldCompl (hImageSubset hxNew)
    · exact hDeletedInteriorNewCompl hxInterior
