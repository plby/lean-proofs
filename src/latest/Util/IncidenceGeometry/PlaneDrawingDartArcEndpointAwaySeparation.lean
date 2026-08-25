import Util.IncidenceGeometry.OrdinaryDrawingImageWithoutEdge
import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.PlaneDrawingDartArcData
import Util.IncidenceGeometry.PlaneDrawingSelectedEdgeAwayFromEndpointCompact
import Util.IncidenceGeometry.PolygonalArcCarrierCompact
import Util.IncidenceGeometry.PolygonalArcVertexMemCarrier
import Util.IncidenceGeometry.PositiveSeparation
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section

lemma PlaneDrawingDartArcEndpointAwaySeparation {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) (d : G.Dart) (r₀ r₁ : ℝ) :
    0 < r₀ →
      0 < r₁ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ x : EuclideanSpace ℝ (Fin 2),
            x ∈ OrdinaryDrawingImageWithoutEdge G D (A.dartEdge d) →
              x ∉ Metric.ball (A.dartArc d).source r₀ ∪
                Metric.ball (A.dartArc d).target r₁ →
                ∀ p : EuclideanSpace ℝ (Fin 2),
                  p ∈ (A.dartArc d).carrier →
                    δ ≤ dist x p := by
  intro hr₀ hr₁
  let e : G.edgeFinset := A.dartEdge d
  let γ : PolygonalArc := A.dartArc d
  let α : PolygonalArc := D.edgeArc e
  let K : Set (EuclideanSpace ℝ (Fin 2)) :=
    OrdinaryDrawingImageWithoutEdge G D e \
      (Metric.ball γ.source r₀ ∪ Metric.ball γ.target r₁)
  have hcarrier : γ.carrier = α.carrier := by
    simpa [γ, α, e] using A.dartArc_carrier d
  have hendpoint :
      (α.source = γ.source ∧ α.target = γ.target) ∨
        (α.source = γ.target ∧ α.target = γ.source) := by
    rcases D.edgeArc_endpoints e with ⟨u, v, _huv_adj, huv_edge, horient⟩
    have hsym : Sym2.mk d.toProd.1 d.toProd.2 = Sym2.mk u v := by
      have hde : d.edge = Sym2.mk u v := by
        have hde_edge : d.edge = e.1 := by
          simpa [e] using (A.dartEdge_eq d).symm
        exact hde_edge.trans huv_edge
      simpa [SimpleGraph.Dart.edge] using hde
    rcases (Sym2.eq_iff.mp hsym) with hsame | hswap
    · rcases hsame with ⟨htail, hhead⟩
      subst u
      subst v
      rcases horient with hforward | hback
      · left
        constructor
        · exact hforward.1.trans (by simpa [γ] using (A.dartArc_source d).symm)
        · exact hforward.2.trans (by simpa [γ] using (A.dartArc_target d).symm)
      · right
        constructor
        · exact hback.1.trans (by simpa [γ] using (A.dartArc_target d).symm)
        · exact hback.2.trans (by simpa [γ] using (A.dartArc_source d).symm)
    · rcases hswap with ⟨htail, hhead⟩
      subst u
      subst v
      rcases horient with hforward | hback
      · right
        constructor
        · exact hforward.1.trans (by simpa [γ] using (A.dartArc_target d).symm)
        · exact hforward.2.trans (by simpa [γ] using (A.dartArc_source d).symm)
      · left
        constructor
        · exact hback.1.trans (by simpa [γ] using (A.dartArc_source d).symm)
        · exact hback.2.trans (by simpa [γ] using (A.dartArc_target d).symm)
  have hK_compact_disjoint : IsCompact K ∧ Disjoint K γ.carrier := by
    rcases hendpoint with hsame | hrev
    · have hstored :=
        PlaneDrawingSelectedEdgeAwayFromEndpointCompact G D hD e α rfl r₀ r₁ hr₀ hr₁
      simpa [K, γ, α, hsame.1, hsame.2, hcarrier] using hstored
    · have hstored :=
        PlaneDrawingSelectedEdgeAwayFromEndpointCompact G D hD e α rfl r₁ r₀ hr₁ hr₀
      simpa [K, γ, α, hrev.1, hrev.2, hcarrier, Set.union_comm] using hstored
  by_cases hK_nonempty : K.Nonempty
  · have hγ_nonempty : γ.carrier.Nonempty := by
      have h0 : 0 < γ.vertices.length := by
        exact lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) γ.length_ge_two
      exact ⟨γ.vertices[0], PolygonalArcVertexMemCarrier γ (List.get_mem γ.vertices ⟨0, h0⟩)⟩
    obtain ⟨δ, hδpos, hδ⟩ :=
      PositiveSeparation hK_nonempty hγ_nonempty hK_compact_disjoint.1
        (PolygonalArcCarrierCompact γ) hK_compact_disjoint.2
    refine ⟨δ, hδpos, ?_⟩
    intro x hximg hxballs p hp
    exact hδ x ⟨by simpa [e] using hximg, by simpa [γ] using hxballs⟩ p
      (by simpa [γ] using hp)
  · refine ⟨1, by norm_num, ?_⟩
    intro x hximg hxballs p hp
    exfalso
    exact hK_nonempty ⟨x, by
      exact ⟨by simpa [e] using hximg, by simpa [γ] using hxballs⟩⟩
