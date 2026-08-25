import Mathlib.Tactic
import Util.IncidenceGeometry.PlaneDrawingDartArcData
import Util.IncidenceGeometry.PolygonalArcSourceEndpointRayCover

open Classical
noncomputable section

lemma PlaneDrawingDartSourceEndpointRayCovers {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D) :
    ∃ sourceRayRadius :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} → ℝ,
      (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        0 < sourceRayRadius v d) ∧
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        let γ := A.dartArc d.1
        let hfirst : 1 < γ.vertices.length :=
          Nat.lt_of_succ_le γ.length_ge_two
        Metric.ball (D.vertexPlacement v) (sourceRayRadius v d) ∩
            (D.edgeArc (A.dartEdge d.1)).carrier ⊆
          {x | ∃ c : ℝ, 0 ≤ c ∧
            x = D.vertexPlacement v +
              c • (γ.vertices[1]'hfirst - D.vertexPlacement v)} := by
  classical
  let sourceRayRadius :
      ∀ v : V, {d : G.Dart // d.toProd.1 = v} → ℝ :=
    fun _ d => Classical.choose (PolygonalArcSourceEndpointRayCover (A.dartArc d.1))
  refine ⟨sourceRayRadius, ?_, ?_⟩
  · intro v d
    dsimp [sourceRayRadius]
    exact (Classical.choose_spec
      (PolygonalArcSourceEndpointRayCover (A.dartArc d.1))).1
  · intro v d
    dsimp
    intro x hx
    let γ : PolygonalArc := A.dartArc d.1
    have hsource : γ.source = D.vertexPlacement v := by
      simpa [γ, d.2] using A.dartArc_source d.1
    have hcarrier : γ.carrier = (D.edgeArc (A.dartEdge d.1)).carrier := by
      simpa [γ] using A.dartArc_carrier d.1
    have hxγ :
        x ∈ Metric.ball γ.source (sourceRayRadius v d) ∩ γ.carrier := by
      constructor
      · simpa [hsource] using hx.1
      · simpa [hcarrier] using hx.2
    have hcover :=
      (Classical.choose_spec
        (PolygonalArcSourceEndpointRayCover (A.dartArc d.1))).2
    rcases hcover hxγ with ⟨c, hc, hx_eq⟩
    refine ⟨c, hc, ?_⟩
    simpa [γ, hsource] using hx_eq
