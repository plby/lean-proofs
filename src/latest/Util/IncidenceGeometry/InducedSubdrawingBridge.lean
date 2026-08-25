import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Mathlib.Combinatorics.SimpleGraph.Copy


open Classical
noncomputable section

lemma InducedSubdrawingBridge {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G) (S : Set V)
    [Fintype S] [Fintype (G.induce S).edgeSet] :
    ∃ DX : OrdinaryPolygonalDrawing (G.induce S),
      DX.vertexPlacement = (fun v : S => D.vertexPlacement v.1) ∧
        (∀ ed : (G.induce S).edgeFinset,
          ∃ eG : G.edgeFinset,
            eG.1 = Sym2.map (Subtype.val : S → V) ed.1 ∧
              (∀ v : V, v ∈ eG.1 → v ∈ S) ∧
              DX.edgeArc ed = D.edgeArc eG) ∧
        (∀ p : EuclideanSpace ℝ (Fin 2),
          p ∈ DX.crossingSet ↔
            ∃ e₁ e₂ : G.edgeFinset,
              e₁ ≠ e₂ ∧
                (∀ v : V, v ∈ e₁.1 → v ∈ S) ∧
                  (∀ v : V, v ∈ e₂.1 → v ∈ S) ∧
                    p ∈ (D.edgeArc e₁).relativeInterior ∧
                      p ∈ (D.edgeArc e₂).relativeInterior) ∧
          (D.adjacentEdgeCrossingCount = 0 →
            ∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄ ⦃e₁ e₂ : G.edgeFinset⦄,
              e₁ ≠ e₂ →
                p ∈ (D.edgeArc e₁).relativeInterior →
                  p ∈ (D.edgeArc e₂).relativeInterior →
                    ¬ ∃ v : V, v ∈ e₁.1 ∧ v ∈ e₂.1) := by
  classical
  let oldEdge : (G.induce S).edgeFinset → G.edgeFinset := fun ed =>
    ⟨Sym2.map (Subtype.val : S → V) ed.1, by
      exact SimpleGraph.mem_edgeFinset.mpr (by
        convert
          (SimpleGraph.Embedding.induce (G := G) S).toHom.map_mem_edgeSet
            (SimpleGraph.mem_edgeFinset.mp ed.2) using 1 <;> rfl)⟩
  have oldEdge_val :
      ∀ ed : (G.induce S).edgeFinset,
        (oldEdge ed).1 = Sym2.map (Subtype.val : S → V) ed.1 := by
    intro ed
    rfl
  have oldEdge_endpoint_mem :
      ∀ (ed : (G.induce S).edgeFinset) {u : V},
        u ∈ (oldEdge ed).1 → u ∈ S := by
    intro ed u hu
    rw [oldEdge_val ed] at hu
    rcases Sym2.mem_map.mp hu with ⟨a, _ha, rfl⟩
    exact a.2
  have oldEdge_injective : Function.Injective oldEdge := by
    intro ed₁ ed₂ h
    apply Subtype.ext
    apply Sym2.map.injective (Subtype.val_injective : Function.Injective (Subtype.val : S → V))
    simpa [oldEdge_val] using congrArg Subtype.val h
  let inducedEdge :
      (e : G.edgeFinset) → (∀ v : V, v ∈ e.1 → v ∈ S) →
        (G.induce S).edgeFinset := fun e hS =>
    let edSym : Sym2 S :=
      (e : Sym2 V).pmap (fun a ha => (⟨a, ha⟩ : S)) hS
    ⟨edSym, by
      have hedSym_map : Sym2.map (Subtype.val : S → V) edSym = e.1 := by
        rw [Sym2.pmap_subtype_map_subtypeVal]
      apply SimpleGraph.mem_edgeFinset.mpr
      exact ((SimpleGraph.Embedding.induce (G := G) S).map_mem_edgeSet_iff).mp
        (show Sym2.map (Subtype.val : S → V) edSym ∈ G.edgeSet from by
          rw [hedSym_map]
          exact SimpleGraph.mem_edgeFinset.mp e.2)⟩
  have inducedEdge_oldEdge :
      ∀ (e : G.edgeFinset) (hS : ∀ v : V, v ∈ e.1 → v ∈ S),
        oldEdge (inducedEdge e hS) = e := by
    intro e hS
    apply Subtype.ext
    change Sym2.map (Subtype.val : S → V)
        ((inducedEdge e hS : (G.induce S).edgeFinset).1) = e.1
    simp [inducedEdge, Sym2.pmap_subtype_map_subtypeVal]
  let retainedCrossingSet : Finset (EuclideanSpace ℝ (Fin 2)) :=
    D.crossingSet.filter (fun p =>
      ∃ e₁ e₂ : G.edgeFinset,
        e₁ ≠ e₂ ∧
          (∀ v : V, v ∈ e₁.1 → v ∈ S) ∧
            (∀ v : V, v ∈ e₂.1 → v ∈ S) ∧
              p ∈ (D.edgeArc e₁).relativeInterior ∧
                p ∈ (D.edgeArc e₂).relativeInterior)
  let restrictedVertexPlacement : S → EuclideanSpace ℝ (Fin 2) :=
    fun v : S => D.vertexPlacement v.1
  let restrictedEdgeArc : (G.induce S).edgeFinset → PolygonalArc :=
    fun ed => D.edgeArc (oldEdge ed)
  let retainedAdjacentCrossingSet : Finset (EuclideanSpace ℝ (Fin 2)) :=
    retainedCrossingSet.filter (fun p =>
      ∃ e₁ e₂ : (G.induce S).edgeFinset,
        e₁ ≠ e₂ ∧
          (∃ v : S, v ∈ e₁.1 ∧ v ∈ e₂.1) ∧
            p ∈ (restrictedEdgeArc e₁).relativeInterior ∧
              p ∈ (restrictedEdgeArc e₂).relativeInterior)
  let DX : OrdinaryPolygonalDrawing (G.induce S) :=
    { vertexPlacement := restrictedVertexPlacement
      vertexPlacement_injective := by
        intro x y hxy
        apply Subtype.ext
        exact D.vertexPlacement_injective hxy
      edgeArc := restrictedEdgeArc
      edgeArc_endpoints := by
        intro ed
        rcases D.edgeArc_endpoints (oldEdge ed) with ⟨a, b, hab, hedge, hends⟩
        have haS : a ∈ S := by
          exact oldEdge_endpoint_mem ed (by rw [hedge]; simp [Sym2.mem_iff])
        have hbS : b ∈ S := by
          exact oldEdge_endpoint_mem ed (by rw [hedge]; simp [Sym2.mem_iff])
        refine ⟨⟨a, haS⟩, ⟨b, hbS⟩, ?_, ?_, ?_⟩
        · simpa using hab
        · apply (Sym2.map.injective
            (Subtype.val_injective : Function.Injective (Subtype.val : S → V)))
          simpa [oldEdge_val ed] using hedge
        · simpa using hends
      crossingSet := retainedCrossingSet
      no_vertex_in_edge_interior := by
        intro v ed
        exact D.no_vertex_in_edge_interior v.1 (oldEdge ed)
      no_three_edge_interiors_meet := by
        intro ed₁ ed₂ ed₃ p h₁₂ h₁₃ h₂₃ hp₁ hp₂ hp₃
        exact D.no_three_edge_interiors_meet
          (oldEdge_injective.ne h₁₂) (oldEdge_injective.ne h₁₃)
          (oldEdge_injective.ne h₂₃) hp₁ hp₂ hp₃
      transverse_intersections := by
        intro ed₁ ed₂ p h₁₂ hp₁ hp₂
        exact D.transverse_intersections (oldEdge_injective.ne h₁₂) hp₁ hp₂
      no_shared_nondegenerate_subarc := by
        intro ed₁ ed₂ h₁₂
        exact D.no_shared_nondegenerate_subarc (oldEdge_injective.ne h₁₂)
      crossingSet_spec := by
        intro p
        constructor
        · intro hp
          have hpRetained :
              ∃ e₁ e₂ : G.edgeFinset,
                e₁ ≠ e₂ ∧
                  (∀ v : V, v ∈ e₁.1 → v ∈ S) ∧
                    (∀ v : V, v ∈ e₂.1 → v ∈ S) ∧
                      p ∈ (D.edgeArc e₁).relativeInterior ∧
                        p ∈ (D.edgeArc e₂).relativeInterior := by
            exact (Finset.mem_filter.mp hp).2
          rcases hpRetained with ⟨e₁, e₂, h₁₂, hS₁, hS₂, hp₁, hp₂⟩
          let ed₁ : (G.induce S).edgeFinset := inducedEdge e₁ hS₁
          let ed₂ : (G.induce S).edgeFinset := inducedEdge e₂ hS₂
          have hed₁_old : oldEdge ed₁ = e₁ := by
            simpa [ed₁] using inducedEdge_oldEdge e₁ hS₁
          have hed₂_old : oldEdge ed₂ = e₂ := by
            simpa [ed₂] using inducedEdge_oldEdge e₂ hS₂
          have hed₁₂ : ed₁ ≠ ed₂ := by
            intro h
            exact h₁₂ (by simpa [hed₁_old, hed₂_old] using congrArg oldEdge h)
          refine ⟨ed₁, ed₂, hed₁₂, ?_, ?_⟩
          · simpa [restrictedEdgeArc, hed₁_old] using hp₁
          · simpa [restrictedEdgeArc, hed₂_old] using hp₂
        · rintro ⟨ed₁, ed₂, h₁₂, hp₁, hp₂⟩
          have hpOld : p ∈ D.crossingSet := by
            exact (D.crossingSet_spec p).2
              ⟨oldEdge ed₁, oldEdge ed₂, oldEdge_injective.ne h₁₂,
                by simpa [restrictedEdgeArc] using hp₁,
                by simpa [restrictedEdgeArc] using hp₂⟩
          have hS₁ : ∀ v : V, v ∈ (oldEdge ed₁).1 → v ∈ S := by
            intro v hv
            exact oldEdge_endpoint_mem ed₁ hv
          have hS₂ : ∀ v : V, v ∈ (oldEdge ed₂).1 → v ∈ S := by
            intro v hv
            exact oldEdge_endpoint_mem ed₂ hv
          exact Finset.mem_filter.mpr
            ⟨hpOld, oldEdge ed₁, oldEdge ed₂, oldEdge_injective.ne h₁₂,
              hS₁, hS₂, by simpa [restrictedEdgeArc] using hp₁,
              by simpa [restrictedEdgeArc] using hp₂⟩
      adjacentEdgeCrossingCount := retainedAdjacentCrossingSet.card
      adjacentEdgeCrossingCount_eq := by
        dsimp [retainedAdjacentCrossingSet]
        simp }
  refine ⟨DX, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro ed
    exact ⟨oldEdge ed, oldEdge_val ed,
      (by
        intro v hv
        exact oldEdge_endpoint_mem ed hv),
      rfl⟩
  · intro p
    constructor
    · intro hp
      have hpRetained : p ∈ retainedCrossingSet := by
        simpa [DX] using hp
      exact (Finset.mem_filter.mp hpRetained).2
    · intro hp
      rcases hp with ⟨e₁, e₂, h₁₂, hS₁, hS₂, hp₁, hp₂⟩
      have hpOld : p ∈ D.crossingSet := by
        exact (D.crossingSet_spec p).2 ⟨e₁, e₂, h₁₂, hp₁, hp₂⟩
      have hpRetained : p ∈ retainedCrossingSet := by
        exact Finset.mem_filter.mpr
          (show p ∈ D.crossingSet ∧
              (∃ e₁ e₂ : G.edgeFinset,
                e₁ ≠ e₂ ∧
                  (∀ v : V, v ∈ e₁.1 → v ∈ S) ∧
                    (∀ v : V, v ∈ e₂.1 → v ∈ S) ∧
                      p ∈ (D.edgeArc e₁).relativeInterior ∧
                        p ∈ (D.edgeArc e₂).relativeInterior) from
            ⟨hpOld, ⟨e₁, e₂, h₁₂, hS₁, hS₂, hp₁, hp₂⟩⟩)
      simpa [DX] using hpRetained
  · intro hAdj p e₁ e₂ h₁₂ hp₁ hp₂ hCommon
    have hpCross : p ∈ D.crossingSet := by
      exact (D.crossingSet_spec p).2 ⟨e₁, e₂, h₁₂, hp₁, hp₂⟩
    let adjacentCrossings : Finset (EuclideanSpace ℝ (Fin 2)) :=
      D.crossingSet.filter (fun p =>
        ∃ e₁ e₂ : G.edgeFinset,
          e₁ ≠ e₂ ∧
            (∃ v : V, v ∈ e₁.1 ∧ v ∈ e₂.1) ∧
              p ∈ (D.edgeArc e₁).relativeInterior ∧
                p ∈ (D.edgeArc e₂).relativeInterior)
    have hcard : adjacentCrossings.card = 0 := by
      have h := D.adjacentEdgeCrossingCount_eq
      rw [hAdj] at h
      exact h.symm
    have hpAdjacent : p ∈ adjacentCrossings := by
      exact Finset.mem_filter.mpr
        ⟨hpCross, e₁, e₂, h₁₂, hCommon, hp₁, hp₂⟩
    have hEmpty : adjacentCrossings = ∅ := Finset.card_eq_zero.mp hcard
    have hpNotAdjacent : p ∉ adjacentCrossings := by
      simp [hEmpty]
    exact hpNotAdjacent hpAdjacent
