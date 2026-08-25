import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

structure GeometricArcDrawing {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] where
  vertexPlacement : V → EuclideanSpace ℝ (Fin 2)
  vertexPlacement_injective : Function.Injective vertexPlacement
  edgeSource : G.edgeFinset → EuclideanSpace ℝ (Fin 2)
  edgeTarget : G.edgeFinset → EuclideanSpace ℝ (Fin 2)
  edgeCarrier : G.edgeFinset → Set (EuclideanSpace ℝ (Fin 2))
  edgeRelativeInterior : G.edgeFinset → Set (EuclideanSpace ℝ (Fin 2))
  edgeArc_endpoints :
    ∀ e : G.edgeFinset,
      ∃ u v : V,
        G.Adj u v ∧ e.1 = Sym2.mk u v ∧
          (((edgeSource e = vertexPlacement u ∧
              edgeTarget e = vertexPlacement v) ∨
            (edgeSource e = vertexPlacement v ∧
              edgeTarget e = vertexPlacement u)))
  edge_is_simple_lineSegment_or_circularArc :
    ∀ e : G.edgeFinset,
      ((edgeSource e ≠ edgeTarget e) ∧
        edgeCarrier e = segment ℝ (edgeSource e) (edgeTarget e) ∧
        edgeRelativeInterior e = openSegment ℝ (edgeSource e) (edgeTarget e)) ∨
      (∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
          (γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)),
        0 < r ∧
          Continuous γ ∧ Function.Injective γ ∧
          (∀ t, dist (γ t) c = r) ∧
          γ ⟨0, by simp⟩ = edgeSource e ∧
          γ ⟨1, by simp⟩ = edgeTarget e ∧
          edgeCarrier e = Set.range γ ∧
          edgeRelativeInterior e =
            Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
              γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩))
  no_vertex_in_edge_interior :
    ∀ (v : V) (e : G.edgeFinset),
      vertexPlacement v ∉ edgeRelativeInterior e
  no_shared_nondegenerate_subarc :
    ∀ ⦃e₁ e₂ : G.edgeFinset⦄,
      e₁ ≠ e₂ →
        ¬ ∃ γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
          Continuous γ ∧ Function.Injective γ ∧
            γ ⟨0, by simp⟩ ≠ γ ⟨1, by simp⟩ ∧
              Set.range γ ⊆ edgeCarrier e₁ ∩ edgeCarrier e₂
  intersectionPoints : Finset (EuclideanSpace ℝ (Fin 2))
  intersectionPoints_spec :
    ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ intersectionPoints ↔
        ∃ e₁ e₂ : G.edgeFinset,
          e₁ ≠ e₂ ∧
            p ∈ edgeRelativeInterior e₁ ∧
              p ∈ edgeRelativeInterior e₂
  localPairCount : ℕ
  localPairCount_eq :
    localPairCount =
      intersectionPoints.sum (fun p =>
        Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
          (fun e => p ∈ edgeRelativeInterior e)).card) 2)
