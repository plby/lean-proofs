import ErdosProblems.Erdos733.ST.EndpointDiskAffineReduction
import ErdosProblems.Erdos733.ST.EndpointUnitDiskWireConstruction

open Classical
noncomputable section

-- [TABLET NODE: EndpointFixedPolygonalDiskFillingClean]
lemma EndpointFixedPolygonalDiskFillingClean {ι : Type*} [Fintype ι]
    (c : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (hρ : 0 < ρ)
    (ha : ∀ i, dist (a i) c = ρ)
    (hb : ∀ i, dist (b i) c = ρ)
    (hdistinct : Function.Injective (fun x : ι ⊕ ι => Sum.elim a b x)) :
    ∃ Γ : ι → PolygonalArc,
      (∀ i,
        (Γ i).source = a i ∧
          (Γ i).target = b i ∧
            (Γ i).carrier ⊆ Metric.closedBall c ρ ∧
              (Γ i).relativeInterior ⊆ Metric.ball c ρ) ∧
      (∀ ⦃i j : ι⦄,
        i ≠ j →
          ¬ ∃ m n : ℕ,
            ∃ (hm : m + 1 < (Γ i).vertices.length)
              (hn : n + 1 < (Γ j).vertices.length),
              ∃ p q : EuclideanSpace ℝ (Fin 2),
                p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∩
                      segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1]) ∧
      (∀ ⦃i j k : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j → i ≠ k → j ≠ k →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              p ∈ (Γ k).relativeInterior → False) ∧
      (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              ∃ m n : ℕ,
                ∃ (hm : m + 1 < (Γ i).vertices.length)
                  (hn : n + 1 < (Γ j).vertices.length),
                  p ∈ segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∧
                    p ∈ segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1] ∧
                      ¬ ∃ t : ℝ,
                        (Γ j).vertices[n + 1] - (Γ j).vertices[n] =
                          t • ((Γ i).vertices[m + 1] - (Γ i).vertices[m])) ∧
      (∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              q ∈ (Γ i).relativeInterior →
                q ∈ (Γ j).relativeInterior →
                  p = q) ∧
      (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ (Γ i).relativeInterior →
            p ∈ (Γ j).relativeInterior →
              Nonempty (OrdinaryCleanLocalCrossing Γ i j p)) := by
-- BODY
  exact EndpointDiskAffineReduction c ρ a b hρ ha hb hdistinct
    (fun a₀ b₀ ha₀ hb₀ hdistinct₀ =>
      EndpointUnitDiskWireConstruction a₀ b₀ ha₀ hb₀ hdistinct₀)
