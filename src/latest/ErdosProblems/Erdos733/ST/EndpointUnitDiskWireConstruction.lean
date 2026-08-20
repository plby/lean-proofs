import ErdosProblems.Erdos733.ST.EndpointUnitDiskAssemblyFromLocalReplacements
import ErdosProblems.Erdos733.ST.EndpointUnitDiskLocalReplacement
import ErdosProblems.Erdos733.ST.EndpointRectangularWireReplacement
import ErdosProblems.Erdos733.ST.EndpointUnitMultiplePointDisks

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitDiskWireConstruction]
lemma EndpointUnitDiskWireConstruction {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (ha : ∀ i, dist (a i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hb : ∀ i, dist (b i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hdistinct : Function.Injective (fun x : ι ⊕ ι => Sum.elim a b x)) :
    ∃ Γ : ι → PolygonalArc,
      (∀ i,
        (Γ i).source = a i ∧
          (Γ i).target = b i ∧
            (Γ i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
              (Γ i).relativeInterior ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
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
  have hChord := EndpointUnitChordMultiplePointControl a b ha hb hdistinct
  have hDisks := EndpointUnitMultiplePointDisks a b ha hb hdistinct
  rcases hDisks with
    ⟨T, r, hT, hrpos, hclosed, hdisjoint, hmiss, hpairOnly, _hdiam⟩
  have hlocal : ∀ z, z ∈ T →
      let κ := {i : ι // z ∈ openSegment ℝ (a i) (b i)}
      ∃ u v : κ → EuclideanSpace ℝ (Fin 2),
        ∃ Ξ : κ → PolygonalArc,
          (∀ i : κ,
            u i ∈ Metric.sphere z (r z) ∧
              v i ∈ Metric.sphere z (r z) ∧
                u i ∈ openSegment ℝ (a i.1) z ∧
                  v i ∈ openSegment ℝ z (b i.1) ∧
                    Metric.closedBall z (r z) ∩ segment ℝ (a i.1) (b i.1) =
                      segment ℝ (u i) (v i)) ∧
            (∀ i : κ,
              (Ξ i).source = u i ∧
                (Ξ i).target = v i ∧
                  (Ξ i).carrier ⊆ Metric.closedBall z (r z) ∧
                    (Ξ i).relativeInterior ⊆ Metric.ball z (r z)) ∧
              (∀ ⦃i j : κ⦄,
                i ≠ j →
                  ¬ ∃ m n : ℕ,
                    ∃ (hm : m + 1 < (Ξ i).vertices.length)
                      (hn : n + 1 < (Ξ j).vertices.length),
                      ∃ p q : EuclideanSpace ℝ (Fin 2),
                        p ≠ q ∧
                          segment ℝ p q ⊆
                            segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∩
                              segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1]) ∧
                (∀ ⦃i j k : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                  i ≠ j → i ≠ k → j ≠ k →
                    p ∈ (Ξ i).relativeInterior →
                      p ∈ (Ξ j).relativeInterior →
                        p ∈ (Ξ k).relativeInterior → False) ∧
                  (∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                    i ≠ j →
                      p ∈ (Ξ i).relativeInterior →
                        p ∈ (Ξ j).relativeInterior →
                          ∃ m n : ℕ,
                            ∃ (hm : m + 1 < (Ξ i).vertices.length)
                              (hn : n + 1 < (Ξ j).vertices.length),
                              p ∈ segment ℝ (Ξ i).vertices[m] (Ξ i).vertices[m + 1] ∧
                                p ∈ segment ℝ (Ξ j).vertices[n] (Ξ j).vertices[n + 1] ∧
                                  ¬ ∃ t : ℝ,
                                    (Ξ j).vertices[n + 1] - (Ξ j).vertices[n] =
                                      t • ((Ξ i).vertices[m + 1] -
                                        (Ξ i).vertices[m])) ∧
                    (∀ ⦃i j : κ⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
                      i ≠ j →
                        p ∈ (Ξ i).relativeInterior →
                          p ∈ (Ξ j).relativeInterior →
                            q ∈ (Ξ i).relativeInterior →
                              q ∈ (Ξ j).relativeInterior →
                                p = q) ∧
                    (∀ ⦃i j : κ⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                      i ≠ j →
                        p ∈ (Ξ i).relativeInterior →
                          p ∈ (Ξ j).relativeInterior →
                            Nonempty (OrdinaryCleanLocalCrossing Ξ i j p)) := by
    intro z hzT
    exact EndpointUnitDiskLocalReplacement a b ha hb hdistinct z (r z)
      ((hT z).mp hzT).1 (hrpos z hzT) (hclosed z hzT)
  exact EndpointUnitDiskAssemblyFromLocalReplacements a b ha hb hdistinct
    T r hT hrpos hclosed hdisjoint hmiss hpairOnly hlocal
