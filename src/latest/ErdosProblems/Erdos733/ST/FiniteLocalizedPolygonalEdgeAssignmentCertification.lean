import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArcNoSharedSubarcTransverse

open Classical
noncomputable section

-- [TABLET NODE: FiniteLocalizedPolygonalEdgeAssignmentCertification]
lemma FiniteLocalizedPolygonalEdgeAssignmentCertification
    {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (edgeArc : G.edgeFinset → PolygonalArc)
    (candidate : Finset (EuclideanSpace ℝ (Fin 2)))
    (hlocalized :
      ∀ p : EuclideanSpace ℝ (Fin 2),
        (∃ e₁ e₂ : G.edgeFinset,
          e₁ ≠ e₂ ∧
            p ∈ (edgeArc e₁).relativeInterior ∧
              p ∈ (edgeArc e₂).relativeInterior) →
          p ∈ candidate) :
    ∃ crossingSet : Finset (EuclideanSpace ℝ (Fin 2)),
      crossingSet ⊆ candidate ∧
        (∀ p : EuclideanSpace ℝ (Fin 2),
          p ∈ crossingSet ↔
            ∃ e₁ e₂ : G.edgeFinset,
              e₁ ≠ e₂ ∧
                p ∈ (edgeArc e₁).relativeInterior ∧
                  p ∈ (edgeArc e₂).relativeInterior) ∧
          (∀ ⦃e₁ e₂ : G.edgeFinset⦄
            ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            e₁ ≠ e₂ →
              p ∈ (edgeArc e₁).relativeInterior →
                p ∈ (edgeArc e₂).relativeInterior →
                  ∃ i j : ℕ,
                    ∃ (hi : i + 1 < (edgeArc e₁).vertices.length)
                      (hj : j + 1 < (edgeArc e₂).vertices.length),
                      p ∈ segment ℝ (edgeArc e₁).vertices[i]
                          (edgeArc e₁).vertices[i + 1] ∧
                        p ∈ segment ℝ (edgeArc e₂).vertices[j]
                            (edgeArc e₂).vertices[j + 1] ∧
                          ¬ ∃ c : ℝ,
                            (edgeArc e₂).vertices[j + 1] -
                                (edgeArc e₂).vertices[j] =
                              c • ((edgeArc e₁).vertices[i + 1] -
                                (edgeArc e₁).vertices[i])) ∧
            ∀ ⦃e₁ e₂ : G.edgeFinset⦄,
              e₁ ≠ e₂ →
                ¬ ∃ i j : ℕ,
                  ∃ (hi : i + 1 < (edgeArc e₁).vertices.length)
                    (hj : j + 1 < (edgeArc e₂).vertices.length),
                    ∃ p q : EuclideanSpace ℝ (Fin 2),
                      p ≠ q ∧
                        segment ℝ p q ⊆
                          segment ℝ (edgeArc e₁).vertices[i]
                              (edgeArc e₁).vertices[i + 1] ∩
                            segment ℝ (edgeArc e₂).vertices[j]
                              (edgeArc e₂).vertices[j + 1] := by
-- BODY
  let crossingSet := candidate.filter (fun p =>
    ∃ e₁ e₂ : G.edgeFinset,
      e₁ ≠ e₂ ∧
        p ∈ (edgeArc e₁).relativeInterior ∧
          p ∈ (edgeArc e₂).relativeInterior)
  have hspec : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ crossingSet ↔
        ∃ e₁ e₂ : G.edgeFinset,
          e₁ ≠ e₂ ∧
            p ∈ (edgeArc e₁).relativeInterior ∧
              p ∈ (edgeArc e₂).relativeInterior := by
    intro p
    constructor
    · intro hp
      simpa [crossingSet] using (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hlocalized p hp, hp⟩
  have hNoShared : ∀ ⦃e₁ e₂ : G.edgeFinset⦄,
      e₁ ≠ e₂ →
        ¬ ∃ i j : ℕ,
          ∃ (hi : i + 1 < (edgeArc e₁).vertices.length)
            (hj : j + 1 < (edgeArc e₂).vertices.length),
            ∃ p q : EuclideanSpace ℝ (Fin 2),
              p ≠ q ∧
                segment ℝ p q ⊆
                  segment ℝ (edgeArc e₁).vertices[i]
                      (edgeArc e₁).vertices[i + 1] ∩
                    segment ℝ (edgeArc e₂).vertices[j]
                      (edgeArc e₂).vertices[j + 1] := by
    intro e₁ e₂ he₁₂ hcommon
    rcases hcommon with ⟨i, j, hi, hj, p, q, hpq, hsubset⟩
    let forbidden : Finset (EuclideanSpace ℝ (Fin 2)) :=
      crossingSet ∪
        {(edgeArc e₁).source, (edgeArc e₁).target,
          (edgeArc e₂).source, (edgeArc e₂).target}
    let f : ℝ → EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap p q
    have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hpq
    let bad : Set ℝ := f ⁻¹' (forbidden : Set (EuclideanSpace ℝ (Fin 2)))
    have hbadFinite : bad.Finite :=
      forbidden.finite_toSet.preimage (fun a _ b _ hab => hf hab)
    have hgood : (Set.Ioo (0 : ℝ) 1 \ bad).Infinite :=
      (Set.Ioo_infinite zero_lt_one).diff hbadFinite
    rcases hgood.nonempty with ⟨t, htIoo, htbad⟩
    let z := f t
    have hzopen : z ∈ openSegment ℝ p q :=
      lineMap_mem_openSegment ℝ p q htIoo
    have hzseg : z ∈ segment ℝ p q :=
      openSegment_subset_segment ℝ p q hzopen
    have hzEdges := hsubset hzseg
    have hzCarrier1 : z ∈ (edgeArc e₁).carrier := by
      rw [(edgeArc e₁).carrier_eq]
      exact ⟨i, hi, hzEdges.1⟩
    have hzCarrier2 : z ∈ (edgeArc e₂).carrier := by
      rw [(edgeArc e₂).carrier_eq]
      exact ⟨j, hj, hzEdges.2⟩
    have hzNotForbidden : z ∉ forbidden := htbad
    have hzNotCrossing : z ∉ crossingSet := by
      intro hzCrossing
      exact hzNotForbidden (by simp [forbidden, hzCrossing])
    have hzNotEnd1 :
        z ∉ ({(edgeArc e₁).source, (edgeArc e₁).target} : Set _) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hz
        exact hzNotForbidden (by simp [forbidden, hz])
      · intro hz
        exact hzNotForbidden (by simp [forbidden, hz])
    have hzNotEnd2 :
        z ∉ ({(edgeArc e₂).source, (edgeArc e₂).target} : Set _) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hz
        exact hzNotForbidden (by simp [forbidden, hz])
      · intro hz
        exact hzNotForbidden (by simp [forbidden, hz])
    apply hzNotCrossing
    rw [hspec]
    refine ⟨e₁, e₂, he₁₂, ?_, ?_⟩
    · rw [(edgeArc e₁).relativeInterior_eq]
      exact ⟨hzCarrier1, hzNotEnd1⟩
    · rw [(edgeArc e₂).relativeInterior_eq]
      exact ⟨hzCarrier2, hzNotEnd2⟩
  have hTransverse : ∀ ⦃e₁ e₂ : G.edgeFinset⦄
      ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e₁ ≠ e₂ →
        p ∈ (edgeArc e₁).relativeInterior →
          p ∈ (edgeArc e₂).relativeInterior →
            ∃ i j : ℕ,
              ∃ (hi : i + 1 < (edgeArc e₁).vertices.length)
                (hj : j + 1 < (edgeArc e₂).vertices.length),
                p ∈ segment ℝ (edgeArc e₁).vertices[i]
                    (edgeArc e₁).vertices[i + 1] ∧
                  p ∈ segment ℝ (edgeArc e₂).vertices[j]
                      (edgeArc e₂).vertices[j + 1] ∧
                    ¬ ∃ c : ℝ,
                      (edgeArc e₂).vertices[j + 1] -
                          (edgeArc e₂).vertices[j] =
                        c • ((edgeArc e₁).vertices[i + 1] -
                          (edgeArc e₁).vertices[i]) := by
    intro e₁ e₂ p he hp1 hp2
    exact PolygonalArcNoSharedSubarcTransverse (edgeArc e₁) (edgeArc e₂)
      (hNoShared he) p hp1 hp2
  refine ⟨crossingSet, ?_, hspec, hTransverse, hNoShared⟩
  intro p hp
  exact (Finset.mem_filter.mp hp).1
