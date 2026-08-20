import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryDrawingImageCompact]
lemma OrdinaryDrawingImageCompact {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G) :
    IsCompact (OrdinaryDrawingImage G D) := by
-- BODY
  have hArc : ∀ γ : PolygonalArc, IsCompact γ.carrier := by
    intro γ
    rw [γ.carrier_eq]
    let segSet : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun i =>
      if h : i + 1 < γ.vertices.length then
        segment ℝ γ.vertices[i] γ.vertices[i + 1]
      else
        ∅
    have h_eq :
        {p | ∃ i : ℕ, ∃ hi : i + 1 < γ.vertices.length,
          p ∈ segment ℝ γ.vertices[i] γ.vertices[i + 1]} =
          ⋃ i ∈ Finset.range γ.vertices.length, segSet i := by
      ext p
      constructor
      · rintro ⟨i, hi, hp⟩
        refine Set.mem_iUnion.2 ⟨i, ?_⟩
        refine Set.mem_iUnion.2 ⟨Finset.mem_range.2 (Nat.lt_of_succ_lt hi), ?_⟩
        simp [segSet, hi, hp]
      · intro hp
        rcases Set.mem_iUnion.1 hp with ⟨i, hp⟩
        rcases Set.mem_iUnion.1 hp with ⟨_, hp⟩
        by_cases hi : i + 1 < γ.vertices.length
        · exact ⟨i, hi, by simpa [segSet, hi] using hp⟩
        · simp [segSet, hi] at hp
    rw [h_eq]
    exact Finset.isCompact_biUnion (Finset.range γ.vertices.length) (fun i _ => by
      by_cases hi : i + 1 < γ.vertices.length
      · simp [segSet, hi]
        rw [segment_eq_image]
        exact isCompact_Icc.image (by fun_prop)
      · simp [segSet, hi])
  rw [OrdinaryDrawingImage]
  exact IsCompact.union
    (Set.Finite.isCompact (Set.finite_range D.vertexPlacement))
    (isCompact_iUnion (fun e : G.edgeFinset => hArc (D.edgeArc e)))
