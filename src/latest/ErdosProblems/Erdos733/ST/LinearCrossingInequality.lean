import ErdosProblems.Erdos733.ST.CrossingNumber
import ErdosProblems.Erdos733.ST.NoAdjacentMinimalDrawing
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawingDeleteEdges
import ErdosProblems.Erdos733.ST.PlanarEdgeBound

open Classical
noncomputable section

-- [TABLET NODE: LinearCrossingInequality]
lemma LinearCrossingInequality {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    (G.edgeFinset.card : ℤ) - 3 * (Fintype.card V : ℤ) ≤
      (CrossingNumber G : ℤ) := by
-- BODY
  classical
  obtain ⟨D, hDmin, _hNoAdjacent⟩ := NoAdjacentMinimalDrawing G
  let crossingPoint := {p // p ∈ D.crossingSet}
  let chosenEdge : crossingPoint → G.edgeFinset := fun x =>
    Classical.choose ((D.crossingSet_spec x.1).mp x.2)
  have chosenEdge_spec :
      ∀ x : crossingPoint,
        ∃ e : G.edgeFinset,
          chosenEdge x ≠ e ∧
            x.1 ∈ (D.edgeArc (chosenEdge x)).relativeInterior ∧
              x.1 ∈ (D.edgeArc e).relativeInterior := by
    intro x
    exact Classical.choose_spec ((D.crossingSet_spec x.1).mp x.2)
  let S : Finset (Sym2 V) :=
    Finset.univ.image (fun x : crossingPoint => (chosenEdge x).1)
  have hS_sub : S ⊆ G.edgeFinset := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨x, _hx, rfl⟩
    exact (chosenEdge x).2
  have hS_card : S.card ≤ D.crossingSet.card := by
    calc
      S.card ≤ (Finset.univ : Finset crossingPoint).card := Finset.card_image_le
      _ = D.crossingSet.card := by simp [crossingPoint]
  obtain ⟨Ddel, hDdel_crossings, hDdel_edges⟩ :=
    OrdinaryPolygonalDrawingDeleteEdges G D S
  have hDdel_zero : Ddel.crossingSet.card = 0 := by
    apply Finset.card_eq_zero.mpr
    ext p
    constructor
    · intro hp
      rw [hDdel_crossings] at hp
      rcases Finset.mem_filter.mp hp with
        ⟨hpOld, e₁, e₂, h₁₂, he₁, he₂, hp₁, hp₂⟩
      let x : crossingPoint := ⟨p, hpOld⟩
      have hchosen_mem : (chosenEdge x).1 ∈ S := by
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
      rcases chosenEdge_spec x with ⟨e, _hchosen_ne, hpChosen, _hpE⟩
      have hchosen_eq : chosenEdge x = e₁ ∨ chosenEdge x = e₂ := by
        by_contra hne
        rw [not_or] at hne
        exact D.no_three_edge_interiors_meet
          hne.1 hne.2 h₁₂ hpChosen hp₁ hp₂
      rcases hchosen_eq with h | h
      · exact (he₁ (h ▸ hchosen_mem)).elim
      · exact (he₂ (h ▸ hchosen_mem)).elim
    · simp
  have hPlanar :
      (G.deleteEdges (S : Set (Sym2 V))).edgeFinset.card ≤
        3 * Fintype.card V :=
    PlanarEdgeBound (G.deleteEdges (S : Set (Sym2 V))) ⟨Ddel, hDdel_zero⟩
  have hS_inter : S ∩ G.edgeFinset = S := Finset.inter_eq_left.mpr hS_sub
  have hRemaining :
      (G.deleteEdges (S : Set (Sym2 V))).edgeFinset.card =
        G.edgeFinset.card - S.card := by
    simpa [hS_inter] using hDdel_edges
  have hS_edge_card : S.card ≤ G.edgeFinset.card := Finset.card_le_card hS_sub
  omega
