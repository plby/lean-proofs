import ErdosProblems.Erdos182.Roof
import ErdosProblems.Erdos182.MultiCompletion
import ErdosProblems.Erdos182.TopColors

/-!
# Exact bipartite degree thinning

Kőnig's line-colouring theorem decomposes a finite bipartite graph of
maximum degree `D` into `D` matchings.  Keeping the `T` largest colour
classes gives a subgraph of maximum degree at most `T` containing at least
the `T / D` fraction of all edges.  This file packages that consequence for
the two-sorted bipartite graphs used in the proof of Erdős Problem 182.
-/

open scoped Classical

namespace Erdos182
namespace BipartiteGraph

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The labelled edge type of a simple two-sorted bipartite graph. -/
def EdgeType (G : BipartiteGraph A B) := {p : A × B // G.Adj p.1 p.2}

instance (G : BipartiteGraph A B) : Finite G.EdgeType :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance (G : BipartiteGraph A B) : Fintype G.EdgeType :=
  Fintype.ofFinite G.EdgeType

/-- Regard the edges of a simple bipartite graph as a bipartite multigraph. -/
def edgeMultigraph (G : BipartiteGraph A B) :
    BipartiteMultigraph A B G.EdgeType where
  left e := e.1.1
  right e := e.1.2

private def edgeTypeEquivSigmaLeftNeighbors (G : BipartiteGraph A B) :
    G.EdgeType ≃ Σ b : B, {a // a ∈ G.leftNeighbors b} where
  toFun e := ⟨e.1.2, ⟨e.1.1, G.mem_leftNeighbors _ _ |>.mpr e.2⟩⟩
  invFun e := ⟨(e.2.1, e.1), G.mem_leftNeighbors _ _ |>.mp e.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem edgeCount_eq_card_edgeType (G : BipartiteGraph A B) :
    G.edgeCount = Fintype.card G.EdgeType := by
  rw [Fintype.card_congr G.edgeTypeEquivSigmaLeftNeighbors,
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  exact (Fintype.card_coe (G.leftNeighbors b)).symm

private def edgeMultigraphLeftFiberEquiv (G : BipartiteGraph A B) (a : A) :
    {e : G.EdgeType // G.edgeMultigraph.left e = a} ≃
      {b // b ∈ G.rightNeighbors a} where
  toFun e := by
    rcases e with ⟨⟨⟨a', b⟩, hab⟩, ha⟩
    change a' = a at ha
    subst a'
    exact ⟨b, G.mem_rightNeighbors _ _ |>.mpr hab⟩
  invFun b := ⟨⟨(a, b.1), G.mem_rightNeighbors _ _ |>.mp b.2⟩, rfl⟩
  left_inv e := by
    rcases e with ⟨⟨⟨a', b⟩, hab⟩, ha⟩
    cases ha
    rfl
  right_inv _ := rfl

private def edgeMultigraphRightFiberEquiv (G : BipartiteGraph A B) (b : B) :
    {e : G.EdgeType // G.edgeMultigraph.right e = b} ≃
      {a // a ∈ G.leftNeighbors b} where
  toFun e := by
    rcases e with ⟨⟨⟨a, b'⟩, hab⟩, hb⟩
    change b' = b at hb
    subst b'
    exact ⟨a, G.mem_leftNeighbors _ _ |>.mpr hab⟩
  invFun a := ⟨⟨(a.1, b), G.mem_leftNeighbors _ _ |>.mp a.2⟩, rfl⟩
  left_inv e := by
    rcases e with ⟨⟨⟨a, b'⟩, hab⟩, hb⟩
    cases hb
    rfl
  right_inv _ := rfl

private theorem edgeMultigraph_left_card (G : BipartiteGraph A B) (a : A) :
    Fintype.card {e : G.EdgeType // G.edgeMultigraph.left e = a} =
      G.leftDegree a := by
  rw [Fintype.card_congr (G.edgeMultigraphLeftFiberEquiv a), leftDegree,
    Fintype.card_coe]

private theorem edgeMultigraph_right_card (G : BipartiteGraph A B) (b : B) :
    Fintype.card {e : G.EdgeType // G.edgeMultigraph.right e = b} =
      G.rightDegree b := by
  rw [Fintype.card_congr (G.edgeMultigraphRightFiberEquiv b), rightDegree,
    Fintype.card_coe]

/-- The union of the colour classes in `S`. -/
noncomputable def colorSubgraph (G : BipartiteGraph A B) {D : ℕ}
    (C : G.edgeMultigraph.ProperColoring D) (S : Finset (Fin D)) :
    BipartiteGraph A B where
  Adj a b := ∃ h : G.Adj a b, C.color ⟨(a, b), h⟩ ∈ S

private theorem colorSubgraph_le (G : BipartiteGraph A B) {D : ℕ}
    (C : G.edgeMultigraph.ProperColoring D) (S : Finset (Fin D)) :
    G.colorSubgraph C S ≤ G := by
  intro a b h
  exact h.choose

private def colorSubgraphEdgeEquiv (G : BipartiteGraph A B) {D : ℕ}
    (C : G.edgeMultigraph.ProperColoring D) (S : Finset (Fin D)) :
    (G.colorSubgraph C S).EdgeType ≃ {e : G.EdgeType // C.color e ∈ S} where
  toFun e :=
    ⟨⟨e.1, e.2.choose⟩, e.2.choose_spec⟩
  invFun e :=
    ⟨e.1.1, ⟨e.1.2, e.2⟩⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private theorem colorSubgraph_edgeCount (G : BipartiteGraph A B) {D : ℕ}
    (C : G.edgeMultigraph.ProperColoring D) (S : Finset (Fin D)) :
    (G.colorSubgraph C S).edgeCount =
      (Finset.univ.filter fun e : G.EdgeType ↦ C.color e ∈ S).card := by
  rw [edgeCount_eq_card_edgeType,
    Fintype.card_congr (G.colorSubgraphEdgeEquiv C S)]
  exact Fintype.card_of_subtype
    (p := fun e : G.EdgeType ↦ C.color e ∈ S)
    (Finset.univ.filter fun e : G.EdgeType ↦ C.color e ∈ S) (by simp)

private theorem colorSubgraph_leftDegree_le (G : BipartiteGraph A B) {D : ℕ}
    (C : G.edgeMultigraph.ProperColoring D) (S : Finset (Fin D)) (a : A) :
    (G.colorSubgraph C S).leftDegree a ≤ S.card := by
  classical
  let H := G.colorSubgraph C S
  let f : {b // b ∈ H.rightNeighbors a} → {i // i ∈ S} := fun b ↦ by
    have hH : H.Adj a b.1 := H.mem_rightNeighbors a b.1 |>.mp b.2
    exact ⟨C.color ⟨(a, b.1), hH.choose⟩, hH.choose_spec⟩
  have hf : Function.Injective f := by
    intro b₁ b₂ hb
    apply Subtype.ext
    have hH₁ : H.Adj a b₁.1 := H.mem_rightNeighbors a b₁.1 |>.mp b₁.2
    have hH₂ : H.Adj a b₂.1 := H.mem_rightNeighbors a b₂.1 |>.mp b₂.2
    have hc : C.color ⟨(a, b₁.1), hH₁.choose⟩ =
        C.color ⟨(a, b₂.1), hH₂.choose⟩ := congrArg Subtype.val hb
    have he := C.left_injective a
      (a₁ := ⟨⟨(a, b₁.1), hH₁.choose⟩, rfl⟩)
      (a₂ := ⟨⟨(a, b₂.1), hH₂.choose⟩, rfl⟩) hc
    exact congrArg (fun e ↦ e.1.1.2) he
  simpa only [H, leftDegree, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

private theorem colorSubgraph_rightDegree_le (G : BipartiteGraph A B) {D : ℕ}
    (C : G.edgeMultigraph.ProperColoring D) (S : Finset (Fin D)) (b : B) :
    (G.colorSubgraph C S).rightDegree b ≤ S.card := by
  classical
  let H := G.colorSubgraph C S
  let f : {a // a ∈ H.leftNeighbors b} → {i // i ∈ S} := fun a ↦ by
    have hH : H.Adj a.1 b := H.mem_leftNeighbors a.1 b |>.mp a.2
    exact ⟨C.color ⟨(a.1, b), hH.choose⟩, hH.choose_spec⟩
  have hf : Function.Injective f := by
    intro a₁ a₂ ha
    apply Subtype.ext
    have hH₁ : H.Adj a₁.1 b := H.mem_leftNeighbors a₁.1 b |>.mp a₁.2
    have hH₂ : H.Adj a₂.1 b := H.mem_leftNeighbors a₂.1 b |>.mp a₂.2
    have hc : C.color ⟨(a₁.1, b), hH₁.choose⟩ =
        C.color ⟨(a₂.1, b), hH₂.choose⟩ := congrArg Subtype.val ha
    have he := C.right_injective b
      (a₁ := ⟨⟨(a₁.1, b), hH₁.choose⟩, rfl⟩)
      (a₂ := ⟨⟨(a₂.1, b), hH₂.choose⟩, rfl⟩) hc
    exact congrArg (fun e ↦ e.1.1.1) he
  simpa only [H, rightDegree, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

/-- Exact bipartite thinning: a graph of maximum degree at most `D` has a
subgraph of maximum degree at most `T` retaining at least a `T / D` fraction
of its edges. -/
theorem exists_bipartite_thinning (G : BipartiteGraph A B) {D T : ℕ}
    (hleft : ∀ a, G.leftDegree a ≤ D)
    (hright : ∀ b, G.rightDegree b ≤ D) (hT : T ≤ D) :
    ∃ H : BipartiteGraph A B,
      H ≤ G ∧
      (∀ a, H.leftDegree a ≤ T) ∧
      (∀ b, H.rightDegree b ≤ T) ∧
      T * G.edgeCount ≤ D * H.edgeCount := by
  classical
  have hmleft : ∀ a,
      Fintype.card {e : G.EdgeType // G.edgeMultigraph.left e = a} ≤ D := by
    intro a
    simpa only [G.edgeMultigraph_left_card a] using hleft a
  have hmright : ∀ b,
      Fintype.card {e : G.EdgeType // G.edgeMultigraph.right e = b} ≤ D := by
    intro b
    simpa only [G.edgeMultigraph_right_card b] using hright b
  obtain ⟨C⟩ := G.edgeMultigraph.exists_properColoring_of_degree_le D hmleft hmright
  let w : Fin D → ℕ := fun i ↦
    (Finset.univ.filter fun e : G.EdgeType ↦ C.color e = i).card
  obtain ⟨S, hScard, hSweight⟩ :=
    exists_top_colors w T (by simpa using hT)
  let H := G.colorSubgraph C S
  refine ⟨H, G.colorSubgraph_le C S, ?_, ?_, ?_⟩
  · intro a
    simpa only [H, hScard] using G.colorSubgraph_leftDegree_le C S a
  · intro b
    simpa only [H, hScard] using G.colorSubgraph_rightDegree_le C S b
  · have htotal : (∑ i, w i) = G.edgeCount := by
      calc
        (∑ i, w i) =
            (Finset.univ.filter fun e : G.EdgeType ↦ C.color e ∈ Finset.univ).card := by
              simpa only [w] using Finset.sum_card_fiberwise_eq_card_filter
                (s := (Finset.univ : Finset G.EdgeType))
                (t := (Finset.univ : Finset (Fin D))) (g := C.color)
        _ = Fintype.card G.EdgeType := by simp
        _ = G.edgeCount := (G.edgeCount_eq_card_edgeType).symm
    have hselected : (∑ i ∈ S, w i) =
        (Finset.univ.filter fun e : G.EdgeType ↦ C.color e ∈ S).card := by
      simpa only [w] using Finset.sum_card_fiberwise_eq_card_filter
        (s := (Finset.univ : Finset G.EdgeType)) (t := S) (g := C.color)
    rw [htotal, hselected, ← G.colorSubgraph_edgeCount C S] at hSweight
    simpa only [Fintype.card_fin, H] using hSweight

end BipartiteGraph
end Erdos182
