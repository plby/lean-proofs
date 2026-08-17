import ErdosProblems.Erdos113.Incidence

open scoped SimpleGraph

namespace Erdos113AnchoredLifts

noncomputable section

open Erdos113ManyLifts Erdos113Incidence

variable {T V : Type*} [Fintype T] [DecidableEq T]
  [Fintype V] [DecidableEq V]

def anchorNeighbors {F : SimpleGraph T} {G : SimpleGraph V}
    [DecidableRel G.Adj] (L : LiftSystem F G) (v y : V) : Finset T :=
  Finset.univ.filter fun t ↦ G.Adj v (L.embed t) ∧ G.Adj (L.embed t) y

@[simp] lemma mem_anchorNeighbors {F : SimpleGraph T} {G : SimpleGraph V}
    [DecidableRel G.Adj] (L : LiftSystem F G) {v y : V} {t : T} :
    t ∈ anchorNeighbors L v y ↔
      G.Adj v (L.embed t) ∧ G.Adj (L.embed t) y := by
  simp [anchorNeighbors]

/-- A lift system whose embedded vertices all lie in the neighborhood of
one anchor.  The anchor-codegree cap controls both the right incidence
degrees and the even-coordinate single fibers. -/
structure AnchoredLiftSystem (F : SimpleGraph T) (G : SimpleGraph V)
    [DecidableRel G.Adj] extends LiftSystem F G where
  anchor : V
  leftCap : ℕ
  rightCap : ℕ
  anchor_adj : ∀ t, G.Adj anchor (toLiftSystem.embed t)
  anchor_cap : ∀ y, IsMiddleVertex toLiftSystem y →
    (anchorNeighbors toLiftSystem anchor y).card ≤ rightCap
  left_cap : ∀ t, (leftPartners toLiftSystem t).card ≤ leftCap

lemma bridgeAnchors_subset_anchorNeighbors
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : AnchoredLiftSystem F G) (u w : V) :
    bridgeAnchors A.toLiftSystem u w ⊆
      anchorNeighbors A.toLiftSystem A.anchor u := by
  intro t ht
  have htdata := (mem_bridgeAnchors A.toLiftSystem).mp ht
  rw [mem_anchorNeighbors]
  exact ⟨A.anchor_adj t, htdata.1.symm⟩

theorem bridgeAnchors_card_le
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : AnchoredLiftSystem F G) (u w : V)
    (hu : IsMiddleVertex A.toLiftSystem u) :
    (bridgeAnchors A.toLiftSystem u w).card ≤ A.rightCap :=
  (Finset.card_le_card (bridgeAnchors_subset_anchorNeighbors A u w)).trans
    (A.anchor_cap u hu)

lemma linked_mem_anchorNeighbors
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : AnchoredLiftSystem F G) {t : T} {y : V}
    (h : Linked A.toLiftSystem t y) :
    t ∈ anchorNeighbors A.toLiftSystem A.anchor y := by
  rw [mem_anchorNeighbors]
  refine ⟨A.anchor_adj t, ?_⟩
  rcases h with ⟨b, hy⟩ | ⟨a, hy⟩
  · exact A.toLiftSystem.adj_left hy
  · exact (A.toLiftSystem.adj_right hy).symm

lemma isMiddleVertex_of_linked
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : AnchoredLiftSystem F G) {t : T} {y : V}
    (h : Linked A.toLiftSystem t y) :
    IsMiddleVertex A.toLiftSystem y := by
  rcases h with ⟨b, hy⟩ | ⟨a, hy⟩
  · exact ⟨t, b, hy⟩
  · exact ⟨a, t, hy⟩

theorem rightPartners_card_le
    {F : SimpleGraph T} {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : AnchoredLiftSystem F G) (y : V) :
    (rightPartners A.toLiftSystem y).card ≤ A.rightCap := by
  by_cases hy : (rightPartners A.toLiftSystem y).Nonempty
  · obtain ⟨t₀, ht₀⟩ := hy
    have hmiddle := isMiddleVertex_of_linked A
      ((mem_rightPartners A.toLiftSystem).mp ht₀)
    calc
      (rightPartners A.toLiftSystem y).card ≤
          (anchorNeighbors A.toLiftSystem A.anchor y).card := by
        apply Finset.card_le_card
        intro t ht
        exact linked_mem_anchorNeighbors A
          ((mem_rightPartners A.toLiftSystem).mp ht)
      _ ≤ A.rightCap := A.anchor_cap y hmiddle
  · simp only [Finset.not_nonempty_iff_eq_empty] at hy
    simp [hy]

end

end Erdos113AnchoredLifts
