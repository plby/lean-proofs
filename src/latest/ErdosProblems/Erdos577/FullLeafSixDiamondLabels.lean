import ErdosProblems.Erdos577.FullLeafSixSecondLabels

/-! The surviving adjacent row has an actual labeling of a single-diagonal block. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.six_diamond_labels (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (ht : G.IsNClique 3 (FullLeafEquality.matchedSecond p s a y))
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (height : contacts G (s.erase y) q.support = 8)
    (hfour : contacts G (FullLeafEquality.matchedSecond p s a y) q.support = 4)
    {u : V} (hu : u ∈ s.erase y) (hrow : 3 ≤ degreeIn G u q.support) :
    ∃ v ∈ FullLeafEquality.matchedSecond p s a y, ∃ w : Quadrilateral G,
      w.support = q.support ∧ (∀ i : Fin 4, G.Adj v (w i) ↔ i = 0 ∨ i = 1) ∧
      G.Adj (w 0) (w 2) ∧ ¬G.Adj (w 1) (w 3) := by
  obtain ⟨v, hv, w, hw, hlabels⟩ :=
    h.six_adjacent_second_labels hcard hn ht q hj hjs hja height hfour hu hrow
  have hnot : ¬G.IsNClique 4 w.support := by
    intro hcl
    let e : Fin 4 ↪ Fin 4 := (Equiv.swap 1 2).toEmbedding
    let r := w.relabelOfClique hcl e
    have hr : r.support = q.support := (w.relabelOfClique_support hcl e).trans hw
    apply h.six_opposite_false hcard hn ht r (by rwa [hr]) (by rwa [hr])
      (by rwa [hr]) (by rwa [hr]) (by rwa [hr]) hu (by rwa [hr]) hv
    · simpa [r, e, Equiv.swap_apply_def] using (hlabels 0).mpr (Or.inl rfl)
    · simpa [r, e] using (hlabels 1).mpr (Or.inr rfl)
  have hupper : edgeCount G w.support ≤ 5 := by
    have hb := edgeCount_le_six G w.card_support
    by_contra hh
    exact hnot (clique_of_four_six w.card_support (by omega))
  have hlower := h.first_high_edges hj hjs (mem_insert_of_mem (mem_erase.mp hu).2) hrow
  have hfive : edgeCount G w.support = 5 := by rw [hw] at hupper ⊢; omega
  obtain ⟨r, hr, hrowr, hdiag, hmissing⟩ :=
    FullLeafHeavy.adjacent_diamond_labels w v hlabels hfive
  exact ⟨v, hv, r, hr.trans hw, hrowr, hdiag, hmissing⟩

end Erdos577.FullLeafCore
