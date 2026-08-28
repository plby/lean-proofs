import ErdosProblems.Erdos577.FullLeafHeavyOpposite

/-! Normalize a two-contact first row and the heavier opposite pair in the adjacent branch. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma adjacent_labels_heavy_opposite (q : Quadrilateral G) (t : Finset V) (x : V)
    (hrow : ∀ i : Fin 4, G.Adj x (q i) ↔ i = 0 ∨ i = 1)
    (hcontacts : 11 ≤ contacts G t q.support) :
    ∃ v : Quadrilateral G, v.support = q.support ∧
      (∀ i : Fin 4, G.Adj x (v i) ↔ i = 0 ∨ i = 1) ∧
      6 ≤ degreeIn G (v 0) t + degreeIn G (v 2) t := by
  by_cases hpair : 6 ≤ degreeIn G (q 0) t + degreeIn G (q 2) t
  · exact ⟨q, rfl, hrow, hpair⟩
  · have hsum := columns_sum q t
    refine ⟨(q.rotate 1).reverse, (q.rotate 1).reverse_support.trans (q.rotate_support 1), ?_, ?_⟩
    · intro i
      rw [Quadrilateral.reverse_apply, Quadrilateral.rotate_apply, hrow]
      fin_cases i <;> decide
    · change 6 ≤ degreeIn G (q 1) t + degreeIn G (q 3) t
      omega

end Erdos577.FullLeafHeavy

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.second_contacts_ge_eleven {j : Finset V}
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x j ≤ 2) :
    11 ≤ contacts G (insert (p.vertices 3) a) j := by
  have hs : contacts G (insert p.leaf s) j ≤ 10 := by
    calc
      contacts G (insert p.leaf s) j ≤ ∑ _ ∈ insert p.leaf s, (2 : ℕ) :=
        sum_le_sum hrows
      _ = 10 := by simp only [sum_const, smul_eq_mul, h.first_five_clique.card_eq]
  rw [h.combined_contacts] at hheavy
  omega

theorem Configuration.adjacent_first_labels {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    {x : V} (hx : x ∈ insert p.leaf s) (htwo : degreeIn G x q.support = 2) :
    ∃ v : Quadrilateral G, v.support = q.support ∧
      ∀ i : Fin 4, G.Adj x (v i) ↔ i = 0 ∨ i = 1 := by
  obtain ⟨v, hv, hrow | hrow⟩ := q.exists_two_contact_labels x htwo
  · refine ⟨v, hv, ?_⟩
    intro i
    rw [hrow]
    fin_cases i <;> decide
  · exact False.elim (h.no_opposite_first_pair hcard hdeg hn v (by rwa [hv])
      (by rwa [hv]) (by rwa [hv]) (by rwa [hv]) (by simpa only [hv] using hrows) hx
      ⟨(hrow 0).mpr (by decide), (hrow 2).mpr (by decide)⟩)

theorem Configuration.not_complete_of_first_two {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    {x : V} (hx : x ∈ insert p.leaf s) (htwo : degreeIn G x q.support = 2) :
    ¬G.IsNClique 4 q.support := by
  intro hcl
  obtain ⟨v, hv, hrow⟩ := h.adjacent_first_labels hcard hdeg hn q hj hjs hja hheavy hrows hx htwo
  have hvcl : G.IsNClique 4 v.support := by rwa [hv]
  let e : Fin 4 ↪ Fin 4 := (Equiv.swap 1 2).toEmbedding
  let w := v.relabelOfClique hvcl e
  have hw : w.support = q.support := (v.relabelOfClique_support hvcl e).trans hv
  apply h.no_opposite_first_pair hcard hdeg hn w (by rwa [hw]) (by rwa [hw])
    (by rwa [hw]) (by rwa [hw]) (by simpa only [hw] using hrows) hx
  constructor
  · simpa [w, e, Equiv.swap_apply_def] using (hrow 0).mpr (Or.inl rfl)
  · simpa [w, e] using (hrow 1).mpr (Or.inr rfl)

theorem Configuration.first_two_edges_le_five {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    {x : V} (hx : x ∈ insert p.leaf s) (htwo : degreeIn G x q.support = 2) :
    edgeCount G q.support ≤ 5 := by
  have hnot := h.not_complete_of_first_two hcard hdeg hn q hj hjs hja hheavy hrows hx htwo
  have hupper := edgeCount_le_six G q.card_support
  by_contra hmore
  exact hnot (clique_of_four_six q.card_support (by omega))

theorem Configuration.adjacent_heavy_preparation {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    {x : V} (hx : x ∈ insert p.leaf s) (htwo : degreeIn G x q.support = 2) :
    ∃ v : Quadrilateral G, v.support = q.support ∧
      (∀ i : Fin 4, G.Adj x (v i) ↔ i = 0 ∨ i = 1) ∧
      6 ≤ degreeIn G (v 0) (insert (p.vertices 3) a) +
        degreeIn G (v 2) (insert (p.vertices 3) a) ∧ edgeCount G v.support ≤ 5 := by
  obtain ⟨v, hv, hrow⟩ := h.adjacent_first_labels hcard hdeg hn q hj hjs hja hheavy hrows hx htwo
  have hsecond := h.second_contacts_ge_eleven hheavy hrows
  obtain ⟨w, hw, hwrow, hpair⟩ := FullLeafHeavy.adjacent_labels_heavy_opposite v
    (insert (p.vertices 3) a) x hrow (by simpa only [hv] using hsecond)
  refine ⟨w, hw.trans hv, hwrow, hpair, ?_⟩
  rw [hw, hv]
  exact h.first_two_edges_le_five hcard hdeg hn q hj hjs hja hheavy hrows hx htwo

end Erdos577.FullLeafCore
