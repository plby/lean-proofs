import ErdosProblems.Erdos577.FullLeafHeavyDiamondRows

/-! Exclude every adjacent first-row pair, using both actual marked-center prohibitions. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

theorem Configuration.diamond_all_two_touch {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    (hdiag : G.Adj (q 0) (q 2))
    (h2 : degreeIn G (q 2) (insert (p.vertices 3) a) ≤ 4)
    (h3 : degreeIn G (q 3) (insert (p.vertices 3) a) ≤ 1)
    (htriple : contacts G (s.erase y) q.support ≤ 5) :
    ∀ w ∈ insert p.leaf s, degreeIn G w q.support = 2 → G.Adj w (q 1) := by
  intro w hw htwo
  by_contra hnot
  have hout : w ∉ q.support := fun hh ↦ disjoint_left.mp (h.five_disjoint_block hj hjs) hw hh
  have hmem : q 1 ∈ q.support := (q.mem_support _).mpr ⟨1, rfl⟩
  have he := degreeIn_erase_add G w (q 1) hmem
  rw [if_neg hnot, htwo] at he
  have hrep := QuadOn.of_triangle (FullLeafHeavy.diamond_low_triangle q hdiag 1 (Or.inl rfl))
    (fun hh ↦ hout (mem_erase.mp hh).2) (by omega : 2 ≤ degreeIn G w (q.support.erase (q 1)))
  have h1 := (degreeIn_mono G (q 1) h.second_five_subset).trans
    (h.core_degree_of_first_replacement hcard hn hw hj hjs hja hmem hrep)
  have h0 := degreeIn_le_card G (q 0) (insert (p.vertices 3) a)
  rw [h.second_five_card] at h0
  have hsum := FullLeafHeavy.columns_sum q (insert (p.vertices 3) a)
  have hsplit := h.first_contacts q.support
  have hX := hrows p.leaf (mem_insert_self _ _)
  have hY := hrows y (mem_insert_of_mem h.exposed)
  rw [h.combined_contacts] at hheavy
  omega

theorem Configuration.adjacent_diamond_false {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    {x : V} (hx : x ∈ insert p.leaf s) (h0 : G.Adj x (q 0)) (h1 : G.Adj x (q 1))
    (hdiag : G.Adj (q 0) (q 2)) (hfive : edgeCount G q.support = 5) : False := by
  obtain ⟨_, h2, h3, _, ht14, hlow, u, hu, _, hrep⟩ :=
    h.diamond_preparation hcard hn q hj hjs hja hheavy hrows hx h0 h1 hdiag hfive
  have hno (w : V) (hw : w ∈ s.erase y) : ¬(G.Adj w (q 0) ∧ G.Adj w (q 2)) :=
    h.no_opposite_first_pair hcard hdeg hn q hj hjs hja hheavy hrows
      (mem_insert_of_mem (mem_erase.mp hw).2)
  have ht5 := FullLeafHeavy.triple_contacts_le_five q (s.erase y) h.first_triple_clique.card_eq
    hno (hlow 1 (Or.inl rfl)) (hlow 3 (Or.inr rfl))
  have htouch := h.diamond_all_two_touch hcard hn q hj hjs hja hheavy hrows hdiag h2 h3 ht5
  have ht4 := FullLeafHeavy.triple_contacts_le_four q (s.erase y) h.first_triple_clique.card_eq
    (fun w hw ↦ hrows w (mem_insert_of_mem (mem_erase.mp hw).2))
    (fun w hw ↦ htouch w (mem_insert_of_mem (mem_erase.mp hw).2)) (hlow 1 (Or.inl rfl))
  have hsplit := h.first_contacts q.support
  have hX := hrows p.leaf (mem_insert_self _ _)
  have hY := hrows y (mem_insert_of_mem h.exposed)
  have hheavy' := hheavy
  rw [h.combined_contacts] at hheavy'
  have h0b := degreeIn_le_card G (q 0) (insert (p.vertices 3) a)
  rw [h.second_five_card] at h0b
  have hsum := FullLeafHeavy.columns_sum q (insert (p.vertices 3) a)
  have h1three : 3 ≤ degreeIn G (q 1) (insert (p.vertices 3) a) := by omega
  have hmem : q 1 ∈ q.support := (q.mem_support _).mpr ⟨1, rfl⟩
  obtain ⟨hr, hb⟩ := h.center_degrees
  by_cases hXtwo : degreeIn G p.leaf q.support = 2
  · have hx1 := htouch p.leaf (mem_insert_self _ _) hXtwo
    obtain ⟨v, hv, hvu, hvr, hv1⟩ := FullLeafHeavy.common_neighbor_ne_of_card_add_two (G := G)
      (insert (p.vertices 3) a) p.center (q 1) u (by rw [h.second_five_card]; omega)
    exact h.center_common_forbidden hcard hn hu hv hvu.symm hvr hj hjs hja
      ⟨q 1, hmem, hx1, hv1, hrep 1 (Or.inl rfl)⟩
  · have hYtwo : degreeIn G y q.support = 2 := by omega
    have hy1 := htouch y (mem_insert_of_mem h.exposed) hYtwo
    obtain ⟨v, hv, hvu, hvb, hv1⟩ := FullLeafHeavy.common_neighbor_ne_of_card_add_two (G := G)
      (insert (p.vertices 3) a) (p.vertices 2) (q 1) u (by rw [h.second_five_card]; omega)
    exact h.second_common_forbidden hcard hn hu hv hvu.symm hvb hj hjs hja
      ⟨q 1, hmem, hy1, hv1, hrep 1 (Or.inl rfl)⟩

theorem Configuration.no_first_two {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    {x : V} (hx : x ∈ insert p.leaf s) : degreeIn G x q.support ≠ 2 := by
  intro htwo
  obtain ⟨v, hv, hrow, hdiag, _, hfive⟩ :=
    h.first_two_diamond_labels hcard hdeg hn q hj hjs hja hheavy hrows hx htwo
  exact h.adjacent_diamond_false hcard hdeg hn v (by rwa [hv]) (by rwa [hv]) (by rwa [hv])
    (by rwa [hv]) (by simpa only [hv] using hrows) hx ((hrow 0).mpr (Or.inl rfl))
    ((hrow 1).mpr (Or.inr rfl)) hdiag hfive

theorem Configuration.first_rows_le_one {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2) :
    ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 1 := by
  intro x hx
  have hb := hrows x hx
  have hne := h.no_first_two hcard hdeg hn q hj hjs hja hheavy hrows hx
  omega

end Erdos577.FullLeafCore
