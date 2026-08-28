import ErdosProblems.Erdos577.FullLeafHeavyTwoLows
import ErdosProblems.Erdos577.CoreObstruction

/-! Every hypothesis of the earlier core obstruction, including its bridge bound, is derived. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.core_vertex_triangle_degree {z : V} (hz : z ∈ a) :
    2 ≤ degreeIn G z p.triangle := by
  have he := contacts_erase_add (G := G) (q := p.triangle) hz
  have hb := contacts_le_card_mul G (a.erase z) p.triangle
  rw [card_erase_of_mem hz, h.core_clique.card_eq, p.triangle_clique.card_eq] at hb
  rw [contacts_comm G a p.triangle] at he
  have hd := h.dense
  omega

theorem Configuration.core_neighbor_replacement {z : V} (hz : z ∈ a) :
    ∃ u ∈ p.triangle, ∃ v ∈ p.triangle, u ≠ v ∧ G.Adj z u ∧
      QuadOn G (insert v (a.erase z)) := by
  have hpos : 0 < degreeIn G z p.triangle := lt_of_lt_of_le (by decide)
    (h.core_vertex_triangle_degree hz)
  obtain ⟨u, hu⟩ := card_pos.mp hpos
  obtain ⟨hu, hzu⟩ := mem_filter.mp hu
  obtain ⟨v, hv, hvu⟩ := exists_mem_ne (by rw [p.triangle_clique.card_eq]; decide) u
  have hr := ((h.feasible.presentPaw_feasible p h.paw).all_triangle_universal_replacements
    h.core h.dense).2 v hv z hz
  exact ⟨u, hu, v, hv, hvu.symm, hzu, hr⟩

theorem Configuration.low_first_contacts {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) (q : Quadrilateral G) (hj : q.support ∈ c.blocks)
    (hjs : q.support ≠ s) (hja : q.support ≠ a) {u : V}
    (hu : u ∈ insert (p.vertices 3) a) (h0 : G.Adj u (q 0)) (h2 : G.Adj u (q 2)) :
    contacts G {q 1, q 3} s ≤ 4 := by
  have hout : u ∉ q.support := fun hh ↦ disjoint_left.mp (h.core_disjoint_block hj hja)
    (h.second_five_subset hu) hh
  have hlow (i : Fin 4) (hi : i = 1 ∨ i = 3) : degreeIn G (q i) s ≤ 2 := by
    have hr := JointFinal.opposite_replace q u hout h0 h2 i hi
    have hb := h.triple_degree_of_second_replacement hcard hn hu hj hjs hja
      ((q.mem_support _).mpr ⟨i, rfl⟩) hr
    have he := degreeIn_erase_add G (q i) y h.exposed
    split_ifs at he <;> omega
  have h13 : q 1 ≠ q 3 := q.injective.ne (by decide : (1 : Fin 4) ≠ 3)
  rw [contacts, sum_pair h13]
  have h1 := hlow 1 (Or.inl rfl)
  have h3 := hlow 3 (Or.inr rfl)
  omega

theorem Configuration.remaining_opposite_core_false {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (hdiag : ¬G.Adj (q 1) (q 3))
    {z₁ z₂ : V} (hz₁ : z₁ ∈ insert (p.vertices 3) a) (hz₂ : z₂ ∈ insert (p.vertices 3) a)
    (hz12 : z₁ ≠ z₂) (h10 : G.Adj z₁ (q 0)) (h11 : G.Adj z₁ (q 1))
    (h12 : G.Adj z₁ (q 2)) (h20 : G.Adj z₂ (q 0)) (h22 : G.Adj z₂ (q 2))
    (hx0 : G.Adj p.leaf (q 0))
    (hopp : ∃ w ∈ insert p.leaf s, G.Adj w (q 0) ∧ G.Adj w (q 2)) : False := by
  have hd : Disjoint p.triangle a :=
    (h.paw_disjoint h.core).mono_left (p.support_eq ▸ subset_insert _ _)
  apply CoreTransfer.core_obstruction (h.feasible.presentPaw_strong hcard hn p h.paw)
    q hj hcard hdeg hn h.core hja.symm
    (fun _ hout htwo ↦ dense_triangle_clique_factor p.triangle_clique h.core_clique hd
      h.dense hout htwo) p.center p.center_mem_triangle p.pendant.symm z₁ z₂
    (h.second_five_subset hz₁) (h.second_five_subset hz₂) hz12
    (h.second_avoids hz₁).2.1 (h.second_avoids hz₂).2.1
    (fun hz ↦ h.core_neighbor_replacement hz) hx0 hdiag h10 h11 h12 h20 h22
  intro hx2
  obtain ⟨w, hw, hw0, hw2⟩ := hopp
  have hws : w ∈ s := by
    rcases mem_insert.mp hw with rfl | hw
    · exact False.elim (hx2 hw2)
    · exact hw
  obtain ⟨hr, he⟩ := FullRow.full_leaf_replacement h.feasible p h.paw h.first h.full w hws
  exact ⟨s, h.first, h.different.symm, hjs.symm, w, hws,
    h.low_first_contacts hcard hn q hj hjs hja hz₁ h10 h12, hr, he, hw0, hw2⟩

end Erdos577.FullLeafCore
