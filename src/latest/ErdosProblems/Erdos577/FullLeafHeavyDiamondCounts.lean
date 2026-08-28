import ErdosProblems.Erdos577.FullLeafHeavyDiamondGeometry

/-! Column bounds and an actual low-vertex replacement row in the adjacent diamond case. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

theorem Configuration.second_column_le_four_of_triangle {x : V} (hx : x ∈ insert p.leaf s)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hscore : edgeCount G j ≤ 5) {v : V} (hv : v ∈ j)
    (htri : TriangleIn G (insert x (j.erase v))) :
    degreeIn G v (insert (p.vertices 3) a) ≤ 4 := by
  have hb := degreeIn_le_card G v (insert (p.vertices 3) a)
  rw [h.second_five_card] at hb
  by_contra hmore
  have hvout : v ∉ p.triangle ∪ a := fun hh ↦
    disjoint_left.mp (h.core_disjoint_block hj hja) hh hv
  obtain ⟨f, hf⟩ := h.two_complete_core_partition hvout (by omega)
  have hbound := h.core_insertion_triangle_bound hx hj hjs hja hv f htri
  omega

theorem Configuration.diamond_preparation {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    {x : V} (hx : x ∈ insert p.leaf s) (h0 : G.Adj x (q 0)) (h1 : G.Adj x (q 1))
    (hdiag : G.Adj (q 0) (q 2)) (hfive : edgeCount G q.support = 5) :
    degreeIn G (q 1) (insert (p.vertices 3) a) ≤ 4 ∧
      degreeIn G (q 2) (insert (p.vertices 3) a) ≤ 4 ∧
      degreeIn G (q 3) (insert (p.vertices 3) a) ≤ 1 ∧
      11 ≤ contacts G (insert (p.vertices 3) a) q.support ∧
      contacts G (insert (p.vertices 3) a) q.support ≤ 14 ∧
      (∀ i : Fin 4, i = 1 ∨ i = 3 → degreeIn G (q i) (s.erase y) ≤ 1) ∧
      ∃ u ∈ insert (p.vertices 3) a, 3 ≤ degreeIn G u q.support ∧
        ∀ i : Fin 4, i = 1 ∨ i = 3 → QuadOn G (insert u (q.support.erase (q i))) := by
  have hmem (i : Fin 4) : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have hxout : x ∉ q.support := fun hh ↦ disjoint_left.mp (h.five_disjoint_block hj hjs) hx hh
  have hlast := h.core_degree_of_first_replacement hcard hn hx hj hjs hja (hmem 3)
    (FullLeafHeavy.diamond_first_replaces_last q hdiag hxout h0 h1)
  have h3 := (degreeIn_mono G (q 3) h.second_five_subset).trans hlast
  have h1b := h.second_column_le_four_of_triangle hx hj hjs hja hfive.le (hmem 1)
    ⟨q.support.erase (q 1), subset_insert _ _,
      FullLeafHeavy.diamond_low_triangle q hdiag 1 (Or.inl rfl)⟩
  have h2b := h.second_column_le_four_of_triangle hx hj hjs hja hfive.le (hmem 2)
    (FullLeafHeavy.adjacent_triangle_remainder q h0 h1)
  have h0b := degreeIn_le_card G (q 0) (insert (p.vertices 3) a)
  rw [h.second_five_card] at h0b
  have hsum := FullLeafHeavy.columns_sum q (insert (p.vertices 3) a)
  have heleven := h.second_contacts_ge_eleven hheavy hrows
  have hthree : ∃ u ∈ insert (p.vertices 3) a, 3 ≤ degreeIn G u q.support := by
    by_contra! hnone
    have hsmall : contacts G (insert (p.vertices 3) a) q.support ≤ 10 := by
      calc
        contacts G (insert (p.vertices 3) a) q.support ≤
            ∑ _ ∈ insert (p.vertices 3) a, (2 : ℕ) :=
          sum_le_sum fun u hu ↦ by have hh := hnone u hu; omega
        _ = 10 := by simp only [sum_const, smul_eq_mul, h.second_five_card]
    omega
  obtain ⟨u, hu, hud⟩ := hthree
  have huout : u ∉ q.support := fun hh ↦
    disjoint_left.mp (h.core_disjoint_block hj hja) (h.second_five_subset hu) hh
  have hrep (i : Fin 4) (hi : i = 1 ∨ i = 3) :=
    FullLeafHeavy.diamond_three_replaces_lows q hdiag huout hud i hi
  have hlow (i : Fin 4) (hi : i = 1 ∨ i = 3) : degreeIn G (q i) (s.erase y) ≤ 1 :=
    h.triple_degree_of_second_replacement hcard hn hu hj hjs hja (hmem i) (hrep i hi)
  exact ⟨h1b, h2b, h3, heleven, by omega, hlow, u, hu, hud, hrep⟩

theorem Configuration.first_two_diamond_labels {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    {x : V} (hx : x ∈ insert p.leaf s) (htwo : degreeIn G x q.support = 2) :
    ∃ v : Quadrilateral G, v.support = q.support ∧
      (∀ i : Fin 4, G.Adj x (v i) ↔ i = 0 ∨ i = 1) ∧
      G.Adj (v 0) (v 2) ∧ ¬G.Adj (v 1) (v 3) ∧ edgeCount G v.support = 5 := by
  obtain ⟨v, hv, hrow⟩ := h.adjacent_first_labels hcard hdeg hn q hj hjs hja hheavy hrows hx htwo
  have hfive := h.first_two_edges_eq_five hcard hdeg hn q hj hjs hja hheavy hrows hx htwo
  obtain ⟨w, hw, hroww, hdiag, hmissing⟩ := FullLeafHeavy.adjacent_diamond_labels v x hrow
    (by simpa only [hv] using hfive)
  exact ⟨w, hw.trans hv, hroww, hdiag, hmissing, by simpa only [hw, hv] using hfive⟩

end Erdos577.FullLeafCore
