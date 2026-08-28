import ErdosProblems.Erdos577.FullRowFirstBlockBound
import ErdosProblems.Erdos577.FullRowColumns
import ErdosProblems.Erdos577.FullRowSwap

/-! Vertex bounds and exact support identities for the full-row inside count. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma degree_union_le (u : V) (s t : Finset V) :
    degreeIn G u (s ∪ t) ≤ degreeIn G u s + degreeIn G u t := by
  unfold degreeIn
  rw [filter_union]
  exact card_union_le _ _

lemma contacts_union_right_le (s t u : Finset V) :
    contacts G s (t ∪ u) ≤ contacts G s t + contacts G s u := by
  simpa only [contacts, sum_add_distrib] using
    (sum_le_sum (fun v (_ : v ∈ s) ↦ degree_union_le (G := G) v t u))

variable [Fintype V]

omit [DecidableRel G.Adj] in
lemma first_swap_cover (p : Paw G) (q : Quadrilateral G) (d : TriangleChain G)
    (ht : d.terminal = q 3) (hT : d.triangle = p.triangle) :
    d.remainder ∪ insert p.leaf (q.support.erase (q 3)) = p.support ∪ q.support := by
  change insert d.terminal d.triangle ∪ _ = _
  rw [ht, hT, p.support_eq]
  ext v
  have hm : v = q 3 → v ∈ q.support := fun he ↦ he ▸ (q.mem_support _).mpr ⟨3, rfl⟩
  simp only [mem_union, mem_insert, mem_erase]
  tauto

theorem direct_vertex_inside_le_six {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hleaf : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s)
    (hxfull : degreeIn G p.leaf a = 4) (hcfull : degreeIn G (p.vertices 3) a = 4)
    (u : V) (hu : u ∈ a) : degreeIn G u (p.support ∪ (q.support ∪ a)) ≤ 6 := by
  have hQ := first_block_degree_le_one_direct hc hcard hn p hp hs q hq hleaf hseven
    ha has hcfull u hu
  have htri := full_column_triangle_bound hc hcard hn p hp ha hxfull u hu
  have hcl := full_leaf_clique hc p hp ha hxfull
  have hA := degreeIn_clique G hcl.isClique hu
  rw [hcl.card_eq] at hA
  have hF : degreeIn G u p.support ≤ 2 := by
    rw [p.support_eq, degreeIn_insert G u p.leaf p.leaf_not_mem_triangle]
    split_ifs <;> omega
  have hQA := degree_union_le (G := G) u q.support a
  have hAll := degree_union_le (G := G) u p.support (q.support ∪ a)
  omega

theorem other_vertex_inside_le_six {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hleaf : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s)
    (hxfull : degreeIn G p.leaf a = 4)
    {b : Finset V} (hb : b ∈ c.blocks) (hbs : b ≠ s)
    (z : V) (hz : z ∈ b) (hzfull : degreeIn G z a = 4)
    (hrep : QuadOn G (insert (p.vertices 3) (b.erase z)))
    (hcore : ∀ v, v ∉ p.triangle ∪ b → 2 ≤ degreeIn G v (p.triangle ∪ b) →
      LocalFactor G (insert v (p.triangle ∪ b)))
    (u : V) (hu : u ∈ a) : degreeIn G u (p.support ∪ (q.support ∪ (b ∪ a))) ≤ 6 := by
  have hQ := first_block_degree_le_one_other hc hcard hn p hp hs q hq hleaf hseven
    ha has hb hbs z hz hzfull hrep u hu
  have hba : b ≠ a := fun he ↦
    full_row_outside (c.property.blocks_quad a ha) z hzfull (he ▸ hz)
  have hcoreBound := full_column_core_bound hc hcard hn p hp ha hxfull hb hba hcore u hu
  have hcl := full_leaf_clique hc p hp ha hxfull
  have hA := degreeIn_clique G hcl.isClique hu
  rw [hcl.card_eq] at hA
  have hxout : p.leaf ∉ p.triangle ∪ b := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact p.leaf_not_mem_triangle hh
    · exact (c.presentPaw p hp).terminal_not_mem_block hb hh
  have hFB : degreeIn G u (p.support ∪ b) ≤ 2 := by
    rw [p.support_eq, insert_union, degreeIn_insert G u p.leaf hxout]
    split_ifs <;> omega
  have hQA := degree_union_le (G := G) u q.support a
  have hAll := degree_union_le (G := G) u (p.support ∪ b) (q.support ∪ a)
  have he : (p.support ∪ b) ∪ (q.support ∪ a) = p.support ∪ (q.support ∪ (b ∪ a)) := by
    rw [union_assoc, union_left_comm b q.support a]
  rw [he] at hAll
  omega

theorem direct_swapped_contacts {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    (q : Quadrilateral G) (d : TriangleChain G)
    (ht : d.terminal = q 3) (hT : d.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks)
    (hxfull : degreeIn G p.leaf a = 4) (hcfull : degreeIn G (p.vertices 3) a = 4)
    (hlast : degreeIn G (q 3) a = 1) : contacts G d.remainder a = 5 := by
  have htri := direct_triangle_contacts hc hcard hn p hp ha hxfull (p.vertices 3)
    (by simp only [Paw.triangle, mem_insert, mem_singleton]; tauto) hcfull
  rw [CoreTransfer.remainder_contacts, ht, hT, hlast, htri]

theorem other_swapped_contacts {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    (q : Quadrilateral G) (d : TriangleChain G)
    (ht : d.terminal = q 3) (hT : d.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks) (hxfull : degreeIn G p.leaf a = 4)
    {b : Finset V} (hb : b ∈ c.blocks) (z : V) (hz : z ∈ b) (hzfull : degreeIn G z a = 4)
    (hcore : ∀ v, v ∉ p.triangle ∪ b → 2 ≤ degreeIn G v (p.triangle ∪ b) →
      LocalFactor G (insert v (p.triangle ∪ b)))
    (hlast : degreeIn G (q 3) a = 1) : contacts G d.remainder a = 1 := by
  have htri := (core_triangle_contacts_zero hc hcard hn p hp ha hxfull hb z hz hzfull hcore).2
  rw [CoreTransfer.remainder_contacts, ht, hT, hlast, htri, add_zero]

end Erdos577.FullRow
