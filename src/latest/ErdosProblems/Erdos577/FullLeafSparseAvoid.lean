import ErdosProblems.Erdos577.FullLeafSparsePreparation

/-! Sparse contacts on the designated sides avoid every core matching edge, TeX9.73. -/

namespace Erdos577.FullLeafSparse

open Finset

variable {V : Type*} [DecidableEq V]

def Attached (G : SimpleGraph V) [DecidableRel G.Adj] (p : Paw G)
    (s a : Finset V) (y v : V) (j : Finset V) : Prop :=
  ((v ∈ s.erase y ∧ FullLeafHeavy.Type40 G p s y j) ∨
    (v ∈ insert (p.vertices 3) a ∧ FullLeafHeavy.Type41 G p a j)) ∧ degreeIn G v j = 1

end Erdos577.FullLeafSparse

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

theorem Configuration.type40_matching_endpoint_zero {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type40 G p s y j)
    {w u : V} (hw : w ∈ s.erase y) (hu : u ∈ insert (p.vertices 3) a) (hwu : G.Adj w u) :
    degreeIn G w j = 0 := by
  have hbound := htype.2.2.1 w hw
  by_contra hnonzero
  have hrow : degreeIn G w j = 1 := by omega
  have hwFirst : w ∈ insert p.leaf s := mem_insert_of_mem (mem_erase.mp hw).2
  obtain ⟨t, ht, hcl, hut, _⟩ := h.second_triangle_through hu
  have htK := ht.trans h.second_five_subset
  have hwout : w ∉ t := fun hh ↦ disjoint_left.mp h.five_disjoint_core hwFirst (htK hh)
  have hpositive : 0 < degreeIn G w t :=
    card_pos.mpr ⟨u, mem_filter.mpr ⟨hut, hwu⟩⟩
  obtain ⟨p', hleaf, htriangle⟩ := Paw.exists_of_triangle hcl hwout hpositive
  have hsupport : p'.support = insert w t := by rw [p'.support_eq, hleaf, htriangle]
  obtain ⟨q, hq⟩ := c.property.blocks_quad j hj
  have hdis : Disjoint p'.support q.support := by
    rw [hsupport, hq]
    exact disjoint_insert_left.mpr
      ⟨fun hh ↦ disjoint_left.mp (h.five_disjoint_block hj hjs) hwFirst hh,
        (h.core_disjoint_block hj hja).mono_left htK⟩
  have hten := FullLeafSparse.triangle_contacts_of_eighteen ht h.second_five_card hcl.card_eq
    (c.property.blocks_quad j hj).card (h.type40_second_contacts hheavy htype)
  have hf := FullLeafSparse.paw_factor_of_one_leaf_eleven p' q hdis
    (by rwa [hleaf, hq]) (by rwa [htriangle, hq])
  rw [hsupport, hq, insert_union] at hf
  exact h.first_no_factor hcard hn hwFirst hj hjs hja htK hcl.card_eq hf

theorem Configuration.type41_matching_endpoint_zero {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type41 G p a j)
    {w u : V} (hw : w ∈ s.erase y) (hu : u ∈ insert (p.vertices 3) a) (hwu : G.Adj w u) :
    degreeIn G u j = 0 := by
  have hbound := htype.1 u hu
  by_contra hnonzero
  have hrow : degreeIn G u j = 1 := by omega
  obtain ⟨hcl, _, hnine⟩ := h.type41_preparation hj hjs hheavy htype
  have huout : u ∉ s.erase y := fun hh ↦ disjoint_left.mp h.five_disjoint_core
    (mem_insert_of_mem (mem_erase.mp hh).2) (h.second_five_subset hu)
  have hpositive : 0 < degreeIn G u (s.erase y) :=
    card_pos.mpr ⟨w, mem_filter.mpr ⟨hw, hwu.symm⟩⟩
  obtain ⟨p', hleaf, htriangle⟩ := Paw.exists_of_triangle h.first_triple_clique huout hpositive
  have hsupport : p'.support = insert u (s.erase y) := by rw [p'.support_eq, hleaf, htriangle]
  obtain ⟨q, hq⟩ := c.property.blocks_quad j hj
  have hdis : Disjoint p'.support q.support := by
    rw [hsupport, hq]
    refine disjoint_insert_left.mpr ⟨fun hh ↦
      disjoint_left.mp (h.core_disjoint_block hj hja) (h.second_five_subset hu) hh, ?_⟩
    exact (h.five_disjoint_block hj hjs).mono_left
      (fun v hv ↦ mem_insert_of_mem (mem_erase.mp hv).2)
  have hf := p'.clique_nine_triangle_factor q hdis (by simpa only [hq] using hcl.isClique)
    (by rw [hleaf, hq]; exact hrow.ge) (by rwa [htriangle, hq])
  rw [hsupport, hq, insert_union] at hf
  exact h.second_no_factor hcard hn hu hj hjs hja hf

theorem Configuration.matching_endpoints_not_sparse {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    {w u : V} (hw : w ∈ s.erase y) (hu : u ∈ insert (p.vertices 3) a) (hwu : G.Adj w u) :
    ¬FullLeafSparse.Attached G p s a y w j ∧ ¬FullLeafSparse.Attached G p s a y u j := by
  constructor
  · rintro ⟨hside, hrow⟩
    rcases hside with ⟨_, h40⟩ | ⟨hw', _⟩
    · have hz := h.type40_matching_endpoint_zero hcard hn hj hjs hja hheavy h40 hw hu hwu
      omega
    · exact disjoint_left.mp h.five_disjoint_core
        (mem_insert_of_mem (mem_erase.mp hw).2) (h.second_five_subset hw')
  · rintro ⟨hside, hrow⟩
    rcases hside with ⟨hu', _⟩ | ⟨_, h41⟩
    · exact disjoint_left.mp h.five_disjoint_core
        (mem_insert_of_mem (mem_erase.mp hu').2) (h.second_five_subset hu)
    · have hz := h.type41_matching_endpoint_zero hcard hn hj hjs hja hheavy h41 hw hu hwu
      omega

end Erdos577.FullLeafCore
