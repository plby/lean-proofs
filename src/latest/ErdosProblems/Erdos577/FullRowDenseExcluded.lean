import ErdosProblems.Erdos577.FullRowDenseFactors
import ErdosProblems.Erdos577.FullRowDistinguishedFactor

/-! Both locations of the distinguished full row exclude the dense heavy-block case. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem dense_factor {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Strong) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (hT : d.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks) (had : a ∈ d.blocks)
    (hxfull : degreeIn G p.leaf a = 4) (v : Quadrilateral G) (hv : v.support = a)
    {j : Finset V} (hj : j ∈ c.blocks) (hjd : j ∈ d.blocks) (hja : j ≠ a)
    (hheavy : 13 ≤ contacts G (CoreTransfer.rows d v) j)
    (hdense : 9 ≤ contacts G d.remainder j)
    (z : V) (hz : z ∉ pathTriple p ∪ (a ∪ j))
    (hrz : G.Adj p.center z) (hzfull : degreeIn G z a = 4) :
    Nonempty (BlockPartition G (insert z (pathTriple p ∪ (a ∪ j)))) := by
  obtain ⟨hzero, _, _, _, _, hrep⟩ := dense_shape hc hd hcard hdeg hn p hp hT ha had
    hxfull v hv hj hjd hja hheavy hdense
  have htriangle : 13 ≤ contacts G p.triangle j + degreeIn G (v 1) j + degreeIn G (v 3) j := by
    rwa [CoreTransfer.rows_contacts d v (hv.symm ▸ had), CoreTransfer.remainder_contacts,
      hzero, hT, zero_add] at hheavy
  have hdis : Disjoint p.support (v.support ∪ j) := by
    rw [hp, hv]
    apply disjoint_union_right.mpr
    exact ⟨c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha),
      c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)⟩
  have hAJ : Disjoint v.support j := by
    rw [hv]
    exact c.property.blocks_disjoint ha hj hja.symm
  have hcardA := (c.property.blocks_quad a ha).card
  have hxA (i : Fin 4) : G.Adj p.leaf (v i) :=
    (degreeIn_eq_card_iff p.leaf a).mp (hxfull.trans hcardA.symm) (v i)
      (hv ▸ (v.mem_support _).mpr ⟨i, rfl⟩)
  have hzA (i : Fin 4) : G.Adj z (v i) :=
    (degreeIn_eq_card_iff z a).mp (hzfull.trans hcardA.symm) (v i)
      (hv ▸ (v.mem_support _).mpr ⟨i, rfl⟩)
  have hrepA (i : Fin 4) : QuadOn G (insert p.leaf (v.support.erase (v i))) := by
    rw [hv]
    exact (full_leaf_replacement hc p hp ha hxfull (v i)
      (hv ▸ (v.mem_support _).mpr ⟨i, rfl⟩)).1
  have hbT : p.vertices 2 ∈ p.triangle := by simp [Paw.triangle]
  have hf := partition_of_dense_contacts p v j hdis hAJ z (by rwa [hv]) hrz hxA hzA
    (c.property.blocks_quad j hj).card htriangle hrepA (hrep (p.vertices 2) hbT)
  simpa only [hv] using hf

theorem direct_dense_false {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Strong) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (hT : d.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks) (had : a ∈ d.blocks)
    (hxfull : degreeIn G p.leaf a = 4) (hcfull : degreeIn G (p.vertices 3) a = 4)
    (v : Quadrilateral G) (hv : v.support = a)
    {j : Finset V} (hj : j ∈ c.blocks) (hjd : j ∈ d.blocks) (hja : j ≠ a)
    (hheavy : 13 ≤ contacts G (CoreTransfer.rows d v) j)
    (hdense : 9 ≤ contacts G d.remainder j) : False := by
  have hthird : p.vertices 3 ∈ c.remainder := hp ▸ (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩
  have hz : p.vertices 3 ∉ pathTriple p ∪ (a ∪ j) := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact third_not_mem_pathTriple p hh
    · rcases mem_union.mp hh with hh | hh
      · exact (mem_sdiff.mp (c.complementPartition.block_subset ha hh)).2 hthird
      · exact (mem_sdiff.mp (c.complementPartition.block_subset hj hh)).2 hthird
  have hf := dense_factor hc hd hcard hdeg hn p hp hT ha had hxfull v hv hj hjd hja
    hheavy hdense (p.vertices 3) hz p.edge13 hcfull
  have hsel : ({a, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset ha (singleton_subset_iff.mpr hj)
  apply hn
  apply hasPacking_of_distinguished_direct hcard p hp {a, j} hsel
  simpa only [biUnion_insert, singleton_biUnion, id_eq] using hf

theorem other_dense_false {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Strong) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (hT : d.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks) (had : a ∈ d.blocks)
    (hxfull : degreeIn G p.leaf a = 4) (v : Quadrilateral G) (hv : v.support = a)
    {j : Finset V} (hj : j ∈ c.blocks) (hjd : j ∈ d.blocks) (hja : j ≠ a)
    (hheavy : 13 ≤ contacts G (CoreTransfer.rows d v) j)
    (hdense : 9 ≤ contacts G d.remainder j)
    {b : Finset V} (hb : b ∈ c.blocks) (hbj : b ≠ j)
    (z : V) (hz : z ∈ b) (hrz : G.Adj p.center z) (hzfull : degreeIn G z a = 4)
    (hrep : QuadOn G (insert (p.vertices 3) (b.erase z))) : False := by
  have hza := full_row_outside (c.property.blocks_quad a ha) z hzfull
  have hba : b ≠ a := fun he ↦ hza (he ▸ hz)
  have hzout : z ∉ pathTriple p ∪ (a ∪ j) := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · have hF := pathTriple_subset p hh
      exact (mem_sdiff.mp (c.complementPartition.block_subset hb hz)).2 (hp ▸ hF)
    · rcases mem_union.mp hh with hh | hh
      · exact hza hh
      · exact disjoint_left.mp (c.property.blocks_disjoint hb hj hbj) hz hh
  have hf := dense_factor hc hd hcard hdeg hn p hp hT ha had hxfull v hv hj hjd hja
    hheavy hdense z hzout hrz hzfull
  have hsel : ({a, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset ha (singleton_subset_iff.mpr hj)
  have hbn : b ∉ ({a, j} : Finset (Finset V)) := by
    simp only [mem_insert, mem_singleton]
    exact not_or.mpr ⟨hba, hbj⟩
  apply hn
  apply hasPacking_of_distinguished_other hcard p hp {a, j} hsel hb hbn hz hrep
  simpa only [biUnion_insert, singleton_biUnion, id_eq] using hf

end Erdos577.FullRow
