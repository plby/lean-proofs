import ErdosProblems.Erdos577.TwoReplacementPartition
import ErdosProblems.Erdos577.JointFirstCompletion

/-! Complete a bridge partial factor through two vertex replacements and a core complement. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem hasPacking_of_bridge_partial {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (p : Paw G) (hp : p.support = c.remainder)
    {s a b : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (hb : b ∈ c.blocks)
    (has : a ≠ s) (hab : a ≠ b) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (bs : Finset (Finset V)) (hsel : bs ⊆ c.blocks)
    (han : a ∉ bs) (hsn : s ∉ bs) (hbn : b ∉ bs)
    {z u : V} (hz : z ∈ a) (hu : u ∈ b)
    (hcore : QuadOn G ((p.triangle ∪ a) \ {z, p.center, p.vertices 2}))
    (hrepP : QuadOn G (insert (q 3) (b.erase u)))
    (hrepQ : QuadOn G (insert (p.vertices 2) (q.support.erase (q 3))))
    (hf : Nonempty (BlockPartition G
      (insert u (insert p.leaf ({z, p.center} ∪ bs.biUnion id))))) : HasPacking G k := by
  have hF (t : Finset V) (ht : t ∈ c.blocks) : Disjoint p.support t := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ht)
  have hFO : Disjoint p.support (bs.biUnion id) := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (biUnion_subset_biUnion_of_subset_left id hsel)
  have hO (t : Finset V) (ht : t ∈ c.blocks) (htn : t ∉ bs) :
      Disjoint (bs.biUnion id) t := by
    rw [disjoint_biUnion_left]
    intro j hj
    exact c.property.blocks_disjoint (hsel hj) ht (fun he ↦ htn (he ▸ hj))
  have hpm (i : Fin 4) : p.vertices i ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hbase (t : Finset V) (ht : t ∈ c.blocks) (htn : t ∉ bs) (hat : a ≠ t) :
      Disjoint (insert p.leaf ({z, p.center} ∪ bs.biUnion id)) t := by
    refine disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp (hF t ht) (hpm 0) hh, ?_⟩
    refine disjoint_union_left.mpr ⟨?_, hO t ht htn⟩
    exact disjoint_insert_left.mpr
      ⟨fun hh ↦ disjoint_left.mp (c.property.blocks_disjoint ha ht hat) hz hh,
        disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp (hF t ht) (hpm 1) hh)⟩
  have hBQ : Disjoint b q.support := by rw [hq]; exact c.property.blocks_disjoint hb hs hbs
  have hbaseQ : Disjoint (insert p.leaf ({z, p.center} ∪ bs.biUnion id)) q.support := by
    rw [hq]
    exact hbase s hs hsn has
  have hsecond := disjoint_union_left.mpr ⟨hbaseQ, hBQ⟩
  have hbx : p.vertices 2 ≠ p.leaf := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)
  have hbr : p.vertices 2 ≠ p.center := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)
  have hbz : p.vertices 2 ≠ z := fun he ↦ disjoint_left.mp (hF a ha) (hpm 2) (he.symm ▸ hz)
  have hwbase : p.vertices 2 ∉ insert p.leaf ({z, p.center} ∪ bs.biUnion id) := by
    simp only [mem_insert, mem_union, mem_singleton, not_or]
    exact ⟨hbx, ⟨hbz, hbr⟩, fun hh ↦ disjoint_left.mp hFO (hpm 2) hh⟩
  have hw : p.vertices 2 ∉
      (insert p.leaf ({z, p.center} ∪ bs.biUnion id) ∪ b) ∪ q.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact (mem_union.mp hh).elim hwbase (fun hh ↦ disjoint_left.mp (hF b hb) (hpm 2) hh)
    · rw [hq] at hh
      exact disjoint_left.mp (hF s hs) (hpm 2) hh
  have hparts := two_replacement_partition (hbase b hb hbn hab) hsecond hu
    ((q.mem_support _).mpr ⟨3, rfl⟩) hw hf hrepP hrepQ
  have he : insert (p.vertices 2)
      ((insert p.leaf ({z, p.center} ∪ bs.biUnion id) ∪ b) ∪ q.support) =
      insert p.leaf ({z, p.center, p.vertices 2} ∪ (insert s (insert b bs)).biUnion id) := by
    rw [hq]
    simp only [biUnion_insert, id_eq, insert_union, singleton_union]
    rw [insert_comm (p.vertices 2) p.leaf, insert_comm (p.vertices 2) z,
      insert_comm (p.vertices 2) p.center]
    congr 4
    ac_rfl
  have huCore : ({z, p.center, p.vertices 2} : Finset V) ⊆ p.triangle ∪ a :=
    insert_subset (mem_union_right _ hz) (insert_subset (mem_union_left _ p.center_mem_triangle)
      (singleton_subset_iff.mpr (mem_union_left _ (by simp [Paw.triangle]))))
  apply JointFirst.hasPacking_of_selected_core hcard p hp ha (insert s (insert b bs))
    (insert_subset hs (insert_subset hb hsel)) ?_ huCore hcore (he ▸ hparts)
  simpa only [mem_insert, not_or] using And.intro has (And.intro hab han)

end Erdos577.JointBridge
