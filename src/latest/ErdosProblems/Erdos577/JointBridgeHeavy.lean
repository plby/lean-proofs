import ErdosProblems.Erdos577.JointBridgeInside
import ErdosProblems.Erdos577.OutsideSelectedCount

/-! The inside budget thirty forces a nine-contact block outside all three selected blocks. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_nine_outside_three {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) (hbs3 : bs.card = 3)
    (r : Finset V) (hr : r.card = 4) (hinside : contacts G r (c.remainder ∪ bs.biUnion id) ≤ 30) :
    ∃ j ∈ c.blocks, j ∉ bs ∧ 9 ≤ contacts G r j := by
  have hblocks := c.card_vertices
  have hsub := card_sdiff_of_subset hbs
  have hge := card_le_card hbs
  obtain ⟨j, hj, hjs, hh⟩ := c.exists_heavy_outside_selected bs hbs r (2 * k) 8 hdeg (by
    rw [hr]
    omega)
  exact ⟨j, hj, hjs, Nat.succ_le_of_lt hh⟩

theorem exists_heavy_arms {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a b : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (hb : b ∈ c.blocks)
    (has : a ≠ s) (hab : a ≠ b) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (u z1 z2 : V) (hu : u ∈ b) (h1 : z1 ∈ a) (h2 : z2 ∈ a) (hne : z1 ≠ z2)
    (hinside : contacts G (arms p u z1 z2) (p.support ∪ q.support ∪ a ∪ b) ≤ 30) :
    ∃ j ∈ c.blocks, j ≠ s ∧ j ≠ a ∧ j ≠ b ∧ 9 ≤ contacts G (arms p u z1 z2) j := by
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hFB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hr4 := arms_card p u z1 z2 hFA hFB (c.property.blocks_disjoint ha hb hab) hu h1 h2 hne
  have hsel : ({s, a, b} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hs (insert_subset ha (singleton_subset_iff.mpr hb))
  have hthree : ({s, a, b} : Finset (Finset V)).card = 3 :=
    card_triple_eq_three_iff.mpr ⟨has.symm, hbs.symm, hab⟩
  have he : c.remainder ∪ ({s, a, b} : Finset (Finset V)).biUnion id =
      p.support ∪ q.support ∪ a ∪ b := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, ← hp, ← hq, union_assoc]
  obtain ⟨j, hj, hjn, hh⟩ := exists_nine_outside_three hcard hdeg {s, a, b} hsel hthree
    (arms p u z1 z2) hr4 (he.symm ▸ hinside)
  simp only [mem_insert, mem_singleton, not_or] at hjn
  exact ⟨j, hj, hjn.1, hjn.2.1, hjn.2.2, hh⟩

end Erdos577.JointBridge
