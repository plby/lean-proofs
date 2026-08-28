import ErdosProblems.Erdos577.JointBridgeCompletion
import ErdosProblems.Erdos577.JointBridgeCoreBound

/-! The leaf and both distinguished core vertices have disjoint neighbor rows on the bridge. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem leaf_core_common_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a b : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (hb : b ∈ c.blocks)
    (has : a ≠ s) (hab : a ≠ b) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseTwo p q)
    (hthree : 3 ≤ degreeIn G (q 3) b)
    {z : V} (hz : z ∈ a) (hrz : G.Adj p.center z)
    (hcore : QuadOn G ((p.triangle ∪ a) \ {z, p.center, p.vertices 2}))
    (u : V) (hu : u ∈ b) : ¬(G.Adj p.leaf u ∧ G.Adj z u) := by
  rintro ⟨hxu, hzu⟩
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hFB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hrF : p.center ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩
  have hur : u ≠ p.center := fun he ↦ disjoint_left.mp hFB hrF (he ▸ hu)
  have hxz : p.leaf ≠ z := fun he ↦ disjoint_left.mp hFA hxF (he.symm ▸ hz)
  have hquad : QuadOn G {u, p.leaf, p.center, z} :=
    QuadOn.of_vertices hur hxz hxu.symm p.pendant hrz hzu
  have he : ({u, p.leaf, p.center, z} : Finset V) =
      insert u (insert p.leaf ({z, p.center} ∪ (∅ : Finset (Finset V)).biUnion id)) := by
    simp only [biUnion_empty, union_empty]
    rw [pair_comm z p.center]
  have hrepP := (JointClaims.eight_terminal_rows hc hcard hn p hp hs hb hbs q hq
    hcase hthree).1 u hu
  have hrepQ := JointClaims.case_two_universal hc p hp hs q hq hcase (q 3)
    ((q.mem_support _).mpr ⟨3, rfl⟩)
  exact hn (hasPacking_of_bridge_partial hcard p hp hs ha hb has hab hbs q hq
    ∅ (empty_subset _) (by simp) (by simp) (by simp) hz hu hcore hrepP hrepQ
    ⟨BlockPartition.single (he ▸ hquad)⟩)

theorem three_rows_on_bridge {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a b : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (hb : b ∈ c.blocks)
    (has : a ≠ s) (hab : a ≠ b) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseTwo p q)
    (hthree : 3 ≤ degreeIn G (q 3) b)
    (hcore : ∀ v, v ∉ p.triangle ∪ a → 2 ≤ degreeIn G v (p.triangle ∪ a) →
      LocalFactor G (insert v (p.triangle ∪ a)))
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a) (hne : z1 ≠ z2)
    (hr1 : G.Adj p.center z1) (hr2 : G.Adj p.center z2)
    (hc1 : QuadOn G ((p.triangle ∪ a) \ {z1, p.center, p.vertices 2}))
    (hc2 : QuadOn G ((p.triangle ∪ a) \ {z2, p.center, p.vertices 2})) :
    contacts G {p.leaf, z1, z2} b ≤ 4 := by
  have hno1 := leaf_core_common_false hc hcard hn p hp hs ha hb has hab hbs q hq hcase
    hthree h1 hr1 hc1
  have hno2 := leaf_core_common_false hc hcard hn p hp hs ha hb has hab hbs q hq hcase
    hthree h2 hr2 hc2
  have hno12 (u : V) (hu : u ∈ b) : ¬(G.Adj z1 u ∧ G.Adj z2 u) := by
    rintro ⟨h1u, h2u⟩
    have hcol := block_core_degree_le_one hc hcard hn p hp hs ha hb has hbs hab.symm
      q hq hcase hthree hcore u hu
    have he := (FullRow.unique_row_of_bound (p.triangle ∪ a) u z1
      (mem_union_right _ h1) h1u.symm hcol).2 z2 (mem_union_right _ h2)
    exact hne ((he.mp h2u.symm).symm)
  have hbound := degree_triple_le_card p.leaf z1 z2 b hno1 hno2 hno12
  rw [(c.property.blocks_quad b hb).card] at hbound
  have h01 := JointCore.contacts_insert_upper (G := G) p.leaf {z1, z2} b
  have h12 := JointCore.contacts_insert_upper (G := G) z1 {z2} b
  rw [contacts_singleton_left] at h12
  omega

end Erdos577.JointBridge
