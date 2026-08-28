import ErdosProblems.Erdos577.AlmostComplete
import ErdosProblems.Erdos577.Attachment

/-! Almost-complete core obstructions inside actual triangle chains. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem terminal_core_degree_le_one_of_dense_clique (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hq : G.IsNClique 4 b)
    (ht : 11 ≤ contacts G c.triangle b) :
    degreeIn G c.terminal (c.triangle ∪ b) ≤ 1 := by
  have hd : Disjoint c.remainder b :=
    c.property.remainder_disjoint.mono le_rfl (c.blockPartition.block_subset hb)
  have htri : c.triangle ⊆ c.remainder := subset_insert _ _
  have hxt : c.terminal ∉ c.triangle := c.property.terminal_not_mem
  have hxb : c.terminal ∉ b := fun h ↦
    (disjoint_left.mp hd) (mem_insert_self c.terminal c.triangle) h
  by_contra hh
  have htwo : 2 ≤ degreeIn G c.terminal (c.triangle ∪ b) := by omega
  have hg := dense_triangle_clique_factor c.property.triangle_clique hq (hd.mono_left htri)
    ht (by simpa only [mem_union, not_or] using And.intro hxt hxb) htwo
  have he : insert c.terminal (c.triangle ∪ b) = c.remainder ∪ b := by
    change insert c.terminal (c.triangle ∪ b) = insert c.terminal c.triangle ∪ b
    exact (insert_union _ _ _).symm
  rw [he] at hg
  exact c.no_local_factor hcard hn hb hg

theorem Strong.terminal_degree_eq_zero_of_dense_clique {c : TriangleChain G} (hc : c.Strong)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hq : G.IsNClique 4 b)
    (ht : 11 ≤ contacts G c.triangle b) : degreeIn G c.terminal b = 0 := by
  have hd : Disjoint c.triangle b :=
    c.property.remainder_disjoint.mono (subset_insert _ _) (c.blockPartition.block_subset hb)
  have hle := c.terminal_core_degree_le_one_of_dense_clique hcard hn hb hq ht
  rw [degreeIn_union G c.terminal hd] at hle
  have ha : degreeIn G c.terminal c.triangle = 1 := hc.attached
  omega

end Erdos577.TriangleChain
