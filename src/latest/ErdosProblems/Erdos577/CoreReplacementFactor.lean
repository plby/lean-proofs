import ErdosProblems.Erdos577.PartitionReplacement
import ErdosProblems.Erdos577.TriangleAssembly
import ErdosProblems.Erdos577.DenseTriangle
import ErdosProblems.Erdos577.TerminalReplacements

/-! A factor on the seven-vertex core plus a block vertex closes with a terminal replacement. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem hasPacking_of_core_replacement (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) {a b : Finset V}
    (ha : a ∈ c.blocks) (hb : b ∈ c.blocks) (hab : a ≠ b) {u : V} (hu : u ∈ a)
    (hcore : LocalFactor G (insert u (c.triangle ∪ b)))
    (hrep : QuadOn G (insert c.terminal (a.erase u))) : HasPacking G k := by
  have hd : Disjoint (c.triangle ∪ b) a := disjoint_union_left.mpr
    ⟨c.triangle_disjoint_block ha, c.property.blocks_disjoint hb ha hab.symm⟩
  have hx : c.terminal ∉ (c.triangle ∪ b) ∪ a := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact (mem_union.mp hh).elim c.property.terminal_not_mem (c.terminal_not_mem_block hb)
    · exact c.terminal_not_mem_block ha hh
  obtain ⟨p⟩ := hcore.partition
  let f := BlockPartition.replacementUnion hd hx hu p (BlockPartition.single hrep)
  have hsel : ({b, a} : Finset (Finset V)) ⊆ c.blocks := by
    intro d hd
    rcases mem_insert.mp hd with hd | hd
    · exact hd ▸ hb
    · exact (mem_singleton.mp hd) ▸ ha
  have he : insert c.terminal ((c.triangle ∪ b) ∪ a) =
      c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id := by
    change _ = insert c.terminal c.triangle ∪ _
    simp only [biUnion_insert, singleton_biUnion, id_eq, insert_union, union_assoc]
  exact c.complementPartition.hasPacking_of_selected_factor hcard {b, a} hsel (he ▸ f)

variable [DecidableRel G.Adj]

theorem Feasible.terminal_degree_le_two_of_core_factor {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {a b : Finset V} (ha : a ∈ c.blocks) (hb : b ∈ c.blocks) (hab : a ≠ b)
    {u : V} (hu : u ∈ a) (hcore : LocalFactor G (insert u (c.triangle ∪ b))) :
    degreeIn G c.terminal a ≤ 2 := by
  by_contra! hh
  exact hn (c.hasPacking_of_core_replacement hcard ha hb hab hu hcore
    (hc.terminal_universal_replace ha (by omega) hu))

end Erdos577.TriangleChain
