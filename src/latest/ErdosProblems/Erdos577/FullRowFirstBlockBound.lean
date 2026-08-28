import ErdosProblems.Erdos577.FullRowCommonFactor
import ErdosProblems.Erdos577.FullRowCompleteBlock
import ErdosProblems.Erdos577.TwoStageReplacement

/-! Actual three- and four-cycle factors bound every outside-block row on the first block. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem first_block_degree_le_one_direct {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hleaf : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s)
    (hfull : degreeIn G (p.vertices 3) a = 4) (u : V) (hu : u ∈ a) :
    degreeIn G u q.support ≤ 1 := by
  by_contra! hrow
  have hd : Disjoint p.support q.support := by
    apply disjoint_left.mpr
    intro v hv hqv
    exact (mem_sdiff.mp (c.complementPartition.block_subset hs (hq ▸ hqv))).2 (hp ▸ hv)
  have hout : u ∉ q.support := by
    intro hh
    exact disjoint_left.mp (c.property.blocks_disjoint ha hs has) hu (hq ▸ hh)
  have hcom := common_insertion hc p hp hs q hq hleaf hseven u hout (by omega)
  have hrep := (c.property.blocks_quad a ha).replace_of_degree_four
    (full_row_outside (c.property.blocks_quad a ha) (p.vertices 3) hfull) hfull hu
  apply hn
  apply hasPacking_of_common_insertion hcard p hp hs q hq hd {a}
    (singleton_subset_iff.mpr ha) (by simpa only [mem_singleton] using has.symm)
    (u := u) (by simpa only [singleton_biUnion, id_eq] using hu) hcom
  simpa only [singleton_biUnion, id_eq] using
    (show Nonempty (BlockPartition G (insert (p.vertices 3) (a.erase u))) from
      ⟨BlockPartition.single hrep⟩)

theorem first_block_degree_le_one_other {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hleaf : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s)
    {b : Finset V} (hb : b ∈ c.blocks) (hbs : b ≠ s)
    (z : V) (hz : z ∈ b) (hfull : degreeIn G z a = 4)
    (hrepB : QuadOn G (insert (p.vertices 3) (b.erase z))) (u : V) (hu : u ∈ a) :
    degreeIn G u q.support ≤ 1 := by
  by_contra! hrow
  have hzout := full_row_outside (c.property.blocks_quad a ha) z hfull
  have hab : a ≠ b := fun he ↦ hzout (he.symm ▸ hz)
  have hdAB := c.property.blocks_disjoint ha hb hab
  have hd : Disjoint p.support q.support := by
    apply disjoint_left.mpr
    intro v hv hqv
    exact (mem_sdiff.mp (c.complementPartition.block_subset hs (hq ▸ hqv))).2 (hp ▸ hv)
  have hout : u ∉ q.support := by
    intro hh
    exact disjoint_left.mp (c.property.blocks_disjoint ha hs has) hu (hq ▸ hh)
  have hcom := common_insertion hc p hp hs q hq hleaf hseven u hout (by omega)
  have hthird : p.vertices 3 ∈ c.remainder := hp ▸ (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩
  have hthirdOut : p.vertices 3 ∉ a ∪ b := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact (mem_sdiff.mp (c.complementPartition.block_subset ha hh)).2 hthird
    · exact (mem_sdiff.mp (c.complementPartition.block_subset hb hh)).2 hthird
  have hrepA := (c.property.blocks_quad a ha).replace_of_degree_four hzout hfull hu
  have hf := LocalFactor.of_two_stage_replacement hdAB hthirdOut hz hu hrepA hrepB
  apply hn
  apply hasPacking_of_common_insertion hcard p hp hs q hq hd {a, b}
    (by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨ha, hb⟩)
    (by simp only [mem_insert, mem_singleton]; exact not_or.mpr ⟨has.symm, hbs.symm⟩)
    (u := u) (by simp only [biUnion_insert, singleton_biUnion, id_eq]; exact mem_union_left _ hu)
    hcom
  simpa only [biUnion_insert, singleton_biUnion, id_eq] using hf.partition

end Erdos577.FullRow
