import ErdosProblems.Erdos577.ReplacementFactors

/-! Complementary partitions can exchange one vertex across their supports. -/

namespace Erdos577.BlockPartition

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def replacementUnion {s t : Finset V} {x u : V} (hd : Disjoint s t)
    (hx : x ∉ s ∪ t) (hu : u ∈ t)
    (p : BlockPartition G (insert u s)) (q : BlockPartition G (insert x (t.erase u))) :
    BlockPartition G (insert x (s ∪ t)) := by
  have hdis : Disjoint (insert u s) (insert x (t.erase u)) := by
    apply disjoint_left.mpr
    intro w hw hq
    rcases mem_insert.mp hw with rfl | hw
    · rcases mem_insert.mp hq with he | hq
      · exact hx (mem_union_right _ (he ▸ hu))
      · exact (mem_erase.mp hq).1 rfl
    · rcases mem_insert.mp hq with rfl | hq
      · exact hx (mem_union_left _ hw)
      · exact disjoint_left.mp hd hw (mem_erase.mp hq).2
  have he : insert u s ∪ insert x (t.erase u) = insert x (s ∪ t) := by
    ext w
    have hwu : w = u → w ∈ t := fun hh ↦ hh ▸ hu
    simp only [mem_union, mem_insert, mem_erase]
    tauto
  exact he ▸ p.union q hdis

end Erdos577.BlockPartition
