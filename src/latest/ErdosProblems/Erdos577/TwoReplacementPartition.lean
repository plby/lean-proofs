import ErdosProblems.Erdos577.PartitionReplacement

/-! Two consecutive vertex replacements join an actual factor and two disjoint four-blocks. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem two_replacement_partition {base first second : Finset V} {u v w : V}
    (hbase : Disjoint base first) (hsecond : Disjoint (base ∪ first) second)
    (hu : u ∈ first) (hv : v ∈ second) (hw : w ∉ (base ∪ first) ∪ second)
    (hf : Nonempty (BlockPartition G (insert u base)))
    (hfirst : QuadOn G (insert v (first.erase u)))
    (hlast : QuadOn G (insert w (second.erase v))) :
    Nonempty (BlockPartition G (insert w ((base ∪ first) ∪ second))) := by
  obtain ⟨part⟩ := hf
  have hvout : v ∉ base ∪ first := fun hh ↦ disjoint_left.mp hsecond hh hv
  let joined := part.replacementUnion hbase hvout hu (BlockPartition.single hfirst)
  exact ⟨joined.replacementUnion hsecond hw hv (BlockPartition.single hlast)⟩

end Erdos577
