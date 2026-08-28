import ErdosProblems.Erdos577.ReplacementFactors

/-! Two consecutive vertex replacements have an exact complementary two-cycle factor. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma LocalFactor.of_two_stage_replacement {s t : Finset V} {x y u : V}
    (hd : Disjoint s t) (hx : x ∉ s ∪ t) (hy : y ∈ t) (hu : u ∈ s)
    (hs : QuadOn G (insert y (s.erase u))) (ht : QuadOn G (insert x (t.erase y))) :
    LocalFactor G (insert x ((s ∪ t).erase u)) := by
  have hx' : x ∉ s.erase u ∪ t := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact hx (mem_union_left _ (mem_erase.mp hh).2)
    · exact hx (mem_union_right _ hh)
  have hu' : u ∉ t := fun hh ↦ disjoint_left.mp hd hu hh
  have hf := LocalFactor.of_replacement (hd.mono_left (erase_subset u s)) hx' hy hs ht
  simpa only [erase_union_distrib, erase_eq_of_notMem hu'] using hf

end Erdos577
