import ErdosProblems.Erdos577.PathMiddleReplacements

/-! Degree consequences of a prohibited common replacement into a complete block. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma no_common_replacement_degree_sum {s : Finset V} (hcl : G.IsNClique 4 s)
    (b c z : V) (hz : z ∉ s) (hrow : 3 ≤ degreeIn G z s)
    (hn : ¬CommonReplacement G b c z s) : degreeIn G b s + degreeIn G c s ≤ 4 := by
  by_contra! hh
  have hbound : ((s.filter (G.Adj b)) ∪ (s.filter (G.Adj c))).card ≤ 4 := by
    rw [← hcl.card_eq]
    exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  obtain ⟨u, hu, hbu, hcu⟩ := common_neighbor_of_union_bound b c s 4 hbound hh
  exact hn ⟨u, hu, hbu, hcu, clique_replace_of_degree_three hcl hz hrow hu⟩

lemma no_common_replacement_degree_le_two {s : Finset V} (hcl : G.IsNClique 4 s)
    (b c z : V) (hz : z ∉ s) (hn : ¬CommonReplacement G b c z s)
    (hcommon : ∃ u ∈ s, G.Adj b u ∧ G.Adj c u) : degreeIn G z s ≤ 2 := by
  by_contra! hh
  obtain ⟨u, hu, hbu, hcu⟩ := hcommon
  exact hn ⟨u, hu, hbu, hcu, clique_replace_of_degree_three hcl hz hh hu⟩

lemma no_common_replacement_degree_le_one {s : Finset V} (hcl : G.IsNClique 4 s)
    (b c z : V) (hz : z ∉ s) (hn : ¬CommonReplacement G b c z s)
    (u : V) (hu : u ∈ s) (hbu : G.Adj b u) (hcu : G.Adj c u) (hzu : ¬G.Adj z u) :
    degreeIn G z s ≤ 1 := by
  by_contra! hh
  have he := degreeIn_erase_add G z u hu
  rw [if_neg hzu] at he
  have htwo : 2 ≤ degreeIn G z (s.erase u) := by omega
  exact hn ⟨u, hu, hbu, hcu, (clique_replace_iff_two_contacts hcl hz hu).mpr htwo⟩

end Erdos577
