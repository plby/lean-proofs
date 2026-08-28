import ErdosProblems.Erdos577.Replacements

/-! Necessary adjacency conditions for replacing every vertex of a quadrilateral. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma QuadOn.universal_replace_degree {s : Finset V} (hs : QuadOn G s) {z : V}
    (hz : z ∉ s) (hr : ∀ v ∈ s, QuadOn G (insert z (s.erase v))) :
    3 ≤ degreeIn G z s := by
  have htwo (v : V) (hv : v ∈ s) : 2 ≤ degreeIn G z (s.erase v) := by
    have h := (hr v hv).two_le_degreeIn (mem_insert_self _ _)
    rw [degreeIn_insert G z z (fun h ↦ hz (mem_erase.mp h).2)] at h
    simpa only [SimpleGraph.irrefl, if_false, Nat.zero_add] using h
  obtain ⟨a, ha⟩ := card_pos.mp (by rw [hs.card]; decide : 0 < s.card)
  have ha2 := htwo a ha
  have hp : 0 < degreeIn G z s := lt_of_lt_of_le (by omega : 0 < degreeIn G z (s.erase a))
    (degreeIn_mono G z (erase_subset a s))
  obtain ⟨v, hv⟩ := card_pos.mp hp
  obtain ⟨hvs, ezv⟩ := mem_filter.mp hv
  have he := degreeIn_erase_add G z v hvs
  rw [if_pos ezv] at he
  have h := htwo v hvs
  omega

lemma universal_replace_adjacent_to_degree_two {s : Finset V} {z v : V}
    (hz : z ∉ s) (hr : ∀ w ∈ s, QuadOn G (insert z (s.erase w)))
    (hv : v ∈ s) (hdeg : degreeIn G v s = 2) : G.Adj z v := by
  have hp : 0 < (s.filter (G.Adj v)).card := by change 0 < degreeIn G v s; omega
  obtain ⟨w, hw⟩ := card_pos.mp hp
  obtain ⟨hws, evw⟩ := mem_filter.mp hw
  have he := degreeIn_erase_add G v w hws
  rw [if_pos evw, hdeg] at he
  have hvnew : v ∈ insert z (s.erase w) := mem_insert_of_mem (mem_erase.mpr ⟨evw.ne, hv⟩)
  have htwo := (hr w hws).two_le_degreeIn hvnew
  rw [degreeIn_insert G v z (fun h ↦ hz (mem_erase.mp h).2)] at htwo
  by_contra hn
  have hvz : ¬G.Adj v z := fun h ↦ hn h.symm
  rw [if_neg hvz] at htwo
  omega

end Erdos577
