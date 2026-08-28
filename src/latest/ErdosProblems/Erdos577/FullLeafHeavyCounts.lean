import ErdosProblems.Erdos577.FullLeafCore

/-! Exact contact sums and replacement consequences for the heavy-block classification. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.first_contacts (j : Finset V) :
    contacts G (insert p.leaf s) j = degreeIn G p.leaf j + degreeIn G y j +
      contacts G (s.erase y) j := by
  have he := sum_erase_add (s := s) (fun v ↦ degreeIn G v j) h.exposed
  rw [contacts, sum_insert h.leaf_out]
  change _ = degreeIn G p.leaf j + degreeIn G y j + ∑ v ∈ s.erase y, degreeIn G v j
  omega

lemma Configuration.combined_contacts (j : Finset V) :
    contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j =
      contacts G (insert p.leaf s) j + contacts G (insert (p.vertices 3) a) j :=
  contacts_union_left G (h.five_disjoint_core.mono_right h.second_five_subset) j

theorem Configuration.core_degree_of_first_replacement {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {x : V} (hx : x ∈ insert p.leaf s) {j : Finset V}
    (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    {v : V} (hv : v ∈ j) (hrep : QuadOn G (insert x (j.erase v))) :
    degreeIn G v (p.triangle ∪ a) ≤ 1 := by
  by_contra htwo
  exact h.first_no_replacement hcard hn hx hj hjs hja hv (by omega) hrep

theorem Configuration.triple_degree_of_second_replacement {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {u : V} (hu : u ∈ insert (p.vertices 3) a) {j : Finset V}
    (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    {v : V} (hv : v ∈ j) (hrep : QuadOn G (insert u (j.erase v))) :
    degreeIn G v (s.erase y) ≤ 1 := by
  by_contra htwo
  exact h.second_no_replacement hcard hn hu hj hjs hja hv (by omega) hrep

theorem Configuration.first_universal_replacements {x : V} (hx : x ∈ insert p.leaf s)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hrow : 3 ≤ degreeIn G x j) :
    ∀ v ∈ j, QuadOn G (insert x (j.erase v)) := by
  obtain ⟨e, he, ht, _, _, _, hkeep⟩ := h.exposed_chain hx
  intro v hv
  simpa only [ht] using he.terminal_universal_replace (hkeep j hj hjs)
    (by simpa only [ht] using hrow) hv

theorem Configuration.complete_of_first_full {x : V} (hx : x ∈ insert p.leaf s)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hrow : degreeIn G x j = 4) :
    G.IsNClique 4 j := by
  obtain ⟨e, he, ht, _, _, _, hkeep⟩ := h.exposed_chain hx
  exact he.clique_of_terminal_degree_four (hkeep j hj hjs) (by simpa only [ht] using hrow)

end Erdos577.FullLeafCore
