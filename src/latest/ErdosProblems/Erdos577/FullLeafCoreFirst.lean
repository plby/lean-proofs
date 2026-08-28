import ErdosProblems.Erdos577.FullLeafCoreConfig

/-! Both first-five factor prohibitions, using actual feasible terminal chains. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.first_no_factor (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {x : V} (hx : x ∈ insert p.leaf s) {j : Finset V}
    (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    {u : Finset V} (hu : u ⊆ p.triangle ∪ a) (hthree : u.card = 3) :
    ¬LocalFactor G (insert x (u ∪ j)) := by
  intro hf
  obtain ⟨e, _, he, ht, _, _, hkeep⟩ := h.exposed_chain hx
  have hsel : ({j} : Finset (Finset V)) ⊆ e.blocks :=
    singleton_subset_iff.mpr (hkeep j hj hjs)
  have hna : a ∉ ({j} : Finset (Finset V)) := by simpa using hja.symm
  have hu' : u ⊆ e.triangle ∪ a := by simpa only [ht] using hu
  have hr : QuadOn G ((e.triangle ∪ a) \ u) := by
    simpa only [ht] using h.core_complement_quad hu hthree
  apply hn (e.hasPacking_of_selected_core hcard (hkeep a h.core h.different)
    {j} hsel hna hu' hr ?_)
  simpa only [singleton_biUnion, id_eq, he] using hf.partition

theorem Configuration.first_no_replacement (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {x : V} (hx : x ∈ insert p.leaf s) {j : Finset V}
    (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    {v : V} (hv : v ∈ j) (htwo : 2 ≤ degreeIn G v (p.triangle ∪ a)) :
    ¬QuadOn G (insert x (j.erase v)) := by
  intro hrep
  obtain ⟨e, _, he, ht, _, _, hkeep⟩ := h.exposed_chain hx
  have hj' := hkeep j hj hjs
  have ha' := hkeep a h.core h.different
  have hd : Disjoint e.triangle a := e.triangle_disjoint_block ha'
  have hout : v ∉ e.triangle ∪ a := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp (e.triangle_disjoint_block hj') hh hv
    · exact disjoint_left.mp (e.property.blocks_disjoint hj' ha' hja) hv hh
  have hfactor := dense_triangle_clique_factor (ht ▸ p.triangle_clique) h.core_clique hd
    (by simpa only [ht] using h.dense) hout (by simpa only [ht] using htwo)
  exact hn (e.hasPacking_of_core_replacement hcard hj' ha' hja hv hfactor
    (by simpa only [he] using hrep))

end Erdos577.FullLeafCore
