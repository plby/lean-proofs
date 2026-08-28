import ErdosProblems.Erdos577.FullLeafCoreBridge

/-! The second-five prohibitions and the matching between the two core sets. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.used_triple {u : V} (hu : u ∈ insert (p.vertices 3) a) :
    ({p.center, p.vertices 2, u} : Finset V) ⊆ p.triangle ∪ a ∧
      ({p.center, p.vertices 2, u} : Finset V).card = 3 := by
  obtain ⟨huK, hur, hub⟩ := h.second_avoids hu
  exact ⟨insert_subset (mem_union_left _ p.center_mem_triangle)
    (insert_subset (mem_union_left _ (by simp [Paw.triangle])) (singleton_subset_iff.mpr huK)),
    card_triple_eq_three_iff.mpr
      ⟨p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2), hur.symm, hub.symm⟩⟩

lemma Configuration.bridge_disjoint_block {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) :
    Disjoint ({p.leaf, p.center, p.vertices 2, y} : Finset V) j := by
  have hsub : ({p.leaf, p.center, p.vertices 2, y} : Finset V) ⊆ p.support ∪ s := by
    have hm (i : Fin 4) : p.vertices i ∈ p.support :=
      (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
    exact insert_subset (mem_union_left _ (hm 0))
      (insert_subset (mem_union_left _ (hm 1))
        (insert_subset (mem_union_left _ (hm 2))
          (singleton_subset_iff.mpr (mem_union_right _ h.exposed))))
  exact (disjoint_union_left.mpr ⟨h.paw_disjoint hj,
    c.property.blocks_disjoint h.first hj hjs.symm⟩).mono_left hsub

theorem Configuration.second_triple_degree {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {u : V} (hu : u ∈ insert (p.vertices 3) a) :
    degreeIn G u (s.erase y) ≤ 1 := by
  by_contra htwo
  have huK := h.second_five_subset hu
  have huS : u ∉ s := fun hh ↦ disjoint_left.mp h.core_disjoint_first huK hh
  have hf := QuadOn.of_triangle h.first_triple_clique
    (fun hh ↦ huS (mem_erase.mp hh).2) (by omega : 2 ≤ degreeIn G u (s.erase y))
  have hp := h.partition_with_bridge hu ∅ (disjoint_empty_right _) (by
    simpa only [union_empty] using (show Nonempty (BlockPartition G (insert u (s.erase y)))
      from ⟨BlockPartition.single hf⟩))
  rw [union_empty] at hp
  obtain ⟨hsub, hthree⟩ := h.used_triple hu
  exact hn (JointCore.hasPacking_of_partial_core hcard p h.paw h.core h.first h.different
    hsub (h.core_complement_quad hsub hthree) hp)

theorem Configuration.second_no_factor {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {u : V} (hu : u ∈ insert (p.vertices 3) a)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a) :
    ¬LocalFactor G (insert u ((s.erase y) ∪ j)) := by
  intro hf
  have hp := h.partition_with_bridge hu j (h.bridge_disjoint_block hj hjs) hf.partition
  have hsel : ({s, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.first (singleton_subset_iff.mpr hj)
  have hna : a ∉ ({s, j} : Finset (Finset V)) := by
    simpa only [mem_insert, mem_singleton, not_or] using And.intro h.different hja.symm
  obtain ⟨hsub, hthree⟩ := h.used_triple hu
  apply hn (JointFirst.hasPacking_of_selected_core hcard p h.paw h.core {s, j} hsel hna
    hsub (h.core_complement_quad hsub hthree) ?_)
  simpa only [biUnion_insert, singleton_biUnion, id_eq] using hp

theorem Configuration.second_no_replacement {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {u : V} (hu : u ∈ insert (p.vertices 3) a)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    {v : V} (hv : v ∈ j) (htwo : 2 ≤ degreeIn G v (s.erase y)) :
    ¬QuadOn G (insert u (j.erase v)) := by
  intro hrep
  have hSJ := c.property.blocks_disjoint h.first hj hjs.symm
  have hvS : v ∉ s := fun hh ↦ disjoint_left.mp hSJ hh hv
  have hquad := QuadOn.of_triangle h.first_triple_clique
    (fun hh ↦ hvS (mem_erase.mp hh).2) htwo
  have hKJ : Disjoint (p.triangle ∪ a) j := disjoint_union_left.mpr
    ⟨(h.paw_disjoint hj).mono_left (p.support_eq ▸ subset_insert _ _),
      c.property.blocks_disjoint h.core hj hja.symm⟩
  have huK := h.second_five_subset hu
  have hout : u ∉ (s.erase y) ∪ j := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp h.core_disjoint_first huK (mem_erase.mp hh).2
    · exact disjoint_left.mp hKJ huK hh
  exact h.second_no_factor hcard hn hu hj hjs hja
    (LocalFactor.of_replacement (hSJ.mono_left (erase_subset _ _)) hout hv hquad hrep)

theorem Configuration.matching_degrees {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) :
    (∀ x ∈ s.erase y, degreeIn G x (insert (p.vertices 3) a) ≤ 1) ∧
      (∀ u ∈ insert (p.vertices 3) a, degreeIn G u (s.erase y) ≤ 1) := by
  refine ⟨fun x hx ↦ ?_, fun _ hu ↦ h.second_triple_degree hcard hn hu⟩
  exact (degreeIn_mono G x h.second_five_subset).trans
    (h.first_core_degree hcard hn (mem_insert_of_mem (mem_erase.mp hx).2))

theorem Configuration.center_degrees :
    4 ≤ degreeIn G p.center (insert (p.vertices 3) a) ∧
      4 ≤ degreeIn G (p.vertices 2) (insert (p.vertices 3) a) := by
  have hout : p.vertices 3 ∉ a := fun hh ↦ disjoint_left.mp (h.paw_disjoint h.core)
    ((mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩) hh
  have hr := every_row_high_of_eleven p.triangle_clique.card_eq h.core_clique.card_eq
    h.dense p.center_mem_triangle
  have hb := every_row_high_of_eleven p.triangle_clique.card_eq h.core_clique.card_eq
    h.dense (show p.vertices 2 ∈ p.triangle by simp [Paw.triangle])
  rw [degreeIn_insert G p.center (p.vertices 3) hout,
    if_pos (show G.Adj p.center (p.vertices 3) from p.edge13),
    degreeIn_insert G (p.vertices 2) (p.vertices 3) hout, if_pos p.edge23]
  omega

end Erdos577.FullLeafCore
