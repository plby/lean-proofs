import ErdosProblems.Erdos577.LargeLeafPreparation

/-! The actual labeled configuration for the full-leaf core in TeX9.71. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure Configuration (c : TriangleChain G) (p : Paw G) (s a : Finset V) (y : V) : Prop where
  feasible : c.Feasible
  paw : p.support = c.remainder
  first : s ∈ c.blocks
  core : a ∈ c.blocks
  different : a ≠ s
  full : degreeIn G p.leaf s = 4
  exposed : y ∈ s
  attached : G.Adj (p.vertices 2) y
  dense : 11 ≤ contacts G p.triangle a

variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.paw_disjoint {j : Finset V} (hj : j ∈ c.blocks) :
    Disjoint p.support j := by
  rw [h.paw]
  exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)

lemma Configuration.first_clique : G.IsNClique 4 s :=
  FullRow.full_leaf_clique h.feasible p h.paw h.first h.full

lemma Configuration.core_clique : G.IsNClique 4 a :=
  ((h.feasible.presentPaw_feasible p h.paw).all_triangle_universal_replacements
    h.core h.dense).1

lemma Configuration.leaf_out : p.leaf ∉ s :=
  (c.presentPaw p h.paw).terminal_not_mem_block h.first

lemma Configuration.core_disjoint_first : Disjoint (p.triangle ∪ a) s :=
  disjoint_union_left.mpr
    ⟨(h.paw_disjoint h.first).mono_left (p.support_eq ▸ subset_insert _ _),
      c.property.blocks_disjoint h.core h.first h.different⟩

lemma Configuration.five_disjoint_core : Disjoint (insert p.leaf s) (p.triangle ∪ a) := by
  apply disjoint_insert_left.mpr
  refine ⟨?_, h.core_disjoint_first.symm⟩
  intro hh
  rcases mem_union.mp hh with hh | hh
  · exact p.leaf_not_mem_triangle hh
  · exact disjoint_left.mp (h.paw_disjoint h.core)
      (p.support_eq ▸ mem_insert_self _ _) hh

lemma Configuration.first_five_clique : G.IsNClique 5 (insert p.leaf s) :=
  h.first_clique.insert ((degreeIn_eq_card_iff p.leaf s).mp
    (h.full.trans h.first_clique.card_eq.symm))

lemma Configuration.first_triple_clique : G.IsNClique 3 (s.erase y) := by
  refine ⟨h.first_clique.isClique.subset (coe_subset.mpr (erase_subset _ _)), ?_⟩
  rw [card_erase_of_mem h.exposed, h.first_clique.card_eq]

lemma Configuration.five_complement_clique {x : V} (hx : x ∈ insert p.leaf s) :
    G.IsNClique 4 ((insert p.leaf s).erase x) := by
  refine ⟨h.first_five_clique.isClique.subset (coe_subset.mpr (erase_subset _ _)), ?_⟩
  rw [card_erase_of_mem hx, h.first_five_clique.card_eq]

lemma Configuration.second_five_card : (insert (p.vertices 3) a).card = 5 := by
  have hout : p.vertices 3 ∉ a := fun hh ↦ disjoint_left.mp (h.paw_disjoint h.core)
    ((mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩) hh
  rw [card_insert_of_notMem hout, h.core_clique.card_eq]

lemma Configuration.second_five_eq :
    insert (p.vertices 3) a = (p.triangle ∪ a) \ {p.center, p.vertices 2} := by
  have hr : p.center ∉ a := fun hh ↦ disjoint_left.mp (h.paw_disjoint h.core)
    (show p.center ∈ p.support from (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩) hh
  have hb : p.vertices 2 ∉ a := fun hh ↦ disjoint_left.mp (h.paw_disjoint h.core)
    ((mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩) hh
  have hcr : p.vertices 3 ≠ p.center := p.vertices.injective.ne (by decide : (3 : Fin 4) ≠ 1)
  have hcb : p.vertices 3 ≠ p.vertices 2 := p.vertices.injective.ne (by decide : (3 : Fin 4) ≠ 2)
  ext v
  simp only [mem_insert, mem_union, mem_sdiff, mem_singleton, Paw.triangle]
  constructor
  · rintro (rfl | hv)
    · exact ⟨Or.inl (Or.inr (Or.inr rfl)), by simpa only [not_or] using And.intro hcr hcb⟩
    · exact ⟨Or.inr hv, fun hh ↦ hh.elim (fun he ↦ hr (he ▸ hv)) (fun he ↦ hb (he ▸ hv))⟩
  · rintro ⟨hh, hn⟩
    rcases hh with hh | hh
    · rcases hh with hh | hh | hh
      · exact False.elim (hn (Or.inl hh))
      · exact False.elim (hn (Or.inr hh))
      · exact Or.inl hh
    · exact Or.inr hh

lemma Configuration.second_five_subset : insert (p.vertices 3) a ⊆ p.triangle ∪ a := by
  rw [h.second_five_eq]
  exact sdiff_subset

lemma Configuration.core_complement_quad {u : Finset V} (hu : u ⊆ p.triangle ∪ a)
    (hthree : u.card = 3) : QuadOn G ((p.triangle ∪ a) \ u) := by
  have hd : Disjoint p.triangle a :=
    (h.paw_disjoint h.core).mono_left (p.support_eq ▸ subset_insert _ _)
  apply JointCore.dense_four_subset p.triangle_clique h.core_clique hd h.dense sdiff_subset
  rw [card_sdiff_of_subset hu, card_union_of_disjoint hd, p.triangle_clique.card_eq,
    h.core_clique.card_eq, hthree]

theorem Configuration.exposed_chain {x : V} (hx : x ∈ insert p.leaf s) :
    ∃ e : TriangleChain G, e.Feasible ∧ e.terminal = x ∧ e.triangle = p.triangle ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore ∧
      ∀ j ∈ c.blocks, j ≠ s → j ∈ e.blocks := by
  rcases mem_insert.mp hx with rfl | hx
  · exact ⟨c.presentPaw p h.paw, h.feasible.presentPaw_feasible p h.paw,
      rfl, rfl, rfl, rfl, fun _ hj _ ↦ hj⟩
  · obtain ⟨hq, he⟩ := FullRow.full_leaf_replacement h.feasible p h.paw h.first h.full x hx
    exact TwoExposed.one_route h.feasible p h.paw h.first x hx hq he

theorem Configuration.first_core_degree {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {x : V} (hx : x ∈ insert p.leaf s) :
    degreeIn G x (p.triangle ∪ a) ≤ 1 := by
  obtain ⟨e, _, he, ht, _, _, hkeep⟩ := h.exposed_chain hx
  have hb := e.terminal_core_degree_le_one_of_dense_clique hcard hn
    (hkeep a h.core h.different) h.core_clique (by simpa only [ht] using h.dense)
  simpa only [he, ht] using hb

end Erdos577.FullLeafCore
