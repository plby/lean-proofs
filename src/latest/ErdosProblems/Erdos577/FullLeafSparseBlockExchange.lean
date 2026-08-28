import ErdosProblems.Erdos577.FullLeafSparseTerminalSwap

/-! Three genuine terminal swaps exchange the two complete blocks and restore the paw. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.full_marked_block_exchange (h : Configuration c p s a y)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hX : degreeIn G p.leaf j = 4) (hY : degreeIn G y j = 4)
    {d : V} (hd : d ∈ j) (hdFull : degreeIn G d (insert p.leaf s) = 5) :
    ∃ e : TriangleChain G, Configuration e p (insert y (j.erase d)) a y ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore := by
  let t := insert p.leaf (s.erase y)
  let j' := insert y (j.erase d)
  have hXj : p.leaf ∉ j := fun hv ↦ disjoint_left.mp (h.paw_disjoint hj)
    (p.support_eq ▸ mem_insert_self _ _) hv
  have hXa : p.leaf ∉ a := fun hv ↦ disjoint_left.mp (h.paw_disjoint h.core)
    (p.support_eq ▸ mem_insert_self _ _) hv
  have hYj : y ∉ j := fun hv ↦
    disjoint_left.mp (c.property.blocks_disjoint h.first hj hjs.symm) h.exposed hv
  have hYa : y ∉ a := fun hv ↦
    disjoint_left.mp (c.property.blocks_disjoint h.first h.core h.different.symm) h.exposed hv
  have hYX : y ≠ p.leaf := fun he ↦ h.leaf_out (he ▸ h.exposed)
  have hYt : y ∉ t := by simp only [t, mem_insert, mem_erase]; tauto
  have htj : t ≠ j := fun he ↦ hXj (he ▸ mem_insert_self _ _)
  have hat : a ≠ t := fun he ↦ hXa (he.symm ▸ mem_insert_self _ _)
  have hj't : j' ≠ t := fun he ↦ hYt (he ▸ mem_insert_self _ _)
  have haj' : a ≠ j' := fun he ↦ hYa (he.symm ▸ mem_insert_self _ _)
  obtain ⟨e₁, he₁, hx₁, ht₁, hedge₁, hcomplete₁, hb₁⟩ :=
    FullRow.exists_full_leaf_swap h.feasible p h.paw h.first h.full y h.exposed
  have hj₁ : j ∈ e₁.blocks := by
    rw [hb₁]
    exact mem_union_left _ (mem_erase.mpr ⟨hjs, hj⟩)
  have htmem₁ : t ∈ e₁.blocks := by
    rw [hb₁]
    exact mem_union_right _ (mem_singleton_self _)
  have ha₁ : a ∈ e₁.blocks := by
    rw [hb₁]
    exact mem_union_left _ (mem_erase.mpr ⟨h.different, h.core⟩)
  obtain ⟨e₂, he₂, hx₂, ht₂, hedge₂, hcomplete₂, hb₂⟩ :=
    FullLeafSparse.full_terminal_swap he₁ hj₁ (by rwa [hx₁]) hd
  rw [hx₁] at hb₂
  have htmem₂ : t ∈ e₂.blocks := by
    rw [hb₂]
    exact mem_union_left _ (mem_erase.mpr ⟨htj, htmem₁⟩)
  have hj'mem₂ : j' ∈ e₂.blocks := by
    rw [hb₂]
    exact mem_union_right _ (mem_singleton_self _)
  have ha₂ : a ∈ e₂.blocks := by
    rw [hb₂]
    exact mem_union_left _ (mem_erase.mpr ⟨hja.symm, ha₁⟩)
  have htcard : t.card = 4 := by
    rw [card_insert_of_notMem (fun hv ↦ h.leaf_out (mem_erase.mp hv).2),
      h.first_triple_clique.card_eq]
  have htSub : t ⊆ insert p.leaf s := insert_subset_insert p.leaf (erase_subset _ _)
  have hdAll := (degreeIn_eq_card_iff d (insert p.leaf s)).mp
    (hdFull.trans h.first_five_clique.card_eq.symm)
  have hdT : degreeIn G e₂.terminal t = 4 := by
    rw [hx₂, ← htcard]
    exact (degreeIn_eq_card_iff d t).mpr (fun v hv ↦ hdAll v (htSub hv))
  obtain ⟨e₃, he₃, hx₃, ht₃, hedge₃, hcomplete₃, hb₃⟩ :=
    FullLeafSparse.full_terminal_swap he₂ htmem₂ hdT (mem_insert_self p.leaf (s.erase y))
  have hj'mem₃ : j' ∈ e₃.blocks := by
    rw [hb₃]
    exact mem_union_left _ (mem_erase.mpr ⟨hj't, hj'mem₂⟩)
  have ha₃ : a ∈ e₃.blocks := by
    rw [hb₃]
    exact mem_union_left _ (mem_erase.mpr ⟨hat, ha₂⟩)
  have hp₃ : p.support = e₃.remainder := by
    change p.support = insert e₃.terminal e₃.triangle
    rw [hx₃, ht₃, ht₂, ht₁, p.support_eq]
  have hfull : degreeIn G p.leaf j' = 4 := by
    have hj4 : j'.card = 4 := by
      rw [card_insert_of_notMem (fun hv ↦ hYj (mem_erase.mp hv).2),
        card_erase_of_mem hd, (c.property.blocks_quad j hj).card]
    rw [← hj4]
    apply (degreeIn_eq_card_iff p.leaf j').mpr
    intro v hv
    rcases mem_insert.mp hv with he | hv
    · subst v
      exact (degreeIn_eq_card_iff p.leaf s).mp
        (h.full.trans h.first_clique.card_eq.symm) y h.exposed
    · exact (degreeIn_eq_card_iff p.leaf j).mp
        (hX.trans (c.property.blocks_quad j hj).card.symm) v (mem_erase.mp hv).2
  refine ⟨e₃, ⟨he₃, hp₃, hj'mem₃, ha₃, haj', hfull, mem_insert_self _ _,
    h.attached, h.dense⟩, ?_, ?_⟩
  · exact hedge₃.trans (hedge₂.trans hedge₁)
  · exact hcomplete₃.trans (hcomplete₂.trans hcomplete₁)

end Erdos577.FullLeafCore
