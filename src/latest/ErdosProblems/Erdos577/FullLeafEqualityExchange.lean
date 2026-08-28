import ErdosProblems.Erdos577.FullLeafEqualityHeavyFull

/-! Swap an unmarked first-block vertex with a full outside column, retaining the marked edge. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.unmarked_block_exchange (h : Configuration c p s a y)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hfull : ∀ x ∈ insert p.leaf s, ∀ d ∈ j, G.Adj x d)
    {u d : V} (hu : u ∈ s.erase y) (hd : d ∈ j) :
    ∃ e : TriangleChain G, Configuration e p (insert d (s.erase u)) a y ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore := by
  let t := insert p.leaf (s.erase u)
  have huS := (mem_erase.mp hu).2
  have hXj : p.leaf ∉ j := fun hv ↦ disjoint_left.mp (h.paw_disjoint hj)
    (p.support_eq ▸ mem_insert_self _ _) hv
  have hXa : p.leaf ∉ a := fun hv ↦ disjoint_left.mp (h.paw_disjoint h.core)
    (p.support_eq ▸ mem_insert_self _ _) hv
  have hdS : d ∉ s := fun hv ↦
    disjoint_left.mp (c.property.blocks_disjoint hj h.first hjs) hd hv
  have hdA : d ∉ a := fun hv ↦
    disjoint_left.mp (c.property.blocks_disjoint hj h.core hja) hd hv
  have htj : t ≠ j := fun he ↦ hXj (he ▸ mem_insert_self _ _)
  have hat : a ≠ t := fun he ↦ hXa (he.symm ▸ mem_insert_self _ _)
  have haNew : a ≠ insert d (s.erase u) := fun he ↦ hdA (he.symm ▸ mem_insert_self _ _)
  obtain ⟨e₁, he₁, hx₁, ht₁, hedge₁, hcomplete₁, hb₁⟩ :=
    FullRow.exists_full_leaf_swap h.feasible p h.paw h.first h.full u huS
  have hj₁ : j ∈ e₁.blocks := by
    rw [hb₁]
    exact mem_union_left _ (mem_erase.mpr ⟨hjs, hj⟩)
  have htmem₁ : t ∈ e₁.blocks := by
    rw [hb₁]
    exact mem_union_right _ (mem_singleton_self _)
  have ha₁ : a ∈ e₁.blocks := by
    rw [hb₁]
    exact mem_union_left _ (mem_erase.mpr ⟨h.different, h.core⟩)
  have huFull : degreeIn G e₁.terminal j = 4 := by
    rw [hx₁, ← (c.property.blocks_quad j hj).card]
    exact (degreeIn_eq_card_iff u j).mpr (hfull u (mem_insert_of_mem huS))
  obtain ⟨e₂, he₂, hx₂, ht₂, hedge₂, hcomplete₂, hb₂⟩ :=
    FullLeafSparse.full_terminal_swap he₁ hj₁ huFull hd
  have htmem₂ : t ∈ e₂.blocks := by
    rw [hb₂]
    exact mem_union_left _ (mem_erase.mpr ⟨htj, htmem₁⟩)
  have ha₂ : a ∈ e₂.blocks := by
    rw [hb₂]
    exact mem_union_left _ (mem_erase.mpr ⟨hja.symm, ha₁⟩)
  have hXout : p.leaf ∉ s.erase u := fun hv ↦ h.leaf_out (mem_erase.mp hv).2
  have htcard : t.card = 4 := by
    rw [card_insert_of_notMem hXout, card_erase_of_mem huS, h.first_clique.card_eq]
  have htSub : t ⊆ insert p.leaf s := insert_subset_insert p.leaf (erase_subset _ _)
  have hdFull : degreeIn G e₂.terminal t = 4 := by
    rw [hx₂, ← htcard]
    exact (degreeIn_eq_card_iff d t).mpr (fun v hv ↦ (hfull v (htSub hv) d hd).symm)
  obtain ⟨e₃, he₃, hx₃, ht₃, hedge₃, hcomplete₃, hb₃⟩ :=
    FullLeafSparse.full_terminal_swap he₂ htmem₂ hdFull (mem_insert_self p.leaf (s.erase u))
  have hnew : insert e₂.terminal (t.erase p.leaf) = insert d (s.erase u) := by
    rw [hx₂, erase_insert hXout]
  have hfirst : insert d (s.erase u) ∈ e₃.blocks := by
    rw [hb₃, hnew]
    exact mem_union_right _ (mem_singleton_self _)
  have ha₃ : a ∈ e₃.blocks := by
    rw [hb₃]
    exact mem_union_left _ (mem_erase.mpr ⟨hat, ha₂⟩)
  have hp₃ : p.support = e₃.remainder := by
    change p.support = insert e₃.terminal e₃.triangle
    rw [hx₃, ht₃, ht₂, ht₁, p.support_eq]
  have hnewFull : degreeIn G p.leaf (insert d (s.erase u)) = 4 := by
    have hc : (insert d (s.erase u)).card = 4 := by
      rw [card_insert_of_notMem (fun hv ↦ hdS (mem_erase.mp hv).2),
        card_erase_of_mem huS, h.first_clique.card_eq]
    rw [← hc]
    apply (degreeIn_eq_card_iff p.leaf (insert d (s.erase u))).mpr
    intro v hv
    rcases mem_insert.mp hv with hv | hv
    · subst v
      exact hfull p.leaf (mem_insert_self _ _) d hd
    · exact (degreeIn_eq_card_iff p.leaf s).mp
        (h.full.trans h.first_clique.card_eq.symm) v (mem_erase.mp hv).2
  have hyNew : y ∈ insert d (s.erase u) :=
    mem_insert_of_mem (mem_erase.mpr ⟨(mem_erase.mp hu).1.symm, h.exposed⟩)
  exact ⟨e₃, ⟨he₃, hp₃, hfirst, ha₃, haNew, hnewFull, hyNew, h.attached, h.dense⟩,
    hedge₃.trans (hedge₂.trans hedge₁), hcomplete₃.trans (hcomplete₂.trans hcomplete₁)⟩

end Erdos577.FullLeafCore
