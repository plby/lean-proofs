import ErdosProblems.Erdos577.TripleForbiddenPairs

/-! Exclude U and V with their actual strong chains, common-triple labels and final factors. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {w u v : V}

theorem UCase.false (s : UCase p a w u v) (h : HighCore c p q a w) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) : False := by
  obtain ⟨hu, hv, huv, hur, hub, hvr, hvb⟩ := s.rows_data
  obtain ⟨j, hj, hjQ, hja, hheavy⟩ := h.exists_nine_outside hcard hdeg hn hu hv huv hur hub hvr hvb
  rw [h.four_contacts hu hv huv j] at hheavy
  obtain ⟨hYu, hYv, huvX⟩ := s.no_common_pairs h hcard hn hj hjQ hja
  have hsmall : degreeIn G p.leaf j ≤ 2 := by
    apply (hc.presentPaw_feasible p h.paw).four_rows_extra_le_two hj (q 3) u v
      (by change 9 ≤ degreeIn G (q 3) j + degreeIn G u j + degreeIn G v j + degreeIn G p.leaf j
          omega) hYu hYv huvX
  obtain ⟨d, hd, hp, _, _, _, _, hkeep⟩ := s.exists_chain h hc hcard hn
  have hjd : j ∈ d.blocks := hkeep j hj hjQ hja
  have ht : ({w, u, v} : Finset V) ⊆ p.triangle ∪ a :=
    fun z hz ↦ (mem_sdiff.mp (s.subset hz)).1
  have hXout : p.leaf ∉ (s.paw h).support ∪ j := by
    rw [Paw.support_eq, s.paw_triangle]
    change p.leaf ∉ insert (q 3) ({w, u, v} : Finset V) ∪ j
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_insert.mp hh with hh | hh
      · exact h.leaf_exposed_ne hh
      · exact h.leaf_outside_core (ht hh)
    · exact h.leaf_outside_block hj hh
  obtain ⟨_, e, hej, hrows, hX2⟩ := hd.toFeasible.common_triple_of_four_rows
    hcard hdeg hn (s.paw h) hp hjd p.leaf hXout hsmall
    (by change 9 ≤ degreeIn G (q 3) j + degreeIn G u j + degreeIn G v j + degreeIn G p.leaf j
        omega) huvX
  change (∀ i : Fin 4, i ≠ 0 → G.Adj u (e i) ∧ G.Adj v (e i)) at hrows
  have hKJ := h.core_disjoint_block hj hja
  have hrK : p.center ∈ p.triangle ∪ a := mem_union_left _ p.center_mem_triangle
  have hvJ : v ∉ j := fun hh ↦ disjoint_left.mp hKJ hv hh
  have hXv : p.leaf ≠ v := fun he ↦ h.leaf_outside_core (he.symm ▸ hv)
  have hXu : p.leaf ≠ u := fun he ↦ h.leaf_outside_core (he.symm ▸ hu)
  have hcommon : CommonReplacement G p.leaf u v j := by
    refine ⟨e 2, hej ▸ (e.mem_support _).mpr ⟨2, rfl⟩, hX2, (hrows 2 (by decide)).1, ?_⟩
    rw [← hej]
    exact e.replace_middle_of_common_three v (by rwa [hej]) (fun i hi ↦ (hrows i hi).2)
  have hdis : Disjoint ({p.leaf, p.center, u} : Finset V) j := by
    simp only [disjoint_insert_left, disjoint_singleton_left]
    exact ⟨h.leaf_outside_block hj, fun hh ↦ disjoint_left.mp hKJ hrK hh,
      fun hh ↦ disjoint_left.mp hKJ hu hh⟩
  have hvout : v ∉ ({p.leaf, p.center, u} : Finset V) ∪ j := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hXv.symm, hvr, huv.symm⟩, hvJ⟩
  have hf := LocalFactor.of_three_path_common p.leaf p.center u v hXu
    p.pendant s.bridge hdis hvout hcommon
  have he : insert v (({p.leaf, p.center, u} : Finset V) ∪ j) =
      insert p.leaf (({u, v, p.center} : Finset V) ∪ j) := by
    ext z
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  have hused : ({u, v, p.center} : Finset V) ⊆ p.triangle ∪ a :=
    insert_subset hu (insert_subset hv (singleton_subset_iff.mpr hrK))
  exact hn (JointCore.hasPacking_of_partial_core hcard p h.paw h.core_block hj hja.symm
    hused s.final_quad (he ▸ hf).partition)

theorem VCase.false (s : VCase p a w u v) (h : HighCore c p q a w) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) : False := by
  obtain ⟨hu, hv, huv, hur, hub, hvr, hvb⟩ := s.rows_data
  obtain ⟨j, hj, hjQ, hja, hheavy⟩ := h.exists_nine_outside hcard hdeg hn hu hv huv hur hub hvr hvb
  rw [h.four_contacts hu hv huv j] at hheavy
  obtain ⟨hXu, hXv, huvY⟩ := s.no_common_pairs h hc hcard hn hj hjQ hja
  have hsmall : degreeIn G (q 3) j ≤ 2 := by
    obtain ⟨d, hd, hY, _, _, _, hblocks⟩ := h.toConfiguration.exists_exposed_chain hc
    have hjd : j ∈ d.blocks := by
      rw [hblocks]
      exact mem_union_left _ (mem_erase.mpr ⟨hjQ, hj⟩)
    have hs := hd.four_rows_extra_le_two hjd p.leaf u v
      (by rw [hY]; omega) (by rwa [hY]) (by rwa [hY]) (by rwa [hY])
    rwa [hY] at hs
  obtain ⟨d, hd, hp, _, _, _, _, hkeep⟩ := s.exists_chain h hc hcard hn
  have hjd : j ∈ d.blocks := hkeep j hj hja
  have ht : ({p.center, u, v} : Finset V) ⊆ p.triangle ∪ a :=
    fun z hz ↦ (mem_sdiff.mp (s.subset hz)).1
  have hYout : q 3 ∉ (s.paw h).support ∪ j := by
    rw [Paw.support_eq, s.paw_triangle]
    change q 3 ∉ insert p.leaf ({p.center, u, v} : Finset V) ∪ j
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_insert.mp hh with hh | hh
      · exact h.leaf_exposed_ne hh.symm
      · exact h.exposed_outside_core (ht hh)
    · exact h.exposed_outside_block hj hjQ hh
  obtain ⟨_, e, hej, hrows, hY2⟩ := hd.toFeasible.common_triple_of_four_rows
    hcard hdeg hn (s.paw h) hp hjd (q 3) hYout hsmall
    (by change 9 ≤ degreeIn G p.leaf j + degreeIn G u j + degreeIn G v j + degreeIn G (q 3) j
        omega) huvY
  change (∀ i : Fin 4, i ≠ 0 → G.Adj u (e i) ∧ G.Adj v (e i)) at hrows
  have hKJ := h.core_disjoint_block hj hja
  have hwK : w ∈ p.triangle ∪ a := mem_union_right _ h.marked
  have hvJ : v ∉ j := fun hh ↦ disjoint_left.mp hKJ hv hh
  have hYv : q 3 ≠ v := fun he ↦ h.exposed_outside_core (he.symm ▸ hv)
  have hYu : q 3 ≠ u := fun he ↦ h.exposed_outside_core (he.symm ▸ hu)
  have hvw : v ≠ w := by
    have hh := (mem_sdiff.mp (s.subset (by simp : v ∈ ({p.center, u, v} : Finset V)))).2
    exact fun he ↦ hh (he ▸ mem_insert_self _ _)
  have hcommon : CommonReplacement G (q 3) u v j := by
    refine ⟨e 2, hej ▸ (e.mem_support _).mpr ⟨2, rfl⟩, hY2, (hrows 2 (by decide)).1, ?_⟩
    rw [← hej]
    exact e.replace_middle_of_common_three v (by rwa [hej]) (fun i hi ↦ (hrows i hi).2)
  have hdis : Disjoint ({q 3, w, u} : Finset V) j := by
    simp only [disjoint_insert_left, disjoint_singleton_left]
    exact ⟨h.exposed_outside_block hj hjQ, fun hh ↦ disjoint_left.mp hKJ hwK hh,
      fun hh ↦ disjoint_left.mp hKJ hu hh⟩
  have hvout : v ∉ ({q 3, w, u} : Finset V) ∪ j := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hYv.symm, hvw, huv.symm⟩, hvJ⟩
  have hf := LocalFactor.of_three_path_common (q 3) w u v hYu
    ((h.exposed_row w h.marked).mpr rfl) s.bridge hdis hvout hcommon
  have he : insert v (({q 3, w, u} : Finset V) ∪ j) =
      insert (q 3) (({u, v, w} : Finset V) ∪ j) := by
    ext z
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  have hused : ({u, v, w} : Finset V) ⊆ p.triangle ∪ a :=
    insert_subset hu (insert_subset hv (singleton_subset_iff.mpr hwK))
  exact h.no_exposed_partial_factor hc hcard hn hj hjQ hja hused s.final_quad (he ▸ hf)

end Erdos577.UniversalTriple
