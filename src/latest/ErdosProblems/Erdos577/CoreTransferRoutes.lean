import ErdosProblems.Erdos577.TerminalSwap
import ErdosProblems.Erdos577.TwoStageReplacement

/-! Direct and bridge routes expose each low vertex and provide actual complementary partitions. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A proved route supplies actual chains and cycle partitions, not a core obstruction. -/
structure Route (c : TriangleChain G) (q : Quadrilateral G) (bs : Finset (Finset V)) : Prop where
  blocks_subset : bs ⊆ c.blocks
  contains_cycle : q.support ∈ bs
  high_contact : G.Adj c.terminal (q 0)
  terminals : ∀ i : Fin 4, i = 1 ∨ i = 3 →
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = q i ∧ d.triangle = c.triangle ∧
      ∀ a ∈ c.blocks, a ∉ bs → a ∈ d.blocks
  complement : ∀ i : Fin 4, i = 1 ∨ i = 3 →
    Nonempty (BlockPartition G (insert c.terminal ((bs.biUnion id).erase (q i))))

theorem direct {c : TriangleChain G} (hc : c.Feasible)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks)
    (hn : ¬G.Adj (q 1) (q 3))
    (hrow : ∀ j : Fin 4, G.Adj c.terminal (q j) ↔ (5 : ℕ).testBit j.val = true) :
    Route c q {q.support} := by
  refine ⟨?_, mem_singleton_self _, (hrow 0).mpr (by decide), ?_, ?_⟩
  · exact singleton_subset_iff.mpr hq
  · intro i hi
    obtain ⟨d, hdf, hdt, htri, _, _, hblocks⟩ := hc.exists_high_pair_terminal q hq hn hrow i hi
    refine ⟨d, hdf, hdt, htri, ?_⟩
    intro a ha hna
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨fun he ↦ hna (he ▸ mem_singleton_self _), ha⟩)
  · intro i hi
    have hr := q.high_pair_replace c.terminal (c.terminal_not_mem_block hq) hrow i hi
    simpa only [singleton_biUnion, id_eq] using (show Nonempty (BlockPartition G
      (insert c.terminal (q.support.erase (q i)))) from ⟨BlockPartition.single hr⟩)

theorem bridge {c : TriangleChain G} (hc : c.Feasible)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks)
    (hn : ¬G.Adj (q 1) (q 3)) {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (y : V) (hy : y ∈ b) (hrep : QuadOn G (insert c.terminal (b.erase y)))
    (hscore : edgeCount G (insert c.terminal (b.erase y)) = edgeCount G b)
    (hrow : ∀ j : Fin 4, G.Adj y (q j) ↔ (5 : ℕ).testBit j.val = true)
    (hhigh : G.Adj c.terminal (q 0)) : Route c q {q.support, b} := by
  have hdis : Disjoint q.support b := c.property.blocks_disjoint hq hb hbq.symm
  have hyq : y ∉ q.support := fun hh ↦ disjoint_left.mp hdis hh hy
  refine ⟨?_, mem_insert_self _ _, hhigh, ?_, ?_⟩
  · intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact hq
    · exact mem_singleton.mp ha ▸ hb
  · intro i hi
    obtain ⟨d₀, hd₀, hx₀, ht₀, _, _, hb₀⟩ := hc.exists_terminal_swap hb hy hrep hscore
    have hq₀ : q.support ∈ d₀.blocks := by
      rw [hb₀]
      exact mem_union_left _ (mem_erase.mpr ⟨hbq.symm, hq⟩)
    have hr₀ : ∀ j : Fin 4, G.Adj d₀.terminal (q j) ↔ (5 : ℕ).testBit j.val = true := by
      intro j
      rw [hx₀]
      exact hrow j
    obtain ⟨d, hdf, hdt, htri, _, _, hblocks⟩ :=
      hd₀.exists_high_pair_terminal q hq₀ hn hr₀ i hi
    refine ⟨d, hdf, hdt, htri.trans ht₀, ?_⟩
    intro a ha hna
    have haq : a ≠ q.support := fun he ↦ hna (he ▸ mem_insert_self _ _)
    have hab : a ≠ b := fun he ↦ hna (he ▸ mem_insert_of_mem (mem_singleton_self _))
    have ha₀ : a ∈ d₀.blocks := by rw [hb₀]; exact mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨haq, ha₀⟩)
  · intro i hi
    have hx : c.terminal ∉ q.support ∪ b := by
      intro hh
      rcases mem_union.mp hh with hh | hh
      · exact c.terminal_not_mem_block hq hh
      · exact c.terminal_not_mem_block hb hh
    have hr := q.high_pair_replace y hyq hrow i hi
    have hf := (LocalFactor.of_two_stage_replacement hdis hx hy
      ((q.mem_support _).mpr ⟨i, rfl⟩) hr hrep).partition
    simpa only [biUnion_insert, singleton_biUnion, id_eq] using hf

end Erdos577.CoreTransfer
