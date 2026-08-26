import ErdosProblems.Erdos547.ShrubHeadProcess

/-!
# The complete private-root phase, processing one head cluster at a time
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : ShrubHostSetup P G I)

theorem process_heads (hT : T.IsTree) (J : Finset I) (E : H.State) (F : Finset ↥P.shrubs)
    (hheads : ∀ S ∈ F, H.head S ∈ J) (hEF : Disjoint E.placed F)
    (hcap : ∀ a j, (E.farLoad a j : ℝ) ≤ H.capacity a j)
    (hbound : H.ReservoirBound E ∅) (hreserved : Disjoint E.occupied (H.reserved F)) :
    ∃ E' : H.State, ∃ B : Finset ↥P.shrubs, B ⊆ F ∧
      E'.placed = E.placed ∪ (F \ B) ∧
      (∀ a j, (E'.farLoad a j : ℝ) ≤ H.capacity a j) ∧ H.ReservoirBound E' ∅ ∧
      ∀ j, ((B.filter (fun S ↦ H.head S = j)).card : ℝ) ≤ 2 * H.ε * H.m := by
  classical
  induction J using Finset.induction_on generalizing E F with
  | empty =>
      have hF : F = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun S hS ↦ Finset.notMem_empty _ (hheads S hS))
      refine ⟨E, ∅, Finset.empty_subset _, ?_, hcap, hbound, ?_⟩
      · simp only [hF, Finset.sdiff_empty, Finset.union_empty]
      · intro j
        simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) H.ε_pos.le) (Nat.cast_nonneg _)
  | @insert i J hiJ ih =>
      let L := F.filter (fun S ↦ H.head S = i)
      have hLF : L ⊆ F := Finset.filter_subset _ _
      have hLhead : ∀ S ∈ L, H.head S = i := fun S hS ↦ (Finset.mem_filter.mp hS).2
      obtain ⟨O⟩ := H.process_same_head hT i L hLhead E F hLF hEF hcap hbound hreserved
      have hnext : ∀ S ∈ F \ L, H.head S ∈ J := by
        intro S hS
        obtain ⟨hSF, hSL⟩ := Finset.mem_sdiff.mp hS
        have hne : H.head S ≠ i := fun he ↦ hSL (Finset.mem_filter.mpr ⟨hSF, he⟩)
        exact (Finset.mem_insert.mp (hheads S hSF)).resolve_left hne
      obtain ⟨E', B', hB', hplaced', hcap', hbound', hsmall'⟩ := ih O.state (F \ L) hnext
        (O.disjoint_pending H hEF) O.capacity O.bound O.reserved
      have hBhead : ∀ S ∈ O.postponed, H.head S = i :=
        fun S hS ↦ hLhead S (O.postponed_sub hS)
      have hBnot : ∀ S ∈ B', H.head S ≠ i := by
        intro S hS he
        obtain ⟨hSF, hSL⟩ := Finset.mem_sdiff.mp (hB' hS)
        exact hSL (Finset.mem_filter.mpr ⟨hSF, he⟩)
      have hsmall : (O.postponed.card : ℝ) ≤ 2 * H.ε * H.m :=
        H.postponed_same_head_count O.state (F \ L) (O.disjoint_pending H hEF) O.capacity
          O.postponed i hBhead O.failed
      have hBsub : O.postponed ∪ B' ⊆ F :=
        Finset.union_subset (O.postponed_sub.trans hLF) (hB'.trans Finset.sdiff_subset)
      have hsplit : (L \ O.postponed) ∪ ((F \ L) \ B') = F \ (O.postponed ∪ B') := by
        ext S
        by_cases hSL : S ∈ L
        · have hSF := hLF hSL
          have hSB' : S ∉ B' := fun h ↦ (Finset.mem_sdiff.mp (hB' h)).2 hSL
          simp only [Finset.mem_union, Finset.mem_sdiff, hSL, hSF, hSB',
            not_false_eq_true, not_true_eq_false, and_false, false_and, and_true, true_and,
            or_false]
        · have hSB : S ∉ O.postponed := fun h ↦ hSL (O.postponed_sub h)
          simp only [Finset.mem_union, Finset.mem_sdiff, hSL, hSB, not_false_eq_true,
            false_and, and_true, false_or]
      refine ⟨E', O.postponed ∪ B', hBsub, ?_, hcap', hbound', ?_⟩
      · rw [hplaced', O.placed_eq, Finset.union_assoc, hsplit]
      · intro j
        by_cases hji : j = i
        · subst j
          have hs : (O.postponed ∪ B').filter (fun S ↦ H.head S = i) ⊆ O.postponed := by
            intro S hS
            obtain ⟨hS, hheadS⟩ := Finset.mem_filter.mp hS
            rcases Finset.mem_union.mp hS with hS | hS
            · exact hS
            · exact (hBnot S hS hheadS).elim
          have hc : (((O.postponed ∪ B').filter (fun S ↦ H.head S = i)).card : ℝ) ≤
              O.postponed.card := by exact_mod_cast Finset.card_le_card hs
          exact hc.trans hsmall
        · have hs : (O.postponed ∪ B').filter (fun S ↦ H.head S = j) ⊆
              B'.filter (fun S ↦ H.head S = j) := by
            intro S hS
            obtain ⟨hS, hheadS⟩ := Finset.mem_filter.mp hS
            rcases Finset.mem_union.mp hS with hS | hS
            · exact (hji (hheadS.symm.trans (hBhead S hS))).elim
            · exact Finset.mem_filter.mpr ⟨hS, hheadS⟩
          have hc : (((O.postponed ∪ B').filter (fun S ↦ H.head S = j)).card : ℝ) ≤
              (B'.filter (fun S ↦ H.head S = j)).card := by exact_mod_cast Finset.card_le_card hs
          exact hc.trans (hsmall' j)

end Erdos547.ShrubHostSetup

#print axioms Erdos547.ShrubHostSetup.process_heads
