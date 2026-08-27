/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialForbiddenRestriction
import ErdosProblems.Erdos207.InitialErdosExtraCount

/-! # A genuine initial configuration can only be deleted by a bank-derived member -/

namespace Erdos207

open Finset

noncomputable section

theorem genuine_initial_minimal_deletion_has_derived_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (bank ambient C : TripleSystemOn V) (hj : 5 ≤ j) (hjq : j ≤ q)
    (hC : C ∈ fullPackingErdosFamily V j) (hCA : C ⊆ ambient)
    (hdisjoint : Disjoint ambient bank)
    (hlegal : ∀ T ∈ ambient, IsLegalExtension (absorberErdosForbiddenConfigurationsOn q bank) ∅ T)
    (hnot : C ∉ minimalForbiddenFamily
      (restrictForbiddenFamily (absorberErdosForbiddenConfigurationsOn q bank) ambient)) :
    ∃ D : TripleSystemOn V, D ∈ derivedAbsorberConfigurations q (D.card + 2) bank ∧
      2 ≤ D.card ∧ D ⊆ C ∧ ¬ C ⊆ D ∧ D.card + 2 ≤ j - 1 := by
  have hfull := (mem_fullPackingErdosFamily j C).mp hC
  have hCnonempty : C.Nonempty := card_pos.mp (by rw [hfull.1.1.1]; omega)
  have hCB : Disjoint C bank := hdisjoint.mono_left hCA
  have hCF : C ∈ absorberErdosForbiddenConfigurationsOn q bank :=
    mem_absorberErdosForbiddenConfigurationsOn_iff.mpr
      ⟨hCnonempty, j, by omega, hjq, C, hfull.1, hfull.2, sdiff_eq_self_iff_disjoint.mpr hCB⟩
  obtain ⟨D, hD, hDC, hCD⟩ := exists_proper_subset_of_not_mem_minimal_restrict hCF hCA hnot
  have hDtwo := restrictForbiddenFamily_card_ge_two
    (fun E hE ↦ (mem_absorberErdosForbiddenConfigurationsOn_iff.mp hE).1) hlegal hD
  have hDcard : D.card < C.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hDC, fun heq ↦ hCD (heq ▸ Subset.rfl)⟩)
  have horder : D.card + 2 ≤ j - 1 := by rw [hfull.1.1.1] at hDcard; omega
  have hDF := (mem_filter.mp hD).1
  have hDorder : D ∈ forbiddenFamilyOfOrder (absorberErdosForbiddenConfigurationsOn q bank) (D.card + 2) :=
    mem_forbiddenFamilyOfOrder.mpr ⟨hDF, by omega⟩
  have hind := forbiddenFamilyOfOrder_subset_absorberInduced (Subset.rfl) (show 4 ≤ D.card + 2 by omega) hDorder
  refine ⟨D, ?_, hDtwo, hDC, hCD, horder⟩
  by_contra hnotDerived
  have hgenuine := genuine_of_induced_not_derived (show 3 ≤ D.card + 2 by omega) hind hnotDerived
  exact hfull.1.2 (D.card + 2) (by omega) horder ⟨D, hDC, hgenuine.2.1⟩

end

end Erdos207
