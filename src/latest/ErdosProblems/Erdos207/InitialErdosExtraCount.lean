/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialErdosSymmetry
import ErdosProblems.Erdos207.DerivedAbsorberCount
import ErdosProblems.Erdos207.AbsorberOrderClass

/-! # The extra initial rooted configurations inherit the bank saving -/

namespace Erdos207

open Finset

noncomputable section

theorem rooted_extra_absorber_subset_derived
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q j : ℕ} {bank : TripleSystemOn V}
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q bank) (hj : 4 ≤ j) (T : TripleOn V) :
    ((forbiddenFamilyOfOrder F j).filter (fun C ↦ T ∈ C)) \ rootedFullPackingErdosFamily j T ⊆
      familyExtensions (derivedAbsorberConfigurations q j bank) {T} := by
  classical
  intro C hC
  obtain ⟨hrooted, hnotFull⟩ := mem_sdiff.mp hC
  obtain ⟨horder, hroot⟩ := mem_filter.mp hrooted
  have hind := forbiddenFamilyOfOrder_subset_absorberInduced hF hj horder
  have hpack := isPacking_of_mem_absorberErdosForbidden (hF (mem_forbiddenFamilyOfOrder.mp horder).1)
  apply mem_familyExtensions_iff.mpr
  refine ⟨?_, singleton_subset_iff.mpr hroot⟩
  by_contra hnotDerived
  have hgenuine := genuine_of_induced_not_derived (by omega) hind hnotDerived
  exact hnotFull ((mem_rootedFullPackingErdosFamily j T C).mpr ⟨hgenuine.2, hpack, hroot⟩)

theorem card_rooted_extra_absorber_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q j : ℕ} {bank : TripleSystemOn V}
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q bank) (hj : 4 ≤ j) (T : TripleOn V) :
    (((forbiddenFamilyOfOrder F j).filter (fun C ↦ T ∈ C)) \ rootedFullPackingErdosFamily j T).card ≤
      pairExactBankExtensionCoefficient q bank * (Fintype.card V + 1) ^ (j - 4) :=
  (card_le_card (rooted_extra_absorber_subset_derived hF hj T)).trans
    (card_familyExtensions_derivedAbsorber_singleton_le q j bank T hj)

theorem card_rooted_absorber_le_full_add_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q j : ℕ} {bank : TripleSystemOn V}
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q bank) (hj : 4 ≤ j) (T : TripleOn V) :
    ((forbiddenFamilyOfOrder F j).filter (fun C ↦ T ∈ C)).card ≤
      (rootedFullPackingErdosFamily j T).card +
        pairExactBankExtensionCoefficient q bank * (Fintype.card V + 1) ^ (j - 4) := by
  let X := (forbiddenFamilyOfOrder F j).filter (fun C ↦ T ∈ C)
  let Y := rootedFullPackingErdosFamily j T
  have hcount := card_sdiff_add_card_inter X Y
  have hint : (X ∩ Y).card ≤ Y.card := card_le_card inter_subset_right
  have hextra := card_rooted_extra_absorber_le hF hj T
  change (X \ Y).card ≤ _ at hextra
  change X.card ≤ Y.card + _
  omega

end

end Erdos207
