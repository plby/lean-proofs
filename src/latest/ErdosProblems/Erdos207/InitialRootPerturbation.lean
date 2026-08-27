/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialMinimalDeletionCount
import ErdosProblems.Erdos207.InitialErdosUnavailableCount
import ErdosProblems.Erdos207.InitialErdosRootDegree

/-! # The two-sided initial rooted perturbation estimate -/

namespace Erdos207

open Finset

noncomputable section

def initialRestrictedAbsorberFamily
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (bank ambient : TripleSystemOn V) : ForbiddenFamilyOn V :=
  minimalForbiddenFamily (restrictForbiddenFamily (absorberErdosForbiddenConfigurationsOn q bank) ambient)

def initialRootExtraBound
    {V : Type*} [Fintype V] [DecidableEq V] (q j : ℕ) (bank : TripleSystemOn V) : ℕ :=
  pairExactBankExtensionCoefficient q bank * (Fintype.card V + 1) ^ (j - 4)

def initialRootDeletionBound
    {V : Type*} [Fintype V] [DecidableEq V] (q j : ℕ) (bank ambient : TripleSystemOn V) : ℕ :=
  ((univ : TripleSystemOn V) \ ambient).card *
      (pairExactBankExtensionCoefficient q (∅ : TripleSystemOn V) * (Fintype.card V + 1) ^ (j - 5)) +
    (verticesOn bank).card * ((2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - 4))

theorem abs_card_sub_le_of_sdiff_bounds
    {α : Type*} [DecidableEq α] (X Y : Finset α) (e m : ℕ)
    (he : (X \ Y).card ≤ e) (hm : (Y \ X).card ≤ m) :
    |(X.card : ℝ) - Y.card| ≤ (e + m : ℕ) := by
  have hX := card_sdiff_add_card_inter X Y
  have hY := card_sdiff_add_card_inter Y X
  have hXY : (X ∩ Y).card ≤ Y.card := card_le_card inter_subset_right
  have hYX : (Y ∩ X).card ≤ X.card := card_le_card inter_subset_right
  have hupperNat : X.card ≤ Y.card + e := by omega
  have hlowerNat : Y.card ≤ X.card + m := by omega
  have hupper : (X.card : ℝ) ≤ Y.card + e := by exact_mod_cast hupperNat
  have hlower : (Y.card : ℝ) ≤ X.card + m := by exact_mod_cast hlowerNat
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rw [Nat.cast_add]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem card_initial_missing_rooted_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (bank ambient : TripleSystemOn V) (T : TripleOn V) (hT : T ∈ ambient)
    (hj : 5 ≤ j) (hjq : j ≤ q) (hdisjoint : Disjoint ambient bank)
    (hlegal : ∀ U ∈ ambient, IsLegalExtension (absorberErdosForbiddenConfigurationsOn q bank) ∅ U) :
    (rootedFullPackingErdosFamily j T \
      (forbiddenFamilyOfOrder (initialRestrictedAbsorberFamily q bank ambient) j).filter (fun C ↦ T ∈ C)).card ≤
      initialRootDeletionBound q j bank ambient := by
  classical
  let F := initialRestrictedAbsorberFamily q bank ambient
  let Y := rootedFullPackingErdosFamily j T
  let X := (forbiddenFamilyOfOrder F j).filter (fun C ↦ T ∈ C)
  let U := Y.filter (fun C ↦ ¬ C ⊆ ambient)
  let M := Y.filter (fun C ↦ C ⊆ ambient ∧ C ∉ F)
  have hsub : Y \ X ⊆ U ∪ M := by
    intro C hC
    obtain ⟨hCY, hCX⟩ := mem_sdiff.mp hC
    by_cases hCA : C ⊆ ambient
    · have hCF : C ∉ F := by
        intro hCF
        have hd := (mem_rootedFullPackingErdosFamily j T C).mp hCY
        exact hCX (mem_filter.mpr ⟨mem_forbiddenFamilyOfOrder.mpr ⟨hCF, hd.1.1.1⟩, hd.2.2⟩)
      exact mem_union_right _ (mem_filter.mpr ⟨hCY, hCA, hCF⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hCY, hCA⟩)
  have hU := card_fullPackingErdos_unavailable_root_loss_le q j ambient T hT hj hjq
  have hM := card_initial_minimal_deletion_le q j bank ambient T hT hj hjq hdisjoint hlegal
  exact ((card_le_card hsub).trans (card_union_le U M)).trans (Nat.add_le_add hU hM)

theorem abs_initial_root_degree_sub_full_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (bank ambient : TripleSystemOn V) (T : TripleOn V) (hT : T ∈ ambient)
    (hj : 5 ≤ j) (hjq : j ≤ q) (hdisjoint : Disjoint ambient bank)
    (hlegal : ∀ U ∈ ambient, IsLegalExtension (absorberErdosForbiddenConfigurationsOn q bank) ∅ U) :
    |(((forbiddenFamilyOfOrder (initialRestrictedAbsorberFamily q bank ambient) j).filter
      (fun C ↦ T ∈ C)).card : ℝ) - (rootedFullPackingErdosFamily j T).card| ≤
      ((initialRootExtraBound q j bank + initialRootDeletionBound q j bank ambient : ℕ) : ℝ) := by
  have hF : initialRestrictedAbsorberFamily q bank ambient ⊆ absorberErdosForbiddenConfigurationsOn q bank :=
    fun _ hC ↦ (mem_minimal_restrict_subset hC).1
  exact abs_card_sub_le_of_sdiff_bounds _ _ _ _ (card_rooted_extra_absorber_le hF (by omega) T)
    (card_initial_missing_rooted_le q j bank ambient T hT hj hjq hdisjoint hlegal)

theorem rootedFullPackingErdosFamily_four_eq_empty
    {V : Type*} [Fintype V] [DecidableEq V] (T : TripleOn V) :
    rootedFullPackingErdosFamily 4 T = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro C hC
  obtain ⟨hE, hpack, _⟩ := (mem_rootedFullPackingErdosFamily 4 T C).mp hC
  exact hpack.no_four_config ⟨C, Subset.rfl, hE.1⟩

def initialRootErrorBound
    {V : Type*} [Fintype V] [DecidableEq V] (q j : ℕ) (bank ambient : TripleSystemOn V) : ℕ :=
  if j = 4 then initialRootExtraBound q j bank
  else initialRootExtraBound q j bank + initialRootDeletionBound q j bank ambient

theorem initial_root_configuration_target_error
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (bank ambient : TripleSystemOn V) (T : TripleOn V) (hT : T ∈ ambient)
    (hj : 4 ≤ j) (hjq : j ≤ q) (hdisjoint : Disjoint ambient bank)
    (hlegal : ∀ U ∈ ambient, IsLegalExtension (absorberErdosForbiddenConfigurationsOn q bank) ∅ U)
    (A : ℝ) (hA : 0 < A) :
    |(((forbiddenFamilyOfOrder (initialRestrictedAbsorberFamily q bank ambient) j).filter
      (fun C ↦ T ∈ C)).card : ℝ) - initialErdosTrajectoryCoefficient V A (j - 3) * A ^ (j - 3)| ≤
      (initialRootErrorBound q j bank ambient : ℝ) := by
  rw [initialErdosTrajectoryCoefficient_target A hA j (by omega) T]
  by_cases hj4 : j = 4
  · subst j
    rw [rootedFullPackingErdosFamily_four_eq_empty, card_empty, Nat.cast_zero, sub_zero,
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hF : initialRestrictedAbsorberFamily q bank ambient ⊆ absorberErdosForbiddenConfigurationsOn q bank :=
      fun _ hC ↦ (mem_minimal_restrict_subset hC).1
    have hupper := card_rooted_absorber_le_full_add_error hF (by omega : 4 ≤ 4) T
    rw [rootedFullPackingErdosFamily_four_eq_empty, card_empty, zero_add] at hupper
    simpa only [initialRootErrorBound, if_pos rfl, ite_true, initialRootExtraBound] using
      (show (((forbiddenFamilyOfOrder (initialRestrictedAbsorberFamily q bank ambient) 4).filter
        (fun C ↦ T ∈ C)).card : ℝ) ≤ (initialRootExtraBound q 4 bank : ℝ) by exact_mod_cast hupper)
  · simpa only [initialRootErrorBound, if_neg hj4] using
      abs_initial_root_degree_sub_full_le q j bank ambient T hT (by omega) hjq hdisjoint hlegal

end

end Erdos207
