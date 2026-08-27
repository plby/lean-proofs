/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberCommonThreatFamily
import ErdosProblems.Erdos207.CommonThreatFamilyMono

/-! # The actual absorber forbidden family in the common-threat weight system -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem isPacking_of_mem_absorberErdosForbidden
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {B C : TripleSystemOn V}
    (hC : C ∈ absorberErdosForbiddenConfigurationsOn q B) : IsPackingOn C := by
  obtain ⟨_, r, _, _, E, _, hpack, hE⟩ := mem_absorberErdosForbiddenConfigurationsOn_iff.mp hC
  apply hpack.mono
  rw [← hE]
  exact sdiff_subset

theorem mem_absorberNontrivialInducedFamily_of_card_ge_two
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {B C : TripleSystemOn V}
    (hC : C ∈ absorberErdosForbiddenConfigurationsOn q B) (hc : 2 ≤ C.card) :
    C ∈ absorberNontrivialInducedFamily q B := by
  obtain ⟨_, r, hr4, hrq, E, hE, hpack, hEC⟩ := mem_absorberErdosForbiddenConfigurationsOn_iff.mp hC
  have hr5 : 5 ≤ r := by
    by_contra h
    have heq : r = 4 := by omega
    subst r
    exact hpack.no_four_config ⟨E, Subset.rfl, hE.1⟩
  have hCE : C ⊆ E := by rw [← hEC]; exact sdiff_subset
  have hsize := card_le_card hCE
  have hEcard := hE.1.1
  apply mem_absorberNontrivialInducedFamily.mpr
  refine ⟨C.card + 2, by omega, by omega, ?_⟩
  exact mem_absorberInducedConfigurationsOn_iff.mpr ⟨by omega, r, hr5, hrq, E, hE, hEC⟩

theorem absorberForbiddenCommonThreat_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (F : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B) :
    HasExtensionBound (fun w : CommonThreatWitness F F T T' ↦ w.remainder)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) (absorberCommonThreatWeightBound q B) := by
  have hcover : ∀ E ∈ F, 2 ≤ E.card → E ∈ absorberNontrivialInducedFamily q B :=
    fun E hE hc ↦ mem_absorberNontrivialInducedFamily_of_card_ge_two (hF hE) hc
  intro H
  exact (extensionWeight_commonThreat_mono T T' _ H hcover hcover).trans
    (absorberCommonThreat_hasExtensionBound q B T T' H)

theorem absorberForbiddenCommonThreat_remainder_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (F : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (w : CommonThreatWitness F F T T') : w.remainder.card ≤ 2 * q := by
  have hcover : ∀ E ∈ F, 2 ≤ E.card → E ∈ absorberNontrivialInducedFamily q B :=
    fun E hE hc ↦ mem_absorberNontrivialInducedFamily_of_card_ge_two (hF hE) hc
  exact absorberCommonThreat_remainder_card_le q B T T' (w.mapFamilies hcover hcover)

end

end Erdos207
