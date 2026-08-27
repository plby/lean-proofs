/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairTwoAwayAbsorberBound
import ErdosProblems.Erdos207.CommonThreatFamilyUnion

/-! # Pair-local selected-witness bounds for subfamilies of the actual absorber family -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def pairTwoAwayThreatMapFamily
    {V : Type*} [Fintype V] [DecidableEq V]
    {F G : ForbiddenFamilyOn V} {T : TripleOn V} {P : PairOn V}
    (hF : F ⊆ G) (w : PairTwoAwayThreatWitness V F T P) : PairTwoAwayThreatWitness V G T P :=
  ⟨⟨w.1.1, hF w.1.2.1, w.1.2.2⟩, w.2⟩

theorem pairTwoAwayThreatMapFamily_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {F G : ForbiddenFamilyOn V} {T : TripleOn V} {P : PairOn V} (hF : F ⊆ G) :
    Function.Injective (pairTwoAwayThreatMapFamily (T := T) (P := P) hF) := by
  intro w u h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun p ↦ p.1.1) h

theorem absorberForbiddenPairThreat_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (F : ForbiddenFamilyOn V) (T : TripleOn V) (P : PairOn V)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B) :
    HasExtensionBound (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) (pairTwoAwayThreatExtensionCoefficient q B : ℕ) := by
  intro H
  have hmono : extensionWeight
      (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) H ≤
      extensionWeight
        (fun w : PairTwoAwayThreatWitness V (absorberErdosForbiddenConfigurationsOn q B) T P ↦
          pairTwoAwayThreatRemainder w) (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) H := by
    apply sum_le_sum_of_injective_code (pairTwoAwayThreatMapFamily hF)
      (pairTwoAwayThreatMapFamily_injective hF)
    intro w
    exact le_rfl
  exact hmono.trans (absorberPairTwoAwayThreatRemainder_hasExtensionBound H)

theorem absorberForbiddenPairThreat_remainder_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (F : ForbiddenFamilyOn V) (T : TripleOn V) (P : PairOn V)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (w : PairTwoAwayThreatWitness V F T P) : (pairTwoAwayThreatRemainder w).card ≤ q := by
  have hc : ∀ C ∈ F, C.card ≤ q := fun C hC ↦ card_le_cutoff_of_mem_absorberErdosForbidden (hF hC)
  exact (card_twoAwayThreatRemainder_le hc w.1).trans (Nat.sub_le q 2)

end

end Erdos207
