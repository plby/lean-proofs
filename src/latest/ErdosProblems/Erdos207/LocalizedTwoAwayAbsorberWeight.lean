/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedTwoAwayExtensionBound
import ErdosProblems.Erdos207.AbsorberOrderClass
import ErdosProblems.Erdos207.AbsorberClosedThreatCount

/-! # The localized special-nibble weight bound for the actual absorber family -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

abbrev LocalizedTwoAwayIndexedCode
    (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V)
    (T : TripleOn V) (a b : V) (U : Finset V) :=
  Σ j : (Icc 4 q : Finset ℕ), LocalizedTwoAwayWitness V (absorberInducedConfigurationsOn q j.1 B) T a b U

def localizedTwoAwayIndexedCode
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {B : TripleSystemOn V}
    {F : ForbiddenFamilyOn V} {T : TripleOn V} {a b : V} {U : Finset V}
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (w : LocalizedTwoAwayWitness V F T a b U) : LocalizedTwoAwayIndexedCode V q B T a b U := by
  let C := w.1.1.1
  let j := C.card + 2
  have hC2 : 2 ≤ C.card := by
    have hlt : 1 < C.card := one_lt_card.mpr
      ⟨T, w.1.2.2.2.1, w.1.1.2, w.1.2.2.1, w.1.2.2.2.2.symm⟩
    omega
  have hj4 : 4 ≤ j := by omega
  have hjq : j ≤ q := card_add_two_le_of_mem_absorberErdosForbidden (hF w.1.2.1)
  have hC : C ∈ absorberInducedConfigurationsOn q j B := by
    apply forbiddenFamilyOfOrder_subset_absorberInduced hF hj4
    exact mem_forbiddenFamilyOfOrder.mpr ⟨w.1.2.1, by dsimp only [j]; omega⟩
  exact ⟨⟨j, mem_Icc.mpr ⟨hj4, hjq⟩⟩, ⟨⟨w.1.1, hC, w.1.2.2⟩, w.2⟩⟩

theorem localizedTwoAwayIndexedCode_injective
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {B : TripleSystemOn V}
    {F : ForbiddenFamilyOn V} {T : TripleOn V} {a b : V} {U : Finset V}
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B) :
    Function.Injective (localizedTwoAwayIndexedCode (T := T) (a := a) (b := b) (U := U) hF) := by
  intro w z h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun v : LocalizedTwoAwayIndexedCode V q B T a b U ↦ v.2.1.1) h

def localizedTwoAwayWeightBound
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) (U : Finset V) : ℝ≥0 :=
  (q + 1 : ℕ) * ((45 * (q + 1) + 28 : ℕ) +
    (U.card : ℝ≥0) * pairExactBankExtensionCoefficient q B / (Fintype.card V + 1 : ℝ≥0))

theorem localizedTwoAway_absorber_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V} {X U : Finset V}
    (F : ForbiddenFamilyOn V) (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (T : TripleOn V) {a b : V} (hab : a ≠ b)
    (hsep : AbsorberSeparatedLevel H X B U)
    (hrootLocal : HasPaddedAbsorberRootLocalization q X B) :
    HasExtensionBound (fun w : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder w)
      (constantTripleWeight (Fintype.card V + 1 : ℝ≥0)⁻¹) (localizedTwoAwayWeightBound q B U) := by
  intro R
  let p : TripleOn V → ℝ≥0 := constantTripleWeight (Fintype.card V + 1 : ℝ≥0)⁻¹
  let K : ℝ≥0 := (45 * (q + 1) + 28 : ℕ) +
    (U.card : ℝ≥0) * pairExactBankExtensionCoefficient q B / (Fintype.card V + 1 : ℝ≥0)
  have hsize : (Icc 4 q).card ≤ q + 1 := by rw [Nat.card_Icc]; omega
  calc
    _ ≤ ∑ z : LocalizedTwoAwayIndexedCode V q B T a b U,
        if R ⊆ localizedTwoAwayRemainder z.2 then setWeight p (localizedTwoAwayRemainder z.2 \ R) else 0 := by
      exact sum_le_sum_of_injective_code (localizedTwoAwayIndexedCode hF)
        (localizedTwoAwayIndexedCode_injective hF)
        (fun w ↦ if R ⊆ localizedTwoAwayRemainder w then setWeight p (localizedTwoAwayRemainder w \ R) else 0)
        (fun z ↦ if R ⊆ localizedTwoAwayRemainder z.2 then setWeight p (localizedTwoAwayRemainder z.2 \ R) else 0)
        (fun _ ↦ le_rfl)
    _ = ∑ j : (Icc 4 q : Finset ℕ), extensionWeight
        (fun w : LocalizedTwoAwayWitness V (absorberInducedConfigurationsOn q j.1 B) T a b U ↦
          localizedTwoAwayRemainder w) p R := by rw [Fintype.sum_sigma]; rfl
    _ ≤ ∑ _j : (Icc 4 q : Finset ℕ), K := by
      apply sum_le_sum
      intro j _
      exact localizedTwoAway_induced_hasExtensionBound T hab (mem_Icc.mp j.2).1
        (mem_Icc.mp j.2).2 hsep hrootLocal R
    _ = (Icc 4 q).card * K := by simp
    _ ≤ (q + 1 : ℕ) * K := mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) (bot_le : 0 ≤ K)
    _ = _ := rfl

theorem localizedTwoAway_absorber_remainder_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {F : ForbiddenFamilyOn V}
    {T : TripleOn V} {a b : V} {U : Finset V}
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (w : LocalizedTwoAwayWitness V F T a b U) : (localizedTwoAwayRemainder w).card ≤ q := by
  have hcard : ∀ C ∈ F, C.card ≤ q := fun C hC ↦
    (Nat.le_add_right C.card 2).trans (card_add_two_le_of_mem_absorberErdosForbidden (hF hC))
  exact (card_twoAwayThreatRemainder_le hcard w.1).trans (Nat.sub_le q 2)

end

end Erdos207
