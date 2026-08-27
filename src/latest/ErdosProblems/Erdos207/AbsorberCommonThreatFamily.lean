/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberCommonThreatWeight
import ErdosProblems.Erdos207.CommonThreatFamilyUnion

/-! # Uniform common-threat weights after summing all configuration orders -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The induced families with at least two outside triangles. -/
def absorberNontrivialInducedFamily
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) :
    ForbiddenFamilyOn V :=
  univ.biUnion fun j : (Icc 4 q : Finset ℕ) ↦ absorberInducedConfigurationsOn q j.1 B

@[simp] theorem mem_absorberNontrivialInducedFamily
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {B E : TripleSystemOn V} :
    E ∈ absorberNontrivialInducedFamily q B ↔
      ∃ j, 4 ≤ j ∧ j ≤ q ∧ E ∈ absorberInducedConfigurationsOn q j B := by
  simp only [absorberNontrivialInducedFamily, mem_biUnion, mem_univ, true_and,
    Subtype.exists, mem_Icc, exists_prop, and_assoc]

def absorberCommonThreatWeightBound
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) : ℝ≥0 :=
  (q + 1 : ℝ≥0) ^ 2 * commonThreatWeightBound q B

theorem absorberCommonThreat_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V) :
    HasExtensionBound
      (fun w : CommonThreatWitness (absorberNontrivialInducedFamily q B)
        (absorberNontrivialInducedFamily q B) T T' ↦ w.remainder)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) (absorberCommonThreatWeightBound q B) := by
  have h := commonThreat_union_hasExtensionBound
    (fun j : (Icc 4 q : Finset ℕ) ↦ absorberInducedConfigurationsOn q j.1 B)
    (fun j : (Icc 4 q : Finset ℕ) ↦ absorberInducedConfigurationsOn q j.1 B)
    T T' (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (fun _ _ ↦ commonThreatWeightBound q B) (by
      intro r s
      exact commonThreat_absorberInduced_hasExtensionBound q r.1 s.1 B T T'
        (mem_Icc.mp r.2).1 (mem_Icc.mp r.2).2 (mem_Icc.mp s.2).2)
  intro H
  refine (h H).trans ?_
  have hc : (Icc 4 q).card ≤ q + 1 := by simp only [Nat.card_Icc]; omega
  have hc' : ((Icc 4 q).card : ℝ≥0) ≤ q + 1 := by exact_mod_cast hc
  simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
  unfold absorberCommonThreatWeightBound
  calc
    _ ≤ (q + 1 : ℝ≥0) * ((q + 1) * commonThreatWeightBound q B) :=
      mul_le_mul hc' (mul_le_mul_of_nonneg_right hc' zero_le) zero_le zero_le
    _ = _ := by ring

theorem absorberCommonThreat_remainder_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V)
    (w : CommonThreatWitness (absorberNontrivialInducedFamily q B)
      (absorberNontrivialInducedFamily q B) T T') : w.remainder.card ≤ 2 * q := by
  obtain ⟨r, _, hr, hfirst⟩ := mem_absorberNontrivialInducedFamily.mp w.first_mem
  obtain ⟨s, _, hs, hsecond⟩ := mem_absorberNontrivialInducedFamily.mp w.second_mem
  rw [w.remainder_card, absorberInducedConfigurationsOn_fixed_card _ hfirst,
    absorberInducedConfigurationsOn_fixed_card _ hsecond]
  omega

end

end Erdos207
