/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GenuineEqualRemainderCount
import ErdosProblems.Erdos207.DerivedAbsorberCount
import ErdosProblems.Erdos207.DistinctEqualRemainderSplit

/-! # The sharp uniform off-diagonal W2 bound for the actual absorber family -/

namespace Erdos207

open Finset

noncomputable section

theorem card_distinctEqualRemainderPairs_induced_nonderived_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V) (hj : 4 ≤ j) :
    (distinctEqualRemainderPairs
      (absorberInducedConfigurationsOn q j B \ derivedAbsorberConfigurations q j B) T T').card ≤
      (2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - 4) := by
  have hpure : ∀ E ∈ absorberInducedConfigurationsOn q j B \ derivedAbsorberConfigurations q j B,
      5 ≤ j ∧ IsErdosConfigOn j E := by
    intro E hE
    exact genuine_of_induced_not_derived (by omega) (mem_sdiff.mp hE).1 (mem_sdiff.mp hE).2
  by_cases hj5 : 5 ≤ j
  · exact card_genuine_distinctEqualRemainderPairs_le T T'
      (fun E hE ↦ (hpure E hE).2) hj5
  · have hempty : absorberInducedConfigurationsOn q j B \ derivedAbsorberConfigurations q j B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro E hE
      exact hj5 (hpure E hE).1
    simp [hempty, distinctEqualRemainderPairs]

theorem card_distinctEqualRemainderPairs_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V) (hj : 4 ≤ j) :
    (distinctEqualRemainderPairs (absorberInducedConfigurationsOn q j B) T T').card ≤
      (2 * pairExactBankExtensionCoefficient q B + 2 ^ (j ^ 3) * (j + 1)) *
        (Fintype.card V + 1) ^ (j - 4) := by
  refine (card_distinctEqualRemainderPairs_le_split (absorberInducedConfigurationsOn q j B)
    (derivedAbsorberConfigurations q j B) T T').trans ?_
  calc
    _ ≤ (pairExactBankExtensionCoefficient q B * (Fintype.card V + 1) ^ (j - 4)) +
        (pairExactBankExtensionCoefficient q B * (Fintype.card V + 1) ^ (j - 4)) +
        (2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - 4) :=
      Nat.add_le_add (Nat.add_le_add
        (card_familyExtensions_derivedAbsorber_singleton_le q j B T hj)
        (card_familyExtensions_derivedAbsorber_singleton_le q j B T' hj))
        (card_distinctEqualRemainderPairs_induced_nonderived_le q j B T T' hj)
    _ = _ := by ring

end

end Erdos207
