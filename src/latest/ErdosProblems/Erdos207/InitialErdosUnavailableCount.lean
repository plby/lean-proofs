/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialErdosSymmetry
import ErdosProblems.Erdos207.AbsorberRootedCount

/-! # The initial rooted loss caused by unavailable triangles -/

namespace Erdos207

open Finset

noncomputable section

theorem card_fullPackingErdos_two_roots_le
    {V : Type*} [Fintype V] [DecidableEq V] (q j : ℕ)
    (T U : TripleOn V) (hTU : T ≠ U) (hj : 5 ≤ j) (hjq : j ≤ q) :
    ((rootedFullPackingErdosFamily j T).filter (fun C ↦ U ∈ C)).card ≤
      pairExactBankExtensionCoefficient q (∅ : TripleSystemOn V) * (Fintype.card V + 1) ^ (j - 5) := by
  have hsub : (rootedFullPackingErdosFamily j T).filter (fun C ↦ U ∈ C) ⊆
      familyExtensions (absorberInducedConfigurationsOn q j (∅ : TripleSystemOn V)) {T, U} := by
    intro C hC
    obtain ⟨hroot, hU⟩ := mem_filter.mp hC
    obtain ⟨hE, _, hT⟩ := (mem_rootedFullPackingErdosFamily j T C).mp hroot
    apply mem_familyExtensions_iff.mpr
    refine ⟨mem_absorberInducedConfigurationsOn_iff.mpr ⟨hE.1.1, j, hj, hjq, C, hE, by simp⟩, ?_⟩
    exact insert_subset_iff.mpr ⟨hT, singleton_subset_iff.mpr hU⟩
  have hrootcard : ({T, U} : TripleSystemOn V).card = 2 := by simp [hTU]
  have hbound := card_familyExtensions_absorberInduced_le_strong q j (∅ : TripleSystemOn V)
    {T, U} (by omega) (by omega)
  have hexp : j - ({T, U} : TripleSystemOn V).card - 3 = j - 5 := by omega
  exact (card_le_card hsub).trans (by simpa only [hexp] using hbound)

theorem card_fullPackingErdos_unavailable_root_loss_le
    {V : Type*} [Fintype V] [DecidableEq V] (q j : ℕ)
    (ambient : TripleSystemOn V) (T : TripleOn V) (hT : T ∈ ambient)
    (hj : 5 ≤ j) (hjq : j ≤ q) :
    ((rootedFullPackingErdosFamily j T).filter (fun C ↦ ¬ C ⊆ ambient)).card ≤
      ((univ : TripleSystemOn V) \ ambient).card *
        (pairExactBankExtensionCoefficient q (∅ : TripleSystemOn V) * (Fintype.card V + 1) ^ (j - 5)) := by
  classical
  let bad := (univ : TripleSystemOn V) \ ambient
  let rooted := rootedFullPackingErdosFamily j T
  have hsub : rooted.filter (fun C ↦ ¬ C ⊆ ambient) ⊆
      bad.biUnion (fun U ↦ rooted.filter (fun C ↦ U ∈ C)) := by
    intro C hC
    obtain ⟨hrooted, hnot⟩ := mem_filter.mp hC
    obtain ⟨U, hUC, hUbad⟩ := not_subset.mp hnot
    exact mem_biUnion.mpr ⟨U, mem_sdiff.mpr ⟨mem_univ _, hUbad⟩, mem_filter.mpr ⟨hrooted, hUC⟩⟩
  calc
    _ ≤ (bad.biUnion (fun U ↦ rooted.filter (fun C ↦ U ∈ C))).card := card_le_card hsub
    _ ≤ ∑ U ∈ bad, (rooted.filter (fun C ↦ U ∈ C)).card := card_biUnion_le
    _ ≤ ∑ _U ∈ bad,
        (pairExactBankExtensionCoefficient q (∅ : TripleSystemOn V) * (Fintype.card V + 1) ^ (j - 5)) := by
      apply sum_le_sum
      intro U hU
      have hTU : T ≠ U := by
        intro heq
        exact (mem_sdiff.mp hU).2 (heq ▸ hT)
      exact card_fullPackingErdos_two_roots_le q j T U hTU hj hjq
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id, bad]

end

end Erdos207
