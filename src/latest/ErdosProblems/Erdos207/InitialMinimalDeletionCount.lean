/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialMinimalDeletion
import ErdosProblems.Erdos207.DerivedBankVertex
import ErdosProblems.Erdos207.BoundedSpanVertexRootCount

/-! # An explicit one-power-saving bound for initial minimalization losses -/

namespace Erdos207

open Finset

noncomputable section

theorem card_fullPackingErdos_vertex_root_le
    {V : Type*} [Fintype V] [DecidableEq V] (j : ℕ) (T : TripleOn V) (v : V) (hv : v ∉ T.1) :
    ((rootedFullPackingErdosFamily j T).filter (fun C ↦ v ∈ verticesOn C)).card ≤
      (2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - 4) := by
  have hbound := card_boundedSpan_family_with_vertex_root
    ((rootedFullPackingErdosFamily j T).filter (fun C ↦ v ∈ verticesOn C)) (insert v T.1) j
    (fun C hC ↦ by
      obtain ⟨hroot, hvC⟩ := mem_filter.mp hC
      have hT := ((mem_rootedFullPackingErdosFamily j T C).mp hroot).2.2
      exact insert_subset_iff.mpr ⟨hvC, fun x hx ↦ mem_biUnion.mpr ⟨T, hT, hx⟩⟩)
    (fun C hC ↦ ((mem_rootedFullPackingErdosFamily j T C).mp (mem_filter.mp hC).1).1.1.2)
  simpa only [card_insert_of_notMem hv, T.2] using hbound

theorem card_fullPackingErdos_bank_touching_le
    {V : Type*} [Fintype V] [DecidableEq V] (j : ℕ) (bank : TripleSystemOn V) (T : TripleOn V) :
    ((rootedFullPackingErdosFamily j T).filter
      (fun C ↦ ∃ v ∈ verticesOn C, v ∈ verticesOn bank ∧ v ∉ T.1)).card ≤
      (verticesOn bank).card * ((2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - 4)) := by
  classical
  let roots := verticesOn bank \ T.1
  let Y := rootedFullPackingErdosFamily j T
  have hsub : Y.filter (fun C ↦ ∃ v ∈ verticesOn C, v ∈ verticesOn bank ∧ v ∉ T.1) ⊆
      roots.biUnion (fun v ↦ Y.filter (fun C ↦ v ∈ verticesOn C)) := by
    intro C hC
    obtain ⟨hCY, v, hvC, hvB, hvT⟩ := mem_filter.mp hC
    exact mem_biUnion.mpr ⟨v, mem_sdiff.mpr ⟨hvB, hvT⟩, mem_filter.mpr ⟨hCY, hvC⟩⟩
  calc
    _ ≤ (roots.biUnion (fun v ↦ Y.filter (fun C ↦ v ∈ verticesOn C))).card := card_le_card hsub
    _ ≤ ∑ v ∈ roots, (Y.filter (fun C ↦ v ∈ verticesOn C)).card := card_biUnion_le
    _ ≤ ∑ _v ∈ roots, ((2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - 4)) := by
      apply sum_le_sum
      intro v hv
      exact card_fullPackingErdos_vertex_root_le j T v (mem_sdiff.mp hv).2
    _ = roots.card * ((2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - 4)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_le_card sdiff_subset)

theorem card_initial_minimal_deletion_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (bank ambient : TripleSystemOn V) (T : TripleOn V) (hT : T ∈ ambient)
    (hj : 5 ≤ j) (hjq : j ≤ q) (hdisjoint : Disjoint ambient bank)
    (hlegal : ∀ U ∈ ambient, IsLegalExtension (absorberErdosForbiddenConfigurationsOn q bank) ∅ U) :
    ((rootedFullPackingErdosFamily j T).filter (fun C ↦ C ⊆ ambient ∧
      C ∉ minimalForbiddenFamily (restrictForbiddenFamily (absorberErdosForbiddenConfigurationsOn q bank) ambient))).card ≤
      (verticesOn bank).card * ((2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - 4)) := by
  classical
  have hTnot : T ∉ bank := fun hTB ↦ Finset.disjoint_left.mp hdisjoint hT hTB
  apply (card_le_card (show (rootedFullPackingErdosFamily j T).filter (fun C ↦ C ⊆ ambient ∧
      C ∉ minimalForbiddenFamily (restrictForbiddenFamily (absorberErdosForbiddenConfigurationsOn q bank) ambient)) ⊆
    (rootedFullPackingErdosFamily j T).filter
      (fun C ↦ ∃ v ∈ verticesOn C, v ∈ verticesOn bank ∧ v ∉ T.1) from ?_)).trans
      (card_fullPackingErdos_bank_touching_le j bank T)
  intro C hC
  obtain ⟨hroot, hCA, hnot⟩ := mem_filter.mp hC
  have hfull : C ∈ fullPackingErdosFamily V j := (mem_filter.mp hroot).1
  obtain ⟨D, hD, hDtwo, hDC, _, _⟩ := genuine_initial_minimal_deletion_has_derived_subset q j bank ambient C
    hj hjq hfull hCA hdisjoint hlegal hnot
  obtain ⟨v, hvD, hvB, hvT⟩ := derivedAbsorber_bank_vertex_outside_root T hD hDtwo hTnot
  exact mem_filter.mpr ⟨hroot, v, verticesOn_mono hDC hvD, hvB, hvT⟩

end

end Erdos207
