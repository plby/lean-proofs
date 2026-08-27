/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalForbiddenAuxiliary
import ErdosProblems.Erdos207.RegularizedForbiddenUnion
import ErdosProblems.Erdos207.GreedyLegality

/-! # Global forbidden avoidance from the actual local constraints -/

namespace Erdos207

open Finset

noncomputable section

theorem avoids_localForbiddenUnion_of_avoids_union
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {A P M : TripleSystemOn V} (q : ℕ) (havoid : AvoidsForbidden (P ∪ M) F) :
    AvoidsForbidden M ((Icc 4 q).biUnion (localForbiddenConfigurations F A P)) := by
  intro S hS hSM
  obtain ⟨j, _hj, hSj⟩ := mem_biUnion.mp hS
  obtain ⟨_hSA, _hcard, C, hC, hSC, hCP⟩ :=
    (mem_localForbiddenConfigurations_iff F A P S j).mp hSj
  apply havoid C hC
  intro T hTC
  by_cases hTS : T ∈ S
  · exact mem_union_right P (hSM hTS)
  · exact mem_union_left M (hCP (mem_sdiff.mpr ⟨hTC, hTS⟩))

theorem avoids_union_of_avoids_localForbiddenUnion
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {A P M : TripleSystemOn V} {q : ℕ}
    (horder : ∀ C ∈ F, C.card + 2 ≤ q)
    (hP : AvoidsForbidden P F) (hsingle : ∀ T ∈ A, ¬ CompletesForbidden F P T)
    (hMA : M ⊆ A)
    (hlocal : AvoidsForbidden M ((Icc 4 q).biUnion (localForbiddenConfigurations F A P))) :
    AvoidsForbidden (P ∪ M) F := by
  classical
  intro C hC hCPM
  let S := C \ P
  have hSM : S ⊆ M := by
    intro T hT
    exact (mem_union.mp (hCPM (mem_sdiff.mp hT).1)).resolve_left (mem_sdiff.mp hT).2
  have hSpos : 0 < S.card := by
    apply card_pos.mpr
    apply nonempty_iff_ne_empty.mpr
    intro hzero
    apply hP C hC
    exact sdiff_eq_empty_iff_subset.mp hzero
  have hStwo : 2 ≤ S.card := by
    by_contra hnot
    have hone : S.card = 1 := by omega
    obtain ⟨T, hST⟩ := card_eq_one.mp hone
    have hTS : T ∈ S := hST.symm ▸ mem_singleton_self T
    have hins := (avoidsForbidden_insert_iff_not_completes hP T).mpr (hsingle T (hMA (hSM hTS)))
    apply hins C hC
    intro U hUC
    by_cases hUP : U ∈ P
    · exact mem_insert_of_mem hUP
    · have hUS : U ∈ S := mem_sdiff.mpr ⟨hUC, hUP⟩
      have hUT : U = T := mem_singleton.mp (hST ▸ hUS)
      exact hUT.symm ▸ mem_insert_self T P
  have hSorder : S.card + 2 ≤ q := by
    have hc := card_le_card (sdiff_subset : C \ P ⊆ C)
    have ho := horder C hC
    dsimp only [S]
    omega
  apply hlocal S _ hSM
  refine mem_biUnion.mpr ⟨S.card + 2, mem_Icc.mpr ⟨by omega, hSorder⟩, ?_⟩
  apply (mem_localForbiddenConfigurations_iff F A P S (S.card + 2)).mpr
  refine ⟨hSM.trans hMA, by omega, C, hC, sdiff_subset, ?_⟩
  intro T hT
  by_contra hTP
  exact (mem_sdiff.mp hT).2 (mem_sdiff.mpr ⟨(mem_sdiff.mp hT).1, hTP⟩)

theorem avoids_union_iff_avoids_localForbiddenUnion
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {A P M : TripleSystemOn V} {q : ℕ}
    (horder : ∀ C ∈ F, C.card + 2 ≤ q)
    (hP : AvoidsForbidden P F) (hsingle : ∀ T ∈ A, ¬ CompletesForbidden F P T)
    (hMA : M ⊆ A) :
    AvoidsForbidden (P ∪ M) F ↔
      AvoidsForbidden M ((Icc 4 q).biUnion (localForbiddenConfigurations F A P)) :=
  ⟨avoids_localForbiddenUnion_of_avoids_union q,
    avoids_union_of_avoids_localForbiddenUnion horder hP hsingle hMA⟩

theorem regularizedForbiddenUnion_local_decode
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (A P : TripleSystemOn V) (q : ℕ) :
    regularizedForbiddenUnion (Function.Embedding.subtype (fun T ↦ T ∈ A)) q
      (fun j ↦ finiteHypergraphOnSubset A (localForbiddenConfigurations F A P j)) =
        (Icc 4 q).biUnion (localForbiddenConfigurations F A P) := by
  classical
  ext S
  simp only [regularizedForbiddenUnion, mem_image, mem_biUnion]
  constructor
  · rintro ⟨C, ⟨j, hj, hC⟩, rfl⟩
    exact ⟨j, hj, (localForbiddenAuxiliary_decode F A P j) ▸ mem_image.mpr ⟨C, hC, rfl⟩⟩
  · rintro ⟨j, hj, hS⟩
    rw [← localForbiddenAuxiliary_decode F A P j] at hS
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hS
    exact ⟨C, ⟨j, hj, hC⟩, rfl⟩

theorem avoids_union_of_avoids_regularizedLocalForbidden
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {A P M : TripleSystemOn V} {q : ℕ}
    (Lstar : ℕ → Finset (Finset {T // T ∈ A}))
    (horder : ∀ C ∈ F, C.card + 2 ≤ q)
    (hP : AvoidsForbidden P F) (hsingle : ∀ T ∈ A, ¬ CompletesForbidden F P T)
    (hMA : M ⊆ A)
    (hcovers : ∀ j ∈ Icc 4 q,
      ∀ E ∈ finiteHypergraphOnSubset A (localForbiddenConfigurations F A P j),
        ∃ C ∈ (Ico 4 j).biUnion Lstar ∪ Lstar j, C ⊆ E)
    (havoid : AvoidsForbidden M (regularizedForbiddenUnion
      (Function.Embedding.subtype (fun T ↦ T ∈ A)) q Lstar)) :
    AvoidsForbidden (P ∪ M) F := by
  apply avoids_union_of_avoids_localForbiddenUnion horder hP hsingle hMA
  have h := avoids_original_union_of_regularized
    (Function.Embedding.subtype (fun T ↦ T ∈ A)) q
    (fun j ↦ finiteHypergraphOnSubset A (localForbiddenConfigurations F A P j)) Lstar hcovers M havoid
  simpa only [regularizedForbiddenUnion_local_decode] using h

end

end Erdos207
