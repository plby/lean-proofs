/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteHypergraphOnSubset
import ErdosProblems.Erdos207.LocalForbiddenConfiguration

/-! # Local forbidden configurations on exactly the available-triangle vertices -/

namespace Erdos207

open Finset

noncomputable section

theorem localForbiddenConfigurations_supported
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (A old : TripleSystemOn V) (j : ℕ) :
    ∀ E ∈ localForbiddenConfigurations F A old j, E ⊆ A := by
  intro E hE
  exact ((mem_localForbiddenConfigurations_iff F A old E j).mp hE).1

theorem localForbiddenConfigurations_packing
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (A old : TripleSystemOn V) (j : ℕ) (hF : ∀ E ∈ F, IsPackingOn E) :
    ∀ C ∈ localForbiddenConfigurations F A old j, IsPackingOn C := by
  intro C hC
  obtain ⟨E, hE, hCE, _hOld⟩ := ((mem_localForbiddenConfigurations_iff F A old C j).mp hC).2.2
  exact (hF E hE).mono hCE

theorem localForbiddenAuxiliary_decode
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (A old : TripleSystemOn V) (j : ℕ) :
    (finiteHypergraphOnSubset A (localForbiddenConfigurations F A old j)).image
      (Finset.map (Function.Embedding.subtype (fun T ↦ T ∈ A))) =
        localForbiddenConfigurations F A old j :=
  finiteHypergraphOnSubset_decode A _ (localForbiddenConfigurations_supported F A old j)

theorem localForbiddenAuxiliary_uniform
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (A old : TripleSystemOn V) (j : ℕ) :
    ∀ E ∈ finiteHypergraphOnSubset A (localForbiddenConfigurations F A old j), E.card = j - 2 :=
  (finiteHypergraphOnSubset_uniform A _ (localForbiddenConfigurations_supported F A old j) (j - 2)).mpr
    (localForbiddenConfigurations_uniform F A old j)

theorem localForbiddenAuxiliary_degree
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (A old : TripleSystemOn V) (j : ℕ) (T : {T // T ∈ A}) :
    finiteHypergraphDegree (finiteHypergraphOnSubset A (localForbiddenConfigurations F A old j)) T =
      finiteHypergraphDegree (localForbiddenConfigurations F A old j) T.val :=
  finiteHypergraphOnSubset_degree A _ (localForbiddenConfigurations_supported F A old j) T

theorem localForbiddenAuxiliary_maxDegree
    {V : Type*} [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V)
    (A old : TripleSystemOn V) (j : ℕ) :
    finiteHypergraphMaxDegree (finiteHypergraphOnSubset A (localForbiddenConfigurations F A old j)) =
      finiteHypergraphMaxDegree (localForbiddenConfigurations F A old j) :=
  finiteHypergraphOnSubset_maxDegree A _ (localForbiddenConfigurations_supported F A old j)

end

end Erdos207
