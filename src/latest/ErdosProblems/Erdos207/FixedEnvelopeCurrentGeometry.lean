/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CurrentAuxiliaryEncoding
import ErdosProblems.Erdos207.FixedEnvelopeLocalization

/-! # The fixed envelope supplies the actual current-process source geometry -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem fixedRandomAllOrders_current_source_geometry
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V]
    {I : Omega → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    {ell : ℕ} (P : FiniteLaw Omega) (W : Vortex V ell)
    (e : (d : Omega) → I d ↪ TripleOn V) (D : Finset V) (q : ℕ) (b : ℕ → ℕ)
    (L Lstar : ℕ → (d : Omega) → Finset (Finset (I d)))
    (F candidates envelope : ℕ → ForbiddenFamilyOn V) (y z a rho : ℕ → ℝ≥0)
    (available old : Omega → TripleSystemOn V)
    (hsupport : ∀ d i, (e d i).1 ⊆ D)
    (hencode : ∀ d, univ.map (e d) = available d)
    (hlocal : ∀ j ∈ Icc 4 q, ∀ d, (L j d).image (Finset.map (e d)) ⊆
      localForbiddenConfigurations ((Icc 4 q).biUnion F) (available d) (old d) j)
    (hresult : ∀ j ∈ Icc 4 q, FixedRandomOrderResult P W e j (b j) (L j)
      (fun d ↦ (Ico 4 j).biUnion (fun i ↦ Lstar i d)) (F j) (candidates j)
      (y j) (z j) (a j) (rho j) (Lstar j) (envelope j)) :
    ∀ d, ∀ B ∈ mapForbiddenFamily (Function.Embedding.subtype (fun v ↦ v ∈ D))
      (regularizedForbiddenUnion (restrictTripleIndexEmbedding D (e d) (hsupport d)) q (fun j ↦ Lstar j d)),
      B ⊆ available d ∧ ∃ j ∈ Icc 4 q, ∃ E ∈ F j ∪ envelope j, B ⊆ E ∧ E \ B ⊆ old d := by
  let H := (Icc 4 q).biUnion (fun j ↦ F j ∪ envelope j)
  have hFH : (Icc 4 q).biUnion F ⊆ H := by
    intro B hB
    obtain ⟨j, hj, hBj⟩ := mem_biUnion.mp hB
    exact mem_biUnion.mpr ⟨j, hj, mem_union_left _ hBj⟩
  intro d B hB
  rw [regularizedForbiddenUnion_restrict_index_map] at hB
  have hloc : ∀ j ∈ Icc 4 q,
      (Lstar j d).image (Finset.map (e d)) ⊆ localForbiddenConfigurations H (available d) (old d) j := by
    intro j hj
    exact (hresult j hj).localizes d ((Icc 4 q).biUnion F) H (available d) (old d) hFH
      (fun E hE ↦ mem_biUnion.mpr ⟨j, hj, hE⟩)
      (fun i ↦ by rw [← hencode d]; exact mem_map.mpr ⟨i, mem_univ _, rfl⟩)
      (hlocal j hj d)
  have hBlocal := regularizedForbiddenUnion_subset_localized_union (e d) q (fun j ↦ Lstar j d)
    H (available d) (old d) hloc hB
  obtain ⟨j, hj, hBj⟩ := mem_biUnion.mp hBlocal
  obtain ⟨hA, _hcard, E, hE, hBE, hOld⟩ :=
    (mem_localForbiddenConfigurations_iff H (available d) (old d) B j).mp hBj
  obtain ⟨j', hj', hEj'⟩ := mem_biUnion.mp hE
  exact ⟨hA, j', hj', E, hEj', hBE, hOld⟩

theorem fixedRandomAllOrders_current_packing
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V]
    {I : Omega → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    {ell : ℕ} (P : FiniteLaw Omega) (W : Vortex V ell)
    (e : (d : Omega) → I d ↪ TripleOn V) (D : Finset V) (q : ℕ) (b : ℕ → ℕ)
    (L Lstar : ℕ → (d : Omega) → Finset (Finset (I d)))
    (F candidates envelope : ℕ → ForbiddenFamilyOn V) (y z a rho : ℕ → ℝ≥0)
    (hsupport : ∀ d i, (e d i).1 ⊆ D)
    (hpacking : ∀ j ∈ Icc 4 q, ∀ d E, E ∈ L j d → IsPackingOn (E.map (e d)))
    (hresult : ∀ j ∈ Icc 4 q, FixedRandomOrderResult P W e j (b j) (L j)
      (fun d ↦ (Ico 4 j).biUnion (fun i ↦ Lstar i d)) (F j) (candidates j)
      (y j) (z j) (a j) (rho j) (Lstar j) (envelope j)) :
    ∀ d, ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j d,
      IsPackingOn (E.map (restrictTripleIndexEmbedding D (e d) (hsupport d))) := by
  intro d j hj E hE
  exact (restrictTripleIndexEmbedding_packing D (e d) (hsupport d) E).mpr
    ((hresult j hj).decoded_packing d (hpacking j hj d) E hE)

end

end Erdos207
