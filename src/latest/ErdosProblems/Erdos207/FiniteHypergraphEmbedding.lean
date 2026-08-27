/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteHypergraphDegrees

/-! # Injective finite-hypergraph encoding preserves vertex and maximum degrees -/

namespace Erdos207

open Finset

noncomputable section

theorem finiteHypergraphDegree_image_map
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (e : I ↪ V) (L : Finset (Finset I)) (v : I) :
    finiteHypergraphDegree (L.image (Finset.map e)) (e v) = finiteHypergraphDegree L v := by
  unfold finiteHypergraphDegree
  rw [filter_image]
  simp only [mem_map']
  exact card_image_of_injective _ (map_injective e)

theorem finiteHypergraphDegree_image_map_eq_zero
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (e : I ↪ V) (L : Finset (Finset I)) (v : V) (hv : ∀ i, e i ≠ v) :
    finiteHypergraphDegree (L.image (Finset.map e)) v = 0 := by
  unfold finiteHypergraphDegree
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro E hE
  obtain ⟨hEL, hvE⟩ := mem_filter.mp hE
  obtain ⟨C, _hC, rfl⟩ := mem_image.mp hEL
  obtain ⟨i, _hi, heq⟩ := mem_map.mp hvE
  exact hv i heq

theorem finiteHypergraphMaxDegree_image_map
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    (e : I ↪ V) (L : Finset (Finset I)) :
    finiteHypergraphMaxDegree (L.image (Finset.map e)) = finiteHypergraphMaxDegree L := by
  apply le_antisymm
  · apply (finiteHypergraphMaxDegree_le_iff _ _).mpr
    intro v
    by_cases hv : ∃ i, e i = v
    · obtain ⟨i, rfl⟩ := hv
      rw [finiteHypergraphDegree_image_map]
      exact finiteHypergraphDegree_le_max L i
    · rw [finiteHypergraphDegree_image_map_eq_zero e L v (by simpa only [not_exists] using hv)]
      exact Nat.zero_le _
  · apply (finiteHypergraphMaxDegree_le_iff _ _).mpr
    intro i
    rw [← finiteHypergraphDegree_image_map e L i]
    exact finiteHypergraphDegree_le_max (L.image (Finset.map e)) (e i)

theorem finiteHypergraph_image_map_uniform
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (e : I ↪ V) (L : Finset (Finset I)) (k : ℕ) :
    (∀ E ∈ L.image (Finset.map e), E.card = k) ↔ ∀ E ∈ L, E.card = k := by
  constructor
  · intro h E hE
    simpa only [card_map] using h (E.map e) (mem_image_of_mem _ hE)
  · intro h E hE
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hE
    simpa only [card_map] using h C hC

end

end Erdos207
