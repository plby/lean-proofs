/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.HighGirthAbsorber
import Mathlib.Logic.Equiv.Fintype

/-! # Exact symmetry of the unperturbed initial Erdős configuration family -/

namespace Erdos207

open Finset

noncomputable section

def fullPackingErdosFamily (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) : ForbiddenFamilyOn V := by
  classical
  exact univ.filter fun C ↦ IsErdosConfigOn r C ∧ IsPackingOn C

def rootedFullPackingErdosFamily
    {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (T : TripleOn V) : ForbiddenFamilyOn V :=
  (fullPackingErdosFamily V r).filter fun C ↦ T ∈ C

theorem mem_fullPackingErdosFamily
    {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (C : TripleSystemOn V) :
    C ∈ fullPackingErdosFamily V r ↔ IsErdosConfigOn r C ∧ IsPackingOn C := by
  classical
  simp only [fullPackingErdosFamily, mem_filter, mem_univ, true_and]

theorem mem_rootedFullPackingErdosFamily
    {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (T : TripleOn V) (C : TripleSystemOn V) :
    C ∈ rootedFullPackingErdosFamily r T ↔ IsErdosConfigOn r C ∧ IsPackingOn C ∧ T ∈ C := by
  simp only [rootedFullPackingErdosFamily, mem_filter, mem_fullPackingErdosFamily, and_assoc]

theorem exists_perm_mapTriple
    {V : Type*} [Fintype V] [DecidableEq V] (T U : TripleOn V) :
    ∃ e : Equiv.Perm V, mapTriple e.toEmbedding T = U := by
  let e₀ : T.1 ≃ U.1 := Fintype.equivOfCardEq (by simp only [Fintype.card_coe, T.2, U.2])
  refine ⟨e₀.extendSubtype, ?_⟩
  apply Subtype.ext
  change T.1.map e₀.extendSubtype.toEmbedding = U.1
  apply eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact e₀.extendSubtype_mem y hy
  · rw [card_map, T.2, U.2]

theorem rootedFullPackingErdosFamily_card_eq
    {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (T U : TripleOn V) :
    (rootedFullPackingErdosFamily r T).card = (rootedFullPackingErdosFamily r U).card := by
  obtain ⟨e, he⟩ := exists_perm_mapTriple T U
  have hbij : Function.Bijective (mapTripleSystem e.toEmbedding) := by
    constructor
    · exact Finset.map_injective (mapTripleEmbedding e.toEmbedding)
    · intro C
      exact ⟨mapTripleSystem e.symm.toEmbedding C, mapTripleSystem_equiv_apply_symm e C⟩
  apply card_bijective (mapTripleSystem e.toEmbedding) hbij
  intro C
  rw [mem_rootedFullPackingErdosFamily, mem_rootedFullPackingErdosFamily]
  constructor
  · rintro ⟨hE, hpack, hT⟩
    refine ⟨IsErdosConfig.map hE e.toEmbedding, hpack.map e.toEmbedding, ?_⟩
    rw [← he]
    exact (mem_mapTripleSystem_iff e.toEmbedding C T).mpr hT
  · rintro ⟨hE, hpack, hU⟩
    have hE' := IsErdosConfig.map hE e.symm.toEmbedding
    have hpack' := hpack.map e.symm.toEmbedding
    rw [mapTripleSystem_equiv_symm_apply] at hE' hpack'
    refine ⟨hE', hpack', ?_⟩
    apply (mem_mapTripleSystem_iff e.toEmbedding C T).mp
    rwa [he]

theorem sum_rootedFullPackingErdosFamily_card
    (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :
    ∑ T : TripleOn V, (rootedFullPackingErdosFamily r T).card =
      (r - 2) * (fullPackingErdosFamily V r).card := by
  classical
  calc
    _ = ∑ T : TripleOn V, ∑ C ∈ fullPackingErdosFamily V r, if T ∈ C then 1 else 0 := by
      simp only [rootedFullPackingErdosFamily, card_eq_sum_ones, sum_filter]
    _ = ∑ C ∈ fullPackingErdosFamily V r, ∑ T : TripleOn V, if T ∈ C then 1 else 0 := sum_comm
    _ = ∑ C ∈ fullPackingErdosFamily V r, C.card := by
      apply sum_congr rfl
      intro C _
      simp
    _ = ∑ _C ∈ fullPackingErdosFamily V r, (r - 2) := by
      apply sum_congr rfl
      intro C hC
      exact ((mem_fullPackingErdosFamily r C).mp hC).1.1.1
    _ = _ := by simp [Nat.mul_comm]

theorem fullPackingErdosFamily_root_incidence
    {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (T : TripleOn V) :
    Fintype.card (TripleOn V) * (rootedFullPackingErdosFamily r T).card =
      (r - 2) * (fullPackingErdosFamily V r).card := by
  have hsum := sum_rootedFullPackingErdosFamily_card V r
  have hconst : (∑ U : TripleOn V, (rootedFullPackingErdosFamily r U).card) =
      Fintype.card (TripleOn V) * (rootedFullPackingErdosFamily r T).card := by
    simp [rootedFullPackingErdosFamily_card_eq r _ T]
  exact hconst.symm.trans hsum

end

end Erdos207
