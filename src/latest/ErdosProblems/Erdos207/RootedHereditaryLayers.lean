/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UniformLayerIncidence

/-! # Rooted layers and one-vertex extensions of a hereditary set family -/

namespace Erdos207

open Finset

noncomputable section

def rootedHereditaryLayer {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (Q : Finset V) (k : ℕ) : Finset (Finset V) := by
  classical
  exact (univ.powersetCard k).filter (fun S ↦ Q ⊆ S ∧ good S)

def hereditaryExtensionVertices {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (S : Finset V) : Finset V := by
  classical
  exact univ.filter (fun v ↦ v ∉ S ∧ good (insert v S))

theorem mem_rootedHereditaryLayer_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (Q S : Finset V) (k : ℕ) :
    S ∈ rootedHereditaryLayer good Q k ↔ S.card = k ∧ Q ⊆ S ∧ good S := by
  classical
  simp [rootedHereditaryLayer]

theorem mem_hereditaryExtensionVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (S : Finset V) (v : V) :
    v ∈ hereditaryExtensionVertices good S ↔ v ∉ S ∧ good (insert v S) := by
  classical
  simp [hereditaryExtensionVertices]

theorem rootedHereditaryLayer_base
    {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (Q : Finset V) (hQ : good Q) :
    rootedHereditaryLayer good Q Q.card = {Q} := by
  ext S
  rw [mem_rootedHereditaryLayer_iff, mem_singleton]
  constructor
  · exact fun h ↦ (eq_of_subset_of_card_le h.2.1 h.1.le).symm
  · rintro rfl
    exact ⟨rfl, Subset.rfl, hQ⟩

theorem hereditaryExtensionVertices_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (Q S : Finset V) (k : ℕ)
    (hQ : Q ⊆ S) (hS : S.card = k) :
    (hereditaryExtensionVertices good S).card =
      ((rootedHereditaryLayer good Q (k + 1)).filter (S ⊆ ·)).card := by
  classical
  apply card_bij (fun v _ ↦ insert v S)
  · intro v hv
    have hm := (mem_hereditaryExtensionVertices_iff good S v).mp hv
    exact mem_filter.mpr ⟨(mem_rootedHereditaryLayer_iff good Q _ _).mpr
      ⟨by rw [card_insert_of_notMem hm.1, hS], hQ.trans (subset_insert _ _), hm.2⟩,
      subset_insert _ _⟩
  · intro v hv w hw heq
    have hvS := ((mem_hereditaryExtensionVertices_iff good S v).mp hv).1
    have hm : v ∈ insert w S := heq ▸ mem_insert_self v S
    exact (mem_insert.mp hm).resolve_right hvS
  · intro J hJ
    have hm := mem_filter.mp hJ
    have hdata := (mem_rootedHereditaryLayer_iff good Q J (k + 1)).mp hm.1
    have hc : (J \ S).card = 1 := by rw [card_sdiff_of_subset hm.2, hdata.1, hS]; omega
    obtain ⟨v, hv⟩ := card_eq_one.mp hc
    have hvJ : v ∈ J \ S := hv.symm ▸ mem_singleton_self v
    have heq : insert v S = J := by
      simpa only [hv, singleton_union] using sdiff_union_of_subset hm.2
    refine ⟨v, (mem_hereditaryExtensionVertices_iff good S v).mpr
      ⟨(mem_sdiff.mp hvJ).2, ?_⟩, heq⟩
    simpa only [heq] using hdata.2.2

theorem rootedHereditaryLayer_extension_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (Q : Finset V) (k : ℕ) (hQ : Q.card ≤ k)
    (hdown : ∀ J S : Finset V, S ⊆ J → good J → good S) :
    (∑ S ∈ rootedHereditaryLayer good Q k, (hereditaryExtensionVertices good S).card) =
      (k + 1 - Q.card) * (rootedHereditaryLayer good Q (k + 1)).card := by
  classical
  calc
    _ = ∑ S ∈ rootedHereditaryLayer good Q k,
        ((rootedHereditaryLayer good Q (k + 1)).filter (S ⊆ ·)).card := by
      apply sum_congr rfl
      intro S hS
      have hm := (mem_rootedHereditaryLayer_iff good Q S k).mp hS
      exact hereditaryExtensionVertices_card good Q S k hm.2.1 hm.1
    _ = _ := uniformLayer_incidence_sum _ _ Q k hQ
      (fun S hS ↦ let hm := (mem_rootedHereditaryLayer_iff good Q S k).mp hS
        ⟨hm.1, hm.2.1⟩)
      (fun J hJ ↦ let hm := (mem_rootedHereditaryLayer_iff good Q J (k + 1)).mp hJ
        ⟨hm.1, hm.2.1⟩)
      (fun J hJ S hSJ hSc hQS ↦ (mem_rootedHereditaryLayer_iff good Q S k).mpr
        ⟨hSc, hQS, hdown J S hSJ
          ((mem_rootedHereditaryLayer_iff good Q J (k + 1)).mp hJ).2.2⟩)

theorem rootedHereditaryLayer_extension_sum_real
    {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (Q : Finset V) (k : ℕ) (hQ : Q.card ≤ k)
    (hdown : ∀ J S : Finset V, S ⊆ J → good J → good S) :
    (∑ S ∈ rootedHereditaryLayer good Q k,
      ((hereditaryExtensionVertices good S).card : ℝ)) =
      (k + 1 - Q.card : ℕ) * ((rootedHereditaryLayer good Q (k + 1)).card : ℝ) := by
  exact_mod_cast rootedHereditaryLayer_extension_sum good Q k hQ hdown

theorem rootedHereditaryLayer_card_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (Q : Finset V) (k : ℕ) (hQ : Q.card ≤ k)
    (hdown : ∀ J S : Finset V, S ⊆ J → good J → good S)
    (lo : ℝ) (hlo : ∀ S ∈ rootedHereditaryLayer good Q k,
      lo ≤ ((hereditaryExtensionVertices good S).card : ℝ)) :
    ((rootedHereditaryLayer good Q k).card : ℝ) * lo ≤
      (k + 1 - Q.card : ℕ) * ((rootedHereditaryLayer good Q (k + 1)).card : ℝ) := by
  rw [← rootedHereditaryLayer_extension_sum_real good Q k hQ hdown]
  simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hlo

theorem rootedHereditaryLayer_card_upper
    {V : Type*} [Fintype V] [DecidableEq V]
    (good : Finset V → Prop) (Q : Finset V) (k : ℕ) (hQ : Q.card ≤ k)
    (hdown : ∀ J S : Finset V, S ⊆ J → good J → good S)
    (hi : ℝ) (hhi : ∀ S ∈ rootedHereditaryLayer good Q k,
      ((hereditaryExtensionVertices good S).card : ℝ) ≤ hi) :
    (k + 1 - Q.card : ℕ) * ((rootedHereditaryLayer good Q (k + 1)).card : ℝ) ≤
      ((rootedHereditaryLayer good Q k).card : ℝ) * hi := by
  rw [← rootedHereditaryLayer_extension_sum_real good Q k hQ hdown]
  simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hhi

end

end Erdos207
