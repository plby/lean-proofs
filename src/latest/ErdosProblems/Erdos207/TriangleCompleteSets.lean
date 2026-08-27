/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RootedHereditaryLayers

/-! # Cliques whose every triangle belongs to the available family -/

namespace Erdos207

open Finset

noncomputable section

def TriangleCompleteSet {V : Type*} [DecidableEq V]
    (E A : Finset (Finset V)) (S : Finset V) : Prop :=
  S.powersetCard 2 ⊆ E ∧ S.powersetCard 3 ⊆ A

theorem TriangleCompleteSet.mono
    {V : Type*} [DecidableEq V] {E A : Finset (Finset V)} {J S : Finset V}
    (hJ : TriangleCompleteSet E A J) (hSJ : S ⊆ J) : TriangleCompleteSet E A S :=
  ⟨(powersetCard_mono hSJ).trans hJ.1, (powersetCard_mono hSJ).trans hJ.2⟩

theorem triangleCompleteSet_pair
    {V : Type*} [DecidableEq V] (E A : Finset (Finset V)) (P : Finset V)
    (hP : P.card = 2) (hPE : P ∈ E) : TriangleCompleteSet E A P := by
  constructor
  · intro Q hQ
    have hm := mem_powersetCard.mp hQ
    have heq : Q = P := eq_of_subset_of_card_le hm.1 (by rw [hP, hm.2])
    simpa only [heq] using hPE
  · intro T hT
    have hm := mem_powersetCard.mp hT
    have hc := card_le_card hm.1
    omega

theorem triangleCompleteSet_triple
    {V : Type*} [DecidableEq V] (E A : Finset (Finset V)) (T : Finset V)
    (hT : T.card = 3) (hTA : T ∈ A) (hTE : T.powersetCard 2 ⊆ E) :
    TriangleCompleteSet E A T := by
  refine ⟨hTE, fun S hS ↦ ?_⟩
  have hm := mem_powersetCard.mp hS
  have heq : S = T := eq_of_subset_of_card_le hm.1 (by rw [hT, hm.2])
  simpa only [heq] using hTA

def triangleSetExtensionVertices {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset (Finset V)) (S : Finset V) : Finset V := by
  classical
  exact univ.filter (fun v ↦ v ∉ S ∧ ∀ P ∈ S.powersetCard 2, insert v P ∈ A)

theorem mem_triangleSetExtensionVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset (Finset V)) (S : Finset V) (v : V) :
    v ∈ triangleSetExtensionVertices A S ↔
      v ∉ S ∧ ∀ P ∈ S.powersetCard 2, insert v P ∈ A := by
  classical
  simp [triangleSetExtensionVertices]

theorem triangleCompleteSet_insert_triangles
    {V : Type*} [DecidableEq V] (A : Finset (Finset V)) (S : Finset V) (v : V)
    (hS : S.powersetCard 3 ⊆ A)
    (hext : ∀ P ∈ S.powersetCard 2, insert v P ∈ A) :
    (insert v S).powersetCard 3 ⊆ A := by
  intro T hT
  have hm := mem_powersetCard.mp hT
  by_cases hv : v ∈ T
  · have hP : T.erase v ∈ S.powersetCard 2 := by
      apply mem_powersetCard.mpr
      refine ⟨?_, ?_⟩
      · intro x hx
        exact (mem_insert.mp (hm.1 (mem_of_mem_erase hx))).resolve_left (mem_erase.mp hx).1
      · rw [card_erase_of_mem hv, hm.2]
    simpa only [insert_erase hv] using hext (T.erase v) hP
  · apply hS
    apply mem_powersetCard.mpr
    refine ⟨?_, hm.2⟩
    intro x hx
    exact (mem_insert.mp (hm.1 hx)).resolve_left (fun heq ↦ hv (heq ▸ hx))

theorem triangleCompleteSet_insert_pairs
    {V : Type*} [DecidableEq V] (E A : Finset (Finset V)) (S : Finset V) (v : V)
    (hS : S.powersetCard 2 ⊆ E) (hsize : 2 ≤ S.card)
    (hA : ∀ T ∈ A, T.powersetCard 2 ⊆ E)
    (hext : ∀ P ∈ S.powersetCard 2, insert v P ∈ A) :
    (insert v S).powersetCard 2 ⊆ E := by
  intro Q hQ
  have hm := mem_powersetCard.mp hQ
  by_cases hv : v ∈ Q
  · have hQS : Q.erase v ⊆ S := by
      intro x hx
      exact (mem_insert.mp (hm.1 (mem_of_mem_erase hx))).resolve_left (mem_erase.mp hx).1
    have hcard : (Q.erase v).card ≤ 2 := by rw [card_erase_of_mem hv, hm.2]; omega
    obtain ⟨P, hQP, hPS, hPc⟩ := exists_subsuperset_card_eq hQS hcard hsize
    have hPA : insert v P ∈ A := hext P (mem_powersetCard.mpr ⟨hPS, hPc⟩)
    apply hA (insert v P) hPA
    apply mem_powersetCard.mpr
    refine ⟨?_, hm.2⟩
    rw [← insert_erase hv]
    exact insert_subset_insert v hQP
  · apply hS
    apply mem_powersetCard.mpr
    refine ⟨?_, hm.2⟩
    intro x hx
    exact (mem_insert.mp (hm.1 hx)).resolve_left (fun heq ↦ hv (heq ▸ hx))

theorem triangleCompleteSet_extensions_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (E A : Finset (Finset V)) (S : Finset V)
    (hS : TriangleCompleteSet E A S) (hsize : 2 ≤ S.card)
    (hA : ∀ T ∈ A, T.powersetCard 2 ⊆ E) :
    hereditaryExtensionVertices (TriangleCompleteSet E A) S = triangleSetExtensionVertices A S := by
  ext v
  rw [mem_hereditaryExtensionVertices_iff, mem_triangleSetExtensionVertices_iff]
  constructor
  · rintro ⟨hv, hgood⟩
    refine ⟨hv, fun P hP ↦ ?_⟩
    have hm := mem_powersetCard.mp hP
    apply hgood.2
    apply mem_powersetCard.mpr
    refine ⟨insert_subset_insert v hm.1, ?_⟩
    rw [card_insert_of_notMem (fun h ↦ hv (hm.1 h)), hm.2]
  · rintro ⟨hv, hext⟩
    exact ⟨hv, triangleCompleteSet_insert_pairs E A S v hS.1 hsize hA hext,
      triangleCompleteSet_insert_triangles A S v hS.2 hext⟩

def eligibleFiveSets {V : Type*} [Fintype V] [DecidableEq V]
    (E A : Finset (Finset V)) : Finset (Finset V) :=
  rootedHereditaryLayer (TriangleCompleteSet E A) ∅ 5

theorem mem_eligibleFiveSets_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (E A : Finset (Finset V)) (J : Finset V) :
    J ∈ eligibleFiveSets E A ↔ J.card = 5 ∧ TriangleCompleteSet E A J := by
  simp only [eligibleFiveSets, mem_rootedHereditaryLayer_iff, empty_subset, true_and]

theorem eligibleFiveSets_rooted
    {V : Type*} [Fintype V] [DecidableEq V]
    (E A : Finset (Finset V)) (Q : Finset V) :
    (eligibleFiveSets E A).filter (Q ⊆ ·) =
      rootedHereditaryLayer (TriangleCompleteSet E A) Q 5 := by
  ext J
  simp only [mem_filter, mem_eligibleFiveSets_iff, mem_rootedHereditaryLayer_iff]
  tauto

end

end Erdos207
