/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.Vortex
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Vertex levels and level-profile counting in a vortex -/

namespace Erdos207

open Finset

noncomputable section

def Vortex.vertexLevelsContaining
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (v : V) : Finset (Fin (ell + 1)) :=
  univ.filter fun i ↦ v ∈ W.U i

lemma Vortex.zero_mem_vertexLevelsContaining
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (v : V) :
    (0 : Fin (ell + 1)) ∈ W.vertexLevelsContaining v := by
  simp [Vortex.vertexLevelsContaining, W.root]

/-- Deepest vortex set containing a vertex. -/
def Vortex.vertexLevel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (v : V) : Fin (ell + 1) :=
  (W.vertexLevelsContaining v).max'
    ⟨0, W.zero_mem_vertexLevelsContaining v⟩

lemma Vortex.mem_at_vertexLevel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (v : V) : v ∈ W.U (W.vertexLevel v) := by
  exact (mem_filter.mp (max'_mem _
    ⟨0, W.zero_mem_vertexLevelsContaining v⟩)).2

lemma Vortex.mem_U_iff_le_vertexLevel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (v : V) (i : Fin (ell + 1)) :
    v ∈ W.U i ↔ i ≤ W.vertexLevel v := by
  constructor
  · intro hv
    apply le_max'
    simp [Vortex.vertexLevelsContaining, hv]
  · intro hi
    exact W.antitone i (W.vertexLevel v) hi (W.mem_at_vertexLevel v)

/-- Vertices at one exact vortex level. -/
def Vortex.verticesAtLevel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin (ell + 1)) : Finset V :=
  univ.filter fun v ↦ W.vertexLevel v = i

@[simp]
lemma Vortex.mem_verticesAtLevel_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin (ell + 1)) (v : V) :
    v ∈ W.verticesAtLevel i ↔ W.vertexLevel v = i := by
  simp [Vortex.verticesAtLevel]

lemma Vortex.verticesAtLevel_subset_U
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin (ell + 1)) :
    W.verticesAtLevel i ⊆ W.U i := by
  intro v hv
  have hlevel := W.mem_verticesAtLevel_iff i v |>.mp hv
  simpa only [hlevel] using W.mem_at_vertexLevel v

lemma Vortex.verticesAtLevel_disjoint
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) {i j : Fin (ell + 1)} (hij : i ≠ j) :
    Disjoint (W.verticesAtLevel i) (W.verticesAtLevel j) := by
  rw [disjoint_left]
  intro v hvi hvj
  exact hij ((W.mem_verticesAtLevel_iff i v).mp hvi |>.symm.trans
    ((W.mem_verticesAtLevel_iff j v).mp hvj))

theorem Vortex.iUnion_verticesAtLevel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) :
    univ.biUnion W.verticesAtLevel = (univ : Finset V) := by
  apply Subset.antisymm (subset_univ _)
  intro v _hv
  exact mem_biUnion.mpr ⟨W.vertexLevel v, mem_univ _,
    (W.mem_verticesAtLevel_iff _ v).mpr rfl⟩

abbrev VortexVertexProfile (ell : ℕ) := Fin (ell + 1) → ℕ

def Vortex.vertexProfile
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (S : Finset V) : VortexVertexProfile ell :=
  fun i ↦ (S ∩ W.verticesAtLevel i).card

lemma Vortex.sum_vertexProfile
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (S : Finset V) :
    ∑ i : Fin (ell + 1), W.vertexProfile S i = S.card := by
  classical
  have hpair :
      ((univ : Finset (Fin (ell + 1))) : Set (Fin (ell + 1))).PairwiseDisjoint
        (fun i ↦ S ∩ W.verticesAtLevel i) := by
    intro i _hi j _hj hij
    exact Disjoint.mono_right inter_subset_right
      (Disjoint.mono_left inter_subset_right
        (W.verticesAtLevel_disjoint hij))
  calc
    ∑ i : Fin (ell + 1), W.vertexProfile S i =
        ∑ i ∈ (univ : Finset (Fin (ell + 1))),
          #(S ∩ W.verticesAtLevel i) := by simp [Vortex.vertexProfile]
    _ = #((univ : Finset (Fin (ell + 1))).biUnion
        (fun i ↦ S ∩ W.verticesAtLevel i)) := (card_biUnion hpair).symm
    _ = #S := by
      congr 1
      ext x
      simp only [mem_biUnion, mem_univ, true_and, mem_inter]
      constructor
      · rintro ⟨i, hxS, _hxi⟩
        exact hxS
      · intro hxS
        exact ⟨W.vertexLevel x, hxS,
          (W.mem_verticesAtLevel_iff _ x).mpr rfl⟩

/-- All vertex subsets having an exact vortex-level profile. -/
def Vortex.vertexSetsWithProfile
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (v : VortexVertexProfile ell) : Finset (Finset V) :=
  univ.filter fun S ↦ W.vertexProfile S = v

@[simp]
lemma Vortex.mem_vertexSetsWithProfile_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (v : VortexVertexProfile ell) (S : Finset V) :
    S ∈ W.vertexSetsWithProfile v ↔ W.vertexProfile S = v := by
  simp [Vortex.vertexSetsWithProfile]

def Vortex.vertexProfileCode
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (v : VortexVertexProfile ell)
    (S : W.vertexSetsWithProfile v) :
    ∀ i : Fin (ell + 1), (W.verticesAtLevel i).powersetCard (v i) :=
  fun i ↦ ⟨S.1 ∩ W.verticesAtLevel i, by
    apply mem_powersetCard.mpr
    refine ⟨inter_subset_right, ?_⟩
    have hprofile := W.mem_vertexSetsWithProfile_iff v S.1 |>.mp S.2
    exact congrFun hprofile i⟩

lemma Vortex.vertexProfileCode_injective
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (v : VortexVertexProfile ell) :
    Function.Injective (W.vertexProfileCode v) := by
  intro S T hST
  apply Subtype.ext
  ext x
  let i := W.vertexLevel x
  have hxlevel : x ∈ W.verticesAtLevel i :=
    (W.mem_verticesAtLevel_iff i x).mpr rfl
  have hi := congrArg (fun f ↦ (f i).1) hST
  change S.1 ∩ W.verticesAtLevel i =
    T.1 ∩ W.verticesAtLevel i at hi
  change x ∈ S.1 ↔ x ∈ T.1
  calc
    x ∈ S.1 ↔ x ∈ S.1 ∩ W.verticesAtLevel i := by simp [hxlevel]
    _ ↔ x ∈ T.1 ∩ W.verticesAtLevel i := by rw [hi]
    _ ↔ x ∈ T.1 := by simp [hxlevel]

/-- A level profile has at most the product of the corresponding vortex-set
powers many realizations. -/
theorem Vortex.card_vertexSetsWithProfile_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (v : VortexVertexProfile ell) :
    (W.vertexSetsWithProfile v).card ≤
      ∏ i : Fin (ell + 1), (W.U i).card ^ v i := by
  calc
    (W.vertexSetsWithProfile v).card =
        Fintype.card (W.vertexSetsWithProfile v) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card
        (∀ i : Fin (ell + 1),
          (W.verticesAtLevel i).powersetCard (v i)) :=
      Fintype.card_le_of_injective (W.vertexProfileCode v)
        (W.vertexProfileCode_injective v)
    _ = ∏ i : Fin (ell + 1),
        Nat.choose (W.verticesAtLevel i).card (v i) := by
      rw [Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro i _hi
      rw [Fintype.card_coe, card_powersetCard]
    _ ≤ ∏ i : Fin (ell + 1),
        (W.verticesAtLevel i).card ^ v i := by
      apply Finset.prod_le_prod'
      intro i _hi
      exact Nat.choose_le_pow _ _
    _ ≤ ∏ i : Fin (ell + 1), (W.U i).card ^ v i := by
      apply Finset.prod_le_prod'
      intro i _hi
      exact pow_le_pow_left₀ zero_le
        (card_le_card (W.verticesAtLevel_subset_U i)) _

end

end Erdos207
