/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.Basic

/-! # Finite vortices and triangle levels -/

namespace Erdos207

open Finset

noncomputable section

/-- A finite nested vortex, indexed from the ambient vertex set at level zero
to its innermost flexible set at level `ell`. -/
structure Vortex (V : Type*) [Fintype V] [DecidableEq V] (ell : ℕ) where
  U : Fin (ell + 1) → Finset V
  root : U 0 = univ
  antitone : ∀ i j, i ≤ j → U j ⊆ U i

def Vortex.levelsContaining
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) : Finset (Fin (ell + 1)) :=
  univ.filter fun i => T.1 ⊆ W.U i

lemma Vortex.zero_mem_levelsContaining
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) :
    (0 : Fin (ell + 1)) ∈ W.levelsContaining T := by
  simp [Vortex.levelsContaining, W.root]

lemma Vortex.levelsContaining_nonempty
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) :
    (W.levelsContaining T).Nonempty :=
  ⟨0, W.zero_mem_levelsContaining T⟩

/-- The largest vortex set containing all three vertices of `T`. -/
def Vortex.level
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) : Fin (ell + 1) :=
  (W.levelsContaining T).max' (W.levelsContaining_nonempty T)

lemma Vortex.mem_levelsContaining_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) (i : Fin (ell + 1)) :
    i ∈ W.levelsContaining T ↔ T.1 ⊆ W.U i := by
  simp [Vortex.levelsContaining]

lemma Vortex.subset_at_level
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) :
    T.1 ⊆ W.U (W.level T) := by
  exact W.mem_levelsContaining_iff T _ |>.mp
    (max'_mem (W.levelsContaining T) (W.levelsContaining_nonempty T))

lemma Vortex.le_level_of_subset
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) (i : Fin (ell + 1))
    (hi : T.1 ⊆ W.U i) : i ≤ W.level T := by
  apply le_max' (W.levelsContaining T) i
  exact W.mem_levelsContaining_iff T i |>.mpr hi

lemma Vortex.subset_iff_le_level
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) (i : Fin (ell + 1)) :
    T.1 ⊆ W.U i ↔ i ≤ W.level T := by
  constructor
  · exact W.le_level_of_subset T i
  · intro hi
    exact (W.subset_at_level T).trans (W.antitone i (W.level T) hi)

/-- All ambient triples whose deepest vortex level is exactly `i`. -/
def Vortex.trianglesAtLevel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin (ell + 1)) : TripleSystemOn V :=
  univ.filter fun T => W.level T = i

@[simp]
lemma Vortex.mem_trianglesAtLevel_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin (ell + 1)) (T : TripleOn V) :
    T ∈ W.trianglesAtLevel i ↔ W.level T = i := by
  simp [Vortex.trianglesAtLevel]

lemma Vortex.trianglesAtLevel_disjoint
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) {i j : Fin (ell + 1)} (hij : i ≠ j) :
    Disjoint (W.trianglesAtLevel i) (W.trianglesAtLevel j) := by
  rw [Finset.disjoint_left]
  intro T hi hj
  exact hij ((W.mem_trianglesAtLevel_iff i T).mp hi |>.symm.trans
    ((W.mem_trianglesAtLevel_iff j T).mp hj))

lemma Vortex.mem_iUnion_trianglesAtLevel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) :
    T ∈ univ.biUnion W.trianglesAtLevel := by
  apply mem_biUnion.mpr
  exact ⟨W.level T, mem_univ _,
    (W.mem_trianglesAtLevel_iff (W.level T) T).mpr rfl⟩

theorem Vortex.iUnion_trianglesAtLevel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) :
    univ.biUnion W.trianglesAtLevel = (univ : TripleSystemOn V) := by
  apply Subset.antisymm
  · exact subset_univ _
  · intro T _hT
    exact W.mem_iUnion_trianglesAtLevel T

/-- The number of members of a triangle family at one vortex level. -/
def Vortex.levelCount
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) (i : Fin (ell + 1)) : ℕ :=
  (C ∩ W.trianglesAtLevel i).card

lemma Vortex.sum_levelCount
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) :
    ∑ i : Fin (ell + 1), W.levelCount C i = C.card := by
  classical
  have hpair :
      ((univ : Finset (Fin (ell + 1))) : Set (Fin (ell + 1))).PairwiseDisjoint
        (fun i ↦ C ∩ W.trianglesAtLevel i) := by
    intro i _hi j _hj hij
    exact Disjoint.mono_right inter_subset_right
      (Disjoint.mono_left inter_subset_right
        (W.trianglesAtLevel_disjoint hij))
  calc
    ∑ i : Fin (ell + 1), W.levelCount C i =
        ∑ i ∈ (univ : Finset (Fin (ell + 1))), #(C ∩ W.trianglesAtLevel i) := by
          simp [Vortex.levelCount]
    _ = #((univ : Finset (Fin (ell + 1))).biUnion
        (fun i ↦ C ∩ W.trianglesAtLevel i)) :=
      (card_biUnion hpair).symm
    _ = #C := by
      congr 1
      ext T
      simp only [mem_biUnion, mem_univ, true_and, mem_inter]
      constructor
      · rintro ⟨i, hTC, _hi⟩
        exact hTC
      · intro hTC
        exact ⟨W.level T, hTC,
          (W.mem_trianglesAtLevel_iff (W.level T) T).mpr rfl⟩

end

end Erdos207
