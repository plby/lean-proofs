/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.SignVectorReindex

/-!
# Iterated deletion--restriction for finite central arrangements

This file proves that strict-face counts are invariant under reindexing and
iterates the one-hyperplane deletion--restriction recurrence along `Fin k`.
-/

namespace Erdos735.SignVector

open Classical
noncomputable section

def finPrefix {k : ℕ} (n : Fin k → Vec3) (i : Fin k) : Fin i → Vec3 :=
  fun j => n ⟨j, lt_trans j.isLt i.isLt⟩

/-- Iterated deletion--restriction. The initial `1` is the unique sign
pattern of the empty arrangement. -/
theorem faceCount_fin_eq_one_add_sum_prefix :
    ∀ k (n : Fin k → Vec3), (∀ i, n i ≠ 0) →
      faceCount n = 1 + ∑ i, restrictedFaceCount (finPrefix n i) (n i) := by
  intro k
  induction k with
  | zero =>
      intro n hn
      have hnfun : n = (fun i : Fin 0 => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst n
      simpa using faceCount_empty
  | succ k ih =>
      intro n hn
      let prev : Fin k → Vec3 := fun i => n i.castSucc
      let last : Vec3 := n (Fin.last k)
      have hprev : ∀ i, prev i ≠ 0 := fun i => hn i.castSucc
      have hlast : last ≠ 0 := hn (Fin.last k)
      have hreindex :
          faceCount n = faceCount (insertNormal prev last) := by
        rw [← faceCount_reindex finSuccEquivLast (insertNormal prev last)]
        congr 1
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [reindexNormals, finSuccEquivLast_last, last, insertNormal]
        · simp [reindexNormals, finSuccEquivLast_castSucc, prev, insertNormal]
      have hsum :
          (∑ i : Fin k, restrictedFaceCount (finPrefix prev i) (prev i)) =
            ∑ i : Fin k,
              restrictedFaceCount (finPrefix n i.castSucc) (n i.castSucc) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
      have hlastprefix :
          restrictedFaceCount prev last =
            restrictedFaceCount (finPrefix n (Fin.last k)) (n (Fin.last k)) := by
        congr 1
      calc
        faceCount n = faceCount prev + restrictedFaceCount prev last := by
          rw [hreindex, faceCount_insertNormal prev hlast]
        _ = (1 + ∑ i, restrictedFaceCount (finPrefix prev i) (prev i)) +
              restrictedFaceCount prev last := by rw [ih prev hprev]
        _ = 1 + ∑ i, restrictedFaceCount (finPrefix n i) (n i) := by
          rw [Fin.sum_univ_castSucc, ← hsum, ← hlastprefix]
          omega

/-- The first inserted hyperplane contributes one new region, so a nonempty
finite arrangement starts with two antipodal faces and thereafter accumulates
the restriction counts of the remaining hyperplanes. -/
theorem faceCount_fin_succ_eq_two_add_sum_tail
    (k : ℕ) (n : Fin (k + 1) → Vec3) (hn : ∀ i, n i ≠ 0) :
    faceCount n = 2 + ∑ i : Fin k,
      restrictedFaceCount (finPrefix n i.succ) (n i.succ) := by
  rw [faceCount_fin_eq_one_add_sum_prefix (k + 1) n hn, Fin.sum_univ_succ]
  have hzero : restrictedFaceCount (finPrefix n (0 : Fin (k + 1))) (n 0) = 1 := by
    have hfun : finPrefix n (0 : Fin (k + 1)) =
        (fun i : Fin 0 => Fin.elim0 i) := by
      funext i
      exact Fin.elim0 i
    rw [hfun]
    change restrictedFaceCount (fun i : Fin 0 => Fin.elim0 i) (n 0) = 1
    exact restrictedFaceCount_empty (n 0)
  rw [hzero]
  omega

end
end Erdos735.SignVector
