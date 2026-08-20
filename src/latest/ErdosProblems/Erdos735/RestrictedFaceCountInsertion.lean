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

import ErdosProblems.Erdos735.SignVectorDoubleRestrictionCount
import ErdosProblems.Erdos735.SignVectorReindex

/-!
# Iterated insertion inside a fixed central plane

This is the one-dimensional analogue of the ordinary face-count insertion formula.  The strict
regions in `ker h` start with one empty sign pattern and each successive normal contributes the
number of strict patterns on its common kernel with `h`.
-/

open scoped BigOperators Matrix

namespace Erdos735.SignVector

open Classical
noncomputable section

def restrictedFinPrefix {k : ℕ} (n : Fin k → Vec3) (i : Fin k) : Fin i → Vec3 :=
  fun j ↦ n ⟨j, lt_trans j.isLt i.isLt⟩

theorem restrictedFaceCount_fin_eq_one_add_sum_double :
    ∀ k (n : Fin k → Vec3) (h : Vec3), (∀ i, h ⨯₃ n i ≠ 0) →
      restrictedFaceCount n h =
        1 + ∑ i, doubleRestrictedFaceCount (restrictedFinPrefix n i) h (n i) := by
  intro k
  induction k with
  | zero =>
      intro n h hind
      have hnfun : n = (fun i : Fin 0 ↦ Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst n
      simpa using restrictedFaceCount_empty h
  | succ k ih =>
      intro n h hind
      let prev : Fin k → Vec3 := fun i ↦ n i.castSucc
      let last : Vec3 := n (Fin.last k)
      have hprev : ∀ i, h ⨯₃ prev i ≠ 0 := fun i ↦ hind i.castSucc
      have hlast : h ⨯₃ last ≠ 0 := hind (Fin.last k)
      have hreindex :
          restrictedFaceCount n h = restrictedFaceCount (insertNormal prev last) h := by
        rw [← restrictedFaceCount_reindex finSuccEquivLast (insertNormal prev last) h]
        congr 1
        funext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp [reindexNormals, finSuccEquivLast_last, last, insertNormal]
        · simp [reindexNormals, finSuccEquivLast_castSucc, prev, insertNormal]
      have hsum :
          (∑ i : Fin k,
              doubleRestrictedFaceCount (restrictedFinPrefix prev i) h (prev i)) =
            ∑ i : Fin k,
              doubleRestrictedFaceCount (restrictedFinPrefix n i.castSucc) h (n i.castSucc) := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      have hlastprefix :
          doubleRestrictedFaceCount prev h last =
            doubleRestrictedFaceCount (restrictedFinPrefix n (Fin.last k)) h
              (n (Fin.last k)) := by
        rfl
      calc
        restrictedFaceCount n h =
            restrictedFaceCount prev h + doubleRestrictedFaceCount prev h last := by
          rw [hreindex, restrictedFaceCount_insertNormal prev hlast]
        _ = (1 + ∑ i,
              doubleRestrictedFaceCount (restrictedFinPrefix prev i) h (prev i)) +
              doubleRestrictedFaceCount prev h last := by rw [ih prev h hprev]
        _ = 1 + ∑ i,
              doubleRestrictedFaceCount (restrictedFinPrefix n i) h (n i) := by
          rw [Fin.sum_univ_castSucc, ← hsum, ← hlastprefix]
          omega

end

end Erdos735.SignVector
