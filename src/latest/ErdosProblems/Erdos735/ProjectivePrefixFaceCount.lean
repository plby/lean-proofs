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

import ErdosProblems.Erdos735.FirstOccurrenceCount
import ErdosProblems.Erdos735.ProjectivePrefixNovelty
import ErdosProblems.Erdos735.FaceCountInsertion

/-! # Restriction counts from ordered projective intersections -/

open scoped BigOperators Matrix LinearAlgebra.Projectivization
open Matrix

namespace Erdos735.ProjectiveArrangement

open Classical SignVector
noncomputable section

def priorNormals {k : ℕ} (p : Fin k → Point) (i : Fin k) : Fin i → Vec3 :=
  fun j ↦ normalVec (p (priorIndex i j))

def prefixIntersections {k : ℕ} (p : Fin k → Point)
    (hp : Function.Injective p) (i : Fin k) : Finset (ℙ ℝ Vec3) :=
  Finset.univ.image (prefixIntersection p hp i)

lemma valuesBefore_prefixIntersection {k : ℕ}
    (p : Fin k → Point) (hp : Function.Injective p)
    (i : Fin k) (j : Fin i) :
    Erdos735.valuesBefore (prefixIntersection p hp i) j =
      intersectionsBefore p hp i j := by
  rfl

theorem doubleRestrictedFaceCount_priorNormals_prefix
    {k : ℕ} (p : Fin k → Point) (hp : Function.Injective p)
    (i : Fin k) (j : Fin i) :
    doubleRestrictedFaceCount
        (restrictedFinPrefix (priorNormals p i) j)
        (normalVec (p i)) (priorNormals p i j) =
      if j.1 = 0 then 1
      else if prefixIntersection p hp i j ∉ intersectionsBefore p hp i j then 2 else 0 := by
  classical
  have hind : normalVec (p i) ⨯₃ priorNormals p i j ≠ 0 := by
    apply normalVec_cross_ne_zero
    exact hp.ne <| by
      intro hij
      have hval := congrArg Fin.val hij
      simp only [priorIndex] at hval
      omega
  by_cases hjzero : j.1 = 0
  · rw [if_pos hjzero]
    have hbound : 0 < i.1 := by omega
    have hj : j = (⟨0, hbound⟩ : Fin i) := Fin.ext hjzero
    rw [hj]
    exact doubleRestrictedFaceCount_fin_zero _ _ _
  · simp only [if_neg hjzero]
    have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hjzero
    let : Nonempty (Fin j) := ⟨⟨0, hjpos⟩⟩
    by_cases hnew : prefixIntersection p hp i j ∉ intersectionsBefore p hp i j
    · rw [if_pos hnew]
      apply doubleRestrictedFaceCount_eq_two _ hind
      intro l
      exact (prefixIntersection_not_mem_intersectionsBefore_iff p hp i j).1 hnew l
    · rw [if_neg hnew]
      apply doubleRestrictedFaceCount_eq_zero_of_exists_dot_cross_eq_zero _ hind
      have hex : ∃ l : Fin j,
          normalVec (p (priorIndex i (earlierPriorIndex j l))) ⬝ᵥ
            (normalVec (p i) ⨯₃ normalVec (p (priorIndex i j))) = 0 := by
        by_contra hall
        apply hnew
        rw [prefixIntersection_not_mem_intersectionsBefore_iff p hp i j]
        push_neg at hall
        exact fun l ↦ hall l
      simpa [restrictedFinPrefix, priorNormals, earlierPriorIndex] using hex

theorem restrictedFaceCount_priorNormals_eq_two_mul_card
    {k : ℕ} (p : Fin k → Point) (hp : Function.Injective p)
    (i : Fin k) (hi : 0 < i.1) :
    restrictedFaceCount (priorNormals p i) (normalVec (p i)) =
      2 * (prefixIntersections p hp i).card := by
  have hind : ∀ j, normalVec (p i) ⨯₃ priorNormals p i j ≠ 0 := by
    intro j
    apply normalVec_cross_ne_zero
    exact hp.ne <| by
      intro hij
      have hval := congrArg Fin.val hij
      simp only [priorIndex] at hval
      omega
  rw [restrictedFaceCount_fin_eq_one_add_sum_double i (priorNormals p i)
    (normalVec (p i)) hind]
  change 1 + ∑ j,
      doubleRestrictedFaceCount (restrictedFinPrefix (priorNormals p i) j)
        (normalVec (p i)) (priorNormals p i j) =
    2 * (Finset.univ.image (prefixIntersection p hp i)).card
  rw [Erdos735.card_image_univ_eq_sum_firstOccurrences i
    (prefixIntersection p hp i)]
  let z : Fin i := ⟨0, hi⟩
  have hnew_zero :
      prefixIntersection p hp i z ∉ intersectionsBefore p hp i z := by
    simp [intersectionsBefore, z]
  have hpoint (j : Fin i) :
      doubleRestrictedFaceCount (restrictedFinPrefix (priorNormals p i) j)
          (normalVec (p i)) (priorNormals p i j) +
          (if j.1 = 0 then 1 else 0) =
        2 * (if prefixIntersection p hp i j ∉
          intersectionsBefore p hp i j then 1 else 0) := by
    rw [doubleRestrictedFaceCount_priorNormals_prefix p hp i j]
    by_cases hjzero : j.1 = 0
    · have hj : j = z := Fin.ext hjzero
      subst j
      simp [z, hnew_zero]
    · by_cases hnew :
          prefixIntersection p hp i j ∉ intersectionsBefore p hp i j
      · simp [hjzero, hnew]
      · simp [hjzero, hnew]
  have hsumzero : (∑ j : Fin i, if j.1 = 0 then 1 else 0) = 1 := by
    apply Finset.sum_eq_single z
    · intro j hj hjz
      have hjval : j.1 ≠ 0 := by
        intro hval
        apply hjz
        exact Fin.ext hval
      simp [hjval]
    · simp
  have hsum :
      (∑ j : Fin i, (
          doubleRestrictedFaceCount (restrictedFinPrefix (priorNormals p i) j)
              (normalVec (p i)) (priorNormals p i j) +
            (if j.1 = 0 then 1 else 0))) =
        ∑ j : Fin i, 2 * (if prefixIntersection p hp i j ∉
          intersectionsBefore p hp i j then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hpoint j
  rw [Finset.sum_add_distrib, hsumzero] at hsum
  have hfactor :
      (∑ j : Fin i, 2 * (if prefixIntersection p hp i j ∉
          intersectionsBefore p hp i j then 1 else 0)) =
        2 * ∑ j : Fin i, if prefixIntersection p hp i j ∉
          intersectionsBefore p hp i j then 1 else 0 := by
    rw [Finset.mul_sum]
  rw [hfactor] at hsum
  simpa only [valuesBefore_prefixIntersection, Nat.add_comm] using hsum

theorem faceCount_normalVec_eq_two_add_prefixIntersections
    (k : ℕ) (p : Fin (k + 1) → Point) (hp : Function.Injective p) :
    faceCount (fun i ↦ normalVec (p i)) =
      2 + ∑ i : Fin k, 2 * (prefixIntersections p hp i.succ).card := by
  rw [faceCount_fin_succ_eq_two_add_sum_tail k (fun i ↦ normalVec (p i))]
  · apply congrArg (fun t : ℕ ↦ 2 + t)
    apply Finset.sum_congr rfl
    intro i hi
    change restrictedFaceCount (priorNormals p i.succ) (normalVec (p i.succ)) = _
    exact restrictedFaceCount_priorNormals_eq_two_mul_card p hp i.succ (by simp)
  · exact fun i ↦ normalVec_ne_zero (p i)

end

end Erdos735.ProjectiveArrangement
