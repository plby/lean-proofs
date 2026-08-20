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

import ErdosProblems.Erdos735.RestrictedFaceCountInsertion

/-! # Counting first occurrences in a finite sequence -/

open scoped BigOperators

namespace Erdos735

open Classical
noncomputable section

def valuesBefore {k : ℕ} {A : Type*} [DecidableEq A]
    (f : Fin k → A) (j : Fin k) : Finset A :=
  Finset.univ.image fun l : Fin j ↦ f ⟨l, lt_trans l.isLt j.isLt⟩

theorem card_image_univ_eq_sum_firstOccurrences {A : Type*} [DecidableEq A] :
    ∀ k (f : Fin k → A),
      (Finset.univ.image f).card =
        ∑ j, if f j ∉ valuesBefore f j then 1 else 0 := by
  intro k
  induction k with
  | zero =>
      intro f
      simp
  | succ k ih =>
      intro f
      let prev : Fin k → A := fun i ↦ f i.castSucc
      have himage : Finset.univ.image f =
          insert (f (Fin.last k)) (Finset.univ.image prev) := by
        ext x
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨j, rfl⟩
          exact Fin.lastCases (Or.inl rfl) (fun i ↦ Or.inr ⟨i, rfl⟩) j
        · rintro (rfl | ⟨i, rfl⟩)
          · exact ⟨Fin.last k, rfl⟩
          · exact ⟨i.castSucc, rfl⟩
      have hbefore_cast (j : Fin k) :
          valuesBefore f j.castSucc = valuesBefore prev j := by
        rfl
      have hbefore_last :
          valuesBefore f (Fin.last k) = Finset.univ.image prev := by
        rfl
      have hsum :
          (∑ i : Fin k, if f i.castSucc ∉ valuesBefore f i.castSucc then 1 else 0) =
            ∑ i : Fin k, if prev i ∉ valuesBefore prev i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hbefore_cast]
      rw [himage, Finset.card_insert_eq_ite, Fin.sum_univ_castSucc]
      rw [hsum, ← ih prev, hbefore_last]
      by_cases hmem : f (Fin.last k) ∈ Finset.univ.image prev
      · simp [hmem]
      · simp [hmem]

end

end Erdos735
