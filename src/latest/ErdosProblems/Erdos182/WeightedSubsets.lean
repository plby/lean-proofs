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

import Mathlib

/-!
# Finite independent weighted subsets

This file gives a small algebraic API for independent Bernoulli sampling on a
finite type.  It deliberately avoids measure theory: an outcome is a finset
and expectations are finite weighted sums over the powerset of `univ`.
-/

open Finset Fintype
open scoped BigOperators

namespace Erdos182

section WeightedSubsets

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mass of a subset in the product Bernoulli distribution with inclusion
probabilities `p`.  No bounds on `p` are required for the algebraic identities. -/
noncomputable def subsetWeight (p : ι → ℝ) (s : Finset ι) : ℝ :=
  (∏ i ∈ s, p i) * ∏ i ∈ (Finset.univ \ s), (1 - p i)

/-- The product of the inclusion odds over a subset. -/
noncomputable def subsetOdds (p : ι → ℝ) (s : Finset ι) : ℝ :=
  ∏ i ∈ s, p i / (1 - p i)

/-- Expectation with respect to `subsetWeight`. -/
noncomputable def subsetExpectation (p : ι → ℝ) (f : Finset ι → ℝ) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset ι).powerset, subsetWeight p s * f s

/-- Bernoulli masses are nonnegative when all inclusion probabilities lie in
the unit interval. -/
theorem subsetWeight_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s : Finset ι) : 0 ≤ subsetWeight p s := by
  classical
  unfold subsetWeight
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i hi ↦ (hp i).1
  · exact Finset.prod_nonneg fun i hi ↦ sub_nonneg.mpr (hp i).2

/-- The Bernoulli mass can equivalently be written as the product of all
exclusion probabilities times the product of the odds on the chosen subset. -/
theorem subsetWeight_eq_prod_compl_mul_odds (p : ι → ℝ)
    (hp : ∀ i, p i ≠ 1) (s : Finset ι) :
    subsetWeight p s = (∏ i, (1 - p i)) * subsetOdds p s := by
  classical
  have hsplit :
      (∏ i ∈ (Finset.univ \ s), (1 - p i)) * (∏ i ∈ s, (1 - p i)) =
        ∏ i, (1 - p i) :=
    Finset.prod_sdiff (f := fun i ↦ (1 - p i : ℝ)) (Finset.subset_univ s)
  have hcancel :
      (∏ i ∈ s, (1 - p i)) * (∏ i ∈ s, p i / (1 - p i)) = ∏ i ∈ s, p i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact mul_div_cancel₀ (p i) (sub_ne_zero.mpr (Ne.symm (hp i)))
  unfold subsetWeight subsetOdds
  calc
    (∏ i ∈ s, p i) * ∏ i ∈ (Finset.univ \ s), (1 - p i) =
        (∏ i ∈ (Finset.univ \ s), (1 - p i)) * ∏ i ∈ s, p i := by ring
    _ = (∏ i ∈ (Finset.univ \ s), (1 - p i)) *
          ((∏ i ∈ s, (1 - p i)) * ∏ i ∈ s, p i / (1 - p i)) := by rw [hcancel]
    _ = ((∏ i ∈ (Finset.univ \ s), (1 - p i)) * ∏ i ∈ s, (1 - p i)) *
          ∏ i ∈ s, p i / (1 - p i) := by ring
    _ = (∏ i, (1 - p i)) * ∏ i ∈ s, p i / (1 - p i) := by rw [hsplit]

/-- The product Bernoulli masses sum to one. -/
theorem sum_subsetWeight (p : ι → ℝ) :
    ∑ s ∈ (Finset.univ : Finset ι).powerset, subsetWeight p s = 1 := by
  classical
  unfold subsetWeight
  rw [← Finset.prod_add]
  simp

/-- The total mass of outcomes containing every element of `t` is the product
of the corresponding inclusion probabilities.  The indicator formulation is
particularly convenient for subsequent expectation calculations. -/
theorem sum_subsetWeight_indicator_superset (p : ι → ℝ) (t : Finset ι) :
    (∑ s ∈ (Finset.univ : Finset ι).powerset,
        if t ⊆ s then subsetWeight p s else 0) = ∏ i ∈ t, p i := by
  classical
  let q : ι → ℝ := fun i ↦ if i ∈ t then 0 else 1 - p i
  have hprod : (∏ i ∈ (Finset.univ : Finset ι), (p i + q i)) = ∏ i ∈ t, p i := by
    simp [q, apply_ite]
  rw [← hprod, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hts : t ⊆ s
  · rw [if_pos hts]
    unfold subsetWeight
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hit : i ∉ t := fun hit ↦ (Finset.mem_sdiff.mp hi).2 (hts hit)
    simp [q, hit]
  · rw [if_neg hts]
    have hi : ∃ i ∈ (Finset.univ \ s), q i = 0 := by
      obtain ⟨i, hit, his⟩ := Finset.not_subset.mp hts
      exact ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, his⟩, by simp [q, hit]⟩
    obtain ⟨i, hi, hqi⟩ := hi
    rw [Finset.prod_eq_zero hi hqi, mul_zero]

/-- Filtered version of `sum_subsetWeight_indicator_superset`. -/
theorem sum_subsetWeight_superset (p : ι → ℝ) (t : Finset ι) :
    (∑ s ∈ (Finset.univ : Finset ι).powerset with t ⊆ s, subsetWeight p s) =
      ∏ i ∈ t, p i := by
  classical
  rw [Finset.sum_filter]
  exact sum_subsetWeight_indicator_superset p t

/-- Linearity of finite weighted expectation under addition. -/
theorem subsetExpectation_add (p : ι → ℝ) (f g : Finset ι → ℝ) :
    subsetExpectation p (fun s ↦ f s + g s) =
      subsetExpectation p f + subsetExpectation p g := by
  classical
  simp only [subsetExpectation, mul_add, Finset.sum_add_distrib]

/-- Linearity of finite weighted expectation under scalar multiplication. -/
theorem subsetExpectation_const_mul (p : ι → ℝ) (c : ℝ) (f : Finset ι → ℝ) :
    subsetExpectation p (fun s ↦ c * f s) = c * subsetExpectation p f := by
  classical
  unfold subsetExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- Expectation commutes with a finite sum of random variables. -/
theorem subsetExpectation_sum {κ : Type*} (p : ι → ℝ) (t : Finset κ)
    (f : κ → Finset ι → ℝ) :
    subsetExpectation p (fun s ↦ ∑ k ∈ t, f k s) =
      ∑ k ∈ t, subsetExpectation p (f k) := by
  classical
  unfold subsetExpectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The expectation of the indicator that every element of `t` was selected. -/
theorem subsetExpectation_indicator_superset (p : ι → ℝ) (t : Finset ι) :
    subsetExpectation p (fun s ↦ if t ⊆ s then 1 else 0) = ∏ i ∈ t, p i := by
  classical
  unfold subsetExpectation
  simp_rw [mul_ite, mul_one, mul_zero]
  exact sum_subsetWeight_indicator_superset p t

/-- The inclusion indicator of one element has expectation `p i`. -/
theorem subsetExpectation_indicator_mem (p : ι → ℝ) (i : ι) :
    subsetExpectation p (fun s ↦ if i ∈ s then 1 else 0) = p i := by
  classical
  simpa only [Finset.singleton_subset_iff, Finset.prod_singleton] using
    subsetExpectation_indicator_superset p ({i} : Finset ι)

/-- A weighted inclusion indicator has the expected first moment. -/
theorem subsetExpectation_weighted_indicator (p : ι → ℝ) (a : ι → ℝ) (i : ι) :
    subsetExpectation p (fun s ↦ if i ∈ s then a i else 0) = p i * a i := by
  calc
    subsetExpectation p (fun s ↦ if i ∈ s then a i else 0) =
        subsetExpectation p (fun s ↦ a i * (if i ∈ s then 1 else 0)) := by
          congr 1
          funext s
          by_cases hi : i ∈ s <;> simp [hi]
    _ = a i * subsetExpectation p (fun s ↦ if i ∈ s then 1 else 0) :=
      subsetExpectation_const_mul p (a i) _
    _ = a i * p i := by rw [subsetExpectation_indicator_mem]
    _ = p i * a i := by ring

/-- Linearity plus the one-coordinate computation: the expected weighted size
of the random subset is the sum of the one-coordinate expectations. -/
theorem subsetExpectation_sum_mem (p a : ι → ℝ) :
    subsetExpectation p (fun s ↦ ∑ i ∈ s, a i) = ∑ i, p i * a i := by
  classical
  calc
    subsetExpectation p (fun s ↦ ∑ i ∈ s, a i) =
        subsetExpectation p (fun s ↦ ∑ i, if i ∈ s then a i else 0) := by
          congr 1
          funext s
          simp
    _ = ∑ i, subsetExpectation p (fun s ↦ if i ∈ s then a i else 0) :=
      subsetExpectation_sum p Finset.univ fun i s ↦ if i ∈ s then a i else 0
    _ = ∑ i, p i * a i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact subsetExpectation_weighted_indicator p a i

/-- If a weighted expectation is positive and all masses are nonnegative, then
some outcome has positive score. -/
theorem exists_pos_of_subsetExpectation_pos (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (f : Finset ι → ℝ)
    (hpos : 0 < subsetExpectation p f) :
    ∃ s ∈ (Finset.univ : Finset ι).powerset, 0 < f s := by
  classical
  by_contra h
  push Not at h
  have hnonpos : subsetExpectation p f ≤ 0 := by
    unfold subsetExpectation
    exact Finset.sum_nonpos fun s hs ↦
      mul_nonpos_of_nonneg_of_nonpos (subsetWeight_nonneg p hp s) (h s hs)
  exact (not_le_of_gt hpos) hnonpos

end WeightedSubsets

end Erdos182
