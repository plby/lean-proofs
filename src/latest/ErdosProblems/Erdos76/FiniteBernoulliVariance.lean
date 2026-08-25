/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.Kahn

/-!
# Variance of the explicit finite Bernoulli sample

This file proves the second-moment calculation needed for elementary finite
nibble estimates.  Everything is phrased as a sum over `U.powerset`; no
measure-theoretic probability space is involved.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteNibble

variable {E : Type*} [DecidableEq E]

/-- The real-valued indicator of membership in a finite sample. -/
def bernoulliIndicator (e : E) (S : Finset E) : ℝ :=
  if e ∈ S then 1 else 0

/-- The centered number of sampled elements of `A`.  The ground set is an
explicit argument so that the expression records which Bernoulli experiment
is being used, although it does not occur in the finite sum itself. -/
def centeredSum (_U : Finset E) (p : E → ℝ) (A S : Finset E) : ℝ :=
  ∑ e ∈ A, (bernoulliIndicator e S - p e)

private lemma sum_mass_mul_indicator {U : Finset E} {p : E → ℝ} {e : E}
    (heU : e ∈ U) :
    ∑ S ∈ U.powerset, bernoulliMass U p S * bernoulliIndicator e S = p e := by
  simpa only [bernoulliIndicator, mul_ite, mul_one, mul_zero, ← sum_filter] using
    (sum_bernoulliMass_filter_mem (p := p) heU)

private lemma sum_mass_mul_indicator_mul_indicator {U : Finset E} {p : E → ℝ}
    {e f : E} (heU : e ∈ U) (hfU : f ∈ U) (hef : e ≠ f) :
    ∑ S ∈ U.powerset,
        bernoulliMass U p S * bernoulliIndicator e S * bernoulliIndicator f S =
      p e * p f := by
  calc
    ∑ S ∈ U.powerset,
        bernoulliMass U p S * bernoulliIndicator e S * bernoulliIndicator f S =
        ∑ S ∈ U.powerset with e ∈ S ∧ f ∈ S, bernoulliMass U p S := by
      rw [sum_filter]
      apply sum_congr rfl
      intro S _
      by_cases heS : e ∈ S <;> by_cases hfS : f ∈ S <;>
        simp [bernoulliIndicator, heS, hfS]
    _ = p e * p f := sum_bernoulliMass_filter_mem_mem heU hfU hef

private lemma sum_mass_mul_indicator_sq {U : Finset E} {p : E → ℝ} {e : E}
    (heU : e ∈ U) :
    ∑ S ∈ U.powerset,
        bernoulliMass U p S * bernoulliIndicator e S * bernoulliIndicator e S =
      p e := by
  calc
    ∑ S ∈ U.powerset,
        bernoulliMass U p S * bernoulliIndicator e S * bernoulliIndicator e S =
        ∑ S ∈ U.powerset with e ∈ S, bernoulliMass U p S := by
      rw [sum_filter]
      apply sum_congr rfl
      intro S _
      by_cases heS : e ∈ S <;> simp [bernoulliIndicator, heS]
    _ = p e := sum_bernoulliMass_filter_mem heU

private lemma sum_mass_mul_centered_mul_centered {U : Finset E} {p : E → ℝ}
    {e f : E} (heU : e ∈ U) (hfU : f ∈ U) :
    ∑ S ∈ U.powerset, bernoulliMass U p S *
        (bernoulliIndicator e S - p e) * (bernoulliIndicator f S - p f) =
      if e = f then p e * (1 - p e) else 0 := by
  by_cases hef : e = f
  · subst f
    rw [if_pos rfl]
    calc
      ∑ S ∈ U.powerset, bernoulliMass U p S *
          (bernoulliIndicator e S - p e) * (bernoulliIndicator e S - p e) =
          ∑ S ∈ U.powerset,
            (bernoulliMass U p S * bernoulliIndicator e S *
                bernoulliIndicator e S -
              2 * p e * (bernoulliMass U p S * bernoulliIndicator e S) +
              p e ^ 2 * bernoulliMass U p S) := by
        apply sum_congr rfl
        intro S _
        ring
      _ =
          (∑ S ∈ U.powerset,
              bernoulliMass U p S * bernoulliIndicator e S *
                bernoulliIndicator e S) -
            2 * p e * (∑ S ∈ U.powerset,
              bernoulliMass U p S * bernoulliIndicator e S) +
            p e ^ 2 * (∑ S ∈ U.powerset, bernoulliMass U p S) := by
        simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
      _ = p e - 2 * p e * p e + p e ^ 2 * 1 := by
        rw [sum_mass_mul_indicator_sq heU, sum_mass_mul_indicator heU,
          sum_bernoulliMass]
      _ = p e * (1 - p e) := by ring
  · rw [if_neg hef]
    calc
      ∑ S ∈ U.powerset, bernoulliMass U p S *
          (bernoulliIndicator e S - p e) * (bernoulliIndicator f S - p f) =
          ∑ S ∈ U.powerset,
            (bernoulliMass U p S * bernoulliIndicator e S *
                bernoulliIndicator f S -
              p f * (bernoulliMass U p S * bernoulliIndicator e S) -
              p e * (bernoulliMass U p S * bernoulliIndicator f S) +
              (p e * p f) * bernoulliMass U p S) := by
        apply sum_congr rfl
        intro S _
        ring
      _ =
          (∑ S ∈ U.powerset,
              bernoulliMass U p S * bernoulliIndicator e S *
                bernoulliIndicator f S) -
            p f * (∑ S ∈ U.powerset,
              bernoulliMass U p S * bernoulliIndicator e S) -
            p e * (∑ S ∈ U.powerset,
              bernoulliMass U p S * bernoulliIndicator f S) +
            p e * p f * (∑ S ∈ U.powerset, bernoulliMass U p S) := by
        simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
      _ = p e * p f - p f * p e - p e * p f + p e * p f * 1 := by
        rw [sum_mass_mul_indicator_mul_indicator heU hfU hef,
          sum_mass_mul_indicator heU, sum_mass_mul_indicator hfU,
          sum_bernoulliMass]
      _ = 0 := by ring

/-- Exact variance identity for a sum of independent, non-identically
distributed Bernoulli indicators on an explicit finite sample space. -/
lemma sum_bernoulliMass_mul_centeredSum_sq {U A : Finset E} {p : E → ℝ}
    (hA : A ⊆ U) :
    ∑ S ∈ U.powerset, bernoulliMass U p S * centeredSum U p A S ^ 2 =
      ∑ e ∈ A, p e * (1 - p e) := by
  calc
    ∑ S ∈ U.powerset, bernoulliMass U p S * centeredSum U p A S ^ 2 =
        ∑ S ∈ U.powerset, ∑ e ∈ A, ∑ f ∈ A,
          bernoulliMass U p S * (bernoulliIndicator e S - p e) *
            (bernoulliIndicator f S - p f) := by
      apply sum_congr rfl
      intro S _
      simp only [centeredSum, pow_two]
      rw [sum_mul_sum]
      simp only [mul_sum, mul_assoc]
    _ = ∑ e ∈ A, ∑ f ∈ A, ∑ S ∈ U.powerset,
          bernoulliMass U p S * (bernoulliIndicator e S - p e) *
            (bernoulliIndicator f S - p f) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro e _
      rw [sum_comm]
    _ = ∑ e ∈ A, ∑ f ∈ A,
          if e = f then p e * (1 - p e) else 0 := by
      apply sum_congr rfl
      intro e heA
      apply sum_congr rfl
      intro f hfA
      exact sum_mass_mul_centered_mul_centered (hA heA) (hA hfA)
    _ = ∑ e ∈ A, p e * (1 - p e) := by
      apply sum_congr rfl
      intro e heA
      simp [heA]

/-- A coefficient-weighted centered Bernoulli sum. -/
def weightedCenteredSum (U : Finset E) (p a : E → ℝ) (S : Finset E) : ℝ :=
  ∑ e ∈ U, a e * (bernoulliIndicator e S - p e)

/-- Exact variance identity for an arbitrary real coefficient-weighted sum
of independent Bernoulli coordinates. -/
lemma sum_bernoulliMass_mul_weightedCenteredSum_sq
    (U : Finset E) (p a : E → ℝ) :
    ∑ S ∈ U.powerset, bernoulliMass U p S * weightedCenteredSum U p a S ^ 2 =
      ∑ e ∈ U, (a e) ^ 2 * p e * (1 - p e) := by
  calc
    ∑ S ∈ U.powerset, bernoulliMass U p S * weightedCenteredSum U p a S ^ 2 =
        ∑ e ∈ U, ∑ f ∈ U, a e * a f *
          (∑ S ∈ U.powerset, bernoulliMass U p S *
            (bernoulliIndicator e S - p e) * (bernoulliIndicator f S - p f)) := by
      calc
        ∑ S ∈ U.powerset,
            bernoulliMass U p S * weightedCenteredSum U p a S ^ 2 =
            ∑ S ∈ U.powerset, ∑ e ∈ U, ∑ f ∈ U,
              a e * a f * (bernoulliMass U p S *
                (bernoulliIndicator e S - p e) *
                  (bernoulliIndicator f S - p f)) := by
          apply sum_congr rfl
          intro S _
          simp only [weightedCenteredSum, pow_two]
          rw [sum_mul_sum]
          simp only [mul_sum]
          apply sum_congr rfl
          intro e _
          apply sum_congr rfl
          intro f _
          ring
        _ = ∑ e ∈ U, ∑ f ∈ U, ∑ S ∈ U.powerset,
              a e * a f * (bernoulliMass U p S *
                (bernoulliIndicator e S - p e) *
                  (bernoulliIndicator f S - p f)) := by
          rw [sum_comm]
          apply sum_congr rfl
          intro e _
          rw [sum_comm]
        _ = ∑ e ∈ U, ∑ f ∈ U, a e * a f *
              (∑ S ∈ U.powerset, bernoulliMass U p S *
                (bernoulliIndicator e S - p e) *
                  (bernoulliIndicator f S - p f)) := by
          apply sum_congr rfl
          intro e _
          apply sum_congr rfl
          intro f _
          simp only [mul_sum]
    _ = ∑ e ∈ U, ∑ f ∈ U,
          a e * a f * (if e = f then p e * (1 - p e) else 0) := by
      apply sum_congr rfl
      intro e heU
      apply sum_congr rfl
      intro f hfU
      rw [sum_mass_mul_centered_mul_centered heU hfU]
    _ = ∑ e ∈ U, (a e) ^ 2 * p e * (1 - p e) := by
      apply sum_congr rfl
      intro e heU
      simp [heU, pow_two]
      ring

/-- Number of indexed coefficient functions whose weighted centered sum has
squared deviation at least `t²`. -/
def weightedDeviationCount {I : Type*} [Fintype I] [DecidableEq I]
    (U : Finset E) (p : E → ℝ) (a : I → E → ℝ) (t : ℝ) (S : Finset E) : ℕ :=
  ((univ : Finset I).filter fun i ↦
    t ^ 2 ≤ weightedCenteredSum U p (a i) S ^ 2).card

private lemma sq_mul_weightedDeviationCount_le_sum_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (U : Finset E) (p : E → ℝ) (a : I → E → ℝ) (t : ℝ) (S : Finset E) :
    t ^ 2 * (weightedDeviationCount U p a t S : ℝ) ≤
      ∑ i, weightedCenteredSum U p (a i) S ^ 2 := by
  let B : Finset I := (univ : Finset I).filter fun i ↦
    t ^ 2 ≤ weightedCenteredSum U p (a i) S ^ 2
  calc
    t ^ 2 * (weightedDeviationCount U p a t S : ℝ) =
        ∑ _i ∈ B, t ^ 2 := by simp [weightedDeviationCount, B, mul_comm]
    _ ≤ ∑ i ∈ B, weightedCenteredSum U p (a i) S ^ 2 := by
      exact sum_le_sum fun i hi ↦ (mem_filter.mp hi).2
    _ ≤ ∑ i, weightedCenteredSum U p (a i) S ^ 2 := by
      exact sum_le_sum_of_subset_of_nonneg (by simp [B])
        (fun i _ _ ↦ sq_nonneg (weightedCenteredSum U p (a i) S))

/-- Aggregate Chebyshev bound for an indexed family of coefficient-weighted
centered Bernoulli sums. -/
lemma sum_bernoulliMass_mul_weightedDeviationCount_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {U : Finset E} {p : E → ℝ} {a : I → E → ℝ} {t : ℝ}
    (hp₀ : ∀ e ∈ U, 0 ≤ p e) (hp₁ : ∀ e ∈ U, p e ≤ 1) (ht : 0 < t) :
    ∑ S ∈ U.powerset,
        bernoulliMass U p S * (weightedDeviationCount U p a t S : ℝ) ≤
      (t ^ 2)⁻¹ * ∑ i, ∑ e ∈ U,
        (a i e) ^ 2 * p e * (1 - p e) := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hmul :
      t ^ 2 * (∑ S ∈ U.powerset,
        bernoulliMass U p S * (weightedDeviationCount U p a t S : ℝ)) ≤
        ∑ i, ∑ e ∈ U, (a i e) ^ 2 * p e * (1 - p e) := by
    calc
      t ^ 2 * (∑ S ∈ U.powerset,
          bernoulliMass U p S * (weightedDeviationCount U p a t S : ℝ)) =
          ∑ S ∈ U.powerset, bernoulliMass U p S *
            (t ^ 2 * (weightedDeviationCount U p a t S : ℝ)) := by
        simp only [mul_sum, mul_left_comm]
      _ ≤ ∑ S ∈ U.powerset, bernoulliMass U p S *
          (∑ i, weightedCenteredSum U p (a i) S ^ 2) := by
        exact sum_le_sum fun S hS ↦ mul_le_mul_of_nonneg_left
          (sq_mul_weightedDeviationCount_le_sum_sq U p a t S)
          (bernoulliMass_nonneg (mem_powerset.mp hS) hp₀ hp₁)
      _ = ∑ i, ∑ S ∈ U.powerset,
          bernoulliMass U p S * weightedCenteredSum U p (a i) S ^ 2 := by
        simp only [mul_sum]
        rw [sum_comm]
      _ = ∑ i, ∑ e ∈ U, (a i e) ^ 2 * p e * (1 - p e) := by
        apply sum_congr rfl
        intro i _
        exact sum_bernoulliMass_mul_weightedCenteredSum_sq U p (a i)
  calc
    ∑ S ∈ U.powerset,
        bernoulliMass U p S * (weightedDeviationCount U p a t S : ℝ) =
        (t ^ 2)⁻¹ * (t ^ 2 * (∑ S ∈ U.powerset,
          bernoulliMass U p S * (weightedDeviationCount U p a t S : ℝ))) := by
      rw [← mul_assoc, inv_mul_cancel₀ ht2.ne', one_mul]
    _ ≤ (t ^ 2)⁻¹ * ∑ i, ∑ e ∈ U,
        (a i e) ^ 2 * p e * (1 - p e) :=
      mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr ht2.le)

/-- Number of indices whose centered sampled count has squared deviation at
least `a²`. -/
def deviationCount {I : Type*} [Fintype I] [DecidableEq I]
    (U : Finset E) (p : E → ℝ) (A : I → Finset E) (a : ℝ) (S : Finset E) : ℕ :=
  ((univ : Finset I).filter fun i ↦ a ^ 2 ≤ centeredSum U p (A i) S ^ 2).card

private lemma sq_mul_deviationCount_le_sum_sq {I : Type*} [Fintype I]
    [DecidableEq I] (U : Finset E) (p : E → ℝ) (A : I → Finset E) (a : ℝ)
    (S : Finset E) :
    a ^ 2 * (deviationCount U p A a S : ℝ) ≤
      ∑ i, centeredSum U p (A i) S ^ 2 := by
  let B : Finset I :=
    (univ : Finset I).filter fun i ↦ a ^ 2 ≤ centeredSum U p (A i) S ^ 2
  calc
    a ^ 2 * (deviationCount U p A a S : ℝ) =
        ∑ _i ∈ B, a ^ 2 := by simp [deviationCount, B, mul_comm]
    _ ≤ ∑ i ∈ B, centeredSum U p (A i) S ^ 2 := by
      exact sum_le_sum fun i hi ↦ (mem_filter.mp hi).2
    _ ≤ ∑ i, centeredSum U p (A i) S ^ 2 := by
      exact sum_le_sum_of_subset_of_nonneg (by simp [B])
        (fun i _ _ ↦ sq_nonneg (centeredSum U p (A i) S))

/-- Finite Chebyshev/first-moment bound: the expected number of indexed sets
whose sampled count deviates by at least `a` is at most the total coordinate
variance divided by `a²`. -/
lemma sum_bernoulliMass_mul_deviationCount_le {I : Type*} [Fintype I]
    [DecidableEq I] {U : Finset E} {p : E → ℝ} {A : I → Finset E} {a : ℝ}
    (hA : ∀ i, A i ⊆ U) (hp₀ : ∀ e ∈ U, 0 ≤ p e)
    (hp₁ : ∀ e ∈ U, p e ≤ 1) (ha : 0 < a) :
    ∑ S ∈ U.powerset,
        bernoulliMass U p S * (deviationCount U p A a S : ℝ) ≤
      (a ^ 2)⁻¹ * ∑ i, ∑ e ∈ A i, p e * (1 - p e) := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hmul :
      a ^ 2 * (∑ S ∈ U.powerset,
        bernoulliMass U p S * (deviationCount U p A a S : ℝ)) ≤
        ∑ i, ∑ e ∈ A i, p e * (1 - p e) := by
    calc
      a ^ 2 * (∑ S ∈ U.powerset,
          bernoulliMass U p S * (deviationCount U p A a S : ℝ)) =
          ∑ S ∈ U.powerset, bernoulliMass U p S *
            (a ^ 2 * (deviationCount U p A a S : ℝ)) := by
        simp only [mul_sum, mul_left_comm]
      _ ≤ ∑ S ∈ U.powerset, bernoulliMass U p S *
          (∑ i, centeredSum U p (A i) S ^ 2) := by
        exact sum_le_sum fun S hS ↦ mul_le_mul_of_nonneg_left
          (sq_mul_deviationCount_le_sum_sq U p A a S)
          (bernoulliMass_nonneg (mem_powerset.mp hS) hp₀ hp₁)
      _ = ∑ i, ∑ S ∈ U.powerset,
          bernoulliMass U p S * centeredSum U p (A i) S ^ 2 := by
        simp only [mul_sum]
        rw [sum_comm]
      _ = ∑ i, ∑ e ∈ A i, p e * (1 - p e) := by
        apply sum_congr rfl
        intro i _
        exact sum_bernoulliMass_mul_centeredSum_sq (hA i)
  calc
    ∑ S ∈ U.powerset,
        bernoulliMass U p S * (deviationCount U p A a S : ℝ) =
        (a ^ 2)⁻¹ * (a ^ 2 * (∑ S ∈ U.powerset,
          bernoulliMass U p S * (deviationCount U p A a S : ℝ))) := by
      rw [← mul_assoc, inv_mul_cancel₀ ha2.ne', one_mul]
    _ ≤ (a ^ 2)⁻¹ * ∑ i, ∑ e ∈ A i, p e * (1 - p e) :=
      mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr ha2.le)

private lemma exists_output_le_average {Omega : Type*} [Fintype Omega]
    (mass output : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (hsum : ∑ omega, mass omega = 1) :
    ∃ omega, output omega ≤ ∑ x, mass x * output x := by
  obtain ⟨omega, homega⟩ :=
    exists_output_ge_average mass (fun x ↦ -output x) hmass hsum
  refine ⟨omega, ?_⟩
  simpa only [mul_neg, sum_neg_distrib, neg_le_neg_iff] using homega

/-- A finite averaging consequence of the expectation estimate: there is an
actual Bernoulli sample whose number of bad indexed sets is bounded by the
sum of their coordinate variances divided by `a²`. -/
lemma exists_sample_deviationCount_le {I : Type*} [Fintype I] [DecidableEq I]
    {U : Finset E} {p : E → ℝ} {A : I → Finset E} {a : ℝ}
    (hA : ∀ i, A i ⊆ U) (hp₀ : ∀ e ∈ U, 0 ≤ p e)
    (hp₁ : ∀ e ∈ U, p e ≤ 1) (ha : 0 < a) :
    ∃ S ⊆ U, (deviationCount U p A a S : ℝ) ≤
      (a ^ 2)⁻¹ * ∑ i, ∑ e ∈ A i, p e * (1 - p e) := by
  let Omega := {S // S ∈ U.powerset}
  let mass : Omega → ℝ := fun S ↦ bernoulliMass U p S.1
  let output : Omega → ℝ := fun S ↦ (deviationCount U p A a S.1 : ℝ)
  have hmass : ∀ S, 0 ≤ mass S := fun S ↦
    bernoulliMass_nonneg (mem_powerset.mp S.2) hp₀ hp₁
  have hsum : ∑ S, mass S = 1 := by
    change ∑ S ∈ U.powerset.attach, bernoulliMass U p S.1 = 1
    rw [Finset.sum_attach]
    exact sum_bernoulliMass U p
  obtain ⟨S, hS⟩ := exists_output_le_average mass output hmass hsum
  refine ⟨S.1, mem_powerset.mp S.2, hS.trans ?_⟩
  let f : Finset E → ℝ := fun T ↦
    bernoulliMass U p T * (deviationCount U p A a T : ℝ)
  change (∑ S ∈ U.powerset.attach, f S.1) ≤ _
  rw [Finset.sum_attach]
  exact sum_bernoulliMass_mul_deviationCount_le hA hp₀ hp₁ ha

/-- Finite averaging extracts one sample satisfying the aggregate weighted
Chebyshev bound. -/
lemma exists_sample_weightedDeviationCount_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {U : Finset E} {p : E → ℝ} {a : I → E → ℝ} {t : ℝ}
    (hp₀ : ∀ e ∈ U, 0 ≤ p e) (hp₁ : ∀ e ∈ U, p e ≤ 1) (ht : 0 < t) :
    ∃ S ⊆ U, (weightedDeviationCount U p a t S : ℝ) ≤
      (t ^ 2)⁻¹ * ∑ i, ∑ e ∈ U,
        (a i e) ^ 2 * p e * (1 - p e) := by
  let Omega := {S // S ∈ U.powerset}
  let mass : Omega → ℝ := fun S ↦ bernoulliMass U p S.1
  let output : Omega → ℝ := fun S ↦ (weightedDeviationCount U p a t S.1 : ℝ)
  have hmass : ∀ S, 0 ≤ mass S := fun S ↦
    bernoulliMass_nonneg (mem_powerset.mp S.2) hp₀ hp₁
  have hsum : ∑ S, mass S = 1 := by
    change ∑ S ∈ U.powerset.attach, bernoulliMass U p S.1 = 1
    rw [Finset.sum_attach]
    exact sum_bernoulliMass U p
  obtain ⟨S, hS⟩ := exists_output_le_average mass output hmass hsum
  refine ⟨S.1, mem_powerset.mp S.2, hS.trans ?_⟩
  let f : Finset E → ℝ := fun T ↦
    bernoulliMass U p T * (weightedDeviationCount U p a t T : ℝ)
  change (∑ S ∈ U.powerset.attach, f S.1) ≤ _
  rw [Finset.sum_attach]
  exact sum_bernoulliMass_mul_weightedDeviationCount_le hp₀ hp₁ ht

/-- Penalized finite averaging: a lower bound on expected reward and an upper
bound on expected penalty can be realized simultaneously by one outcome. -/
lemma exists_output_sub_penalty_ge
    {Omega : Type*} [Fintype Omega] (mass reward penalty : Omega → ℝ)
    {rewardLower penaltyUpper lambda : ℝ}
    (hmass : ∀ omega, 0 ≤ mass omega) (hsum : ∑ omega, mass omega = 1)
    (hreward : rewardLower ≤ ∑ omega, mass omega * reward omega)
    (hpenalty : ∑ omega, mass omega * penalty omega ≤ penaltyUpper)
    (hlambda : 0 ≤ lambda) :
    ∃ omega, rewardLower - lambda * penaltyUpper ≤
      reward omega - lambda * penalty omega := by
  let output : Omega → ℝ := fun omega ↦ reward omega - lambda * penalty omega
  obtain ⟨omega, homega⟩ := exists_output_ge_average mass output hmass hsum
  refine ⟨omega, ?_⟩
  calc
    rewardLower - lambda * penaltyUpper ≤
        (∑ x, mass x * reward x) -
          lambda * (∑ x, mass x * penalty x) := by
      exact sub_le_sub hreward (mul_le_mul_of_nonneg_left hpenalty hlambda)
    _ = ∑ x, mass x * output x := by
      simp only [output, mul_sub, sum_sub_distrib, mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ output omega := homega

/-- A one-round alteration and a family of weighted concentration conditions
can be optimized simultaneously.  The reward is the isolated (hence
matching) part of the Bernoulli sample, and the penalty is the number of
indexed weighted sums which deviate by at least `t`. -/
lemma exists_isolatedSample_sub_weightedDeviationPenalty
    {V I : Type*} [DecidableEq V] [Fintype E] [Fintype I] [DecidableEq I]
    (H : FiniteHypergraph V E) {p : E → ℝ} {a : I → E → ℝ}
    {t lambda : ℝ} (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (ht : 0 < t) (hlambda : 0 ≤ lambda) :
    ∃ S : Finset E, H.IsMatching (H.isolatedSample S) ∧
      ((∑ e, p e) -
          (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0)) -
          lambda * ((t ^ 2)⁻¹ * ∑ i, ∑ e,
            (a i e) ^ 2 * p e * (1 - p e)) ≤
        ((H.isolatedSample S).card : ℝ) -
          lambda * (weightedDeviationCount univ p a t S : ℝ) := by
  let mass : Finset E → ℝ := fun S ↦ bernoulliMass univ p S
  let reward : Finset E → ℝ := fun S ↦ ((H.isolatedSample S).card : ℝ)
  let penalty : Finset E → ℝ := fun S ↦ (weightedDeviationCount univ p a t S : ℝ)
  have hmass : ∀ S, 0 ≤ mass S := fun S ↦
    bernoulliMass_nonneg (subset_univ S) (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e)
  have hsum : ∑ S, mass S = 1 := by
    simpa [mass] using sum_bernoulliMass (univ : Finset E) p
  have hreward :
      (∑ e, p e) -
          (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) ≤
        ∑ S, mass S * reward S := by
    simpa [mass, reward] using
      (sum_bernoulliMass_mul_isolatedSample_card_ge H p hp₀ hp₁)
  have hpenalty :
      ∑ S, mass S * penalty S ≤
        (t ^ 2)⁻¹ * ∑ i, ∑ e, (a i e) ^ 2 * p e * (1 - p e) := by
    simpa [mass, penalty] using
      (sum_bernoulliMass_mul_weightedDeviationCount_le
        (U := (univ : Finset E)) (a := a)
        (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e) ht)
  obtain ⟨S, hS⟩ := exists_output_sub_penalty_ge mass reward penalty
    hmass hsum hreward hpenalty hlambda
  refine ⟨S, H.isolatedSample_isMatching S, ?_⟩
  simpa [reward, penalty] using hS

end FiniteNibble

end

end Erdos76
