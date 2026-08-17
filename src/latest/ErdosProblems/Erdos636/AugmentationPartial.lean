/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos636.AntiConcentration
import ErdosProblems.Erdos636.CollisionCounting
import ErdosProblems.Erdos636.Hypergeometric
import ErdosProblems.Erdos636.SliceMoments

/-!
# Partial exposure in the Kwan--Sudakov augmentation

This file isolates the finite probabilistic content of Claim 4.8 in the
Kwan--Sudakov proof.  There are two layers.

* `exists_partialExposure_of_probability_bounds` is the exact simultaneous
  selection argument.  It combines a union bound for persistence of all
  pairwise diversity events with two first-moment degree counts and the
  collision-graph first moment.
* `slice_collision_probability_le_of_l1_equal_sum` discharges the collision
  hypothesis from the graph-theoretic assumptions actually furnished by the
  structural lemma: bounded integral incidence vectors, equal total degree,
  and linear pairwise `ℓ¹` distance.

All probabilities are normalized cardinalities of finite types.  No
independence assumption is used in the simultaneous-selection theorem.
-/

open scoped BigOperators

namespace Erdos636
namespace AugmentationPartial

open Classical Finset
open Erdos88.Concentration
open Erdos88.Fourier

universe u v w

noncomputable section

/-! ## Linear statistics on fixed-size slices -/

section ProductLinear

open Erdos88.BooleanSlices

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
variable {kappa : Type v} [Fintype kappa] [DecidableEq kappa]

/-- A real linear statistic on a product of signed fixed-size slices.  An
ordinary uniform subset is the one-bucket specialization with no negative
coordinates. -/
noncomputable def productLinear (P : BucketPartition alpha kappa)
    {plus minus : kappa → ℕ} (a : alpha → ℝ)
    (S : ProductSignedSlicePoint P plus minus) : ℝ :=
  ∑ x, a x * productSignedSliceValue P S x

lemma abs_productSignedSliceValue_le_one (P : BucketPartition alpha kappa)
    {plus minus : kappa → ℕ} (S : ProductSignedSlicePoint P plus minus)
    (x : alpha) : |productSignedSliceValue P S x| ≤ 1 := by
  simp only [productSignedSliceValue, signedSliceValue]
  split_ifs <;> norm_num

/-- A legal exchange in one bucket changes a bounded linear statistic by at
most `4B`.  The constant `4` covers ternary signed slices; the ordinary
zero-negative slice has the sharper constant `2`, but this uniform version
is sufficient for every partial-exposure tail. -/
lemma abs_productLinear_sub_le (P : BucketPartition alpha kappa)
    {plus minus : kappa → ℕ} (a : alpha → ℝ) (B : ℝ)
    (hB : ∀ x, |a x| ≤ B)
    (S T : ProductSignedSlicePoint P plus minus)
    (hST : IsProductSignedSwitch P S T) :
    |productLinear P a S - productLinear P a T| ≤ 4 * B := by
  obtain ⟨k, i, j, _hi, _hj, hij, hswap⟩ := hST
  let zS : alpha → ℝ := productSignedSliceValue P S
  let zT : alpha → ℝ := productSignedSliceValue P T
  have hsum : productLinear P a T - productLinear P a S =
      (a i - a j) * (zS j - zS i) := by
    rw [productLinear, productLinear, ← Finset.sum_sub_distrib]
    calc
      ∑ x, (a x * zT x - a x * zS x) =
          ∑ x ∈ ({i, j} : Finset alpha),
            (a x * zT x - a x * zS x) := by
        symm
        apply Finset.sum_subset (by simp)
        intro x _hx hxnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
        have hx := hswap x
        simp only [hxnot.1, hxnot.2, if_false] at hx
        change a x * productSignedSliceValue P T x -
          a x * productSignedSliceValue P S x = 0
        rw [hx]
        ring
      _ = (a i - a j) * (zS j - zS i) := by
        have hi := hswap i
        have hj := hswap j
        simp only [if_pos, hij, hij.symm, if_false] at hi hj
        dsimp only [zT, zS]
        rw [Finset.sum_insert (by simpa using hij), Finset.sum_singleton]
        rw [hi, hj]
        ring
  rw [abs_sub_comm, hsum, abs_mul]
  have haij : |a i - a j| ≤ 2 * B := by
    calc
      |a i - a j| ≤ |a i| + |a j| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB i) (hB j)
      _ = 2 * B := by ring
  have hz : |zS j - zS i| ≤ 2 := by
    calc
      |zS j - zS i| ≤ |zS j| + |zS i| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add
        (abs_productSignedSliceValue_le_one P S j)
        (abs_productSignedSliceValue_le_one P S i)
      _ = 2 := by norm_num
  nlinarith [abs_nonneg (a i - a j), abs_nonneg (zS j - zS i)]

/-- Hypergeometric concentration for a bounded linear statistic, with all
constants explicit.  This is the direct input for the diversity-persistence
and degree-good parts of the partial exposure. -/
theorem productLinear_two_sided_probability {K : ℕ}
    (P : BucketPartition alpha (Fin K)) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (a : alpha → ℝ) (B t : ℝ)
    (hL : 0 < Finset.univ.sum (fun k : Fin K ↦ plus k + minus k))
    (hBpos : 0 < B) (ht : 0 ≤ t) (hbounded : ∀ x, |a x| ≤ B) :
    Erdos88.Concentration.uniformProbability
      (fun S : ProductSignedSlicePoint P plus minus ↦
        t ≤ |productLinear (plus := plus) (minus := minus) P a S -
          Erdos88.Concentration.uniformExpectation
            (productLinear (plus := plus) (minus := minus) P a)|) ≤
      2 * Real.exp
        (-t ^ 2 / (2 * (Finset.univ.sum
          (fun k : Fin K ↦ plus k + minus k)) * (4 * B) ^ 2)) := by
  apply Hypergeometric.productSignedSlice_two_sided_probability
    P plus minus hcount e (productLinear P a) (4 * B) t hL (by positivity) ht
  intro S T hST
  exact abs_productLinear_sub_le P a B hbounded S T hST

end ProductLinear

section ExactMean

open Erdos88.BooleanSlices

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]

/-- Exact first moment of an incidence sum on a uniform fixed-cardinality
subset.  In the outer exposure `s = 2 n_D`; this identifies the centre used
by `productLinear_two_sided_probability` without an asymptotic argument. -/
theorem expectation_incidenceSum_booleanSlicePoint
    (s : ℕ) (a : alpha → ℝ) (hs : s ≤ Fintype.card alpha) :
    letI : Nonempty (BooleanSlicePoint (Finset.univ : Finset alpha) s) :=
      SliceMoments.nonempty_booleanSlicePoint Finset.univ s (by simpa using hs)
    Erdos88.Concentration.uniformExpectation
        (fun S : BooleanSlicePoint (Finset.univ : Finset alpha) s ↦
          ∑ i ∈ S.1, a i) =
      (s : ℝ) / Fintype.card alpha * ∑ i, a i := by
  letI : Nonempty (BooleanSlicePoint (Finset.univ : Finset alpha) s) :=
    SliceMoments.nonempty_booleanSlicePoint Finset.univ s (by simpa using hs)
  have h := SliceMoments.expectation_sum_booleanSlicePoint
    (Finset.univ : Finset alpha) s a (by simpa using hs)
      (Finset.univ_nonempty : (Finset.univ : Finset alpha).Nonempty)
  rw [Fintype.expect_eq_sum_div_card] at h
  simpa only [Erdos88.Concentration.uniformExpectation, Finset.card_univ] using h

end ExactMean

/-! ## Finite simultaneous selection -/

variable {Omega : Type u} [Fintype Omega] [Nonempty Omega]

/-- The expectation of an event indicator is its normalized counting
probability. -/
lemma uniformExpectation_indicator (P : Omega → Prop) :
    uniformExpectation (fun omega ↦ if P omega then (1 : ℝ) else 0) =
      uniformProbability P := by
  classical
  unfold uniformExpectation uniformProbability
  congr 1
  rw [Finset.sum_ite]
  simp

/-- Positive normalized counting probability produces an actual outcome. -/
lemma exists_of_uniformProbability_pos (P : Omega → Prop)
    (hP : 0 < uniformProbability P) : ∃ omega, P omega := by
  classical
  by_contra h
  push Not at h
  have hzero : uniformProbability P = 0 := by
    unfold uniformProbability
    simp only [h, Finset.filter_false, Finset.card_empty, Nat.cast_zero,
      zero_div]
  linarith

/-- Quantitative four-event union bound, stated in the form used by the
outer exposure.  The proof averages the sum of the four failure indicators;
this avoids any measure-theoretic complement bookkeeping. -/
theorem one_sub_four_failure_bounds_le_probability_good
    (bad₀ bad₁ bad₂ bad₃ : Omega → Prop)
    (p₀ p₁ p₂ p₃ : ℝ)
    (h₀ : uniformProbability bad₀ ≤ p₀)
    (h₁ : uniformProbability bad₁ ≤ p₁)
    (h₂ : uniformProbability bad₂ ≤ p₂)
    (h₃ : uniformProbability bad₃ ≤ p₃) :
    1 - (p₀ + p₁ + p₂ + p₃) ≤
      uniformProbability (fun omega ↦
        ¬ bad₀ omega ∧ ¬ bad₁ omega ∧
          ¬ bad₂ omega ∧ ¬ bad₃ omega) := by
  classical
  let score : Omega → ℝ := fun omega ↦
    ((if bad₀ omega then 1 else 0) +
      (if bad₁ omega then 1 else 0)) +
      (if bad₂ omega then 1 else 0) +
      (if bad₃ omega then 1 else 0)
  have hscoreMean : uniformExpectation score =
      uniformProbability bad₀ + uniformProbability bad₁ +
        uniformProbability bad₂ + uniformProbability bad₃ := by
    dsimp only [score]
    rw [uniformExpectation_add, uniformExpectation_add,
      uniformExpectation_add]
    simp only [uniformExpectation_indicator]
  let good : Omega → Prop := fun omega ↦
    ¬ bad₀ omega ∧ ¬ bad₁ omega ∧
      ¬ bad₂ omega ∧ ¬ bad₃ omega
  letI : DecidablePred good := Classical.decPred good
  have hpoint (omega : Omega) :
      1 ≤ (if good omega then (1 : ℝ) else 0) + score omega := by
    by_cases hbad₀ : bad₀ omega
    · simp only [good, score, hbad₀, not_true_eq_false, false_and,
        if_false, if_true, zero_add]
      split_ifs <;> norm_num
    by_cases hbad₁ : bad₁ omega
    · simp only [good, score, hbad₀, hbad₁, not_false_eq_true,
        not_true_eq_false, true_and, false_and, if_false, if_true, zero_add]
      split_ifs <;> norm_num
    by_cases hbad₂ : bad₂ omega
    · simp only [good, score, hbad₀, hbad₁, hbad₂,
        not_false_eq_true, not_true_eq_false, true_and, false_and, if_false,
        if_true, zero_add]
      split_ifs <;> norm_num
    by_cases hbad₃ : bad₃ omega
    · simp [good, score, hbad₀, hbad₁, hbad₂, hbad₃]
    · simp [good, score, hbad₀, hbad₁, hbad₂, hbad₃]
  have hcardOmega : (0 : ℝ) < Fintype.card Omega := by
    exact_mod_cast Fintype.card_pos
  have honeMean :
      1 ≤ uniformExpectation
        (fun omega ↦ (if good omega then (1 : ℝ) else 0) + score omega) := by
    rw [uniformExpectation]
    apply (le_div_iff₀ hcardOmega).2
    simp only [one_mul]
    calc
      (Fintype.card Omega : ℝ) = ∑ _omega : Omega, (1 : ℝ) := by simp
      _ ≤ ∑ omega : Omega,
          ((if good omega then (1 : ℝ) else 0) + score omega) :=
        Finset.sum_le_sum fun omega _homega ↦ hpoint omega
  have hgoodMean : uniformExpectation
      (fun omega ↦ if good omega then (1 : ℝ) else 0) =
        uniformProbability good := by
    exact uniformExpectation_indicator good
  rw [uniformExpectation_add, hgoodMean, hscoreMean] at honeMean
  change 1 - (p₀ + p₁ + p₂ + p₃) ≤ uniformProbability good
  have hsum : uniformProbability bad₀ + uniformProbability bad₁ +
      uniformProbability bad₂ + uniformProbability bad₃ ≤
        p₀ + p₁ + p₂ + p₃ := by
    gcongr
  linarith

/-- If the sum of four failure-probability bounds is strictly below one,
there is an outcome at which none of the failures occurs. -/
lemma exists_avoiding_four_events
    (bad₀ bad₁ bad₂ bad₃ : Omega → Prop)
    (p₀ p₁ p₂ p₃ : ℝ)
    (h₀ : uniformProbability bad₀ ≤ p₀)
    (h₁ : uniformProbability bad₁ ≤ p₁)
    (h₂ : uniformProbability bad₂ ≤ p₂)
    (h₃ : uniformProbability bad₃ ≤ p₃)
    (hbudget : p₀ + p₁ + p₂ + p₃ < 1) :
    ∃ omega, ¬ bad₀ omega ∧ ¬ bad₁ omega ∧
      ¬ bad₂ omega ∧ ¬ bad₃ omega := by
  classical
  let score : Omega → ℝ := fun omega ↦
    ((if bad₀ omega then 1 else 0) +
      (if bad₁ omega then 1 else 0)) +
      (if bad₂ omega then 1 else 0) +
      (if bad₃ omega then 1 else 0)
  have hscoreMean : uniformExpectation score =
      uniformProbability bad₀ + uniformProbability bad₁ +
        uniformProbability bad₂ + uniformProbability bad₃ := by
    dsimp only [score]
    rw [uniformExpectation_add, uniformExpectation_add,
      uniformExpectation_add]
    simp only [uniformExpectation_indicator]
  have hsum : uniformProbability bad₀ + uniformProbability bad₁ +
      uniformProbability bad₂ + uniformProbability bad₃ ≤
        p₀ + p₁ + p₂ + p₃ := by
    gcongr
  by_contra hexists
  push Not at hexists
  have hone (omega : Omega) : 1 ≤ score omega := by
    by_cases hbad₀ : bad₀ omega
    · simp only [score, hbad₀, if_true]
      split_ifs <;> norm_num
    by_cases hbad₁ : bad₁ omega
    · simp only [score, hbad₀, hbad₁, if_false, if_true,
        zero_add]
      split_ifs <;> norm_num
    by_cases hbad₂ : bad₂ omega
    · simp only [score, hbad₀, hbad₁, hbad₂, if_false,
        if_true, zero_add]
      split_ifs <;> norm_num
    by_cases hbad₃ : bad₃ omega
    · simp [score, hbad₀, hbad₁, hbad₂, hbad₃]
    exact (hbad₃ (hexists omega hbad₀ hbad₁ hbad₂)).elim
  have hcardOmega : (0 : ℝ) < Fintype.card Omega := by
    exact_mod_cast Fintype.card_pos
  have honeMean : 1 ≤ uniformExpectation score := by
    rw [uniformExpectation]
    apply (le_div_iff₀ hcardOmega).2
    simp only [one_mul]
    calc
      (Fintype.card Omega : ℝ) = ∑ _omega : Omega, (1 : ℝ) := by simp
      _ ≤ ∑ omega : Omega, score omega :=
        Finset.sum_le_sum fun omega _homega ↦ hone omega
  rw [hscoreMean] at honeMean
  linarith

/-! ## Exact simultaneous partial-exposure selector -/

variable {J : Type v} [LinearOrder J]

/-- A finite abstract form of the partial exposure claim.

`S₀` and `X₀` are the two disjoint matching subfamilies.  The event
`diverse i j omega` says that the pair `i,j` retains the required restricted
neighbourhood diversity.  The event `degreeGood i omega` is the desired
square-root degree window.  Finally, `value i omega` is the exposed degree;
its equality graph on `S₀` is the collision graph.

The four displayed summands in `hbudget` are, respectively, the union bound
for all pairs in `X₀`, the two Markov bounds for bad degree cells, and the
Markov bound for collision edges. -/
theorem exists_partialExposure_of_probability_bounds
    {K : Type w} [DecidableEq K]
    (S₀ X₀ : Finset J) (hdisjoint : Disjoint S₀ X₀)
    (diverse : J → J → Omega → Prop)
    (degreeGood : J → Omega → Prop)
    (value : J → Omega → K)
    (pDiv pDegree pCollision tS tX tCollision : ℝ)
    (htS : 0 < tS) (htX : 0 < tX) (htCollision : 0 < tCollision)
    (hdiverse : ∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j →
      uniformProbability (fun omega ↦ ¬ diverse i j omega) ≤ pDiv)
    (hdegree : ∀ i ∈ S₀ ∪ X₀,
      uniformProbability (fun omega ↦ ¬ degreeGood i omega) ≤ pDegree)
    (hdiverseSymm : ∀ i j omega, diverse i j omega ↔ diverse j i omega)
    (hcollision : ∀ i ∈ S₀, ∀ j ∈ S₀, i ≠ j →
      uniformProbability (fun omega ↦ value i omega = value j omega) ≤
        pCollision)
    (hbudget :
      X₀.card.choose 2 * pDiv +
          S₀.card * pDegree / tS +
          X₀.card * pDegree / tX +
          S₀.card.choose 2 * pCollision / tCollision < 1) :
    ∃ omega,
      (∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j → diverse i j omega) ∧
      ((S₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tS ∧
      ((X₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tX ∧
      ((CollisionCounting.collisionEdges S₀ value omega).card : ℝ) <
        tCollision := by
  classical
  let pairBad : (J × J) → Omega → Prop := fun ij omega ↦
    ¬ diverse ij.1 ij.2 omega
  have hpair : ∀ ij ∈ CollisionCounting.possibleEdges X₀,
      uniformProbability (pairBad ij) ≤ pDiv := by
    rintro ⟨i, j⟩ hij
    simp only [CollisionCounting.possibleEdges, Finset.mem_filter,
      Finset.mem_offDiag] at hij
    exact hdiverse i hij.1.1 j hij.1.2.1 hij.1.2.2
  have hdivFail :
      uniformProbability (fun omega ↦
        (1 : ℝ) ≤ CollisionCounting.eventCount
          (CollisionCounting.possibleEdges X₀) pairBad omega) ≤
        X₀.card.choose 2 * pDiv := by
    have h := CollisionCounting.uniformProbability_eventCount_ge_le
      (CollisionCounting.possibleEdges X₀) pairBad pDiv 1 (by norm_num) hpair
    simpa using h
  have hdegS :
      uniformProbability (fun omega ↦ tS ≤
        CollisionCounting.eventCount S₀
          (fun i omega ↦ ¬ degreeGood i omega) omega) ≤
        S₀.card * pDegree / tS := by
    apply CollisionCounting.uniformProbability_eventCount_ge_le
      S₀ (fun i omega ↦ ¬ degreeGood i omega) pDegree tS htS
    intro i hi
    exact hdegree i (Finset.mem_union_left X₀ hi)
  have hdegX :
      uniformProbability (fun omega ↦ tX ≤
        CollisionCounting.eventCount X₀
          (fun i omega ↦ ¬ degreeGood i omega) omega) ≤
        X₀.card * pDegree / tX := by
    apply CollisionCounting.uniformProbability_eventCount_ge_le
      X₀ (fun i omega ↦ ¬ degreeGood i omega) pDegree tX htX
    intro i hi
    exact hdegree i (Finset.mem_union_right S₀ hi)
  have hcoll :
      uniformProbability (fun omega ↦ tCollision ≤
        (CollisionCounting.collisionEdges S₀ value omega).card) ≤
        S₀.card.choose 2 * pCollision / tCollision :=
    CollisionCounting.uniformProbability_card_collisionEdges_ge_le
      S₀ value pCollision tCollision htCollision hcollision
  obtain ⟨omega, h₀, h₁, h₂, h₃⟩ := exists_avoiding_four_events
    (Omega := Omega)
    (fun omega ↦ (1 : ℝ) ≤ CollisionCounting.eventCount
      (CollisionCounting.possibleEdges X₀) pairBad omega)
    (fun omega ↦ tS ≤ CollisionCounting.eventCount S₀
      (fun i omega ↦ ¬ degreeGood i omega) omega)
    (fun omega ↦ tX ≤ CollisionCounting.eventCount X₀
      (fun i omega ↦ ¬ degreeGood i omega) omega)
    (fun omega ↦ tCollision ≤
      (CollisionCounting.collisionEdges S₀ value omega).card)
    (X₀.card.choose 2 * pDiv)
    (S₀.card * pDegree / tS)
    (X₀.card * pDegree / tX)
    (S₀.card.choose 2 * pCollision / tCollision)
    hdivFail hdegS hdegX hcoll hbudget
  refine ⟨omega, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    by_contra hbad
    apply h₀
    have hlt : i < j ∨ j < i := lt_or_gt_of_ne hij
    rcases hlt with hijlt | hjilt
    · have hmem : (i, j) ∈ CollisionCounting.possibleEdges X₀ := by
        simp [CollisionCounting.possibleEdges, hi, hj, hij, hijlt]
      have hone : 1 ≤ CollisionCounting.eventCount
          (CollisionCounting.possibleEdges X₀) pairBad omega := by
        have hone' : 1 ≤ ((CollisionCounting.possibleEdges X₀).filter
            fun ij ↦ ¬ diverse ij.1 ij.2 omega).card := by
          rw [Finset.one_le_card]
          exact ⟨(i, j), Finset.mem_filter.mpr ⟨hmem, hbad⟩⟩
        simpa only [CollisionCounting.eventCount, pairBad] using hone'
      exact_mod_cast hone
    · have hsymm : ¬ diverse j i omega := by
        exact fun hji ↦ hbad ((hdiverseSymm i j omega).mpr hji)
      have hmem : (j, i) ∈ CollisionCounting.possibleEdges X₀ := by
        simp [CollisionCounting.possibleEdges, hi, hj, hij.symm, hjilt]
      have hone : 1 ≤ CollisionCounting.eventCount
          (CollisionCounting.possibleEdges X₀) pairBad omega := by
        have hone' : 1 ≤ ((CollisionCounting.possibleEdges X₀).filter
            fun ij ↦ ¬ diverse ij.1 ij.2 omega).card := by
          rw [Finset.one_le_card]
          exact ⟨(j, i), Finset.mem_filter.mpr ⟨hmem, hsymm⟩⟩
        simpa only [CollisionCounting.eventCount, pairBad] using hone'
      exact_mod_cast hone
  · simpa [CollisionCounting.eventCount] using (not_le.mp h₁)
  · simpa [CollisionCounting.eventCount] using (not_le.mp h₂)
  · exact not_le.mp h₃

/-- Probability form of `exists_partialExposure_of_probability_bounds`.

The conclusion is deliberately quantitative: if the displayed four-term
budget is at most `1 / 4`, then the good partial exposure has probability at
least `3 / 4`.  This is the form that composes with the conditional full
exposure and the exact nested-uniform marginal law. -/
theorem one_sub_budget_le_partialExposure_probability
    {K : Type w} [DecidableEq K]
    (S₀ X₀ : Finset J) (_hdisjoint : Disjoint S₀ X₀)
    (diverse : J → J → Omega → Prop)
    (degreeGood : J → Omega → Prop)
    (value : J → Omega → K)
    (pDiv pDegree pCollision tS tX tCollision : ℝ)
    (htS : 0 < tS) (htX : 0 < tX) (htCollision : 0 < tCollision)
    (hdiverse : ∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j →
      uniformProbability (fun omega ↦ ¬ diverse i j omega) ≤ pDiv)
    (hdegree : ∀ i ∈ S₀ ∪ X₀,
      uniformProbability (fun omega ↦ ¬ degreeGood i omega) ≤ pDegree)
    (hdiverseSymm : ∀ i j omega, diverse i j omega ↔ diverse j i omega)
    (hcollision : ∀ i ∈ S₀, ∀ j ∈ S₀, i ≠ j →
      uniformProbability (fun omega ↦ value i omega = value j omega) ≤
        pCollision) :
    1 - (X₀.card.choose 2 * pDiv +
          S₀.card * pDegree / tS +
          X₀.card * pDegree / tX +
          S₀.card.choose 2 * pCollision / tCollision) ≤
      uniformProbability (fun omega ↦
        (∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j → diverse i j omega) ∧
        ((S₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tS ∧
        ((X₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tX ∧
        ((CollisionCounting.collisionEdges S₀ value omega).card : ℝ) <
          tCollision) := by
  classical
  let pairBad : (J × J) → Omega → Prop := fun ij omega ↦
    ¬ diverse ij.1 ij.2 omega
  have hpair : ∀ ij ∈ CollisionCounting.possibleEdges X₀,
      uniformProbability (pairBad ij) ≤ pDiv := by
    rintro ⟨i, j⟩ hij
    simp only [CollisionCounting.possibleEdges, Finset.mem_filter,
      Finset.mem_offDiag] at hij
    exact hdiverse i hij.1.1 j hij.1.2.1 hij.1.2.2
  have hdivFail :
      uniformProbability (fun omega ↦
        (1 : ℝ) ≤ CollisionCounting.eventCount
          (CollisionCounting.possibleEdges X₀) pairBad omega) ≤
        X₀.card.choose 2 * pDiv := by
    have h := CollisionCounting.uniformProbability_eventCount_ge_le
      (CollisionCounting.possibleEdges X₀) pairBad pDiv 1 (by norm_num) hpair
    simpa using h
  have hdegS :
      uniformProbability (fun omega ↦ tS ≤
        CollisionCounting.eventCount S₀
          (fun i omega ↦ ¬ degreeGood i omega) omega) ≤
        S₀.card * pDegree / tS := by
    apply CollisionCounting.uniformProbability_eventCount_ge_le
      S₀ (fun i omega ↦ ¬ degreeGood i omega) pDegree tS htS
    intro i hi
    exact hdegree i (Finset.mem_union_left X₀ hi)
  have hdegX :
      uniformProbability (fun omega ↦ tX ≤
        CollisionCounting.eventCount X₀
          (fun i omega ↦ ¬ degreeGood i omega) omega) ≤
        X₀.card * pDegree / tX := by
    apply CollisionCounting.uniformProbability_eventCount_ge_le
      X₀ (fun i omega ↦ ¬ degreeGood i omega) pDegree tX htX
    intro i hi
    exact hdegree i (Finset.mem_union_right S₀ hi)
  have hcoll :
      uniformProbability (fun omega ↦ tCollision ≤
        (CollisionCounting.collisionEdges S₀ value omega).card) ≤
        S₀.card.choose 2 * pCollision / tCollision :=
    CollisionCounting.uniformProbability_card_collisionEdges_ge_le
      S₀ value pCollision tCollision htCollision hcollision
  have hraw := one_sub_four_failure_bounds_le_probability_good
    (Omega := Omega)
    (fun omega ↦ (1 : ℝ) ≤ CollisionCounting.eventCount
      (CollisionCounting.possibleEdges X₀) pairBad omega)
    (fun omega ↦ tS ≤ CollisionCounting.eventCount S₀
      (fun i omega ↦ ¬ degreeGood i omega) omega)
    (fun omega ↦ tX ≤ CollisionCounting.eventCount X₀
      (fun i omega ↦ ¬ degreeGood i omega) omega)
    (fun omega ↦ tCollision ≤
      (CollisionCounting.collisionEdges S₀ value omega).card)
    (X₀.card.choose 2 * pDiv)
    (S₀.card * pDegree / tS)
    (X₀.card * pDegree / tX)
    (S₀.card.choose 2 * pCollision / tCollision)
    hdivFail hdegS hdegX hcoll
  refine hraw.trans (uniformProbability_mono ?_)
  intro omega hgood
  rcases hgood with ⟨h₀, h₁, h₂, h₃⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi j hj hij
    by_contra hbad
    apply h₀
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hmem : (i, j) ∈ CollisionCounting.possibleEdges X₀ := by
        simp [CollisionCounting.possibleEdges, hi, hj, hij, hijlt]
      have hone' : 1 ≤ ((CollisionCounting.possibleEdges X₀).filter
          fun ij ↦ ¬ diverse ij.1 ij.2 omega).card := by
        rw [Finset.one_le_card]
        exact ⟨(i, j), Finset.mem_filter.mpr ⟨hmem, hbad⟩⟩
      exact_mod_cast (show 1 ≤ CollisionCounting.eventCount
        (CollisionCounting.possibleEdges X₀) pairBad omega by
          simpa only [CollisionCounting.eventCount, pairBad] using hone')
    · have hsymm : ¬ diverse j i omega :=
        fun hji ↦ hbad ((hdiverseSymm i j omega).mpr hji)
      have hmem : (j, i) ∈ CollisionCounting.possibleEdges X₀ := by
        simp [CollisionCounting.possibleEdges, hi, hj, hij.symm, hjilt]
      have hone' : 1 ≤ ((CollisionCounting.possibleEdges X₀).filter
          fun ij ↦ ¬ diverse ij.1 ij.2 omega).card := by
        rw [Finset.one_le_card]
        exact ⟨(j, i), Finset.mem_filter.mpr ⟨hmem, hsymm⟩⟩
      exact_mod_cast (show 1 ≤ CollisionCounting.eventCount
        (CollisionCounting.possibleEdges X₀) pairBad omega by
          simpa only [CollisionCounting.eventCount, pairBad] using hone')
  · simpa [CollisionCounting.eventCount] using (not_le.mp h₁)
  · simpa [CollisionCounting.eventCount] using (not_le.mp h₂)
  · exact not_le.mp h₃

/-! ## Anti-concentration from incidence-vector diversity -/

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- The integer coefficient sum selected by a Boolean slice. -/
noncomputable def incidenceSum (s : ℕ) (a : I → ℤ)
    (omega : BoolSlice I s) : ℝ :=
  AntiConcentration.sliceLinear s (fun i ↦ (a i : ℝ)) omega

/-- Pairwise `ℓ¹` diversity plus equal population totals gives the exact
point-mass estimate needed for collision edges in Claim 4.8.

The coefficients `a i - a j` have absolute value at most `2B`, total sum
zero, and `ℓ¹` mass at least `theta * |I|`.  The small-total-sum form of
the checked Fourier--Esseen theorem therefore applies with centre zero. -/
theorem slice_collision_probability_le_of_l1_equal_sum
    {J : Type v} (a : J → I → ℤ) (i j : J)
    (B s : ℕ) (c theta : ℝ) [Nonempty (BoolSlice I s)]
    (hc₀ : 0 < c) (hc₁ : c ≤ 1 / 2) (htheta : 0 < theta)
    (hB : 1 ≤ B) (hI : 0 < Fintype.card I)
    (hbounded : ∀ q x, |a q x| ≤ (B : ℤ))
    (hequal : ∑ x, a i x = ∑ x, a j x)
    (hl₁ : theta * Fintype.card I ≤
      ∑ x, |((a i x - a j x : ℤ) : ℝ)|)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s) :
    uniformProbability (fun omega : BoolSlice I s ↦
        incidenceSum s (a i) omega = incidenceSum s (a j) omega) ≤
      AntiConcentration.variancePointMassConstant c (theta ^ 2 / 4) (2 * B) /
        Real.sqrt (Fintype.card I : ℝ) := by
  classical
  let d : I → ℤ := fun x ↦ a i x - a j x
  have htwoB : 1 ≤ 2 * B := by omega
  have hdbounded : ∀ x, |d x| ≤ ((2 * B : ℕ) : ℤ) := by
    intro x
    dsimp only [d]
    calc
      |a i x - a j x| ≤ |a i x| + |a j x| := abs_sub _ _
      _ ≤ (B : ℤ) + B := add_le_add (hbounded i x) (hbounded j x)
      _ = ((2 * B : ℕ) : ℤ) := by push_cast; ring
  have hmean : (Fintype.card I : ℝ) * 0 = ∑ x, (d x : ℝ) := by
    simp only [mul_zero]
    push_cast [d]
    rw [Finset.sum_sub_distrib]
    exact_mod_cast (sub_eq_zero.mpr hequal).symm
  have hsmall : |∑ x, (d x : ℝ)| < theta / 2 * Fintype.card I := by
    rw [← hmean]
    simp only [mul_zero, abs_zero]
    positivity
  have hanti := AntiConcentration.slice_point_probability_le_of_integer_l1_small_sum
    d 0 c theta (2 * B) s hc₀ hc₁ htheta htwoB hI hdbounded hmean
      (by simpa [d] using hl₁) hsmall hsel hunsel 0
  have hevent :
      (fun omega : BoolSlice I s ↦
          incidenceSum s (a i) omega = incidenceSum s (a j) omega) =
        (fun omega ↦ AntiConcentration.sliceLinear s
          (fun x ↦ (d x : ℝ)) omega = 0) := by
    funext omega
    apply propext
    have hlinear :
        AntiConcentration.sliceLinear s (fun x ↦ (d x : ℝ)) omega =
          incidenceSum s (a i) omega - incidenceSum s (a j) omega := by
      simp only [incidenceSum, AntiConcentration.sliceLinear, d]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [Int.cast_sub]
      ring
    rw [hlinear]
    exact sub_eq_zero.symm
  rw [hevent]
  change finProbability (BoolSlice I s)
    (fun omega ↦ AntiConcentration.sliceLinear s
      (fun x ↦ (d x : ℝ)) omega = 0) ≤ _
  exact hanti

/-- **Balanced partial exposure from integer incidence vectors.**

This is the consumable Claim 4.8 interface.  The sample `omega` is a
uniform `s`-subset of the finite population `I` (in the application,
`s = 2 n_D` and `I` is the subtype corresponding to `U₀`).  Bounded
integral incidence vectors with equal total sums and pairwise linear `ℓ¹`
diversity supply the collision estimate internally.  The two remaining
inputs are exactly the hypergeometric tail bounds for restricted diversity
and the degree window, obtainable from
`productLinear_two_sided_probability` and the exact centre above. -/
theorem one_sub_incidence_budget_le_partialExposure_probability
    {J : Type v} [LinearOrder J]
    (S₀ X₀ : Finset J) (hdisjoint : Disjoint S₀ X₀)
    (a : J → I → ℤ) (B s : ℕ) (c theta : ℝ)
    [Nonempty (BoolSlice I s)]
    (hc₀ : 0 < c) (hc₁ : c ≤ 1 / 2) (htheta : 0 < theta)
    (hB : 1 ≤ B) (hI : 0 < Fintype.card I)
    (hbounded : ∀ q x, |a q x| ≤ (B : ℤ))
    (hequal : ∀ i ∈ S₀, ∀ j ∈ S₀, i ≠ j →
      ∑ x, a i x = ∑ x, a j x)
    (hl₁ : ∀ i ∈ S₀, ∀ j ∈ S₀, i ≠ j →
      theta * Fintype.card I ≤
        ∑ x, |((a i x - a j x : ℤ) : ℝ)|)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (diverse : J → J → BoolSlice I s → Prop)
    (degreeGood : J → BoolSlice I s → Prop)
    (pDiv pDegree tS tX tCollision : ℝ)
    (htS : 0 < tS) (htX : 0 < tX) (htCollision : 0 < tCollision)
    (hdiverse : ∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j →
      uniformProbability (fun omega ↦ ¬ diverse i j omega) ≤ pDiv)
    (hdegree : ∀ i ∈ S₀ ∪ X₀,
      uniformProbability (fun omega ↦ ¬ degreeGood i omega) ≤ pDegree)
    (hdiverseSymm : ∀ i j omega, diverse i j omega ↔ diverse j i omega) :
    let pCollision :=
      AntiConcentration.variancePointMassConstant c (theta ^ 2 / 4) (2 * B) /
        Real.sqrt (Fintype.card I : ℝ)
    1 - (X₀.card.choose 2 * pDiv +
          S₀.card * pDegree / tS +
          X₀.card * pDegree / tX +
          S₀.card.choose 2 * pCollision / tCollision) ≤
      uniformProbability (fun omega ↦
        (∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j → diverse i j omega) ∧
        ((S₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tS ∧
        ((X₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tX ∧
        ((CollisionCounting.collisionEdges S₀
          (fun i omega ↦ incidenceSum s (a i) omega) omega).card : ℝ) <
            tCollision) := by
  classical
  dsimp only
  apply one_sub_budget_le_partialExposure_probability
    S₀ X₀ hdisjoint diverse degreeGood
      (fun i omega ↦ incidenceSum s (a i) omega)
      pDiv pDegree
      (AntiConcentration.variancePointMassConstant c (theta ^ 2 / 4) (2 * B) /
        Real.sqrt (Fintype.card I : ℝ))
      tS tX tCollision htS htX htCollision hdiverse hdegree hdiverseSymm
  intro i hi j hj hij
  exact slice_collision_probability_le_of_l1_equal_sum
    a i j B s c theta hc₀ hc₁ htheta hB hI hbounded
      (hequal i hi j hj hij) (hl₁ i hi j hj hij) hsel hunsel

/-- **The threshold-parameterized `2 n_D` partial-exposure theorem.**

The three thresholds are independent.  In the graph application one may take
`tS = tX = s₀ / 2` and `tCollision = L_H * √nD`; the exact cost of those
choices is visible in the four-term budget. -/
theorem three_fourths_le_incidence_partialExposure_probability_two_nD_of_thresholds
    {J : Type v} [LinearOrder J]
    (S₀ X₀ : Finset J) (hdisjoint : Disjoint S₀ X₀)
    (a : J → I → ℤ) (B nD : ℕ) (c theta : ℝ)
    [Nonempty (BoolSlice I (2 * nD))]
    (hc₀ : 0 < c) (hc₁ : c ≤ 1 / 2) (htheta : 0 < theta)
    (hB : 1 ≤ B) (hI : 0 < Fintype.card I)
    (hbounded : ∀ q x, |a q x| ≤ (B : ℤ))
    (hequal : ∀ i ∈ S₀, ∀ j ∈ S₀, i ≠ j →
      ∑ x, a i x = ∑ x, a j x)
    (hl₁ : ∀ i ∈ S₀, ∀ j ∈ S₀, i ≠ j →
      theta * Fintype.card I ≤
        ∑ x, |((a i x - a j x : ℤ) : ℝ)|)
    (hsel : c * Fintype.card I ≤ ((2 * nD : ℕ) : ℝ))
    (hunsel : c * Fintype.card I ≤
      (Fintype.card I : ℝ) - ((2 * nD : ℕ) : ℝ))
    (diverse : J → J → BoolSlice I (2 * nD) → Prop)
    (degreeGood : J → BoolSlice I (2 * nD) → Prop)
    (pDiv pDegree tS tX tCollision : ℝ)
    (htS : 0 < tS) (htX : 0 < tX) (htCollision : 0 < tCollision)
    (hdiverse : ∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j →
      uniformProbability (fun omega ↦ ¬ diverse i j omega) ≤ pDiv)
    (hdegree : ∀ i ∈ S₀ ∪ X₀,
      uniformProbability (fun omega ↦ ¬ degreeGood i omega) ≤ pDegree)
    (hdiverseSymm : ∀ i j omega, diverse i j omega ↔ diverse j i omega)
    (hbudget :
      let pCollision :=
        AntiConcentration.variancePointMassConstant c (theta ^ 2 / 4) (2 * B) /
          Real.sqrt (Fintype.card I : ℝ)
      X₀.card.choose 2 * pDiv +
          S₀.card * pDegree / tS +
          X₀.card * pDegree / tX +
          S₀.card.choose 2 * pCollision / tCollision ≤ 1 / 4) :
    3 / 4 ≤ uniformProbability (fun omega : BoolSlice I (2 * nD) ↦
      (∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j → diverse i j omega) ∧
      ((S₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tS ∧
      ((X₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tX ∧
      ((CollisionCounting.collisionEdges S₀
        (fun i omega ↦ incidenceSum (2 * nD) (a i) omega) omega).card : ℝ) <
          tCollision) := by
  let pCollision :=
    AntiConcentration.variancePointMassConstant c (theta ^ 2 / 4) (2 * B) /
      Real.sqrt (Fintype.card I : ℝ)
  let budget :=
    X₀.card.choose 2 * pDiv +
      S₀.card * pDegree / tS +
      X₀.card * pDegree / tX +
      S₀.card.choose 2 * pCollision / tCollision
  have hbudget' : budget ≤ 1 / 4 := by
    simpa only [budget, pCollision] using hbudget
  have hprob := one_sub_incidence_budget_le_partialExposure_probability
    (I := I) S₀ X₀ hdisjoint a B (2 * nD) c theta hc₀ hc₁ htheta
      hB hI hbounded hequal hl₁ hsel hunsel diverse degreeGood
      pDiv pDegree tS tX tCollision htS htX htCollision
      hdiverse hdegree hdiverseSymm
  have hprob' : 1 - budget ≤
      uniformProbability (fun omega : BoolSlice I (2 * nD) ↦
        (∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j → diverse i j omega) ∧
        ((S₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tS ∧
        ((X₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tX ∧
        ((CollisionCounting.collisionEdges S₀
          (fun i omega ↦ incidenceSum (2 * nD) (a i) omega) omega).card : ℝ) <
            tCollision) := by
    simpa only [budget, pCollision] using hprob
  linarith

/-- **The `2 n_D` / square-root-threshold form of partial exposure.**

An element of `BoolSlice I (2 * nD)` is literally a selected set `D₁` of
cardinality `2 nD`.  Under the explicit four-term failure budget, with all
three exceptional-count thresholds fixed to `√nD`, at least three quarters
of those sets simultaneously preserve every required `X₀`-pair diversity,
leave fewer than `√nD` degree-bad cells in each matching family, and create
fewer than `√nD` collision edges in `S₀`. -/
theorem three_fourths_le_incidence_partialExposure_probability_two_nD
    {J : Type v} [LinearOrder J]
    (S₀ X₀ : Finset J) (hdisjoint : Disjoint S₀ X₀)
    (a : J → I → ℤ) (B nD : ℕ) (c theta : ℝ)
    [Nonempty (BoolSlice I (2 * nD))]
    (hnD : 0 < nD)
    (hc₀ : 0 < c) (hc₁ : c ≤ 1 / 2) (htheta : 0 < theta)
    (hB : 1 ≤ B) (hI : 0 < Fintype.card I)
    (hbounded : ∀ q x, |a q x| ≤ (B : ℤ))
    (hequal : ∀ i ∈ S₀, ∀ j ∈ S₀, i ≠ j →
      ∑ x, a i x = ∑ x, a j x)
    (hl₁ : ∀ i ∈ S₀, ∀ j ∈ S₀, i ≠ j →
      theta * Fintype.card I ≤
        ∑ x, |((a i x - a j x : ℤ) : ℝ)|)
    (hsel : c * Fintype.card I ≤ ((2 * nD : ℕ) : ℝ))
    (hunsel : c * Fintype.card I ≤
      (Fintype.card I : ℝ) - ((2 * nD : ℕ) : ℝ))
    (diverse : J → J → BoolSlice I (2 * nD) → Prop)
    (degreeGood : J → BoolSlice I (2 * nD) → Prop)
    (pDiv pDegree : ℝ)
    (hdiverse : ∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j →
      uniformProbability (fun omega ↦ ¬ diverse i j omega) ≤ pDiv)
    (hdegree : ∀ i ∈ S₀ ∪ X₀,
      uniformProbability (fun omega ↦ ¬ degreeGood i omega) ≤ pDegree)
    (hdiverseSymm : ∀ i j omega, diverse i j omega ↔ diverse j i omega)
    (hbudget :
      let pCollision :=
        AntiConcentration.variancePointMassConstant c (theta ^ 2 / 4) (2 * B) /
          Real.sqrt (Fintype.card I : ℝ)
      X₀.card.choose 2 * pDiv +
          S₀.card * pDegree / Real.sqrt (nD : ℝ) +
          X₀.card * pDegree / Real.sqrt (nD : ℝ) +
          S₀.card.choose 2 * pCollision / Real.sqrt (nD : ℝ) ≤ 1 / 4) :
    3 / 4 ≤ uniformProbability (fun omega : BoolSlice I (2 * nD) ↦
      (∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j → diverse i j omega) ∧
      ((S₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) <
        Real.sqrt (nD : ℝ) ∧
      ((X₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) <
        Real.sqrt (nD : ℝ) ∧
      ((CollisionCounting.collisionEdges S₀
        (fun i omega ↦ incidenceSum (2 * nD) (a i) omega) omega).card : ℝ) <
          Real.sqrt (nD : ℝ)) := by
  let tau : ℝ := Real.sqrt (nD : ℝ)
  have htau : 0 < tau := by
    dsimp only [tau]
    apply Real.sqrt_pos.2
    exact_mod_cast hnD
  let pCollision :=
    AntiConcentration.variancePointMassConstant c (theta ^ 2 / 4) (2 * B) /
      Real.sqrt (Fintype.card I : ℝ)
  let budget :=
    X₀.card.choose 2 * pDiv +
      S₀.card * pDegree / tau +
      X₀.card * pDegree / tau +
      S₀.card.choose 2 * pCollision / tau
  have hbudget' : budget ≤ 1 / 4 := by
    simpa only [budget, pCollision, tau] using hbudget
  have hprob := one_sub_incidence_budget_le_partialExposure_probability
    (I := I) S₀ X₀ hdisjoint a B (2 * nD) c theta hc₀ hc₁ htheta
      hB hI hbounded hequal hl₁ hsel hunsel diverse degreeGood
      pDiv pDegree tau tau tau htau htau htau hdiverse hdegree hdiverseSymm
  have hprob' : 1 - budget ≤
      uniformProbability (fun omega : BoolSlice I (2 * nD) ↦
        (∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j → diverse i j omega) ∧
        ((S₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tau ∧
        ((X₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tau ∧
        ((CollisionCounting.collisionEdges S₀
          (fun i omega ↦ incidenceSum (2 * nD) (a i) omega) omega).card : ℝ) <
            tau) := by
    simpa only [budget, pCollision] using hprob
  change 3 / 4 ≤ uniformProbability (fun omega : BoolSlice I (2 * nD) ↦
    (∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j → diverse i j omega) ∧
    ((S₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tau ∧
    ((X₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tau ∧
    ((CollisionCounting.collisionEdges S₀
      (fun i omega ↦ incidenceSum (2 * nD) (a i) omega) omega).card : ℝ) < tau)
  linarith

end

end AugmentationPartial
end Erdos636
