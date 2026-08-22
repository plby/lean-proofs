/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.ProfileWeightUpper

/-!
# Multi-step critical-offspring bridges

The critical negative-binomial transition kernel has total mass one.  This
file records the corresponding finite-step bridge kernel.  In particular,
after any finite block of profile coordinates has been erased, the total
mass leading to one prescribed endpoint is at most one.  This is the scalar
Markov input for the buffered asymmetric pair splice.
-/

open scoped BigOperators

namespace Erdos1165.ProfileTransitionBridge

open AppendixFirstMoment

noncomputable section

/-- The `steps`-step transition mass of the critical offspring chain. -/
def iteratedTransition : ℕ → ℕ → ℕ → ℝ
  | 0, a, b => if a = b then 1 else 0
  | steps + 1, a, b =>
      ∑' c : ℕ, transitionMass a c * iteratedTransition steps c b

/-- Every finite-step bridge is a nonnegative subprobability.  The proof
uses only row normalization of `transitionMass`; no local-limit estimate is
involved. -/
theorem iteratedTransition_nonneg_le_one : ∀ steps a b,
    0 ≤ iteratedTransition steps a b ∧ iteratedTransition steps a b ≤ 1 := by
  intro steps
  induction steps with
  | zero =>
      intro a b
      simp only [iteratedTransition]
      split <;> norm_num
  | succ steps ih =>
      intro a b
      have hterm0 : ∀ c : ℕ,
          0 ≤ transitionMass a c * iteratedTransition steps c b :=
        fun c ↦ mul_nonneg (transitionMass_nonneg _ _) (ih c b).1
      have htermLe : ∀ c : ℕ,
          transitionMass a c * iteratedTransition steps c b ≤
            transitionMass a c := by
        intro c
        nlinarith [transitionMass_nonneg a c, (ih c b).1, (ih c b).2]
      have hsum : Summable (fun c : ℕ ↦
          transitionMass a c * iteratedTransition steps c b) :=
        Summable.of_nonneg_of_le hterm0 htermLe
          (summable_transitionMass a)
      constructor
      · exact tsum_nonneg hterm0
      · rw [iteratedTransition]
        calc
          (∑' c : ℕ, transitionMass a c *
              iteratedTransition steps c b) ≤
              ∑' c : ℕ, transitionMass a c :=
            hsum.tsum_le_tsum htermLe (summable_transitionMass a)
          _ = 1 := tsum_transitionMass a

theorem iteratedTransition_nonneg (steps a b : ℕ) :
    0 ≤ iteratedTransition steps a b :=
  (iteratedTransition_nonneg_le_one steps a b).1

theorem iteratedTransition_le_one (steps a b : ℕ) :
    iteratedTransition steps a b ≤ 1 :=
  (iteratedTransition_nonneg_le_one steps a b).2

/-- The multi-step transition kernel is normalized in its terminal state.
This stronger row statement is what permits the three erased buffer
coordinates to be summed without paying their cardinality. -/
theorem summable_iteratedTransition_and_tsum_eq_one : ∀ steps a,
    Summable (iteratedTransition steps a) ∧
      ∑' b : ℕ, iteratedTransition steps a b = 1 := by
  intro steps
  induction steps with
  | zero =>
      intro a
      constructor
      · simpa only [iteratedTransition, eq_comm] using
          (hasSum_ite_eq a (1 : ℝ)).summable
      · simpa only [iteratedTransition] using
          (tsum_ite_eq' a (fun _ : ℕ ↦ (1 : ℝ)))
  | succ steps ih =>
      intro a
      let f : ℕ × ℕ → ℝ := fun q ↦
        transitionMass a q.1 * iteratedTransition steps q.1 q.2
      have hf0 : 0 ≤ f := by
        intro q
        exact mul_nonneg (transitionMass_nonneg _ _)
          (iteratedTransition_nonneg _ _ _)
      have hrow (c : ℕ) : Summable (fun b ↦ f (c, b)) := by
        exact Summable.mul_left (transitionMass a c) (ih c).1
      have hrowSum (c : ℕ) : (∑' b : ℕ, f (c, b)) =
          transitionMass a c := by
        dsimp only [f]
        rw [(ih c).1.tsum_mul_left, (ih c).2, mul_one]
      have houter : Summable (fun c : ℕ ↦ ∑' b : ℕ, f (c, b)) := by
        simpa only [hrowSum] using summable_transitionMass a
      have hf : Summable f :=
        (summable_prod_of_nonneg hf0).2 ⟨hrow, houter⟩
      have hswap : Summable (f ∘ Equiv.prodComm ℕ ℕ) :=
        ((Equiv.prodComm ℕ ℕ).summable_iff).2 hf
      have hterminal : Summable (fun b : ℕ ↦ ∑' c : ℕ, f (c, b)) := by
        simpa [Equiv.prodComm] using hswap.prod
      constructor
      · simpa only [iteratedTransition] using hterminal
      · rw [show (∑' b : ℕ, iteratedTransition (steps + 1) a b) =
            ∑' b : ℕ, ∑' c : ℕ, f (c, b) by rfl]
        rw [hf.tsum_comm]
        simp_rw [hrowSum]
        exact tsum_transitionMass a

theorem summable_iteratedTransition (steps a : ℕ) :
    Summable (iteratedTransition steps a) :=
  (summable_iteratedTransition_and_tsum_eq_one steps a).1

theorem tsum_iteratedTransition (steps a : ℕ) :
    (∑' b : ℕ, iteratedTransition steps a b) = 1 :=
  (summable_iteratedTransition_and_tsum_eq_one steps a).2

/-- An arbitrary finite set of terminal states, followed by uniformly
bounded nonnegative tail weights, still has total bridge--tail mass at most
that uniform bound.  This is the exact form used when the few profile
coordinates meeting the opposite centre's separation annulus are erased. -/
theorem sum_iteratedTransition_mul_le
    (steps a : ℕ) (states : Finset ℕ) (tail : ℕ → ℝ) {bound : ℝ}
    (hbound0 : 0 ≤ bound)
    (htail : ∀ b ∈ states, tail b ≤ bound) :
    ∑ b ∈ states, iteratedTransition steps a b * tail b ≤ bound := by
  have hbridgeSum :
      (∑ b ∈ states, iteratedTransition steps a b) ≤ 1 := by
    calc
      (∑ b ∈ states, iteratedTransition steps a b) ≤
          ∑' b : ℕ, iteratedTransition steps a b := by
        exact (summable_iteratedTransition steps a).sum_le_tsum states
          (fun b _hb ↦ iteratedTransition_nonneg steps a b)
      _ = 1 := tsum_iteratedTransition steps a
  calc
    (∑ b ∈ states, iteratedTransition steps a b * tail b) ≤
        ∑ b ∈ states, iteratedTransition steps a b * bound := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (htail b hb)
        (iteratedTransition_nonneg steps a b)
    _ = (∑ b ∈ states, iteratedTransition steps a b) * bound := by
      rw [Finset.sum_mul]
    _ ≤ 1 * bound :=
      mul_le_mul_of_nonneg_right hbridgeSum hbound0
    _ = bound := one_mul bound

/-- The preceding estimate with the actual constrained state window at a
specified scale. -/
theorem sum_allowed_iteratedTransition_mul_le
    (steps a scale : ℕ) (delta : ℝ) (tail : ℕ → ℝ) {bound : ℝ}
    (hbound0 : 0 ≤ bound)
    (htail : ∀ b ∈ allowedValues delta scale, tail b ≤ bound) :
    ∑ b ∈ allowedValues delta scale,
        iteratedTransition steps a b * tail b ≤ bound :=
  sum_iteratedTransition_mul_le steps a (allowedValues delta scale) tail
    hbound0 htail

end

end Erdos1165.ProfileTransitionBridge
