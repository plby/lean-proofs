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
import ErdosProblems.Erdos722.NibbleMean
import Mathlib

/-!
# Variance from jump and first-moment bounds

Freedman's gain over a bounded-differences estimate enters through the
elementary inequality `X² ≤ J |X|` when `|X| ≤ J`.  This module records
that finite weighted-sum argument once, and packages it for every indexed
barrier observable.
-/

namespace Erdos722.NibbleVariance

open Finset
open Erdos722.NibbleProcess
open Erdos722.NibbleBarrier
open Erdos722.StoppedFreedman
open Erdos722.AdaptiveChernoff

noncomputable section

variable {n r : ℕ}

lemma sum_mul_sq_le_mul_sum_abs
    {A : Type*} [Fintype A]
    (p x : A → ℝ) (J : ℝ)
    (hp : ∀ a, 0 ≤ p a) (hJ : 0 ≤ J)
    (hx : ∀ a, p a = 0 ∨ |x a| ≤ J) :
    (∑ a, p a * (x a) ^ 2) ≤
      J * ∑ a, p a * |x a| := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  rcases hx a with hzero | hbound
  · simp [hzero]
  have habs0 : 0 ≤ |x a| := abs_nonneg _
  have hsquare : (x a) ^ 2 = |x a| ^ 2 := by rw [sq_abs]
  rw [hsquare]
  calc
    p a * |x a| ^ 2 ≤ p a * (J * |x a|) := by
      apply mul_le_mul_of_nonneg_left _ (hp a)
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right hbound habs0
    _ = J * (p a * |x a|) := by ring

/-- A simultaneous jump bound and conditional absolute-first-moment bound
imply the variance hypothesis consumed by `NibbleBarrier`. -/
theorem barrier_variance_of_absMoment
    {host H : Finset (Finset (Fin n))}
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ)
    (jump absBudget : BarrierIndex host r → ℕ → ℝ)
    {depth : ℕ}
    (hjumpNonneg : ∀ z i, 0 ≤ jump z i)
    (hjump : ∀ z history Q,
      history.length < depth →
      FollowsAvailable H r [] history →
      AllGood (fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap c h < 0) history →
      Q ∈ availableCliques H r history →
      |observableIncrement
        (barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap) z history Q| ≤
        jump z history.length)
    (habs : ∀ z history,
      history.length < depth →
      FollowsAvailable H r [] history →
      AllGood (fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap c h < 0) history →
      (∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q *
          |observableIncrement
            (barrierObservable host H r degreeUpper degreeLower
              cliqueUpper cliqueLower faceWeight faceCap) z history Q|) ≤
        absBudget z history.length) :
    ∀ z history,
      history.length < depth →
      FollowsAvailable H r [] history →
      AllGood (fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap c h < 0) history →
      (∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q *
          (observableIncrement
            (barrierObservable host H r degreeUpper degreeLower
              cliqueUpper cliqueLower faceWeight faceCap) z history Q) ^ 2) ≤
        jump z history.length * absBudget z history.length := by
  intro z history hlen hfollow hall
  calc
    (∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q *
          (observableIncrement
            (barrierObservable host H r degreeUpper degreeLower
              cliqueUpper cliqueLower faceWeight faceCap) z history Q) ^ 2) ≤
      jump z history.length *
        ∑ Q : Finset (Fin n),
          uniformStep (availableCliques H r) history Q *
            |observableIncrement
              (barrierObservable host H r degreeUpper degreeLower
                cliqueUpper cliqueLower faceWeight faceCap) z history Q| := by
        apply sum_mul_sq_le_mul_sum_abs
          (A := Finset (Fin n))
          (p := fun Q ↦ uniformStep (availableCliques H r) history Q)
          (x := fun Q ↦ observableIncrement
            (barrierObservable host H r degreeUpper degreeLower
              cliqueUpper cliqueLower faceWeight faceCap) z history Q)
          (J := jump z history.length)
        · intro Q
          exact uniformStep_nonneg (availableCliques H r) history Q
        · exact hjumpNonneg z history.length
        · intro Q
          by_cases hQ : Q ∈ availableCliques H r history
          · exact Or.inr (hjump z history Q hlen hfollow hall hQ)
          · exact Or.inl (by simp [uniformStep, hQ])
    _ ≤ jump z history.length * absBudget z history.length := by
      exact mul_le_mul_of_nonneg_left
        (habs z history hlen hfollow hall)
        (hjumpNonneg z history.length)

end

end Erdos722.NibbleVariance
