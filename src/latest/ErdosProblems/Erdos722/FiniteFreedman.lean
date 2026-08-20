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
import ErdosProblems.Erdos722.AdaptiveChernoff
import Mathlib

/-!
# A finite variance-sensitive transition-tree inequality

The random-greedy nibble is naturally a finite probability tree.  This file
proves the exponential supermartingale estimate directly on that tree.  The
only analytic input is the elementary inequality
`exp z ≤ 1 + z + z²` for `|z| ≤ 1`.

The resulting exponent is a slightly weaker constant than the usual
Freedman inequality, but it has the same variance-sensitive form and is more
than sufficient for the polynomial error envelopes used below.
-/

namespace Erdos722.FiniteFreedman

open Finset Real
open Erdos722.AdaptiveChernoff

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Probability that the sum of the next `depth` real increments is at least
`threshold`. -/
def realTailMass (step : List α → α → ℝ) (inc : List α → α → ℝ) :
    List α → ℕ → ℝ → ℝ
  | _history, 0, threshold => if threshold ≤ 0 then 1 else 0
  | history, depth + 1, threshold =>
      ∑ a : α, step history a *
        realTailMass step inc (history ++ [a]) depth
          (threshold - inc history a)

/-- Exponential moment of the sum of the next `depth` real increments. -/
def realMGF (step : List α → α → ℝ) (inc : List α → α → ℝ)
    (t : ℝ) : List α → ℕ → ℝ
  | _history, 0 => 1
  | history, depth + 1 =>
      ∑ a : α, step history a * Real.exp (t * inc history a) *
        realMGF step inc t (history ++ [a]) depth

/-- Sum of increments along a concrete continuation. -/
def pathSum (inc : List α → α → ℝ) : List α → List α → ℝ
  | _history, [] => 0
  | history, a :: rest =>
      inc history a + pathSum inc (history ++ [a]) rest

lemma pathSum_append (inc : List α → α → ℝ)
    (history xs ys : List α) :
    pathSum inc history (xs ++ ys) =
      pathSum inc history xs + pathSum inc (history ++ xs) ys := by
  induction xs generalizing history with
  | nil => simp [pathSum]
  | cons a xs ih =>
      simp only [List.cons_append, pathSum]
      rw [ih]
      simp [List.append_assoc]
      ring

/-- Mass of the union of finitely many real-valued upper-tail events. -/
noncomputable def multiRealTailMass {β : Type*} [Fintype β]
    (step : List α → α → ℝ) (inc : β → List α → α → ℝ) :
    List α → ℕ → (β → ℝ) → ℝ
  | _history, 0, threshold =>
      if ∃ b, threshold b ≤ 0 then 1 else 0
  | history, depth + 1, threshold =>
      ∑ a : α, step history a *
        multiRealTailMass step inc (history ++ [a]) depth
          (fun b ↦ threshold b - inc b history a)

/-- The variance budget accumulated over consecutive levels. -/
def varianceBudget (v : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _start, 0 => 0
  | start, depth + 1 => v start + varianceBudget v (start + 1) depth

lemma varianceBudget_const_mul (c : ℝ) (v : ℕ → ℝ)
    (start depth : ℕ) :
    varianceBudget (fun i ↦ c * v i) start depth =
      c * varianceBudget v start depth := by
  induction depth generalizing start with
  | zero => simp [varianceBudget]
  | succ depth ih =>
      simp only [varianceBudget]
      rw [ih]
      ring

lemma varianceBudget_mul_const (c : ℝ) (v : ℕ → ℝ)
    (start depth : ℕ) :
    varianceBudget (fun i ↦ v i * c) start depth =
      varianceBudget v start depth * c := by
  simpa [mul_comm] using varianceBudget_const_mul c v start depth

lemma exp_le_one_add_self_add_sq {z : ℝ} (hz : |z| ≤ 1) :
    Real.exp z ≤ 1 + z + z ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hz
  have hle : Real.exp z - 1 - z ≤ |Real.exp z - 1 - z| := le_abs_self _
  linarith

variable (step : List α → α → ℝ)

section TransitionMass

variable
  (hstep_nonneg : ∀ history a, 0 ≤ step history a)
  (hstep_sum : ∀ history, ∑ a : α, step history a = 1)

include hstep_nonneg hstep_sum

theorem realTailMass_nonneg (inc : List α → α → ℝ) :
    ∀ history depth threshold,
      0 ≤ realTailMass step inc history depth threshold := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      by_cases h : threshold ≤ 0 <;> simp [realTailMass, h]
  | succ depth ih =>
      intro threshold
      simp only [realTailMass]
      apply Finset.sum_nonneg
      intro a _ha
      exact mul_nonneg (hstep_nonneg history a)
        (ih (history ++ [a]) _)

theorem realTailMass_le_one (inc : List α → α → ℝ) :
    ∀ history depth threshold,
      realTailMass step inc history depth threshold ≤ 1 := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      by_cases h : threshold ≤ 0 <;> simp [realTailMass, h]
  | succ depth ih =>
      intro threshold
      simp only [realTailMass]
      calc
        (∑ a : α, step history a *
            realTailMass step inc (history ++ [a]) depth
              (threshold - inc history a)) ≤
            ∑ a : α, step history a * 1 := by
          apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left
            (ih (history ++ [a]) _) (hstep_nonneg history a)
        _ = 1 := by simpa using hstep_sum history

theorem multiRealTailMass_nonneg {β : Type*} [Fintype β]
    (inc : β → List α → α → ℝ) :
    ∀ history depth threshold,
      0 ≤ multiRealTailMass step inc history depth threshold := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      simp only [multiRealTailMass]
      split <;> norm_num
  | succ depth ih =>
      intro threshold
      simp only [multiRealTailMass]
      apply Finset.sum_nonneg
      intro a _ha
      exact mul_nonneg (hstep_nonneg history a)
        (ih (history ++ [a]) _)

theorem multiRealTailMass_le_one {β : Type*} [Fintype β]
    (inc : β → List α → α → ℝ) :
    ∀ history depth threshold,
      multiRealTailMass step inc history depth threshold ≤ 1 := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      simp only [multiRealTailMass]
      split <;> norm_num
  | succ depth ih =>
      intro threshold
      simp only [multiRealTailMass]
      calc
        (∑ a : α, step history a *
            multiRealTailMass step inc (history ++ [a]) depth
              (fun b ↦ threshold b - inc b history a)) ≤
            ∑ a : α, step history a * 1 := by
          apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left
            (ih (history ++ [a]) _) (hstep_nonneg history a)
        _ = 1 := by simpa using hstep_sum history

/-- Finite union bound for real-valued upper-tail mass. -/
theorem multiRealTailMass_le_sum_realTailMass
    {β : Type*} [Fintype β] [DecidableEq β]
    (inc : β → List α → α → ℝ) :
    ∀ history depth threshold,
      multiRealTailMass step inc history depth threshold ≤
        ∑ b : β, realTailMass step (inc b) history depth (threshold b) := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      simp only [multiRealTailMass, realTailMass]
      by_cases hex : ∃ b, threshold b ≤ 0
      · rw [if_pos hex]
        obtain ⟨b, hb⟩ := hex
        have hbmem : b ∈ (Finset.univ : Finset β) := Finset.mem_univ b
        have hsingle := Finset.single_le_sum
          (s := (Finset.univ : Finset β))
          (f := fun c : β ↦ (if threshold c ≤ 0 then 1 else 0 : ℝ))
          (fun c _hc ↦ by split <;> norm_num) hbmem
        simpa [hb] using hsingle
      · rw [if_neg hex]
        exact Finset.sum_nonneg fun b _hb ↦ by
          split <;> norm_num
  | succ depth ih =>
      intro threshold
      simp only [multiRealTailMass, realTailMass]
      calc
        (∑ a : α, step history a *
            multiRealTailMass step inc (history ++ [a]) depth
              (fun b ↦ threshold b - inc b history a)) ≤
            ∑ a : α, step history a *
              (∑ b : β, realTailMass step (inc b) (history ++ [a]) depth
                (threshold b - inc b history a)) := by
          apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left
            (ih (history ++ [a]) _) (hstep_nonneg history a)
        _ = ∑ b : β, ∑ a : α, step history a *
              realTailMass step (inc b) (history ++ [a]) depth
                (threshold b - inc b history a) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
        _ = _ := by rfl

theorem realMGF_nonneg (inc : List α → α → ℝ) (t : ℝ) :
    ∀ history depth, 0 ≤ realMGF step inc t history depth := by
  intro history depth
  induction depth generalizing history with
  | zero => simp [realMGF]
  | succ depth ih =>
      simp only [realMGF]
      apply Finset.sum_nonneg
      intro a _ha
      exact mul_nonneg
        (mul_nonneg (hstep_nonneg history a) (Real.exp_nonneg _))
        (ih (history ++ [a]))

/-- One-step conditional exponential-moment estimate. -/
theorem oneStepRealMGF_le
    (inc : List α → α → ℝ) (v : ℕ → ℝ) {t : ℝ}
    (ht : 0 ≤ t)
    (hbound : ∀ history a, |t * inc history a| ≤ 1)
    (hmean : ∀ history,
      (∑ a : α, step history a * inc history a) ≤ 0)
    (hvar : ∀ history,
      (∑ a : α, step history a * (inc history a) ^ 2) ≤
        v history.length) :
    ∀ history,
      (∑ a : α, step history a * Real.exp (t * inc history a)) ≤
        Real.exp (t ^ 2 * v history.length) := by
  intro history
  have hpoly :
      (∑ a : α, step history a * Real.exp (t * inc history a)) ≤
        1 + t * (∑ a : α, step history a * inc history a) +
          t ^ 2 * (∑ a : α, step history a * (inc history a) ^ 2) := by
    calc
      (∑ a : α, step history a * Real.exp (t * inc history a)) ≤
          ∑ a : α, step history a *
            (1 + t * inc history a + (t * inc history a) ^ 2) := by
        apply Finset.sum_le_sum
        intro a _ha
        exact mul_le_mul_of_nonneg_left
          (exp_le_one_add_self_add_sq (hbound history a))
          (hstep_nonneg history a)
      _ = 1 + t * (∑ a : α, step history a * inc history a) +
          t ^ 2 * (∑ a : α, step history a * (inc history a) ^ 2) := by
        calc
          (∑ a : α, step history a *
              (1 + t * inc history a + (t * inc history a) ^ 2)) =
              ∑ a : α, (step history a +
                t * (step history a * inc history a) +
                t ^ 2 * (step history a * (inc history a) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro a _ha
            ring
          _ = (∑ a : α, step history a) +
              t * (∑ a : α, step history a * inc history a) +
              t ^ 2 * (∑ a : α, step history a * (inc history a) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.mul_sum, Finset.mul_sum]
          _ = _ := by rw [hstep_sum history]
  have hmeanTerm : t * (∑ a : α, step history a * inc history a) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht (hmean history)
  have hvarTerm :
      t ^ 2 * (∑ a : α, step history a * (inc history a) ^ 2) ≤
        t ^ 2 * v history.length :=
    mul_le_mul_of_nonneg_left (hvar history) (sq_nonneg t)
  calc
    (∑ a : α, step history a * Real.exp (t * inc history a)) ≤
        1 + t * (∑ a : α, step history a * inc history a) +
          t ^ 2 * (∑ a : α, step history a * (inc history a) ^ 2) := hpoly
    _ ≤ 1 + t ^ 2 * v history.length := by linarith
    _ ≤ Real.exp (t ^ 2 * v history.length) := by
      simpa [add_comm] using Real.add_one_le_exp
        (t ^ 2 * v history.length)

/-- Iterated variance-sensitive exponential-moment bound. -/
theorem realMGF_le
    (inc : List α → α → ℝ) (v : ℕ → ℝ)
    (hv : ∀ i, 0 ≤ v i) {t : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ history a, |t * inc history a| ≤ 1)
    (hmean : ∀ history,
      (∑ a : α, step history a * inc history a) ≤ 0)
    (hvar : ∀ history,
      (∑ a : α, step history a * (inc history a) ^ 2) ≤
        v history.length) :
    ∀ history depth,
      realMGF step inc t history depth ≤
        Real.exp (t ^ 2 * varianceBudget v history.length depth) := by
  intro history depth
  induction depth generalizing history with
  | zero => simp [realMGF, varianceBudget]
  | succ depth ih =>
      let future := Real.exp
        (t ^ 2 * varianceBudget v (history.length + 1) depth)
      have hfuture : ∀ a : α,
          realMGF step inc t (history ++ [a]) depth ≤ future := by
        intro a
        simpa [future] using ih (history ++ [a])
      simp only [realMGF]
      calc
        (∑ a : α, step history a * Real.exp (t * inc history a) *
            realMGF step inc t (history ++ [a]) depth) ≤
          ∑ a : α, (step history a * Real.exp (t * inc history a)) *
            future := by
          apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left (hfuture a)
            (mul_nonneg (hstep_nonneg history a) (Real.exp_nonneg _))
        _ = (∑ a : α, step history a * Real.exp (t * inc history a)) *
            future := by rw [Finset.sum_mul]
        _ ≤ Real.exp (t ^ 2 * v history.length) * future := by
          exact mul_le_mul_of_nonneg_right
            (oneStepRealMGF_le step hstep_nonneg hstep_sum inc v ht
              hbound hmean hvar history)
            (Real.exp_nonneg _)
        _ = Real.exp
            (t ^ 2 * varianceBudget v history.length (depth + 1)) := by
          rw [← Real.exp_add]
          simp only [future, varianceBudget]
          congr 1
          ring

/-- Exponential Markov inequality for a real-valued transition tree. -/
theorem realTailMass_le_exp_mul_mgf
    (inc : List α → α → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ history depth threshold,
      realTailMass step inc history depth threshold ≤
        Real.exp (-t * threshold) * realMGF step inc t history depth := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      by_cases h : threshold ≤ 0
      · simp only [realTailMass, if_pos h, realMGF, mul_one]
        exact Real.one_le_exp (by nlinarith)
      · simp [realTailMass, h, realMGF, Real.exp_nonneg]
  | succ depth ih =>
      intro threshold
      simp only [realTailMass, realMGF]
      calc
        (∑ a : α, step history a *
            realTailMass step inc (history ++ [a]) depth
              (threshold - inc history a)) ≤
          ∑ a : α, step history a *
            (Real.exp (-t * (threshold - inc history a)) *
              realMGF step inc t (history ++ [a]) depth) := by
          apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left
            (ih (history ++ [a]) _) (hstep_nonneg history a)
        _ = Real.exp (-t * threshold) *
            (∑ a : α, step history a * Real.exp (t * inc history a) *
              realMGF step inc t (history ++ [a]) depth) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _ha
          have hexp : Real.exp (-t * (threshold - inc history a)) =
              Real.exp (-t * threshold) * Real.exp (t * inc history a) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hexp]
          ring

/-- Combined finite variance-sensitive tail bound. -/
theorem realTailMass_le_variance
    (inc : List α → α → ℝ) (v : ℕ → ℝ)
    (hv : ∀ i, 0 ≤ v i) {t : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ history a, |t * inc history a| ≤ 1)
    (hmean : ∀ history,
      (∑ a : α, step history a * inc history a) ≤ 0)
    (hvar : ∀ history,
      (∑ a : α, step history a * (inc history a) ^ 2) ≤
        v history.length) :
    ∀ history depth threshold,
      realTailMass step inc history depth threshold ≤
        Real.exp (-t * threshold) *
          Real.exp (t ^ 2 * varianceBudget v history.length depth) := by
  intro history depth threshold
  exact (realTailMass_le_exp_mul_mgf step hstep_nonneg hstep_sum inc ht
      history depth threshold).trans
    (mul_le_mul_of_nonneg_left
      (realMGF_le step hstep_nonneg hstep_sum inc v hv ht hbound hmean hvar
        history depth) (Real.exp_nonneg _))

/-- A union-tail mass below one yields a positive path below every real
threshold simultaneously. -/
theorem exists_path_of_multiRealTailMass_lt_one
    {β : Type*} [Fintype β] [DecidableEq β]
    (inc : β → List α → α → ℝ) :
    ∀ history depth threshold,
      multiRealTailMass step inc history depth threshold < 1 →
        ∃ path : List α, path.length = depth ∧
          PathPositive step history path ∧
          ∀ b : β, pathSum (inc b) history path < threshold b := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold htail
      refine ⟨[], rfl, trivial, ?_⟩
      intro b
      have hpos : 0 < threshold b := by
        by_contra hnot
        have hex : ∃ c, threshold c ≤ 0 := ⟨b, le_of_not_gt hnot⟩
        simp [multiRealTailMass, hex] at htail
      simpa [pathSum] using hpos
  | succ depth ih =>
      intro threshold htail
      have hchildLe (a : α) :
          multiRealTailMass step inc (history ++ [a]) depth
            (fun b ↦ threshold b - inc b history a) ≤ 1 :=
        multiRealTailMass_le_one step hstep_nonneg hstep_sum inc _ _ _
      have hex : ∃ a : α, 0 < step history a ∧
          multiRealTailMass step inc (history ++ [a]) depth
            (fun b ↦ threshold b - inc b history a) < 1 := by
        by_contra hnot
        push_neg at hnot
        have hterm (a : α) :
            step history a *
                multiRealTailMass step inc (history ++ [a]) depth
                  (fun b ↦ threshold b - inc b history a) =
              step history a := by
          by_cases hzero : step history a = 0
          · simp [hzero]
          · have hpos : 0 < step history a :=
              lt_of_le_of_ne (hstep_nonneg history a) (Ne.symm hzero)
            have hone : 1 ≤ multiRealTailMass step inc
                (history ++ [a]) depth
                (fun b ↦ threshold b - inc b history a) := hnot a hpos
            have heq := le_antisymm (hchildLe a) hone
            rw [heq, mul_one]
        have heq : multiRealTailMass step inc history (depth + 1)
            threshold = 1 := by
          simp only [multiRealTailMass]
          calc
            (∑ a : α, step history a *
                multiRealTailMass step inc (history ++ [a]) depth
                  (fun b ↦ threshold b - inc b history a)) =
                ∑ a : α, step history a := by
              apply Finset.sum_congr rfl
              intro a _ha
              exact hterm a
            _ = 1 := hstep_sum history
        rw [heq] at htail
        exact (lt_irrefl 1 htail).elim
      obtain ⟨a, hstepPos, hchild⟩ := hex
      obtain ⟨rest, hlen, hpositive, hsums⟩ :=
        ih (history ++ [a])
          (fun b ↦ threshold b - inc b history a) hchild
      refine ⟨a :: rest, by simp [hlen], ⟨hstepPos, hpositive⟩, ?_⟩
      intro b
      simp only [pathSum]
      linarith [hsums b]

/-- Simultaneous finite variance-sensitive upper-tail theorem. -/
theorem exists_path_of_sum_variance_lt_one
    {β : Type*} [Fintype β] [DecidableEq β]
    (inc : β → List α → α → ℝ) (v : β → ℕ → ℝ)
    (hv : ∀ b i, 0 ≤ v b i) {t : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ b history a, |t * inc b history a| ≤ 1)
    (hmean : ∀ b history,
      (∑ a : α, step history a * inc b history a) ≤ 0)
    (hvar : ∀ b history,
      (∑ a : α, step history a * (inc b history a) ^ 2) ≤
        v b history.length)
    {history : List α} {depth : ℕ} {threshold : β → ℝ}
    (hsmall : (∑ b : β,
      Real.exp (-t * threshold b) *
        Real.exp (t ^ 2 * varianceBudget (v b) history.length depth)) < 1) :
    ∃ path : List α, path.length = depth ∧
      PathPositive step history path ∧
      ∀ b : β, pathSum (inc b) history path < threshold b := by
  apply exists_path_of_multiRealTailMass_lt_one step hstep_nonneg hstep_sum inc
  apply lt_of_le_of_lt
    (multiRealTailMass_le_sum_realTailMass step hstep_nonneg hstep_sum inc
      history depth threshold)
  apply lt_of_le_of_lt _ hsmall
  apply Finset.sum_le_sum
  intro b _hb
  exact realTailMass_le_variance step hstep_nonneg hstep_sum (inc b) (v b)
    (hv b) ht (hbound b) (hmean b) (hvar b) history depth (threshold b)

end TransitionMass

end

end Erdos722.FiniteFreedman
