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
import Mathlib

/-!
# A finite adaptive Chernoff bound

The random-greedy extension lemma needs concentration for indicators whose
law may depend on all earlier choices.  For the finite applications here it
is cleaner to work directly with a transition tree than to introduce a
measure-theoretic filtration.  This file proves the exponential-moment
argument by induction on the remaining depth.
-/

namespace Erdos722.AdaptiveChernoff

open Finset Real

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `0`/`1` value of the overload indicator at one transition. -/
def hitBit (hit : List α → α → Bool) (history : List α) (a : α) : ℕ :=
  if hit history a then 1 else 0

/-- Probability of at least `threshold` further hits in a finite transition
tree. -/
def tailMass (step : List α → α → ℝ) (hit : List α → α → Bool) :
    List α → ℕ → ℕ → ℝ
  | _history, 0, threshold => if threshold = 0 then 1 else 0
  | history, depth + 1, threshold =>
      ∑ a : α, step history a *
        tailMass step hit (history ++ [a]) depth
          (threshold - hitBit hit history a)

/-- Exponential moment of the number of further hits. -/
def adaptiveMGF (step : List α → α → ℝ) (hit : List α → α → Bool)
    (t : ℝ) : List α → ℕ → ℝ
  | _history, 0 => 1
  | history, depth + 1 =>
      ∑ a : α, step history a *
        Real.exp (t * hitBit hit history a) *
          adaptiveMGF step hit t (history ++ [a]) depth

/-- Sum of the deterministic conditional-probability budgets along the
next `depth` levels. -/
def adaptiveBudget (p : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _start, 0 => 0
  | start, depth + 1 => p start + adaptiveBudget p (start + 1) depth

/-- Positivity of every transition along a concrete continuation. -/
def PathPositive (step : List α → α → ℝ) : List α → List α → Prop
  | _history, [] => True
  | history, a :: rest =>
      0 < step history a ∧ PathPositive step (history ++ [a]) rest

/-- Number of hits along a concrete continuation. -/
def pathHits (hit : List α → α → Bool) : List α → List α → ℕ
  | _history, [] => 0
  | history, a :: rest =>
      hitBit hit history a + pathHits hit (history ++ [a]) rest

/-- Mass of the union of finitely many overload events.  Each threshold is
decremented when its corresponding indicator fires. -/
noncomputable def multiTailMass {β : Type*} [Fintype β]
    (step : List α → α → ℝ) (hit : β → List α → α → Bool) :
    List α → ℕ → (β → ℕ) → ℝ
  | _history, 0, threshold =>
      if ∃ b, threshold b = 0 then 1 else 0
  | history, depth + 1, threshold =>
      ∑ a : α, step history a *
        multiTailMass step hit (history ++ [a]) depth
          (fun b ↦ threshold b - hitBit (hit b) history a)

/-! ## Uniform transition kernels -/

/-- Uniform mass on a nonempty finite set of legal next choices. -/
def uniformStep (legal : List α → Finset α) (history : List α) (a : α) : ℝ :=
  if a ∈ legal history then ((legal history).card : ℝ)⁻¹ else 0

theorem uniformStep_nonneg (legal : List α → Finset α) :
    ∀ history a, 0 ≤ uniformStep legal history a := by
  intro history a
  simp only [uniformStep]
  split <;> positivity

theorem sum_uniformStep (legal : List α → Finset α)
    (hnonempty : ∀ history, (legal history).Nonempty) :
    ∀ history, ∑ a : α, uniformStep legal history a = 1 := by
  intro history
  have hcard : (0 : ℝ) < (legal history).card := by
    exact_mod_cast Finset.card_pos.mpr (hnonempty history)
  simp [uniformStep, hcard.ne']

theorem uniformStep_pos_iff (legal : List α → Finset α)
    (hnonempty : ∀ history, (legal history).Nonempty)
    (history : List α) (a : α) :
    0 < uniformStep legal history a ↔ a ∈ legal history := by
  have hcard : (0 : ℝ) < (legal history).card := by
    exact_mod_cast Finset.card_pos.mpr (hnonempty history)
  by_cases ha : a ∈ legal history
  · simp [uniformStep, ha, inv_pos.mpr hcard]
  · simp [uniformStep, ha]

variable (step : List α → α → ℝ)

section TransitionMass

variable
  (hstep_nonneg : ∀ history a, 0 ≤ step history a)
  (hstep_sum : ∀ history, ∑ a : α, step history a = 1)

include hstep_nonneg hstep_sum

theorem tailMass_nonneg (hit : List α → α → Bool) :
    ∀ history depth threshold,
      0 ≤ tailMass step hit history depth threshold := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      by_cases h : threshold = 0 <;> simp [tailMass, h]
  | succ depth ih =>
      intro threshold
      simp only [tailMass]
      apply Finset.sum_nonneg
      intro a _ha
      exact mul_nonneg (hstep_nonneg history a)
        (ih (history ++ [a]) _)

theorem tailMass_zero (hit : List α → α → Bool) :
    ∀ history depth, tailMass step hit history depth 0 = 1 := by
  intro history depth
  induction depth generalizing history with
  | zero => simp [tailMass]
  | succ depth ih =>
      simp only [tailMass, Nat.zero_sub, ih]
      simpa using hstep_sum history

theorem tailMass_le_one (hit : List α → α → Bool) :
    ∀ history depth threshold,
      tailMass step hit history depth threshold ≤ 1 := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      by_cases h : threshold = 0 <;> simp [tailMass, h]
  | succ depth ih =>
      intro threshold
      simp only [tailMass]
      calc
        (∑ a : α, step history a *
            tailMass step hit (history ++ [a]) depth
              (threshold - hitBit hit history a)) ≤
            ∑ a : α, step history a * 1 := by
          apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left
            (ih (history ++ [a]) _) (hstep_nonneg history a)
        _ = 1 := by simpa using hstep_sum history

theorem multiTailMass_nonneg {β : Type*} [Fintype β]
    (hit : β → List α → α → Bool) :
    ∀ history depth threshold,
      0 ≤ multiTailMass step hit history depth threshold := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      simp only [multiTailMass]
      split <;> norm_num
  | succ depth ih =>
      intro threshold
      simp only [multiTailMass]
      apply Finset.sum_nonneg
      intro a _ha
      exact mul_nonneg (hstep_nonneg history a)
        (ih (history ++ [a]) _)

theorem multiTailMass_le_one {β : Type*} [Fintype β]
    (hit : β → List α → α → Bool) :
    ∀ history depth threshold,
      multiTailMass step hit history depth threshold ≤ 1 := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      simp only [multiTailMass]
      split <;> norm_num
  | succ depth ih =>
      intro threshold
      simp only [multiTailMass]
      calc
        (∑ a : α, step history a *
            multiTailMass step hit (history ++ [a]) depth
              (fun b ↦ threshold b - hitBit (hit b) history a)) ≤
            ∑ a : α, step history a * 1 := by
          apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left
            (ih (history ++ [a]) _) (hstep_nonneg history a)
        _ = 1 := by simpa using hstep_sum history

/-- Finite union bound for overload mass. -/
theorem multiTailMass_le_sum_tailMass
    {β : Type*} [Fintype β] [DecidableEq β]
    (hit : β → List α → α → Bool) :
    ∀ history depth threshold,
      multiTailMass step hit history depth threshold ≤
        ∑ b : β, tailMass step (hit b) history depth (threshold b) := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      simp only [multiTailMass, tailMass]
      by_cases hex : ∃ b, threshold b = 0
      · rw [if_pos hex]
        obtain ⟨b, hb⟩ := hex
        have hbmem : b ∈ (Finset.univ : Finset β) := Finset.mem_univ b
        have hterm : (1 : ℝ) ≤
            (if threshold b = 0 then 1 else 0) := by simp [hb]
        have hsingle := Finset.single_le_sum
          (s := (Finset.univ : Finset β))
          (f := fun c : β ↦ (if threshold c = 0 then 1 else 0 : ℝ))
          (fun c _hc ↦ by
            by_cases hcz : threshold c = 0 <;> simp [hcz]) hbmem
        exact hterm.trans hsingle
      · rw [if_neg hex]
        exact Finset.sum_nonneg fun b _hb ↦ by
          split <;> norm_num
  | succ depth ih =>
      intro threshold
      simp only [multiTailMass, tailMass]
      calc
        (∑ a : α, step history a *
            multiTailMass step hit (history ++ [a]) depth
              (fun b ↦ threshold b - hitBit (hit b) history a)) ≤
            ∑ a : α, step history a *
              (∑ b : β, tailMass step (hit b) (history ++ [a]) depth
                (threshold b - hitBit (hit b) history a)) := by
          apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left
            (ih (history ++ [a]) _) (hstep_nonneg history a)
        _ = ∑ b : β, ∑ a : α, step history a *
              tailMass step (hit b) (history ++ [a]) depth
                (threshold b - hitBit (hit b) history a) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
        _ = _ := by rfl

theorem adaptiveMGF_nonneg (hit : List α → α → Bool) (t : ℝ) :
    ∀ history depth, 0 ≤ adaptiveMGF step hit t history depth := by
  intro history depth
  induction depth generalizing history with
  | zero => simp [adaptiveMGF]
  | succ depth ih =>
      simp only [adaptiveMGF]
      apply Finset.sum_nonneg
      intro a _ha
      exact mul_nonneg
        (mul_nonneg (hstep_nonneg history a) (Real.exp_nonneg _))
        (ih (history ++ [a]))

theorem one_le_adaptiveMGF (hit : List α → α → Bool)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ history depth, 1 ≤ adaptiveMGF step hit t history depth := by
  intro history depth
  induction depth generalizing history with
  | zero => simp [adaptiveMGF]
  | succ depth ih =>
      simp only [adaptiveMGF]
      calc
        1 = ∑ a : α, step history a := (hstep_sum history).symm
        _ ≤ ∑ a : α, step history a *
            Real.exp (t * hitBit hit history a) *
              adaptiveMGF step hit t (history ++ [a]) depth := by
          apply Finset.sum_le_sum
          intro a _ha
          have he : 1 ≤ Real.exp (t * hitBit hit history a) := by
            apply Real.one_le_exp
            positivity
          calc
            step history a = step history a * 1 * 1 := by ring
            _ ≤ step history a *
                Real.exp (t * hitBit hit history a) * 1 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left he (hstep_nonneg history a))
                (by norm_num)
            _ ≤ step history a *
                Real.exp (t * hitBit hit history a) *
                  adaptiveMGF step hit t (history ++ [a]) depth := by
              exact mul_le_mul_of_nonneg_left
                (ih (history ++ [a]))
                (mul_nonneg (hstep_nonneg history a) (Real.exp_nonneg _))

/-- The one-step Bernoulli exponential-moment identity. -/
theorem oneStepMGF_eq
    (hit : List α → α → Bool) (history : List α) (t : ℝ) :
    (∑ a : α, step history a *
        Real.exp (t * hitBit hit history a)) =
      1 + (Real.exp t - 1) *
        (∑ a : α, step history a * hitBit hit history a) := by
  have hpoint (a : α) :
      Real.exp (t * hitBit hit history a) =
        1 + (Real.exp t - 1) * hitBit hit history a := by
    simp only [hitBit]
    split <;> simp
  calc
    (∑ a : α, step history a *
        Real.exp (t * hitBit hit history a)) =
        ∑ a : α, (step history a +
          (Real.exp t - 1) *
            (step history a * hitBit hit history a)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [hpoint]
      ring
    _ = (∑ a : α, step history a) +
        (Real.exp t - 1) *
          (∑ a : α, step history a * hitBit hit history a) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hstep_sum]

/-- Adaptive exponential-moment bound from deterministic conditional hit
probability caps. -/
theorem adaptiveMGF_le
    (hit : List α → α → Bool) (p : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    {t : ℝ} (ht : 0 ≤ t)
    (hhit : ∀ history,
      (∑ a : α, step history a * hitBit hit history a) ≤
        p history.length) :
    ∀ history depth,
      adaptiveMGF step hit t history depth ≤
        Real.exp ((Real.exp t - 1) *
          adaptiveBudget p history.length depth) := by
  intro history depth
  induction depth generalizing history with
  | zero => simp [adaptiveMGF, adaptiveBudget]
  | succ depth ih =>
      have hx : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp ht)
      let future := Real.exp ((Real.exp t - 1) *
        adaptiveBudget p (history.length + 1) depth)
      have hfuture : ∀ a : α,
          adaptiveMGF step hit t (history ++ [a]) depth ≤ future := by
        intro a
        simpa [future] using ih (history ++ [a])
      have honeStep :
          (∑ a : α, step history a *
              Real.exp (t * hitBit hit history a)) ≤
            Real.exp ((Real.exp t - 1) * p history.length) := by
        rw [oneStepMGF_eq step hstep_nonneg hstep_sum]
        calc
          1 + (Real.exp t - 1) *
              (∑ a : α, step history a * hitBit hit history a) ≤
              1 + (Real.exp t - 1) * p history.length := by
            simpa [add_comm] using add_le_add_left
              (mul_le_mul_of_nonneg_left (hhit history) hx) 1
          _ ≤ Real.exp ((Real.exp t - 1) * p history.length) := by
            simpa [add_comm] using Real.add_one_le_exp
              ((Real.exp t - 1) * p history.length)
      simp only [adaptiveMGF]
      calc
        (∑ a : α, step history a *
            Real.exp (t * hitBit hit history a) *
              adaptiveMGF step hit t (history ++ [a]) depth) ≤
            ∑ a : α, (step history a *
              Real.exp (t * hitBit hit history a)) * future := by
          apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left (hfuture a)
            (mul_nonneg (hstep_nonneg history a) (Real.exp_nonneg _))
        _ = (∑ a : α, step history a *
              Real.exp (t * hitBit hit history a)) * future := by
          rw [Finset.sum_mul]
        _ ≤ Real.exp ((Real.exp t - 1) * p history.length) * future := by
          exact mul_le_mul_of_nonneg_right honeStep (Real.exp_nonneg _)
        _ = Real.exp ((Real.exp t - 1) *
              adaptiveBudget p history.length (depth + 1)) := by
          rw [← Real.exp_add]
          simp only [future, adaptiveBudget]
          congr 1
          ring

/-- Exponential Markov inequality on the transition tree. -/
theorem tailMass_le_exp_mul_mgf
    (hit : List α → α → Bool) {t : ℝ} (ht : 0 ≤ t) :
    ∀ history depth threshold,
      tailMass step hit history depth threshold ≤
        Real.exp (-t * threshold) * adaptiveMGF step hit t history depth := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold
      by_cases hm : threshold = 0
      · subst threshold; simp [tailMass, adaptiveMGF]
      · simp [tailMass, adaptiveMGF, hm, Real.exp_nonneg]
  | succ depth ih =>
      intro threshold
      by_cases hm : threshold = 0
      · subst threshold
        rw [tailMass_zero step hstep_nonneg hstep_sum]
        simpa using one_le_adaptiveMGF step hstep_nonneg hstep_sum hit ht
          history (depth + 1)
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
        simp only [tailMass, adaptiveMGF]
        calc
          (∑ a : α, step history a *
              tailMass step hit (history ++ [a]) depth
                (m + 1 - hitBit hit history a)) ≤
              ∑ a : α, step history a *
                (Real.exp (-t *
                  ((m + 1 - hitBit hit history a : ℕ) : ℝ)) *
                  adaptiveMGF step hit t (history ++ [a]) depth) := by
            apply Finset.sum_le_sum
            intro a _ha
            exact mul_le_mul_of_nonneg_left
              (ih (history ++ [a]) _) (hstep_nonneg history a)
          _ = Real.exp (-t * (m + 1)) *
              (∑ a : α, step history a *
                Real.exp (t * hitBit hit history a) *
                  adaptiveMGF step hit t (history ++ [a]) depth) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _ha
            simp only [hitBit]
            split
            · simp only [Nat.add_sub_cancel, Nat.cast_one, mul_one]
              have hleft : Real.exp (-(t * ((1 + m : ℕ) : ℝ))) *
                  Real.exp t = Real.exp (-t * (m : ℝ)) := by
                rw [← Real.exp_add]
                congr 1
                push_cast
                ring
              calc
                step history a *
                    (Real.exp (-t * (m : ℝ)) *
                      adaptiveMGF step hit t (history ++ [a]) depth) =
                    step history a * Real.exp (-t * (m : ℝ)) *
                      adaptiveMGF step hit t (history ++ [a]) depth := by ring
                _ = step history a *
                      (Real.exp (-(t * ((1 + m : ℕ) : ℝ))) * Real.exp t) *
                      adaptiveMGF step hit t (history ++ [a]) depth := by
                    rw [hleft]
                _ = Real.exp (-t * ((m + 1 : ℕ) : ℝ)) *
                      (step history a * Real.exp t *
                        adaptiveMGF step hit t (history ++ [a]) depth) := by
                    push_cast
                    ring_nf
                _ = Real.exp (-t * ((m : ℝ) + 1)) *
                      (step history a * Real.exp t *
                        adaptiveMGF step hit t (history ++ [a]) depth) := by
                    norm_num
            · simp
              ring
          _ = Real.exp (-t * ((m + 1 : ℕ) : ℝ)) *
              (∑ a : α, step history a *
                Real.exp (t * hitBit hit history a) *
                  adaptiveMGF step hit t (history ++ [a]) depth) := by
            norm_num [Nat.cast_succ]

/-- Combined adaptive Chernoff bound. -/
theorem tailMass_le_chernoff
    (hit : List α → α → Bool) (p : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    {t : ℝ} (ht : 0 ≤ t)
    (hhit : ∀ history,
      (∑ a : α, step history a * hitBit hit history a) ≤
        p history.length) :
    ∀ history depth threshold,
      tailMass step hit history depth threshold ≤
        Real.exp (-t * threshold) *
          Real.exp ((Real.exp t - 1) *
            adaptiveBudget p history.length depth) := by
  intro history depth threshold
  exact (tailMass_le_exp_mul_mgf step hstep_nonneg hstep_sum hit ht
      history depth threshold).trans
    (mul_le_mul_of_nonneg_left
      (adaptiveMGF_le step hstep_nonneg hstep_sum hit p hp ht hhit
        history depth) (Real.exp_nonneg _))

/-- A tail mass strictly below one yields a concrete positive-probability
path with fewer than the threshold number of hits. -/
theorem exists_path_of_tailMass_lt_one
    (hit : List α → α → Bool) :
    ∀ history depth threshold,
      tailMass step hit history depth threshold < 1 →
        ∃ path : List α, path.length = depth ∧
          PathPositive step history path ∧
          pathHits hit history path < threshold := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold htail
      refine ⟨[], rfl, trivial, ?_⟩
      simp only [tailMass] at htail
      by_cases hm : threshold = 0
      · simp [hm] at htail
      · simp [pathHits]
        omega
  | succ depth ih =>
      intro threshold htail
      have htailLe (a : α) :
          tailMass step hit (history ++ [a]) depth
              (threshold - hitBit hit history a) ≤ 1 :=
        tailMass_le_one step hstep_nonneg hstep_sum hit _ _ _
      have hex : ∃ a : α, 0 < step history a ∧
          tailMass step hit (history ++ [a]) depth
              (threshold - hitBit hit history a) < 1 := by
        by_contra hnot
        push_neg at hnot
        have hterm (a : α) :
            step history a *
                tailMass step hit (history ++ [a]) depth
                  (threshold - hitBit hit history a) =
              step history a := by
          by_cases hzero : step history a = 0
          · simp [hzero]
          · have hpos : 0 < step history a :=
              lt_of_le_of_ne (hstep_nonneg history a) (Ne.symm hzero)
            have hone : 1 ≤ tailMass step hit (history ++ [a]) depth
                (threshold - hitBit hit history a) :=
              hnot a hpos
            have heq := le_antisymm (htailLe a) hone
            calc
              step history a *
                  tailMass step hit (history ++ [a]) depth
                    (threshold - hitBit hit history a) =
                  step history a * 1 := by rw [heq]
              _ = step history a := by ring
        have heq : tailMass step hit history (depth + 1) threshold = 1 := by
          simp only [tailMass]
          calc
            (∑ a : α, step history a *
                tailMass step hit (history ++ [a]) depth
                  (threshold - hitBit hit history a)) =
                ∑ a : α, step history a := by
              apply Finset.sum_congr rfl
              intro a _ha
              exact hterm a
            _ = 1 := hstep_sum history
        rw [heq] at htail
        exact (lt_irrefl 1 htail).elim
      obtain ⟨a, hstepPos, hchild⟩ := hex
      obtain ⟨rest, hlen, hpositive, hhits⟩ :=
        ih (history ++ [a])
          (threshold - hitBit hit history a) hchild
      refine ⟨a :: rest, by simp [hlen], ⟨hstepPos, hpositive⟩, ?_⟩
      simp only [pathHits]
      have hbit : hitBit hit history a ≤ 1 := by
        unfold hitBit
        split <;> omega
      omega

/-- If the union-overload mass is below one, one positive path stays below
every threshold simultaneously. -/
theorem exists_path_of_multiTailMass_lt_one
    {β : Type*} [Fintype β] [DecidableEq β]
    (hit : β → List α → α → Bool) :
    ∀ history depth threshold,
      multiTailMass step hit history depth threshold < 1 →
        ∃ path : List α, path.length = depth ∧
          PathPositive step history path ∧
          ∀ b : β, pathHits (hit b) history path < threshold b := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      intro threshold htail
      refine ⟨[], rfl, trivial, ?_⟩
      intro b
      have hnonzero : threshold b ≠ 0 := by
        intro hb
        have hex : ∃ c, threshold c = 0 := ⟨b, hb⟩
        simp [multiTailMass, hex] at htail
      simp [pathHits]
      omega
  | succ depth ih =>
      intro threshold htail
      have hchildLe (a : α) :
          multiTailMass step hit (history ++ [a]) depth
            (fun b ↦ threshold b - hitBit (hit b) history a) ≤ 1 :=
        multiTailMass_le_one step hstep_nonneg hstep_sum hit _ _ _
      have hex : ∃ a : α, 0 < step history a ∧
          multiTailMass step hit (history ++ [a]) depth
            (fun b ↦ threshold b - hitBit (hit b) history a) < 1 := by
        by_contra hnot
        push_neg at hnot
        have hterm (a : α) :
            step history a *
                multiTailMass step hit (history ++ [a]) depth
                  (fun b ↦ threshold b - hitBit (hit b) history a) =
              step history a := by
          by_cases hzero : step history a = 0
          · simp [hzero]
          · have hpos : 0 < step history a :=
              lt_of_le_of_ne (hstep_nonneg history a) (Ne.symm hzero)
            have hone : 1 ≤ multiTailMass step hit (history ++ [a]) depth
                (fun b ↦ threshold b - hitBit (hit b) history a) :=
              hnot a hpos
            have heq := le_antisymm (hchildLe a) hone
            calc
              step history a *
                  multiTailMass step hit (history ++ [a]) depth
                    (fun b ↦ threshold b - hitBit (hit b) history a) =
                  step history a * 1 := by rw [heq]
              _ = step history a := by ring
        have heq : multiTailMass step hit history (depth + 1) threshold = 1 := by
          simp only [multiTailMass]
          calc
            (∑ a : α, step history a *
                multiTailMass step hit (history ++ [a]) depth
                  (fun b ↦ threshold b - hitBit (hit b) history a)) =
                ∑ a : α, step history a := by
              apply Finset.sum_congr rfl
              intro a _ha
              exact hterm a
            _ = 1 := hstep_sum history
        rw [heq] at htail
        exact (lt_irrefl 1 htail).elim
      obtain ⟨a, hstepPos, hchild⟩ := hex
      obtain ⟨rest, hlen, hpositive, hhits⟩ :=
        ih (history ++ [a])
          (fun b ↦ threshold b - hitBit (hit b) history a) hchild
      refine ⟨a :: rest, by simp [hlen], ⟨hstepPos, hpositive⟩, ?_⟩
      intro b
      simp only [pathHits]
      have hbit : hitBit (hit b) history a ≤ 1 := by
        unfold hitBit
        split <;> omega
      have hrest := hhits b
      omega

/-- Union-bound form of the path extractor. -/
theorem exists_path_of_sum_tailMass_lt_one
    {β : Type*} [Fintype β] [DecidableEq β]
    (hit : β → List α → α → Bool)
    {history : List α} {depth : ℕ} {threshold : β → ℕ}
    (hsmall : (∑ b : β,
      tailMass step (hit b) history depth (threshold b)) < 1) :
    ∃ path : List α, path.length = depth ∧
      PathPositive step history path ∧
      ∀ b : β, pathHits (hit b) history path < threshold b := by
  apply exists_path_of_multiTailMass_lt_one step hstep_nonneg hstep_sum hit
  exact (multiTailMass_le_sum_tailMass step hstep_nonneg hstep_sum hit
    history depth threshold).trans_lt hsmall

/-- Simultaneous adaptive Chernoff extractor. -/
theorem exists_path_of_sum_chernoff_lt_one
    {β : Type*} [Fintype β] [DecidableEq β]
    (hit : β → List α → α → Bool)
    (p : β → ℕ → ℝ) (hp : ∀ b i, 0 ≤ p b i)
    {t : ℝ} (ht : 0 ≤ t)
    (hhit : ∀ b history,
      (∑ a : α, step history a * hitBit (hit b) history a) ≤
        p b history.length)
    {history : List α} {depth : ℕ} {threshold : β → ℕ}
    (hsmall : (∑ b : β,
      Real.exp (-t * threshold b) *
        Real.exp ((Real.exp t - 1) *
          adaptiveBudget (p b) history.length depth)) < 1) :
    ∃ path : List α, path.length = depth ∧
      PathPositive step history path ∧
      ∀ b : β, pathHits (hit b) history path < threshold b := by
  apply exists_path_of_sum_tailMass_lt_one step hstep_nonneg hstep_sum hit
  exact (Finset.sum_le_sum fun b _hb ↦
    tailMass_le_chernoff step hstep_nonneg hstep_sum (hit b) (p b)
      (hp b) ht (hhit b) history depth (threshold b)).trans_lt hsmall

/-- Convenient final form: a numerical Chernoff bound below one produces a
positive transition path satisfying the desired load cap. -/
theorem exists_path_of_chernoff_lt_one
    (hit : List α → α → Bool) (p : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    {t : ℝ} (ht : 0 ≤ t)
    (hhit : ∀ history,
      (∑ a : α, step history a * hitBit hit history a) ≤
        p history.length)
    {history : List α} {depth threshold : ℕ}
    (hsmall : Real.exp (-t * threshold) *
        Real.exp ((Real.exp t - 1) *
          adaptiveBudget p history.length depth) < 1) :
    ∃ path : List α, path.length = depth ∧
      PathPositive step history path ∧
      pathHits hit history path < threshold := by
  apply exists_path_of_tailMass_lt_one step hstep_nonneg hstep_sum hit
  exact (tailMass_le_chernoff step hstep_nonneg hstep_sum hit p hp ht hhit
    history depth threshold).trans_lt hsmall

end TransitionMass

end

end Erdos722.AdaptiveChernoff
