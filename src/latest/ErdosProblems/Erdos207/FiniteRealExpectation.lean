/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteProbability
import Mathlib.Analysis.Complex.Exponential

/-!
# Real-valued expectations for finite laws

The counting and moment layer uses nonnegative expectations.  Martingale
increments and centered trajectory errors are real-valued, so this file adds
the corresponding finite-sum expectation and its bind, support, and indicator
identities.
-/

namespace Erdos207

open scoped BigOperators NNReal

noncomputable section

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- Expectation of a real-valued function under a finite law. -/
def expectationReal (L : FiniteLaw Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, (L.mass ω : ℝ) * X ω

@[simp]
theorem expectationReal_const (L : FiniteLaw Ω) (c : ℝ) :
    L.expectationReal (fun _ ↦ c) = c := by
  rw [expectationReal, ← Finset.sum_mul]
  norm_cast
  rw [L.sum_mass]
  simp

@[simp]
theorem expectationReal_zero (L : FiniteLaw Ω) :
    L.expectationReal (fun _ ↦ 0) = 0 := by
  simp [expectationReal]

theorem expectationReal_add (L : FiniteLaw Ω) (X Y : Ω → ℝ) :
    L.expectationReal (fun ω ↦ X ω + Y ω) =
      L.expectationReal X + L.expectationReal Y := by
  simp only [expectationReal, mul_add, Finset.sum_add_distrib]

theorem expectationReal_sub (L : FiniteLaw Ω) (X Y : Ω → ℝ) :
    L.expectationReal (fun ω ↦ X ω - Y ω) =
      L.expectationReal X - L.expectationReal Y := by
  simp only [expectationReal, mul_sub, Finset.sum_sub_distrib]

theorem expectationReal_mul_const (L : FiniteLaw Ω) (X : Ω → ℝ) (c : ℝ) :
    L.expectationReal (fun ω ↦ X ω * c) = L.expectationReal X * c := by
  simp only [expectationReal, mul_assoc, Finset.sum_mul]

theorem expectationReal_const_mul (L : FiniteLaw Ω) (c : ℝ) (X : Ω → ℝ) :
    L.expectationReal (fun ω ↦ c * X ω) = c * L.expectationReal X := by
  simp only [expectationReal]
  calc
    (∑ ω, ↑(L.mass ω) * (c * X ω)) =
        ∑ ω, c * (↑(L.mass ω) * X ω) := by
      apply Finset.sum_congr rfl
      intro ω _hω
      ring
    _ = c * ∑ ω, ↑(L.mass ω) * X ω := by rw [Finset.mul_sum]

@[simp]
theorem expectationReal_pure [DecidableEq Ω] (x : Ω) (X : Ω → ℝ) :
    (pure x).expectationReal X = X x := by
  classical
  unfold expectationReal
  rw [Finset.sum_eq_single x]
  · simp [pure]
  · intro y _hy hyx
    simp [pure, hyx]
  · simp

/-- Finite law of total expectation. -/
theorem expectationReal_bind
    {Ξ : Type*} [Fintype Ξ] (L : FiniteLaw Ω)
    (K : Ω → FiniteLaw Ξ) (X : Ξ → ℝ) :
    (bind L K).expectationReal X =
      L.expectationReal (fun ω ↦ (K ω).expectationReal X) := by
  unfold expectationReal bind
  change (∑ y, (↑(∑ x, L.mass x * (K x).mass y) : ℝ) * X y) = _
  push_cast
  calc
    (∑ y, (∑ x, ↑(L.mass x) * ↑((K x).mass y)) * X y) =
        ∑ y, ∑ x, ↑(L.mass x) * (↑((K x).mass y) * X y) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ∑ x, ∑ y, ↑(L.mass x) *
        (↑((K x).mass y) * X y) := Finset.sum_comm
    _ = ∑ x, ↑(L.mass x) *
        (∑ y, ↑((K x).mass y) * X y) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
    _ = _ := rfl

/-- Expectation under a pushforward is expectation of the pullback. -/
theorem expectationReal_map
    {Ξ : Type*} [Fintype Ξ] [DecidableEq Ξ]
    (f : Ω → Ξ) (L : FiniteLaw Ω) (X : Ξ → ℝ) :
    (map f L).expectationReal X = L.expectationReal (fun ω ↦ X (f ω)) := by
  classical
  have hmap : map f L = bind L (fun x ↦ pure (f x)) := by
    apply FiniteLaw.ext
    intro y
    change (∑ x, if f x = y then L.mass x else 0) =
      ∑ x, L.mass x * (if y = f x then 1 else 0)
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hxy : f x = y
    · simp [hxy]
    · simp [hxy, Ne.symm hxy]
  rw [hmap, expectationReal_bind]
  simp

/-- Real expectation under the uniform law is the normalized finite sum. -/
theorem expectationReal_uniform [Nonempty Ω] (X : Ω → ℝ) :
    (uniform : FiniteLaw Ω).expectationReal X =
      (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, X ω := by
  unfold expectationReal uniform
  push_cast
  rw [Finset.mul_sum]

/-- Expectation monotonicity when the comparison is only required on the
positive-mass support. -/
theorem expectationReal_mono_of_supported
    (L : FiniteLaw Ω) {P : Ω → Prop} (hP : L.SupportedOn P)
    {X Y : Ω → ℝ} (hXY : ∀ ω, P ω → X ω ≤ Y ω) :
    L.expectationReal X ≤ L.expectationReal Y := by
  unfold expectationReal
  apply Finset.sum_le_sum
  intro ω _hω
  by_cases hm : 0 < L.mass ω
  · exact mul_le_mul_of_nonneg_left (hXY ω (hP ω hm)) (by positivity)
  · have hm0 : L.mass ω = 0 :=
      le_antisymm (not_lt.mp hm) (zero_le : 0 ≤ L.mass ω)
    simp [hm0]

/-- Two observables agreeing on the positive-mass support have the same
expectation. -/
theorem expectationReal_congr_of_supported
    (L : FiniteLaw Ω) {P : Ω → Prop} (hP : L.SupportedOn P)
    {X Y : Ω → ℝ} (hXY : ∀ ω, P ω → X ω = Y ω) :
    L.expectationReal X = L.expectationReal Y := by
  apply le_antisymm
  · exact expectationReal_mono_of_supported L hP fun ω hω ↦
      (hXY ω hω).le
  · exact expectationReal_mono_of_supported L hP fun ω hω ↦
      (hXY ω hω).ge

/-- Unconditional expectation monotonicity. -/
theorem expectationReal_mono (L : FiniteLaw Ω)
    {X Y : Ω → ℝ} (hXY : ∀ ω, X ω ≤ Y ω) :
    L.expectationReal X ≤ L.expectationReal Y := by
  apply expectationReal_mono_of_supported L
    (P := fun _ ↦ True) (fun _ _ ↦ trivial)
  exact fun ω _ ↦ hXY ω

/-- The expectation of an event indicator is the real coercion of its
probability. -/
theorem expectationReal_indicator (L : FiniteLaw Ω) (P : Ω → Prop)
    [DecidablePred P] :
    L.expectationReal (fun ω ↦ if P ω then 1 else 0) =
      (L.probability P : ℝ) := by
  classical
  unfold expectationReal probability
  push_cast
  apply Finset.sum_congr rfl
  intro ω _hω
  by_cases hP : P ω <;> simp [hP]

/-- Real-valued Markov inequality for a nonnegative random variable. -/
theorem probability_coe_le_expectationReal_div
    (L : FiniteLaw Ω) (X : Ω → ℝ) (a : ℝ)
    (ha : 0 < a) (hX : ∀ ω, 0 ≤ X ω) :
    (L.probability (fun ω ↦ a ≤ X ω) : ℝ) ≤
      L.expectationReal X / a := by
  apply (le_div_iff₀ ha).2
  rw [← L.expectationReal_indicator,
    ← L.expectationReal_mul_const]
  apply L.expectationReal_mono
  intro ω
  by_cases hω : a ≤ X ω
  · simp [hω]
  · simp [hω, hX ω]

end FiniteLaw

end

end Erdos207
