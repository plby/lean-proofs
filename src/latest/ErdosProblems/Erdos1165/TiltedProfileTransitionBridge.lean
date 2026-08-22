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

import ErdosProblems.Erdos1165.ProfileTransitionBridge

/-!
# Exponentially tilted critical-offspring bridges

The exact radial-word cutoff contributes a factor `r` for every excursion
count in an erased profile coordinate.  This file evaluates that finite
critical branching-chain exponential moment exactly.  Only four steps are
needed by the asymmetric three-coordinate buffer, but the statements are
given for arbitrary finite depth.
-/

open scoped BigOperators

namespace Erdos1165.TiltedProfileTransitionBridge

open AppendixFirstMoment NegativeBinomial

noncomputable section

/-- Scalar recursion for the exponential moment of successive generations
of the critical geometric branching chain. -/
def tiltParameter : ℕ → ℝ → ℝ
  | 0, _r => 1
  | steps + 1, r => 1 / (2 - r * tiltParameter steps r)

/-- Total tilted mass of a chain of the specified depth. -/
def tiltedPathMass : ℕ → ℝ → ℕ → ℝ
  | 0, _r, _a => 1
  | steps + 1, r, a =>
      ∑' b : ℕ, r ^ b * transitionMass a b * tiltedPathMass steps r b

/-- Literal mass of one finite sequence in the tilted branching chain. -/
def tiltedPathWeightENNReal : (steps : ℕ) → ℝ → ℕ →
    (Fin steps → ℕ) → ENNReal
  | 0, _r, _a, _path => 1
  | steps + 1, r, a, path =>
      ENNReal.ofReal (r ^ path 0 * transitionMass a (path 0)) *
        tiltedPathWeightENNReal steps r (path 0) (Fin.tail path)

/-- Exact probability-generating series of one critical transition,
including the absorbing-zero row. -/
theorem hasSum_pow_mul_transitionMass
    {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s < 2) (a : ℕ) :
    HasSum (fun b : ℕ ↦ s ^ b * transitionMass a b)
      ((1 / (2 - s)) ^ a) := by
  by_cases ha : a = 0
  · subst a
    have hfun :
        (fun b : ℕ ↦ s ^ b * transitionMass 0 b) =
          fun b : ℕ ↦ if b = 0 then 1 else 0 := by
      funext b
      rw [transitionMass_zero_left]
      split_ifs with hb
      · subst b
        simp
      · simp [hb]
    rw [hfun]
    simpa using (hasSum_ite_eq 0 (1 : ℝ))
  · have haPos : 0 < a := Nat.pos_of_ne_zero ha
    have hr : ‖s / 2‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith
    have hseries :=
      (NegativeBinomial.hasSum_coefficient_mul_pow
        (r := s / 2) hr haPos).mul_left ((1 / 2 : ℝ) ^ a)
    have hfun :
        (fun b : ℕ ↦ s ^ b * transitionMass a b) =
          fun b : ℕ ↦ (1 / 2 : ℝ) ^ a *
            ((NegativeBinomial.coefficient a b : ℝ) * (s / 2) ^ b) := by
      funext b
      rw [transitionMass_of_pos haPos, NegativeBinomial.mass]
      norm_num only [one_div, one_sub_div]
      rw [div_pow]
      ring
    rw [hfun]
    have hden : 2 - s ≠ 0 := by linarith
    have hden' : 1 - s / 2 ≠ 0 := by
      intro h
      apply hden
      linarith
    have hvalue :
        (1 / 2 : ℝ) ^ a * (1 / (1 - s / 2) ^ a) =
          (1 / (2 - s)) ^ a := by
      rw [show (1 / (1 - s / 2) ^ a : ℝ) =
          (1 / (1 - s / 2)) ^ a by rw [one_div_pow]]
      rw [← mul_pow]
      congr 1
      field_simp
    rw [← hvalue]
    exact hseries

theorem summable_pow_mul_transitionMass
    {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s < 2) (a : ℕ) :
    Summable (fun b : ℕ ↦ s ^ b * transitionMass a b) :=
  (hasSum_pow_mul_transitionMass hs0 hs2 a).summable

/-- Exact finite-depth tilted mass.  The side condition says that every
successive generating-function argument remains below its radius of
convergence. -/
theorem tiltedPathMass_eq : ∀ steps (r : ℝ),
    0 < r →
    (∀ j < steps, r * tiltParameter j r < 2) →
    ∀ a : ℕ, tiltedPathMass steps r a = tiltParameter steps r ^ a := by
  intro steps
  induction steps with
  | zero =>
      intro r _hr _hconv a
      simp [tiltedPathMass, tiltParameter]
  | succ steps ih =>
      intro r hr hconv a
      have hprevConv : ∀ j < steps, r * tiltParameter j r < 2 := by
        intro j hj
        exact hconv j (by omega)
      have hs2 : r * tiltParameter steps r < 2 := hconv steps (by omega)
      have hparamPos : 0 < tiltParameter steps r := by
        cases steps with
        | zero => simp [tiltParameter]
        | succ prior =>
            rw [tiltParameter]
            have hden : 0 < 2 - r * tiltParameter prior r := by
              linarith [hconv prior (by omega)]
            positivity
      have hs0 : 0 ≤ r * tiltParameter steps r :=
        mul_nonneg hr.le hparamPos.le
      rw [tiltedPathMass]
      simp_rw [ih r hr hprevConv]
      have hsum := hasSum_pow_mul_transitionMass hs0 hs2 a
      have hfun :
          (fun b : ℕ ↦ r ^ b * transitionMass a b *
              tiltParameter steps r ^ b) =
            fun b : ℕ ↦
              (r * tiltParameter steps r) ^ b * transitionMass a b := by
        funext b
        rw [mul_pow]
        ring
      rw [hfun, hsum.tsum_eq, tiltParameter]

lemma tiltedPathMass_nonneg (steps : ℕ) {r : ℝ} (hr : 0 ≤ r) (a : ℕ) :
    0 ≤ tiltedPathMass steps r a := by
  induction steps generalizing a with
  | zero => simp [tiltedPathMass]
  | succ steps ih =>
      rw [tiltedPathMass]
      exact tsum_nonneg fun b ↦ mul_nonneg
        (mul_nonneg (pow_nonneg hr b) (transitionMass_nonneg a b)) (ih b)

/-- Literal finite sequences sum to the scalar tilted path mass.  The
radius-of-convergence hypothesis is exactly the one used by
`tiltedPathMass_eq`. -/
theorem tsum_tiltedPathWeightENNReal_eq : ∀ steps (r : ℝ),
    0 < r →
    (∀ j < steps, r * tiltParameter j r < 2) →
    ∀ a : ℕ,
      (∑' path : Fin steps → ℕ,
          tiltedPathWeightENNReal steps r a path) =
        ENNReal.ofReal (tiltedPathMass steps r a) := by
  intro steps
  induction steps with
  | zero =>
      intro r _hr _hconv a
      simp [tiltedPathWeightENNReal, tiltedPathMass]
  | succ steps ih =>
      intro r hr hconv a
      have hprevConv : ∀ j < steps, r * tiltParameter j r < 2 := by
        intro j hj
        exact hconv j (by omega)
      have hs2 : r * tiltParameter steps r < 2 := hconv steps (by omega)
      have hparamPos : 0 < tiltParameter steps r := by
        cases steps with
        | zero => simp [tiltParameter]
        | succ prior =>
            rw [tiltParameter]
            have hden : 0 < 2 - r * tiltParameter prior r := by
              linarith [hconv prior (by omega)]
            positivity
      have hs0 : 0 ≤ r * tiltParameter steps r :=
        mul_nonneg hr.le hparamPos.le
      have hinner (b : ℕ) :
          tiltedPathMass steps r b = tiltParameter steps r ^ b :=
        tiltedPathMass_eq steps r hr hprevConv b
      have hsummable : Summable (fun b : ℕ ↦
          r ^ b * transitionMass a b * tiltedPathMass steps r b) := by
        have hs := summable_pow_mul_transitionMass hs0 hs2 a
        apply hs.congr
        intro b
        rw [hinner b, mul_pow]
        ring
      have hterm : ∀ b : ℕ,
          0 ≤ r ^ b * transitionMass a b * tiltedPathMass steps r b := by
        intro b
        exact mul_nonneg
          (mul_nonneg (pow_nonneg hr.le b) (transitionMass_nonneg a b))
          (tiltedPathMass_nonneg steps hr.le b)
      calc
        (∑' path : Fin (steps + 1) → ℕ,
            tiltedPathWeightENNReal (steps + 1) r a path) =
            ∑' pair : ℕ × (Fin steps → ℕ),
              tiltedPathWeightENNReal (steps + 1) r a
                ((Fin.consEquiv (fun _ : Fin (steps + 1) ↦ ℕ)) pair) := by
                  exact (Equiv.tsum_eq
                    (Fin.consEquiv (fun _ : Fin (steps + 1) ↦ ℕ))
                    (fun path ↦
                      tiltedPathWeightENNReal (steps + 1) r a path)).symm
        _ = ∑' pair : ℕ × (Fin steps → ℕ),
              ENNReal.ofReal
                  (r ^ pair.1 * transitionMass a pair.1) *
                tiltedPathWeightENNReal steps r pair.1 pair.2 := by
                  apply tsum_congr
                  intro pair
                  have htail : Fin.tail
                      ((Fin.consEquiv
                        (fun _ : Fin (steps + 1) ↦ ℕ)) pair) = pair.2 := by
                    ext i
                    rfl
                  rw [tiltedPathWeightENNReal, htail]
                  rfl
        _ = ∑' b : ℕ, ∑' tail : Fin steps → ℕ,
              ENNReal.ofReal (r ^ b * transitionMass a b) *
                tiltedPathWeightENNReal steps r b tail := by
                  exact @ENNReal.tsum_prod ℕ (Fin steps → ℕ)
                    (fun b tail ↦
                      ENNReal.ofReal (r ^ b * transitionMass a b) *
                        tiltedPathWeightENNReal steps r b tail)
        _ = ∑' b : ℕ,
              ENNReal.ofReal (r ^ b * transitionMass a b) *
                ENNReal.ofReal (tiltedPathMass steps r b) := by
                  apply tsum_congr
                  intro b
                  rw [ENNReal.tsum_mul_left, ih r hr hprevConv b]
        _ = ∑' b : ℕ,
              ENNReal.ofReal
                (r ^ b * transitionMass a b * tiltedPathMass steps r b) := by
                  apply tsum_congr
                  intro b
                  rw [ENNReal.ofReal_mul
                    (mul_nonneg (pow_nonneg hr.le b)
                      (transitionMass_nonneg a b))]
        _ = ENNReal.ofReal (tiltedPathMass (steps + 1) r a) := by
                  rw [tiltedPathMass,
                    ENNReal.ofReal_tsum_of_nonneg hterm hsummable]

private lemma one_div_one_sub_le {u : ℝ}
    (hu0 : 0 ≤ u) (huHalf : u ≤ 1 / 2) :
    1 / (1 - u) ≤ 1 + 2 * u := by
  have hden : 0 < 1 - u := by linarith
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg u]

private lemma tiltParameter_succ_bounds
    {steps : ℕ} {r epsilon K : ℝ}
    (hrOne : 1 ≤ r) (hrUpper : r ≤ 1 + 3 * epsilon)
    (hepsilon0 : 0 ≤ epsilon) (hK0 : 0 ≤ K)
    (hzOne : 1 ≤ tiltParameter steps r)
    (hzUpper : tiltParameter steps r ≤ 1 + K * epsilon)
    (hcross : 3 * K * epsilon ≤ 1)
    (hhalf : (K + 4) * epsilon ≤ 1 / 2) :
    1 ≤ tiltParameter (steps + 1) r ∧
      tiltParameter (steps + 1) r ≤ 1 + (2 * (K + 4)) * epsilon ∧
      r * tiltParameter steps r < 2 := by
  let z := tiltParameter steps r
  have hz0 : 0 ≤ z := hzOne.trans' (by norm_num)
  have hr0 : 0 ≤ r := hrOne.trans' (by norm_num)
  have hprodLower : 1 ≤ r * z := by
    nlinarith [mul_le_mul hrOne hzOne (by norm_num : (0 : ℝ) ≤ 1) hr0]
  have hcross' : 3 * K * epsilon ^ 2 ≤ epsilon := by
    have := mul_le_mul_of_nonneg_right hcross hepsilon0
    nlinarith
  have hprodUpper : r * z ≤ 1 + (K + 4) * epsilon := by
    calc
      r * z ≤ (1 + 3 * epsilon) * (1 + K * epsilon) := by gcongr
      _ ≤ 1 + (K + 4) * epsilon := by
        nlinarith
  have hprodTwo : r * z < 2 := by
    have : (K + 4) * epsilon < 1 := hhalf.trans_lt (by norm_num)
    linarith
  have hden : 0 < 2 - r * z := by linarith
  have hu0 : 0 ≤ r * z - 1 := by linarith
  have huHalf : r * z - 1 ≤ 1 / 2 := by linarith
  have hinv := one_div_one_sub_le hu0 huHalf
  change 1 ≤ 1 / (2 - r * z) ∧
    1 / (2 - r * z) ≤ 1 + (2 * (K + 4)) * epsilon ∧ r * z < 2
  refine ⟨?_, ?_, hprodTwo⟩
  · apply (le_div_iff₀ hden).2
    linarith
  · calc
      1 / (2 - r * z) = 1 / (1 - (r * z - 1)) := by ring_nf
      _ ≤ 1 + 2 * (r * z - 1) := hinv
      _ ≤ 1 + (2 * (K + 4)) * epsilon := by linarith

/-- Four erased generations have a uniformly small tilt when the one-step
weight is within `epsilon` of one. -/
theorem tiltParameter_four_le
    {r epsilon : ℝ} (hrOne : 1 ≤ r) (hrUpper : r ≤ 1 + 3 * epsilon)
    (hepsilon0 : 0 ≤ epsilon) (hepsilonSmall : epsilon ≤ 1 / 512) :
    (∀ j ≤ 4, 1 ≤ tiltParameter j r ∧
      tiltParameter j r ≤ 1 + 120 * epsilon) ∧
      ∀ j < 4, r * tiltParameter j r < 2 := by
  have h0 : 1 ≤ tiltParameter 0 r := by simp [tiltParameter]
  have hstep0 := tiltParameter_succ_bounds
    (steps := 0) (K := 0) hrOne hrUpper hepsilon0 (by norm_num) h0
    (by simp [tiltParameter]) (by norm_num)
    (by nlinarith)
  have hstep1 := tiltParameter_succ_bounds
    (steps := 1) (K := 8) hrOne hrUpper hepsilon0 (by norm_num)
    hstep0.1 (by nlinarith [hstep0.2.1])
    (by nlinarith) (by nlinarith)
  have hstep2 := tiltParameter_succ_bounds
    (steps := 2) (K := 24) hrOne hrUpper hepsilon0 (by norm_num)
    hstep1.1 (by nlinarith [hstep1.2.1])
    (by nlinarith) (by nlinarith)
  have hstep3 := tiltParameter_succ_bounds
    (steps := 3) (K := 56) hrOne hrUpper hepsilon0 (by norm_num)
    hstep2.1 (by nlinarith [hstep2.2.1])
    (by nlinarith) (by nlinarith)
  constructor
  · intro j hj
    interval_cases j
    · exact ⟨h0, by simp [tiltParameter]; nlinarith⟩
    · exact ⟨hstep0.1, by nlinarith [hstep0.2.1]⟩
    · exact ⟨hstep1.1, by nlinarith [hstep1.2.1]⟩
    · exact ⟨hstep2.1, by nlinarith [hstep2.2.1]⟩
    · exact ⟨hstep3.1, by nlinarith [hstep3.2.1]⟩
  · intro j hj
    interval_cases j
    · exact hstep0.2.2
    · exact hstep1.2.2
    · exact hstep2.2.2
    · exact hstep3.2.2

/-- The exact cutoff tilt over any at-most-four-coordinate block is bounded
by one fixed constant once the terminal scale is at least five and the
incoming count has the natural parabolic size. -/
theorem tiltedPathMass_exactCutoff_le_exp_threeSixty
    {n steps a : ℕ} (hn : 5 ≤ n) (hsteps : steps ≤ 4)
    (ha : (a : ℝ) ≤ 3 * (n : ℝ) ^ 2) :
    tiltedPathMass steps ((1 + 1 / (n : ℝ) ^ 4) ^ 2) a ≤
      Real.exp 360 := by
  let epsilon : ℝ := 1 / (n : ℝ) ^ 4
  let r : ℝ := (1 + epsilon) ^ 2
  have hn0 : (0 : ℝ) < n := by positivity
  have hepsilon0 : 0 ≤ epsilon := by dsimp [epsilon]; positivity
  have hepsilonOne : epsilon ≤ 1 := by
    dsimp only [epsilon]
    have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 1)]
    simpa using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnPow)
  have hepsilonSmall : epsilon ≤ 1 / 512 := by
    dsimp only [epsilon]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 4)
      (by norm_num : (0 : ℝ) < 512)]
    have hnReal : (5 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hnReal 4]
  have hrOne : 1 ≤ r := by
    dsimp only [r]
    nlinarith [sq_nonneg epsilon]
  have hrUpper : r ≤ 1 + 3 * epsilon := by
    dsimp only [r]
    nlinarith [mul_le_mul_of_nonneg_left hepsilonOne hepsilon0]
  have hparameter := tiltParameter_four_le hrOne hrUpper
    hepsilon0 hepsilonSmall
  have hconv : ∀ j < steps, r * tiltParameter j r < 2 := by
    intro j hj
    exact hparameter.2 j (hj.trans_le hsteps)
  have hexact := tiltedPathMass_eq steps r (by positivity) hconv a
  have hz := (hparameter.1 steps hsteps).2
  have hz0 : 0 ≤ tiltParameter steps r :=
    (hparameter.1 steps hsteps).1.trans' (by norm_num)
  have hexpBase : 1 + 120 * epsilon ≤ Real.exp (120 * epsilon) := by
    simpa only [add_comm] using Real.add_one_le_exp (120 * epsilon)
  have hpow : tiltParameter steps r ^ a ≤
      Real.exp (120 * epsilon) ^ a :=
    pow_le_pow_left₀ hz0 (hz.trans hexpBase) a
  have hea : 120 * epsilon * (a : ℝ) ≤ 360 := by
    have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hnSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have heq : epsilon * (n : ℝ) ^ 2 = 1 / (n : ℝ) ^ 2 := by
      dsimp only [epsilon]
      field_simp
    have hinv : 1 / (n : ℝ) ^ 2 ≤ (1 : ℝ) := by
      simpa using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnSq)
    calc
      120 * epsilon * (a : ℝ) ≤
          120 * epsilon * (3 * (n : ℝ) ^ 2) := by gcongr
      _ = 360 * (1 / (n : ℝ) ^ 2) := by rw [← heq]; ring
      _ ≤ 360 * 1 := by gcongr
      _ = 360 := by ring
  change tiltedPathMass steps r a ≤ Real.exp 360
  rw [hexact]
  calc
    tiltParameter steps r ^ a ≤ Real.exp (120 * epsilon) ^ a := hpow
    _ = Real.exp (120 * epsilon * (a : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp 360 := Real.exp_le_exp.mpr hea

/-- ENNReal sequence-sum form of the four-coordinate cutoff estimate. -/
theorem tsum_tiltedPathWeightENNReal_exactCutoff_le_exp_threeSixty
    {n steps a : ℕ} (hn : 5 ≤ n) (hsteps : steps ≤ 4)
    (ha : (a : ℝ) ≤ 3 * (n : ℝ) ^ 2) :
    (∑' path : Fin steps → ℕ,
        tiltedPathWeightENNReal steps
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2) a path) ≤
      ENNReal.ofReal (Real.exp 360) := by
  let epsilon : ℝ := 1 / (n : ℝ) ^ 4
  let r : ℝ := (1 + epsilon) ^ 2
  have hepsilon0 : 0 ≤ epsilon := by dsimp [epsilon]; positivity
  have hepsilonOne : epsilon ≤ 1 := by
    dsimp only [epsilon]
    have hnOne : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show 1 ≤ n by omega)
    have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 1)]
    simpa using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnPow)
  have hepsilonSmall : epsilon ≤ 1 / 512 := by
    dsimp only [epsilon]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 4)
      (by norm_num : (0 : ℝ) < 512)]
    have hnReal : (5 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hnReal 4]
  have hrOne : 1 ≤ r := by
    dsimp only [r]
    nlinarith [sq_nonneg epsilon]
  have hrUpper : r ≤ 1 + 3 * epsilon := by
    dsimp only [r]
    nlinarith [mul_le_mul_of_nonneg_left hepsilonOne hepsilon0]
  have hparameter := tiltParameter_four_le hrOne hrUpper
    hepsilon0 hepsilonSmall
  have hconv : ∀ j < steps, r * tiltParameter j r < 2 := by
    intro j hj
    exact hparameter.2 j (hj.trans_le hsteps)
  have heq := tsum_tiltedPathWeightENNReal_eq steps r
    (by positivity) hconv a
  change (∑' path : Fin steps → ℕ,
      tiltedPathWeightENNReal steps r a path) ≤ _
  rw [heq]
  exact ENNReal.ofReal_le_ofReal
    (tiltedPathMass_exactCutoff_le_exp_threeSixty hn hsteps ha)

end

end Erdos1165.TiltedProfileTransitionBridge
