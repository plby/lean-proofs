/- leanprover/lean4:v4.33.0 -/
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

import ErdosProblems.Erdos721.HunterFourierCutoff
import Mathlib.Data.Nat.Choose.Sum

/-!
# An explicit finite Fourier cutoff for Hunter's torus argument

The one-dimensional kernel is the centered binomial Laurent polynomial
obtained from `(1 + z)^(2m)`.  Its coefficients are nonnegative, its
constant coefficient is one, its total coefficient mass is at most
`2m + 1`, and its value has Gaussian decay away from zero.  Taking products
over the coordinates and replacing the product kernel `G` by `2G - 1`
gives the cutoff required by the quantitative orbit lemma.
-/

namespace Erdos721.HunterKernel

open scoped BigOperators ComplexConjugate

noncomputable def centralChoose (m : ℕ) : ℝ :=
  (Nat.choose (2 * m) m : ℝ)

noncomputable def oneDCoeff (m : ℕ) (a : Fin (2 * m + 1)) : ℝ :=
  (Nat.choose (2 * m) a.val : ℝ) / centralChoose m

noncomputable def oneDKernel (m : ℕ) (x : AddCircle (1 : ℝ)) : ℝ :=
  Complex.normSq (1 + fourier 1 x) ^ m / centralChoose m

lemma centralChoose_pos (m : ℕ) : 0 < centralChoose m := by
  unfold centralChoose
  exact_mod_cast Nat.choose_pos (by omega : m ≤ 2 * m)

lemma oneDCoeff_nonneg (m : ℕ) (a : Fin (2 * m + 1)) :
    0 ≤ oneDCoeff m a := by
  exact div_nonneg (by positivity) (centralChoose_pos m).le

lemma oneDCoeff_middle (m : ℕ) :
    oneDCoeff m ⟨m, by omega⟩ = 1 := by
  rw [oneDCoeff]
  change (Nat.choose (2 * m) m : ℝ) / centralChoose m = 1
  rw [div_eq_one_iff_eq (centralChoose_pos m).ne']
  rfl

lemma centered_binomial_expansion (m : ℕ) (z : ℂ) (hz : z ≠ 0) :
    (∑ a : Fin (2 * m + 1), ((Nat.choose (2 * m) a.val : ℕ) : ℂ) *
        z ^ ((a.val : ℤ) - (m : ℤ))) =
      z ^ (-(m : ℤ)) * (1 + z) ^ (2 * m) := by
  rw [show (∑ a : Fin (2 * m + 1), ((Nat.choose (2 * m) a.val : ℕ) : ℂ) *
        z ^ ((a.val : ℤ) - (m : ℤ))) =
      ∑ a ∈ Finset.range (2 * m + 1), ((Nat.choose (2 * m) a : ℕ) : ℂ) *
        z ^ ((a : ℤ) - (m : ℤ)) by
          simpa using Fin.sum_univ_eq_sum_range
            (fun a : ℕ => ((Nat.choose (2 * m) a : ℕ) : ℂ) *
              z ^ ((a : ℤ) - (m : ℤ))) (2 * m + 1)]
  rw [add_comm 1 z, add_pow]
  rw [Finset.mul_sum]
  simp only [one_pow, mul_one]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_range] at ha
  have ha' : a ≤ 2 * m := by omega
  rw [zpow_sub₀ hz]
  simp only [zpow_natCast]
  simp only [zpow_neg, zpow_natCast, div_eq_mul_inv]
  ring

lemma inv_mul_one_add_sq_eq_normSq {z : ℂ} (hz : ‖z‖ = 1) :
    z⁻¹ * (1 + z) ^ 2 = (Complex.normSq (1 + z) : ℂ) := by
  have hzinv : z⁻¹ = conj z := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
    norm_num
  rw [hzinv, Complex.normSq_eq_conj_mul_self]
  rw [map_add]
  simp only [map_one]
  have hunit : conj z * z = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
    norm_num
  rw [pow_two]
  calc
    conj z * ((1 + z) * (1 + z)) =
        (conj z * (1 + z)) * (1 + z) := by ring
    _ = ((1 + conj z) * (1 + z)) := by
      rw [show conj z * (1 + z) = conj z + conj z * z by ring, hunit]
      ring

lemma fourier_eq_zpow (n : ℤ) (x : AddCircle (1 : ℝ)) :
    fourier n x = fourier 1 x ^ n := by
  simp [fourier_apply, AddCircle.toCircle_zsmul]

lemma oneDKernel_expansion (m : ℕ) (x : AddCircle (1 : ℝ)) :
    (oneDKernel m x : ℂ) =
      ∑ a : Fin (2 * m + 1), (oneDCoeff m a : ℂ) *
        fourier ((a.val : ℤ) - (m : ℤ)) x := by
  let z : ℂ := fourier 1 x
  have hzNorm : ‖z‖ = 1 := by
    simp [z, fourier_apply, Circle.norm_coe]
  have hz : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzNorm]; norm_num)
  have hbin := centered_binomial_expansion m z hz
  have hbase := inv_mul_one_add_sq_eq_normSq hzNorm
  calc
    (oneDKernel m x : ℂ) =
        (Complex.normSq (1 + z) : ℂ) ^ m *
          ((centralChoose m : ℝ) : ℂ)⁻¹ := by
      simp [oneDKernel, z, div_eq_mul_inv]
    _ = (z ^ (-(m : ℤ)) * (1 + z) ^ (2 * m)) *
          ((centralChoose m : ℝ) : ℂ)⁻¹ := by
      congr 1
      rw [← hbase, mul_pow]
      change (z⁻¹) ^ m * ((1 + z) ^ 2) ^ m =
        z ^ (-(m : ℤ)) * (1 + z) ^ (2 * m)
      rw [inv_pow, ← zpow_natCast, ← zpow_neg, pow_mul]
    _ = (∑ a : Fin (2 * m + 1),
          ((Nat.choose (2 * m) a.val : ℕ) : ℂ) *
            z ^ ((a.val : ℤ) - (m : ℤ))) *
          ((centralChoose m : ℝ) : ℂ)⁻¹ := by rw [hbin]
    _ = ∑ a : Fin (2 * m + 1), (oneDCoeff m a : ℂ) *
          fourier ((a.val : ℤ) - (m : ℤ)) x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [fourier_eq_zpow]
      simp only [oneDCoeff, div_eq_mul_inv]
      dsimp [z]
      push_cast
      ring

lemma sum_oneDCoeff_le (m : ℕ) :
    ∑ a : Fin (2 * m + 1), oneDCoeff m a ≤ 2 * m + 1 := by
  rw [show (∑ a : Fin (2 * m + 1), oneDCoeff m a) =
      (4 : ℝ) ^ m / centralChoose m by
    simp only [oneDCoeff, ← Finset.sum_div]
    congr 1
    rw [show (∑ a : Fin (2 * m + 1), (Nat.choose (2 * m) a.val : ℝ)) =
        ((∑ a ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) a : ℕ) : ℝ) by
      simp only [Nat.cast_sum]
      simpa using Fin.sum_univ_eq_sum_range
        (fun a : ℕ => (Nat.choose (2 * m) a : ℝ)) (2 * m + 1)]
    rw [Nat.sum_range_choose]
    norm_num [pow_mul]]
  rw [div_le_iff₀ (centralChoose_pos m)]
  unfold centralChoose
  norm_cast
  exact Nat.four_pow_le_two_mul_add_one_mul_central_binom m

lemma normSq_one_add_add_normSq_one_sub {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.normSq (1 + z) + Complex.normSq (1 - z) = 4 := by
  rw [Complex.normSq_add, Complex.normSq_sub]
  simp only [Complex.normSq_one, Complex.normSq_eq_norm_sq, hz, one_pow,
    one_mul, map_one]
  ring

lemma normSq_one_add_fourier_le (x : AddCircle (1 : ℝ)) :
    Complex.normSq (1 + fourier 1 x) ≤ 4 - 16 * ‖x‖ ^ 2 := by
  let z : ℂ := fourier 1 x
  have hzNorm : ‖z‖ = 1 := by
    simp [z, fourier_apply, Circle.norm_coe]
  have hchord : 4 * ‖x‖ ≤ ‖1 - z‖ := by
    exact Erdos721.HunterFourierCutoff.four_norm_le_norm_one_sub_fourier x
  have hsquare : 16 * ‖x‖ ^ 2 ≤ ‖1 - z‖ ^ 2 := by
    nlinarith [norm_nonneg (1 - z), norm_nonneg x]
  have hsum := normSq_one_add_add_normSq_one_sub hzNorm
  simp only [Complex.normSq_eq_norm_sq] at hsum
  dsimp [z] at hsum hsquare ⊢
  rw [Complex.normSq_eq_norm_sq]
  nlinarith

lemma four_mul_one_sub_nonneg (x : AddCircle (1 : ℝ)) :
    0 ≤ 4 * (1 - 4 * ‖x‖ ^ 2) := by
  have hx : ‖x‖ ≤ 1 / 2 := by
    rw [← Erdos721.HunterPhase.abs_centeredCoord_eq_norm]
    exact Erdos721.HunterTorus.abs_centeredCoord_le_half x
  have hx0 := norm_nonneg x
  nlinarith

lemma oneDKernel_le_geometric (m : ℕ) (x : AddCircle (1 : ℝ)) :
    oneDKernel m x ≤ (2 * m + 1) * (1 - 4 * ‖x‖ ^ 2) ^ m := by
  have hq0 : 0 ≤ Complex.normSq (1 + fourier 1 x) :=
    Complex.normSq_nonneg _
  have hb0 : 0 ≤ 4 * (1 - 4 * ‖x‖ ^ 2) := four_mul_one_sub_nonneg x
  have hq : Complex.normSq (1 + fourier 1 x) ≤
      4 * (1 - 4 * ‖x‖ ^ 2) := by
    convert normSq_one_add_fourier_le x using 1 <;> ring
  have hpow := pow_le_pow_left₀ hq0 hq m
  have hcentral : (4 : ℝ) ^ m ≤ (2 * m + 1) * centralChoose m := by
    unfold centralChoose
    norm_cast
    exact Nat.four_pow_le_two_mul_add_one_mul_central_binom m
  rw [oneDKernel, div_le_iff₀ (centralChoose_pos m)]
  calc
    Complex.normSq (1 + fourier 1 x) ^ m ≤
        (4 * (1 - 4 * ‖x‖ ^ 2)) ^ m := hpow
    _ = (4 : ℝ) ^ m * (1 - 4 * ‖x‖ ^ 2) ^ m := by rw [mul_pow]
    _ ≤ ((2 * m + 1) * centralChoose m) *
          (1 - 4 * ‖x‖ ^ 2) ^ m := by
      exact mul_le_mul_of_nonneg_right hcentral (pow_nonneg (by nlinarith [hb0]) _)
    _ = ((2 * m + 1) * (1 - 4 * ‖x‖ ^ 2) ^ m) * centralChoose m := by ring

lemma oneDKernel_le_exp (m : ℕ) (x : AddCircle (1 : ℝ)) :
    oneDKernel m x ≤ (2 * m + 1) *
      Real.exp (-4 * m * ‖x‖ ^ 2) := by
  refine (oneDKernel_le_geometric m x).trans ?_
  have hbase : 1 - 4 * ‖x‖ ^ 2 ≤ Real.exp (-4 * ‖x‖ ^ 2) := by
    convert Real.add_one_le_exp (-4 * ‖x‖ ^ 2) using 1 <;> ring
  have hbase0 : 0 ≤ 1 - 4 * ‖x‖ ^ 2 := by
    have := four_mul_one_sub_nonneg x
    nlinarith
  have hpow := pow_le_pow_left₀ hbase0 hbase m
  calc
    (2 * m + 1) * (1 - 4 * ‖x‖ ^ 2) ^ m ≤
        (2 * m + 1) * (Real.exp (-4 * ‖x‖ ^ 2)) ^ m := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 * m + 1) * Real.exp (-4 * m * ‖x‖ ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

open Erdos721.HunterTorus Erdos721.HunterDistributedCenters
  Erdos721.HunterDiophantine Erdos721.HunterFourierCutoff

noncomputable def kernelCoeff (D m : ℕ) (a : FrequencyCode D m) : ℝ :=
  ∏ i, oneDCoeff m (a i)

noncomputable def kernelValue (D m : ℕ) (x : Torus D) : ℝ :=
  ∏ i, oneDKernel m (x i)

lemma torusCharacter_eq_prod_fourier {D : ℕ} (xi : Fin D → ℤ)
    (x : Torus D) :
    torusCharacter xi x = ∏ i, fourier (xi i) (x i) := by
  simp only [torusCharacter, integerDot, fourier_apply]
  classical
  have hsum (s : Finset (Fin D)) :
      AddCircle.toCircle (∑ i ∈ s, xi i • x i) =
        ∏ i ∈ s, (AddCircle.toCircle (xi i • x i) : ℂ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha]
        calc
          (AddCircle.toCircle (xi a • x a + ∑ i ∈ s, xi i • x i) : ℂ) =
              (AddCircle.toCircle (xi a • x a) : ℂ) *
                (AddCircle.toCircle (∑ i ∈ s, xi i • x i) : ℂ) := by
            rw [AddCircle.toCircle_add, Circle.coe_mul]
          _ = (AddCircle.toCircle (xi a • x a) : ℂ) *
                ∏ i ∈ s, (AddCircle.toCircle (xi i • x i) : ℂ) := by rw [ih]
  simpa using hsum Finset.univ

lemma kernelValue_expansion (D m : ℕ) (x : Torus D) :
    (kernelValue D m x : ℂ) =
      ∑ a : FrequencyCode D m, (kernelCoeff D m a : ℂ) *
        torusCharacter (decodeFrequency a) x := by
  rw [kernelValue]
  push_cast
  simp_rw [oneDKernel_expansion]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [kernelCoeff, torusCharacter_eq_prod_fourier]
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  rfl

lemma kernelCoeff_nonneg (D m : ℕ) (a : FrequencyCode D m) :
    0 ≤ kernelCoeff D m a := by
  exact Finset.prod_nonneg fun i _hi => oneDCoeff_nonneg m (a i)

lemma kernelCoeff_zero (D m : ℕ) :
    kernelCoeff D m (zeroFrequencyCode D m) = 1 := by
  simp [kernelCoeff, zeroFrequencyCode, oneDCoeff_middle]

lemma sum_kernelCoeff_le (D m : ℕ) :
    ∑ a : FrequencyCode D m, kernelCoeff D m a ≤ (2 * m + 1) ^ D := by
  rw [show (∑ a : FrequencyCode D m, kernelCoeff D m a) =
      ∏ _i : Fin D, ∑ a : Fin (2 * m + 1), oneDCoeff m a by
    rw [Fintype.prod_sum]
    rfl]
  calc
    (∏ _i : Fin D, ∑ a : Fin (2 * m + 1), oneDCoeff m a) ≤
        ∏ _i : Fin D, (2 * m + 1 : ℝ) := by
      exact Finset.prod_le_prod
        (fun i _hi => Finset.sum_nonneg fun a _ha => oneDCoeff_nonneg m a)
        (fun i _hi => sum_oneDCoeff_le m)
    _ = (2 * m + 1) ^ D := by simp

noncomputable def cutoffCoeff (D m : ℕ) (a : FrequencyCode D m) : ℝ :=
  2 * kernelCoeff D m a - if a = zeroFrequencyCode D m then 1 else 0

noncomputable def cutoffValue (D m : ℕ) (x : Torus D) : ℝ :=
  2 * kernelValue D m x - 1

lemma cutoffCoeff_nonneg (D m : ℕ) (a : FrequencyCode D m) :
    0 ≤ cutoffCoeff D m a := by
  classical
  by_cases ha : a = zeroFrequencyCode D m
  · subst a
    simp [cutoffCoeff, kernelCoeff_zero]
  · simp [cutoffCoeff, ha, kernelCoeff_nonneg]

lemma cutoffCoeff_zero (D m : ℕ) :
    cutoffCoeff D m (zeroFrequencyCode D m) = 1 := by
  norm_num [cutoffCoeff, kernelCoeff_zero]

lemma cutoffValue_expansion (D m : ℕ) (x : Torus D) :
    (cutoffValue D m x : ℂ) =
      ∑ a : FrequencyCode D m, (cutoffCoeff D m a : ℂ) *
        torusCharacter (decodeFrequency a) x := by
  classical
  rw [cutoffValue]
  push_cast
  rw [kernelValue_expansion]
  simp only [cutoffCoeff]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ a : FrequencyCode D m,
        (2 : ℂ) * (kernelCoeff D m a : ℂ) *
          torusCharacter (decodeFrequency a) x) =
      2 * ∑ a : FrequencyCode D m, (kernelCoeff D m a : ℂ) *
          torusCharacter (decodeFrequency a) x by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    ring]
  have hdelta :
      (∑ a : FrequencyCode D m,
        (((if a = zeroFrequencyCode D m then 1 else 0 : ℝ) : ℂ)) *
          torusCharacter (decodeFrequency a) x) = 1 := by
    calc
      _ = ∑ a : FrequencyCode D m,
          if a = zeroFrequencyCode D m then
            torusCharacter (decodeFrequency a) x else 0 := by
        apply Finset.sum_congr rfl
        intro a _ha
        by_cases ha : a = zeroFrequencyCode D m <;> simp [ha]
      _ = 1 := by simp [torusCharacter_zero_frequency]
  rw [hdelta]

lemma sum_cutoffCoeff_le (D m : ℕ) :
    ∑ a : FrequencyCode D m, cutoffCoeff D m a ≤
      2 * (2 * m + 1) ^ D := by
  classical
  have hsum0 : 0 ≤ ∑ a : FrequencyCode D m, kernelCoeff D m a :=
    Finset.sum_nonneg fun a _ha => kernelCoeff_nonneg D m a
  calc
    ∑ a : FrequencyCode D m, cutoffCoeff D m a =
        2 * (∑ a : FrequencyCode D m, kernelCoeff D m a) - 1 := by
      simp only [cutoffCoeff, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
    _ ≤ 2 * (∑ a : FrequencyCode D m, kernelCoeff D m a) := by linarith
    _ ≤ 2 * (2 * m + 1) ^ D := by
      exact mul_le_mul_of_nonneg_left (sum_kernelCoeff_le D m) (by norm_num)

lemma oneDKernel_nonneg (m : ℕ) (x : AddCircle (1 : ℝ)) :
    0 ≤ oneDKernel m x := by
  exact div_nonneg (pow_nonneg (Complex.normSq_nonneg _) _)
    (centralChoose_pos m).le

lemma oneDKernel_le_base (m : ℕ) (x : AddCircle (1 : ℝ)) :
    oneDKernel m x ≤ 2 * m + 1 := by
  refine (oneDKernel_le_exp m x).trans ?_
  have hexp : Real.exp (-4 * m * ‖x‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hx0 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
    nlinarith
  nlinarith [show (0 : ℝ) ≤ 2 * m + 1 by positivity]

lemma kernelValue_le_outside {D m : ℕ} {radius : ℝ} (hradius : 0 ≤ radius)
    {x : Torus D} (hx : x ∉ centeredBox D radius) :
    kernelValue D m x ≤ (2 * m + 1) ^ D *
      Real.exp (-4 * m * radius ^ 2) := by
  classical
  have hexists : ∃ i : Fin D, radius < ‖x i‖ := by
    simp only [centeredBox, Set.mem_pi, Set.mem_univ, forall_const,
      Metric.mem_closedBall, dist_zero_right, not_forall, not_le] at hx
    exact hx
  obtain ⟨i, hi⟩ := hexists
  have hisquare : radius ^ 2 < ‖x i‖ ^ 2 := by
    nlinarith [norm_nonneg (x i)]
  have hexple : Real.exp (-4 * m * ‖x i‖ ^ 2) ≤
      Real.exp (-4 * m * radius ^ 2) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hspecial : oneDKernel m (x i) ≤
      (2 * m + 1) * Real.exp (-4 * m * radius ^ 2) :=
    (oneDKernel_le_exp m (x i)).trans
      (mul_le_mul_of_nonneg_left hexple (by positivity))
  rw [kernelValue]
  calc
    (∏ j : Fin D, oneDKernel m (x j)) ≤
        ∏ j : Fin D, (2 * m + 1) *
          (if j = i then Real.exp (-4 * m * radius ^ 2) else 1) := by
      apply Finset.prod_le_prod
      · intro j _hj
        exact oneDKernel_nonneg m (x j)
      · intro j _hj
        by_cases hji : j = i
        · subst j
          simpa using hspecial
        · simp [hji, oneDKernel_le_base]
    _ = (2 * m + 1) ^ D * Real.exp (-4 * m * radius ^ 2) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- The normalized product binomial kernel, shifted by `-1`, is a concrete
finite Fourier cutoff whenever its Gaussian tail is at most one half. -/
noncomputable def binomialFourierCutoff (D m : ℕ) (radius : ℝ)
    (hradius : 0 ≤ radius)
    (hdecay : 2 * (2 * m + 1) ^ D *
      Real.exp (-4 * m * radius ^ 2) ≤ 1) :
    FourierCutoff D m radius (2 * (2 * m + 1) ^ D) where
  coeff := cutoffCoeff D m
  value := cutoffValue D m
  coeff_nonneg := cutoffCoeff_nonneg D m
  coeff_zero := cutoffCoeff_zero D m
  expansion := cutoffValue_expansion D m
  nonpos_outside := by
    intro x hx
    have hkernel := kernelValue_le_outside (m := m) hradius hx
    rw [cutoffValue]
    nlinarith
  coeff_sum_le := sum_cutoffCoeff_le D m

end Erdos721.HunterKernel
