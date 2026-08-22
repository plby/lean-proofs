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

import ErdosProblems.Erdos1165.BufferedStoppedSuccessfulPointEvent
import ErdosProblems.Erdos1165.AnnularIntegratedProfileKernel
import ErdosProblems.Erdos1165.TiltedProfileTransitionBridge

/-!
# Scalar cost of a buffered exact profile

The exact radial-word cutoff is split into a uniformly bounded retained
factor and an exponential tilt on the erased coordinates.  The latter is
the finite branching-chain moment evaluated in
`TiltedProfileTransitionBridge`.
-/

open scoped BigOperators

namespace Erdos1165.BufferedProfileCostUpper

open AppendixFirstMoment AnnularRadialProfileWords
open AnnularIntegratedProfileKernel
open BufferedStoppedSuccessfulPointEvent BufferedSuccessfulProfile

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Replace every erased internal coordinate by its parabolic centre. -/
def fillBufferedProfile {n : ℕ} (low high : ℕ) (m : Profile n) : Profile n :=
  fun i ↦ if RetainedCoordinate low high (scaleIndex i) then
    m i else profileCenter (scaleIndex i)

@[simp] lemma fillBufferedProfile_apply_retained
    {n low high : ℕ} (m : Profile n) (i : Fin (n - 1))
    (hi : RetainedCoordinate low high (scaleIndex i)) :
    fillBufferedProfile low high m i = m i := by
  simp [fillBufferedProfile, hi]

@[simp] lemma fillBufferedProfile_apply_erased
    {n low high : ℕ} (m : Profile n) (i : Fin (n - 1))
    (hi : ¬ RetainedCoordinate low high (scaleIndex i)) :
    fillBufferedProfile low high m i = profileCenter (scaleIndex i) := by
  simp [fillBufferedProfile, hi]

lemma fillBufferedProfile_isConstrained
    {n low high : ℕ} {delta : ℝ} {m : Profile n}
    (hm : IsBufferedInternalProfile low high delta m) :
    IsConstrainedProfile delta (fillBufferedProfile low high m) := by
  intro i
  by_cases hi : RetainedCoordinate low high (scaleIndex i)
  · rw [fillBufferedProfile_apply_retained m i hi]
    simpa [InProfileWindow, profileCenter] using hm i hi
  · rw [fillBufferedProfile_apply_erased m i hi, InProfileWindow]
    simp only [Nat.cast_ofNat, sub_self, abs_zero]
    exact Real.rpow_nonneg (by positivity) _

/-- Sum of the exact profile coordinates which survive the buffer. -/
def retainedProfileSum {n : ℕ} (low high : ℕ) (m : Profile n) : ℕ :=
  ∑ i ∈ Finset.univ.filter
      (fun i : Fin (n - 1) ↦ RetainedCoordinate low high (scaleIndex i)), m i

/-- Sum of the exact coordinates in the erased interval. -/
def erasedProfileSum {n : ℕ} (low high : ℕ) (m : Profile n) : ℕ :=
  ∑ i ∈ Finset.univ.filter
      (fun i : Fin (n - 1) ↦ ¬ RetainedCoordinate low high (scaleIndex i)), m i

lemma profileList_sum_eq_retained_add_erased
    {n low high : ℕ} (m : Profile n) :
    (profileList m).sum =
      retainedProfileSum low high m + erasedProfileSum low high m := by
  rw [profileList, List.sum_ofFn]
  unfold retainedProfileSum erasedProfileSum
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ)
    (p := fun i : Fin (n - 1) ↦ RetainedCoordinate low high (scaleIndex i))]

lemma profileList_sum_le_three_mul_cube
    {n : ℕ} {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    (profileList m).sum ≤ 3 * n ^ 3 := by
  have hentry : ∀ a ∈ profileList m, a ≤ 3 * n ^ 2 := by
    rw [profileList, List.forall_mem_ofFn_iff]
    exact constrainedProfile_entry_le_three_mul_n_sq hdelta hm
  have hsum := List.sum_le_card_nsmul (profileList m) (3 * n ^ 2) hentry
  have hlength : (profileList m).length = n - 1 := by simp [profileList]
  calc
    (profileList m).sum ≤ (n - 1) * (3 * n ^ 2) := by
      simpa [hlength, nsmul_eq_mul] using hsum
    _ ≤ n * (3 * n ^ 2) :=
      Nat.mul_le_mul_right (3 * n ^ 2) (Nat.sub_le n 1)
    _ = 3 * n ^ 3 := by ring

lemma retainedProfileSum_le_three_mul_cube
    {n low high : ℕ} {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsBufferedInternalProfile low high delta m) :
    retainedProfileSum low high m ≤ 3 * n ^ 3 := by
  let q := fillBufferedProfile low high m
  have hq : IsConstrainedProfile delta q := fillBufferedProfile_isConstrained hm
  have heq : retainedProfileSum low high m = retainedProfileSum low high q := by
    unfold retainedProfileSum
    apply Finset.sum_congr rfl
    intro i hi
    exact (fillBufferedProfile_apply_retained m i
      (Finset.mem_filter.mp hi).2).symm
  rw [heq]
  exact (show retainedProfileSum low high q ≤ (profileList q).sum by
    rw [profileList, List.sum_ofFn]
    unfold retainedProfileSum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ ↦ Nat.zero_le _)).trans
    (profileList_sum_le_three_mul_cube hdelta hq)

/-- The part of the exact word cutoff depending only on retained
coordinates costs at most `exp 9`. -/
theorem retained_exactCutoffFactor_le_exp_nine
    {n low high : ℕ} (hn : 5 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsBufferedInternalProfile low high delta m) :
    (1 + 1 / (n : ℝ) ^ 4) ^
        (2 * (retainedProfileSum low high m + n ^ 3) + 1) ≤
      Real.exp 9 := by
  let epsilon : ℝ := 1 / (n : ℝ) ^ 4
  let common : ℝ := 1 + epsilon
  let L : ℕ := 2 * (retainedProfileSum low high m + n ^ 3) + 1
  have hn0 : (0 : ℝ) < n := by positivity
  have hepsilon0 : 0 ≤ epsilon := by dsimp [epsilon]; positivity
  have hcommon0 : 0 ≤ common := by dsimp [common]; positivity
  have hcommonExp : common ≤ Real.exp epsilon := by
    dsimp only [common]
    simpa only [add_comm] using Real.add_one_le_exp epsilon
  have hL : L ≤ 8 * n ^ 3 + 1 := by
    dsimp only [L]
    have hsum := retainedProfileSum_le_three_mul_cube hdelta hm
    omega
  have heL : epsilon * (L : ℝ) ≤ 9 := by
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hcast : (L : ℝ) ≤ 8 * (n : ℝ) ^ 3 + 1 := by exact_mod_cast hL
    have hinv : 1 / (n : ℝ) ≤ 1 := by
      simpa using one_div_le_one_div_of_le
        (by norm_num : (0 : ℝ) < 1) hnOne
    have hinv4 : 1 / (n : ℝ) ^ 4 ≤ 1 := by
      have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
        nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 1)]
      simpa using one_div_le_one_div_of_le
        (by norm_num : (0 : ℝ) < 1) hnPow
    calc
      epsilon * (L : ℝ) ≤
          (1 / (n : ℝ) ^ 4) * (8 * (n : ℝ) ^ 3 + 1) := by
        dsimp only [epsilon]
        gcongr
      _ = 8 * (1 / (n : ℝ)) + 1 / (n : ℝ) ^ 4 := by
        field_simp
      _ ≤ 8 * 1 + 1 := by gcongr
      _ = 9 := by ring
  change common ^ L ≤ Real.exp 9
  calc
    common ^ L ≤ Real.exp epsilon ^ L :=
      pow_le_pow_left₀ hcommon0 hcommonExp L
    _ = Real.exp (epsilon * (L : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp 9 := Real.exp_le_exp.mpr heL

lemma exactCutoffFactor_eq_retained_mul_erased
    {n low high : ℕ} (m : Profile n) :
    (1 + 1 / (n : ℝ) ^ 4) ^ exactProfileRadialWordMaxTransitions m =
      (1 + 1 / (n : ℝ) ^ 4) ^
          (2 * (retainedProfileSum low high m + n ^ 3) + 1) *
        ((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
          erasedProfileSum low high m := by
  unfold exactProfileRadialWordMaxTransitions
  rw [profileList_sum_eq_retained_add_erased m]
  rw [show 2 * (retainedProfileSum low high m +
        erasedProfileSum low high m + n ^ 3) + 1 =
      (2 * (retainedProfileSum low high m + n ^ 3) + 1) +
        2 * erasedProfileSum low high m by omega]
  rw [pow_add, ← pow_mul]

end

end Erdos1165.BufferedProfileCostUpper
