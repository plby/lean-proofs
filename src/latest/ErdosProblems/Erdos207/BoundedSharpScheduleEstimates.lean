/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedSharpInitialLaw
import ErdosProblems.Erdos207.RealFloorSchedules

/-!
# Discrete estimates for bounded sharp survival schedules
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

lemma realLinearFloorSchedule_le_initial
    {d₀ i : ℕ} {rate buffer : ℝ}
    (hrate : 0 ≤ rate) (hbuffer : 0 ≤ buffer) :
    realLinearFloorSchedule (d₀ : ℝ) rate buffer i ≤ d₀ := by
  apply realLinearFloorSchedule_le_nat
  push_cast
  nlinarith

lemma boundedSharpSurvivalTheta_mono_of_le
    {M d d₀ K : ℕ} (hdd₀ : d ≤ d₀) :
    boundedSharpSurvivalTheta M d₀ K ≤
      boundedSharpSurvivalTheta M d K := by
  unfold boundedSharpSurvivalTheta
  have hsub : d - K ≤ d₀ - K := Nat.sub_le_sub_right hdd₀ K
  have hnum : M - (d₀ - K) ≤ M - (d - K) := Nat.sub_le_sub_left hsub M
  gcongr

lemma boundedSharpSurvivalSchedule_le_one
    {n M K : ℕ} {d : ℕ → ℕ}
    (hM : 0 < M) :
    ∀ i, boundedSharpSurvivalSchedule n (fun _ ↦ M) d K i ≤ 1 := by
  intro i
  by_cases hi : i < n
  · simpa only [boundedSharpSurvivalSchedule, if_pos hi] using
      boundedSharpSurvivalTheta_le_one M (d i) K hM
  · simp [boundedSharpSurvivalSchedule, if_neg hi]

lemma cumulativeSurvival_boundedSharp_le_one
    {n M K : ℕ} {d : ℕ → ℕ} (hM : 0 < M) :
    cumulativeSurvival
        (boundedSharpSurvivalSchedule n (fun _ ↦ M) d K) n ≤ 1 := by
  unfold cumulativeSurvival
  apply Finset.prod_le_one
  · exact fun _ _ ↦ bot_le
  · intro i _hi
    exact boundedSharpSurvivalSchedule_le_one hM i

lemma cumulativeSurvival_boundedSharp_pos
    {n M d₀ K : ℕ} {d : ℕ → ℕ}
    (heffective : d₀ - K < M)
    (hd : ∀ i, i < n → d i ≤ d₀) :
    0 < cumulativeSurvival
      (boundedSharpSurvivalSchedule n (fun _ ↦ M) d K) n := by
  unfold cumulativeSurvival
  apply Finset.prod_pos
  intro i hi
  have hin : i < n := mem_range.mp hi
  have htheta₀ : 0 < boundedSharpSurvivalTheta M d₀ K :=
    boundedSharpSurvivalTheta_pos M d₀ K heffective
  have hmono := boundedSharpSurvivalTheta_mono_of_le
    (M := M) (K := K) (hd i hin)
  simpa only [boundedSharpSurvivalSchedule, if_pos hin] using
    htheta₀.trans_le hmono

lemma transferPointWeight_boundedSharp_const_le
    {n D M d₀ K N : ℕ} {d : ℕ → ℕ} {C : ℝ≥0}
    (hD : 0 < D) (hM : 0 < M) (hN : 0 < N)
    (heffective : d₀ - K < M)
    (hd : ∀ i, i < n → d i ≤ d₀)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (N + 1 : ℝ≥0)⁻¹)
    (hfactor :
      (boundedSharpSurvivalTheta M d₀ K ^ K)⁻¹ ≤ C) :
    transferPointWeight
        (boundedSharpSurvivalSchedule n (fun _ ↦ M) d K)
        (boundedSharpTransferSchedule n (fun _ ↦ D) (fun _ ↦ M) d K) n ≤
      C * (N : ℝ≥0)⁻¹ := by
  let theta : ℕ → ℝ≥0 :=
    boundedSharpSurvivalSchedule n (fun _ ↦ M) d K
  let rho : ℕ → ℝ≥0 :=
    boundedSharpTransferSchedule n (fun _ ↦ D) (fun _ ↦ M) d K
  have hthetaOne : ∀ i, theta i ≤ 1 :=
    boundedSharpSurvivalSchedule_le_one hM
  have hprefix : ∀ i, cumulativeSurvival theta i ≤ 1 := by
    intro i
    unfold cumulativeSurvival
    apply Finset.prod_le_one
    · exact fun _ _ ↦ bot_le
    · intro j _hj
      exact hthetaOne j
  have htheta₀pos : 0 < boundedSharpSurvivalTheta M d₀ K :=
    boundedSharpSurvivalTheta_pos M d₀ K heffective
  have hrho : ∀ i, i < n → rho i ≤ (D : ℝ≥0)⁻¹ * C := by
    intro i hi
    have hmono : boundedSharpSurvivalTheta M d₀ K ≤
        boundedSharpSurvivalTheta M (d i) K :=
      boundedSharpSurvivalTheta_mono_of_le (hd i hi)
    have hpowmono : boundedSharpSurvivalTheta M d₀ K ^ K ≤
        boundedSharpSurvivalTheta M (d i) K ^ K :=
      pow_le_pow_left' hmono K
    have hpowpos : 0 < boundedSharpSurvivalTheta M d₀ K ^ K := by
      positivity
    have hpowipos : 0 < boundedSharpSurvivalTheta M (d i) K ^ K :=
      hpowpos.trans_le hpowmono
    have hinv : (boundedSharpSurvivalTheta M (d i) K ^ K)⁻¹ ≤
        (boundedSharpSurvivalTheta M d₀ K ^ K)⁻¹ :=
      (inv_le_inv₀ hpowipos hpowpos).mpr hpowmono
    simp only [rho, boundedSharpTransferSchedule, if_pos hi,
      boundedSharpTransferRho]
    exact mul_le_mul_right (hinv.trans hfactor) _
  calc
    transferPointWeight theta rho n =
        ∑ i ∈ range n, rho i * cumulativeSurvival theta i ^ 3 := rfl
    _ ≤ ∑ _i ∈ range n, (D : ℝ≥0)⁻¹ * C := by
      apply sum_le_sum
      intro i hi
      have hin : i < n := mem_range.mp hi
      calc
        rho i * cumulativeSurvival theta i ^ 3 ≤ rho i * 1 := by
          gcongr
          exact pow_le_one₀ bot_le (hprefix i)
        _ ≤ (D : ℝ≥0)⁻¹ * C := by simpa using hrho i hin
    _ = (n : ℝ≥0) * (D : ℝ≥0)⁻¹ * C := by
      simp
      ring
    _ ≤ (N + 1 : ℝ≥0)⁻¹ * C := by gcongr
    _ ≤ (N : ℝ≥0)⁻¹ * C := by
      apply mul_le_mul_left
      exact (inv_le_inv₀ (by positivity : (0 : ℝ≥0) < N + 1)
        (by exact_mod_cast hN : (0 : ℝ≥0) < N)).mpr
          (by exact_mod_cast Nat.le_succ N)
    _ = C * (N : ℝ≥0)⁻¹ := by ring

lemma large_pattern_paid_by_error
    {K m : ℕ} {C b x : ℝ≥0}
    (hm : K < m) (hCb : 1 ≤ C ^ (K + 1) * b) (hC : 1 ≤ C) :
    1 ≤ C ^ m * (x + b) := by
  have hpow : C ^ (K + 1) ≤ C ^ m :=
    pow_le_pow_right' hC (by omega)
  calc
    1 ≤ C ^ (K + 1) * b := hCb
    _ ≤ C ^ m * b := by gcongr
    _ ≤ C ^ m * (x + b) := by gcongr; exact le_add_left le_rfl

/-- Retrospective cancellation in its schedule-independent form.  A cubic
prefix-survival factor cancels a correspondingly small time-dependent
availability denominator.  This is the estimate used in the long initial
phase; unlike `transferPointWeight_boundedSharp_const_le`, it does not replace
all availability floors by their terminal minimum. -/
lemma transferPointWeight_boundedSharp_le_of_cubic_normalized
    {n N K : ℕ} {D M d : ℕ → ℕ} {A B : ℝ≥0}
    (hN : 0 < N) (hn : n ≤ N ^ 2)
    (hfactor : ∀ i, i < n →
      (boundedSharpSurvivalTheta (M i) (d i) K ^ K)⁻¹ ≤ A)
    (hnormalized : ∀ i, i < n →
      (D i : ℝ≥0)⁻¹ *
          cumulativeSurvival
            (boundedSharpSurvivalSchedule n M d K) i ^ 3 ≤
        B * (N : ℝ≥0)⁻¹ ^ 3) :
    transferPointWeight
        (boundedSharpSurvivalSchedule n M d K)
        (boundedSharpTransferSchedule n D M d K) n ≤
      (A * B) * (N : ℝ≥0)⁻¹ := by
  let theta : ℕ → ℝ≥0 := boundedSharpSurvivalSchedule n M d K
  let rho : ℕ → ℝ≥0 := boundedSharpTransferSchedule n D M d K
  calc
    transferPointWeight theta rho n =
        ∑ i ∈ range n, rho i * cumulativeSurvival theta i ^ 3 := rfl
    _ ≤ ∑ _i ∈ range n,
        A * (B * (N : ℝ≥0)⁻¹ ^ 3) := by
      apply sum_le_sum
      intro i hi
      have hin : i < n := mem_range.mp hi
      simp only [rho, boundedSharpTransferSchedule, if_pos hin,
        boundedSharpTransferRho]
      calc
        ((D i : ℝ≥0)⁻¹ *
              (boundedSharpSurvivalTheta (M i) (d i) K ^ K)⁻¹) *
            cumulativeSurvival theta i ^ 3 =
            (boundedSharpSurvivalTheta (M i) (d i) K ^ K)⁻¹ *
              ((D i : ℝ≥0)⁻¹ *
                cumulativeSurvival theta i ^ 3) := by ring
        _ ≤ A * (B * (N : ℝ≥0)⁻¹ ^ 3) := by
          exact mul_le_mul (hfactor i hin)
            (by simpa only [theta] using hnormalized i hin) zero_le zero_le
    _ = (n : ℝ≥0) * (A * (B * (N : ℝ≥0)⁻¹ ^ 3)) := by simp
    _ ≤ ((N : ℝ≥0) ^ 2) *
        (A * (B * (N : ℝ≥0)⁻¹ ^ 3)) := by
      gcongr
      exact_mod_cast hn
    _ = (A * B) * (N : ℝ≥0)⁻¹ := by
      have hN' : (N : ℝ≥0) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp

end

end Erdos207
