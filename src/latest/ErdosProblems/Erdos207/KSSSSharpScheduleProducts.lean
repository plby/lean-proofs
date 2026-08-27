/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPowerSharpSchedule
import ErdosProblems.Erdos207.KSSSSharpAffineEnvelope

/-! # Constant survival and inverse-ambient point bounds for the actual coupled schedules -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem KSSSPowerParameters.sharp_schedule_survival_point
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (hratio : (Fintype.card V : ℝ) / 6 ≤ A / E)
    (hEupper : E ≤ (Fintype.card V : ℝ) ^ 2)
    (hEquadratic : (Fintype.card V : ℝ) ^ 2 ≤ 16 * E) :
    let scale := (Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B
    let d := fun i : ℕ ↦ ksssRoundedPairFloor q a E A scale B i
    let D := fun i : ℕ ↦ ksssRoundedAvailabilityFloor q a E A scale B i
    let M := fun i : ℕ ↦ ksssRoundedAvailabilityCeil q a E A scale B i
    cumulativeSurvival (boundedSharpSurvivalSchedule n M d (3 * t)) n ≤
        2 * Real.toNNReal (ksssEdgeDensity E n) ∧
      transferPointWeight (boundedSharpSurvivalSchedule n M d (3 * t))
        (boundedSharpTransferSchedule n D M d (3 * t)) n ≤
        (1048576 * Real.toNNReal (Real.exp (∑ d ∈ ksssOrders q, coeff d))) *
          (Fintype.card V : ℝ≥0)⁻¹ := by
  let N : ℝ := Fintype.card V
  let scale := N / (t : ℝ) ^ ksssPowerErrorExponent b B
  let d := fun i : ℕ ↦ ksssRoundedPairFloor q a E A scale B i
  let D := fun i : ℕ ↦ ksssRoundedAvailabilityFloor q a E A scale B i
  let M := fun i : ℕ ↦ ksssRoundedAvailabilityCeil q a E A scale B i
  let R := ksssSharpClockEnvelope E t b
  let C : ℝ≥0 := Real.toNNReal (Real.exp (∑ d ∈ ksssOrders q, coeff d))
  let eps : ℝ≥0 := 16 / (t : ℝ≥0) ^ (b + 1)
  have hNpos : 0 < Fintype.card V := by linarith [P.ambient_pos]
  have hNreal : 0 < N := by dsimp only [N]; exact_mod_cast hNpos
  have hEpos : 0 < Real.toNNReal E := Real.toNNReal_pos.mpr P.edge_pos
  have hCpos : 0 < C := Real.toNNReal_pos.mpr (Real.exp_pos _)
  have hCeq : (C : ℝ) = Real.exp (∑ d ∈ ksssOrders q, coeff d) := Real.coe_toNNReal _ (Real.exp_pos _).le
  have hEeq : (Real.toNNReal E : ℝ) = E := Real.coe_toNNReal _ P.edge_pos.le
  have hlocal := fun (i : ℕ) (hi : i ≤ n) ↦ P.sharp_schedule_bounds i (Nat.cast_nonneg _) (P.density_floor i hi) hratio
  have hscalar := fun (i : ℕ) (hi : i ≤ n) ↦ P.scalar_bounds i (Nat.cast_nonneg _) (P.density_floor i hi)
  have henv := ksssSharpClockEnvelope_bounds E t b n P.edge_pos P.scale_large (P.density_floor n le_rfl)
  have htpos : (0 : ℝ≥0) < t := by exact_mod_cast (show 0 < t by linarith [P.scale_large])
  have heps : eps ≤ 1 := by
    apply (div_le_one (pow_pos htpos _)).mpr
    exact_mod_cast (show 16 ≤ t ^ (b + 1) from
      (show 16 ≤ t by linarith [P.scale_large]).trans
        (by simpa only [pow_one] using Nat.pow_le_pow_right (by linarith [P.scale_large] : 0 < t) (by omega : 1 ≤ b + 1)))
  have hclockNN : ∀ i, i ≤ n → 3 * (i : ℝ≥0) ≤ Real.toNNReal E := by
    intro i hi
    rw [← NNReal.coe_le_coe]
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, hEeq] using (hscalar i hi).clock_strict.le
  have hM : ∀ i, i < n → 0 < M i := fun i hi ↦ (hlocal i hi.le).upper_pos
  have hloss : ∀ i, i < n → (R i - R (i + 1)) * (M i : ℝ≥0) ≤ R i * (d i - 3 * t : ℕ) := by
    intro i hi
    rw [show R i - R (i + 1) = 3 * (1 - eps) from henv.decrement i hi]
    calc
      _ ≤ (Real.toNNReal E - 3 * (i : ℝ≥0)) * (d i - 3 * t : ℕ) := by
        rw [← NNReal.coe_le_coe]
        simp only [NNReal.coe_mul, NNReal.coe_sub heps, eps, NNReal.coe_div, NNReal.coe_pow,
          NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_sub (hclockNN i hi.le), hEeq]
        have hclockId : E * ksssEdgeDensity E i = E - 3 * (i : ℝ) := by
          unfold ksssEdgeDensity
          field_simp [P.edge_pos.ne']
        simpa only [hclockId] using (hlocal i hi.le).affine_loss
      _ ≤ _ := mul_le_mul_of_nonneg_right (henv.lower i hi.le) zero_le
  have htheta := boundedSharpSurvivalSchedule_le_nnreal_envelope_ratio M d (3 * t) R hM
    henv.positive henv.decreasing hloss
  have hsurvival := (cumulativeSurvival_le_envelope_ratio
    (boundedSharpSurvivalSchedule n M d (3 * t)) R henv.positive htheta n le_rfl).trans henv.final_ratio
  have hquadratic : (Fintype.card V : ℝ≥0) ^ 2 ≤ 16 * R 0 := by
    rw [show R 0 = Real.toNNReal E from henv.initial, ← NNReal.coe_le_coe]
    simpa only [NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_mul, NNReal.coe_ofNat, hEeq] using hEquadratic
  have hcubic : ∀ i, i < n → (D i : ℝ≥0)⁻¹ * R i ^ 3 ≤ (128 * C) * (Fintype.card V : ℝ≥0) ^ 3 := by
    intro i hi
    let p := Real.toNNReal (ksssEdgeDensity E i)
    let x := Real.toNNReal (ksssPairTrajectory (ksssOrders q) a E A i)
    have hpR := ksssEdgeDensity_pos P.edge_pos (hscalar i hi.le).clock_strict
    have hxR := ksssPairTrajectory_pos (ksssOrders q) a P.edge_pos P.available_pos (hscalar i hi.le).clock_strict
    have hx : 0 < x := Real.toNNReal_pos.mpr hxR
    have hpEq : (p : ℝ) = ksssEdgeDensity E i := Real.coe_toNNReal _ hpR.le
    have hxEq : (x : ℝ) = ksssPairTrajectory (ksssOrders q) a E A i := Real.coe_toNNReal _ hxR.le
    have hDnat : 0 < D i := (hlocal i hi.le).floor_pos
    have hD : 0 < (D i : ℝ≥0) := by exact_mod_cast hDnat
    have hEupperNN : Real.toNNReal E ≤ (Fintype.card V : ℝ≥0) ^ 2 := by
      rw [← NNReal.coe_le_coe]
      simpa only [hEeq, NNReal.coe_pow, NNReal.coe_natCast] using hEupper
    have hpair : (Fintype.card V : ℝ≥0) * p ^ 2 / (2 * C) ≤ x := by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
        NNReal.coe_ofNat, hpEq, hxEq, hCeq]
      have hbound := ksssPairTrajectory_lower_fixed_initial_ratio (ksssOrders q) a coeff E A i N
        (Real.exp (∑ d ∈ ksssOrders q, coeff d)) P.edge_pos hNreal (Real.exp_pos _)
        (Nat.cast_nonneg _) (hscalar i hi.le).clock_strict P.coefficient_nonneg P.coefficient_bound hratio le_rfl
      convert hbound using 1 <;> dsimp only [N] <;> ring
    have hfloorNN : Real.toNNReal E * p * x ≤ 8 * (D i : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat, hEeq, hpEq, hxEq]
      have hbound := (hlocal i hi.le).floor_lower
      change E * ksssEdgeDensity E i * ksssPairTrajectory (ksssOrders q) a E A i / 8 ≤ (D i : ℝ) at hbound
      linarith only [hbound]
    have hR : R i ≤ 2 * (Real.toNNReal E * p) := by
      rw [show Real.toNNReal E * p = Real.toNNReal E - 3 * (i : ℝ≥0) from
        ksssEdgeDensity_nnreal_clock E i P.edge_pos (hscalar i hi.le).clock_strict]
      exact henv.upper i hi.le
    exact sharp_clock_cubic_cancellation (Fintype.card V) (Real.toNNReal E) p x C (D i) (R i)
      hCpos hx hD hEupperNN hpair hfloorNN hR
  have hpoint := transferPointWeight_boundedSharp_le_of_envelope hNpos P.horizon
    (fun i hi ↦ (hlocal i hi.le).transfer_factor) hM henv.positive henv.decreasing hloss hquadratic hcubic
  refine ⟨hsurvival, ?_⟩
  convert hpoint using 1 <;> dsimp only [C] <;> ring

end

end Erdos207
