/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SparseSharpSchedule
import ErdosProblems.Erdos207.SparseCubicTransfer
import ErdosProblems.Erdos207.KSSSSharpAffineEnvelope

/-! # Sparse-stage survival and selection with the actual initial normalization -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem KSSSPowerParameters.sparse_sharp_schedule_survival_point
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin c : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (hcb : 2 * c ≤ b) (hfloor : ∀ i : ℕ, i ≤ n → 1 / (t : ℝ) ^ c ≤ ksssEdgeDensity E i) :
    let scale := (Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B
    let d := fun i : ℕ ↦ ksssRoundedPairFloor q a E A scale B i
    let D := fun i : ℕ ↦ ksssRoundedAvailabilityFloor q a E A scale B i
    let M := fun i : ℕ ↦ ksssRoundedAvailabilityCeil q a E A scale B i
    cumulativeSurvival (boundedSharpSurvivalSchedule n M d (3 * t)) n ≤
        2 * Real.toNNReal (ksssEdgeDensity E n) ∧
      transferPointWeight (boundedSharpSurvivalSchedule n M d (3 * t))
        (boundedSharpTransferSchedule n D M d (3 * t)) n ≤
        128 * Real.toNNReal (Real.exp (∑ d ∈ ksssOrders q, coeff d)) * Real.toNNReal E / Real.toNNReal A := by
  let N : ℝ := Fintype.card V
  let scale := N / (t : ℝ) ^ ksssPowerErrorExponent b B
  let d := fun i : ℕ ↦ ksssRoundedPairFloor q a E A scale B i
  let D := fun i : ℕ ↦ ksssRoundedAvailabilityFloor q a E A scale B i
  let M := fun i : ℕ ↦ ksssRoundedAvailabilityCeil q a E A scale B i
  let R := ksssSharpClockEnvelope E t c
  let C : ℝ≥0 := Real.toNNReal (Real.exp (∑ d ∈ ksssOrders q, coeff d))
  let eps : ℝ≥0 := 16 / (t : ℝ≥0) ^ (c + 1)
  let p := fun i : ℕ ↦ Real.toNNReal (ksssEdgeDensity E i)
  have hApos : 0 < Real.toNNReal A := Real.toNNReal_pos.mpr P.available_pos
  have hCeq : (C : ℝ) = Real.exp (∑ d ∈ ksssOrders q, coeff d) := Real.coe_toNNReal _ (Real.exp_pos _).le
  have hEeq : (Real.toNNReal E : ℝ) = E := Real.coe_toNNReal _ P.edge_pos.le
  have hAeq : (Real.toNNReal A : ℝ) = A := Real.coe_toNNReal _ P.available_pos.le
  have hlocal := fun (i : ℕ) (hi : i ≤ n) ↦ P.sparse_sharp_schedule_bounds hcb i (Nat.cast_nonneg _) (hfloor i hi)
  have hscalar := fun (i : ℕ) (hi : i ≤ n) ↦ P.scalar_bounds i (Nat.cast_nonneg _) (P.density_floor i hi)
  have henv := ksssSharpClockEnvelope_bounds E t c n P.edge_pos P.scale_large (hfloor n le_rfl)
  have htpos : (0 : ℝ≥0) < t := by exact_mod_cast (show 0 < t by linarith [P.scale_large])
  have heps : eps ≤ 1 := by
    apply (div_le_one (pow_pos htpos _)).mpr
    exact_mod_cast (show 16 ≤ t ^ (c + 1) from
      (show 16 ≤ t by linarith [P.scale_large]).trans
        (by simpa only [pow_one] using Nat.pow_le_pow_right (by linarith [P.scale_large] : 0 < t) (by omega : 1 ≤ c + 1)))
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
        have hid : E * ksssEdgeDensity E i = E - 3 * (i : ℝ) := by
          unfold ksssEdgeDensity
          field_simp [P.edge_pos.ne']
        simpa only [hid] using (hlocal i hi.le).affine_loss
      _ ≤ _ := mul_le_mul_of_nonneg_right (henv.lower i hi.le) zero_le
  have htheta := boundedSharpSurvivalSchedule_le_nnreal_envelope_ratio M d (3 * t) R hM
    henv.positive henv.decreasing hloss
  have hprefix : ∀ i, i ≤ n → cumulativeSurvival (boundedSharpSurvivalSchedule n M d (3 * t)) i ≤ 2 * p i := by
    intro i hi
    calc
      _ ≤ R i / R 0 := cumulativeSurvival_le_envelope_ratio _ R henv.positive htheta i hi
      _ ≤ 2 * (Real.toNNReal E - 3 * (i : ℝ≥0)) / Real.toNNReal E := by
        rw [show R 0 = Real.toNNReal E from henv.initial]
        exact div_le_div_of_nonneg_right (henv.upper i hi) zero_le
      _ = _ := by
        dsimp only [p]
        rw [ksssEdgeDensity_nnreal_ratio E i P.edge_pos (hscalar i hi).clock_strict]
        ring
  refine ⟨hprefix n le_rfl, ?_⟩
  apply transferPointWeight_sparse_initial_scale n (3 * t) D M d (Real.toNNReal A) (Real.toNNReal E) C p hApos
  · rw [← NNReal.coe_le_coe, NNReal.coe_natCast, hEeq]
    have h := (hscalar n le_rfl).clock_strict
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  · exact fun i hi ↦ (hlocal i hi.le).floor_pos
  · exact fun i hi ↦ (hlocal i hi.le).transfer_factor
  · intro i hi
    rw [← NNReal.coe_le_coe]
    have hp := ksssEdgeDensity_pos P.edge_pos (hscalar i hi.le).clock_strict
    have hpEq : (p i : ℝ) = ksssEdgeDensity E i := Real.coe_toNNReal _ hp.le
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_natCast, hAeq, hCeq, hpEq]
    exact sparse_availability_cubic_lower E A _ _ _ (D i) P.edge_pos (Real.exp_pos _) hp.le
      (ksssPairTrajectory_lower_initial_normalization (ksssOrders q) a coeff E A i _ P.edge_pos P.available_pos
        (Real.exp_pos _) (Nat.cast_nonneg _) (hscalar i hi.le).clock_strict P.coefficient_nonneg P.coefficient_bound le_rfl)
      (hlocal i hi.le).floor_lower
  · exact fun i hi ↦ hprefix i hi.le

end

end Erdos207
