/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSSharpPowerBudgets
import ErdosProblems.Erdos207.NeighborPowerScale

/-! # The established power hierarchy supplies the sharp initial schedule budgets -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem KSSSPowerParameters.sharp_schedule_power_sizes
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (time : ℝ) (htime : 0 ≤ time) (hfloor : 1 / (t : ℝ) ^ b ≤ ksssEdgeDensity E time) :
    (t : ℝ) ^ (b + 3) ≤ ksssPairTrajectory (ksssOrders q) a E A time ∧
      (t : ℝ) ^ 2 ≤ E * ksssEdgeDensity E time := by
  let N : ℝ := Fintype.card V
  let R := ksssPowerDenominatorExponent q b B k Rmin
  have hs := P.scalar_bounds time htime hfloor
  have ht : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by linarith [P.scale_large])
  have htpos : (0 : ℝ) < t := by linarith
  have hscale : (t : ℝ) ^ R ≤ N := by dsimp only [R, N]; exact_mod_cast P.power_scale
  have hpairGap : 4 * b + 4 ≤ R := by
    dsimp only [R, ksssPowerDenominatorExponent, ksssPowerErrorExponent]
    omega
  have hclockGap : 2 + 2 * b ≤ R * 2 := by omega
  constructor
  · apply le_trans _ hs.pair_lower
    apply (le_div_iff₀ (pow_pos htpos _)).mpr
    calc
      _ = (t : ℝ) ^ (4 * b + 4) := by rw [← pow_add]; congr 1; omega
      _ ≤ (t : ℝ) ^ R := pow_le_pow_right₀ ht hpairGap
      _ ≤ N := hscale
  · apply le_trans _ hs.clock_lower
    apply (le_div_iff₀ (pow_pos htpos _)).mpr
    calc
      _ = (t : ℝ) ^ (2 + 2 * b) := (pow_add _ _ _).symm
      _ ≤ (t : ℝ) ^ (R * 2) := pow_le_pow_right₀ ht hclockGap
      _ = ((t : ℝ) ^ R) ^ 2 := pow_mul _ _ _
      _ ≤ N ^ 2 := pow_le_pow_left₀ (pow_nonneg (by positivity) R) hscale 2

structure KSSSSharpScheduleBounds
    (q b B t : ℕ) (a : ℕ → ℝ) (E A N time : ℝ) : Prop where
  floor_pos : 0 < ksssRoundedAvailabilityFloor q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time
  upper_pos : 0 < ksssRoundedAvailabilityCeil q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time
  pair_le_upper : ksssRoundedPairFloor q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time ≤
    ksssRoundedAvailabilityCeil q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time
  effective_lt_upper : ksssRoundedPairFloor q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time - 3 * t <
    ksssRoundedAvailabilityCeil q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time
  affine_loss : 3 * (1 - 16 / (t : ℝ) ^ (b + 1)) *
      (ksssRoundedAvailabilityCeil q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time : ℝ) ≤
    (E * ksssEdgeDensity E time) *
      ((ksssRoundedPairFloor q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time - 3 * t : ℕ) : ℝ)
  floor_lower : E * ksssEdgeDensity E time * ksssPairTrajectory (ksssOrders q) a E A time / 8 ≤
    (ksssRoundedAvailabilityFloor q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time : ℝ)
  transfer_factor : (boundedSharpSurvivalTheta
      (ksssRoundedAvailabilityCeil q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time)
      (ksssRoundedPairFloor q a E A (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time) (3 * t) ^ (3 * t))⁻¹ ≤
    (2 : ℝ≥0)

theorem KSSSPowerParameters.sharp_schedule_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (time : ℝ) (htime : 0 ≤ time) (hfloor : 1 / (t : ℝ) ^ b ≤ ksssEdgeDensity E time)
    (hratio : (Fintype.card V : ℝ) / 6 ≤ A / E) :
    KSSSSharpScheduleBounds q b B t a E A (Fintype.card V) time := by
  let N : ℝ := Fintype.card V
  let L := E * ksssEdgeDensity E time
  let x := ksssPairTrajectory (ksssOrders q) a E A time
  let e := ksssErrorEnvelope E (N / (t : ℝ) ^ ksssPowerErrorExponent b B) B time
  let eps := 16 / (t : ℝ) ^ (b + 1)
  have hs := P.scalar_bounds time htime hfloor
  have hsizes := P.sharp_schedule_power_sizes time htime hfloor
  have ht : (32 : ℝ) ≤ t := by exact_mod_cast P.scale_large
  have htpos : (0 : ℝ) < t := by linarith
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast (show 0 < Fintype.card V by linarith [P.ambient_pos])
  have hbudgets := sharp_power_rounding_budgets t x L b ht hsizes.1 hsizes.2
  have hL : 6 ≤ L := by
    have ht2 : (t : ℝ) ≤ (t : ℝ) ^ 2 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t) (by norm_num : 1 ≤ 2)
    linarith only [hsizes.2, ht2, ht]
  have hx : 0 < x := by linarith only [hbudgets.2.2.2.2.2]
  have he0 : 0 ≤ e := by linarith only [hs.error_two]
  have hxbase := ksssPairTrajectory_lower_fixed_initial_ratio (ksssOrders q) a coeff E A time N t
    P.edge_pos hN htpos htime hs.clock_strict P.coefficient_nonneg P.coefficient_bound hratio P.coefficient_budget.poisson
  have he : e ≤ eps * x / 8 := by
    have h := ksss_pair_relative_error_fine E N t time x b B hN htpos hfloor hxbase
    convert h using 1 <;> dsimp only [e, eps] <;> ring
  have hround : ((3 * t : ℕ) : ℝ) + 2 ≤ eps * x / 8 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbudgets.2.2.1
  have hsmall : 6 * ((3 * t : ℕ) : ℝ) ≤ L := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc, show (6 : ℝ) * 3 = 18 by norm_num]
      using hbudgets.2.2.2.1
  have hcoherence := rounded_sharp_schedule_coherence L x e (3 * t) hL hx he0
  have hfloorLower : L * x / 8 ≤ (⌊L * (x - e) / 3⌋₊ : ℝ) :=
    rounded_availability_lower L x e hL hbudgets.2.2.2.2.2 hs.error_small
  refine ⟨?_, hcoherence.1, hcoherence.2.1, hcoherence.2.2.1,
    rounded_sharp_affine_loss L x e eps (3 * t) hL hx.le he0 hbudgets.1 hbudgets.2.1 he hround,
    hfloorLower, rounded_sharp_transfer_factor_le_two L x e (3 * t) hL hx he0 hsmall⟩
  have hpos : (0 : ℝ) < ⌊L * (x - e) / 3⌋₊ := (by positivity : 0 < L * x / 8).trans_le hfloorLower
  change 0 < ⌊L * (x - e) / 3⌋₊
  exact_mod_cast hpos

end

end Erdos207
