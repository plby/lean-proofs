/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryDegreePowerBudgets
import ErdosProblems.Erdos207.SourceReservePowerFailure
import ErdosProblems.Erdos207.EventualSourceMomentBudgets

/-! # A fixed preliminary degree moment and cutoff work uniformly at every sufficiently large scale -/

namespace Erdos207

open scoped NNReal

theorem eventually_source_preliminary_degree_budget
    (reserveExp b v d L R decay : ℕ) (eta0 constant : ℝ≥0) (heta0 : 0 < eta0)
    (hsizeGap : 2*reserveExp+2*b+1 ≤ L)
    (hrateGap : 2*reserveExp+2*b+v+1 ≤ d) :
    ∃ s B T : ℕ, 1 ≤ s ∧ 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ (N n : ℕ) (u p eta rate error : ℝ≥0), N ≤ t^R → n ≤ t^R →
      (n : ℝ≥0) ≤ (t : ℝ≥0)^v*u → (t : ℝ≥0)^L ≤ u →
      1/(t : ℝ≥0)^b ≤ p → eta0 ≤ eta →
      rate ≤ (2*constant)/(t : ℝ≥0)^d → error ≤ 1/(t : ℝ≥0)^B →
      let r := 1/(t : ℝ≥0)^reserveExp
      let mu := r^2*p^2*eta*u
      512 ≤ mu ∧ 2*s ≤ ⌊mu/256⌋₊+1 ∧
        sourcePreliminaryDegreeFailure N n ⌊mu/256⌋₊ s rate constant error ≤ 1/(t : ℝ≥0)^decay := by
  let s := R+decay+1
  let B := R*s+R+decay+1
  let A : ℝ≥0 := 1024*constant/eta0
  let coefficient : ℝ≥0 := A^s+(2*constant)^s
  obtain ⟨T, hT⟩ := exists_nat_ge (max 1 (max coefficient (512*(s+1 : ℝ≥0)/eta0)))
  have hT1 : 1 ≤ T := by exact_mod_cast (le_max_left _ _).trans hT
  refine ⟨s, B, T, by dsimp only [s]; omega, hT1, ?_⟩
  intro t ht N n u p eta rate error hN hn hsize hu hp heta hrate herror
  dsimp only
  have ht1 : 1 ≤ t := hT1.trans ht
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht1
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le htNN
  have hthreshold : max 1 (max coefficient (512*(s+1 : ℝ≥0)/eta0)) ≤ (t : ℝ≥0) :=
    hT.trans (by exact_mod_cast ht)
  have hcoef : coefficient ≤ (t : ℝ≥0) := (le_max_left _ _).trans ((le_max_right _ _).trans hthreshold)
  have hmassThreshold : 512*(s+1 : ℝ≥0)/eta0 ≤ (t : ℝ≥0) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hthreshold)
  let r : ℝ≥0 := 1/(t : ℝ≥0)^reserveExp
  let mu := r^2*p^2*eta*u
  have hmuLower : eta0*(t : ℝ≥0) ≤ mu := by
    simpa only [pow_one] using reserve_internal_supply_power_lower (t : ℝ≥0) u r p eta eta0
      reserveExp b L 1 htNN le_rfl hp heta hu hsizeGap
  have hmuLarge : 512*(s+1 : ℝ≥0) ≤ mu := by
    have hh := (div_le_iff₀ heta0).mp hmassThreshold
    have hh' : 512*(s+1 : ℝ≥0) ≤ eta0*(t : ℝ≥0) := by
      simpa only [mul_comm (t : ℝ≥0) eta0] using hh
    exact hh'.trans hmuLower
  have hmu512 : 512 ≤ mu := by
    calc
      (512 : ℝ≥0) ≤ 512*(s+1 : ℝ≥0) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (zero_le (a := (s : ℝ≥0))) : (1 : ℝ≥0) ≤ s+1) (zero_le (a := (512 : ℝ≥0)))
      _ ≤ _ := hmuLarge
  have hmoment : 2*s ≤ ⌊mu/256⌋₊+1 := by
    have hh : (2*s : ℝ≥0) ≤ mu/256 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 256)).mpr
      calc
        _ = 512*(s : ℝ≥0) := by ring
        _ ≤ 512*(s+1 : ℝ≥0) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le) zero_le
        _ ≤ _ := hmuLarge
    have hf := hh.trans (Nat.lt_floor_add_one (mu/256)).le
    exact_mod_cast hf
  have hmain : 2*(n : ℝ≥0)*rate/(⌊mu/256⌋₊+1) ≤ A/(t : ℝ≥0) := by
    have hh := preliminary_rounded_degree_mean_power
      (t : ℝ≥0) n u p r eta eta0 (2*constant) 1 rate reserveExp b v d 1
      htNN ((pow_pos ht0 L).trans_le hu) heta0 hp le_rfl heta
      (by simpa only [one_mul] using hsize) hrate hrateGap
    calc
      _ ≤ (512*(2*constant)*1/eta0)/(t : ℝ≥0)^1 := hh
      _ = A/(t : ℝ≥0) := by simp only [A, pow_one]; ring
  have htail := sourcePreliminaryDegreeFailure_power_le N n ⌊mu/256⌋₊ s R 1 B (decay+1)
    (t : ℝ≥0) rate constant error A htNN (by exact_mod_cast hN) (by exact_mod_cast hn)
    (by simpa only [pow_one] using hmain) herror (by dsimp only [s]; omega) (by dsimp only [B]; omega)
  refine ⟨hmu512, hmoment, htail.trans ?_⟩
  exact inverse_power_absorb_coefficient (t : ℝ≥0) coefficient decay ht0 hcoef

end Erdos207
