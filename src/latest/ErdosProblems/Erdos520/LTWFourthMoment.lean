import ErdosProblems.Erdos520.HypercontractiveInterpolation
import ErdosProblems.Erdos520.CaichAuxiliaryMomentTail
import Mathlib.Algebra.Order.Chebyshev

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# A short-interval fourth moment for LTW interpolation

The Lau--Tenenbaum--Wu interpolation argument needs a fourth-moment saving
in the interval length.  This file derives one directly from the finite
Bonami inequality already proved for the Rademacher model.  Two elementary
Cauchy--Schwarz steps (packaged as the fourth-power mean inequality) trade
the `tau_3` energy for a global `tau_81` sum.  The resulting logarithmic
power is deliberately coarse, but the length exponent `3/2` is stronger
than the `4/3` exponent needed on the root-exponential mesh.
-/

theorem card_caichIntervalSupport (a L : ℕ) :
    (caichIntervalSupport a L).card = L := by
  unfold caichIntervalSupport
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact Nat.add_left_cancel (Nat.add_right_cancel hij)

/-- The exact Bonami energy for an interval may be restricted to its
squarefree members, since all other Rademacher-multiplicative coefficients
vanish. -/
noncomputable def ltwSquarefreeIntervalEnergy (a L : ℕ) : ℝ :=
  ∑ n ∈ (caichIntervalSupport a L).filter Squarefree,
    (orderedDivisorCount 3 n : ℝ)

theorem ltwSquarefreeIntervalEnergy_nonneg (a L : ℕ) :
    0 ≤ ltwSquarefreeIntervalEnergy a L := by
  unfold ltwSquarefreeIntervalEnergy
  positivity

theorem integral_abs_fIntervalSum_pow_four_le_energy_sq
    (a L x : ℕ) (hax : a + L ≤ x) :
    (∫ omega, |fIntervalSum omega a L| ^ 4 ∂μ) ≤
      ltwSquarefreeIntervalEnergy a L ^ 2 := by
  let I : ℝ := ∫ omega, |fIntervalSum omega a L| ^ 4 ∂μ
  let E : ℝ := ltwSquarefreeIntervalEnergy a L
  have hI : 0 ≤ I := integral_nonneg fun omega ↦ by positivity
  have hroot : I ^ (1 / (2 : ℝ)) ≤ E := by
    have hbonami := caichFiniteRMFSum_bonami_energy
      2 (by norm_num) x (caichIntervalSupport a L) (fun _ ↦ 1)
        (caichIntervalSupport_subset_Ioc hax)
    have henergy := caichIntegerWalshEnergy_eq_divisorWeight
      2 x (caichIntervalSupport a L) (fun _ ↦ 1)
        (caichIntervalSupport_subset_Ioc hax)
    simp only [caichFiniteRMFSum_one, sum_caichIntervalSupport_f,
      one_pow, mul_one, show 2 * 2 - 1 = 3 by norm_num] at hbonami henergy
    rw [henergy] at hbonami
    simpa only [I, E, ltwSquarefreeIntervalEnergy] using! hbonami
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hI _) hroot 2
  have hrootPow : (I ^ (1 / (2 : ℝ))) ^ 2 = I := by
    convert! Real.rpow_inv_natCast_pow hI (by norm_num : (2 : ℕ) ≠ 0) using 1 <;>
      norm_num
  rw [hrootPow] at hpow
  exact hpow

private theorem orderedDivisorCount_three_pow_four_eq_eightyOne
    {n : ℕ} (hn : Squarefree n) :
    (orderedDivisorCount 3 n : ℝ) ^ 4 =
      (orderedDivisorCount 81 n : ℝ) := by
  rw [orderedDivisorCount_eq_pow_card_primeFactors_of_squarefree 3 hn,
    orderedDivisorCount_eq_pow_card_primeFactors_of_squarefree 81 hn]
  norm_cast
  calc
    (3 ^ n.primeFactors.card) ^ 4 =
        3 ^ (n.primeFactors.card * 4) := by rw [pow_mul]
    _ =
        3 ^ (4 * n.primeFactors.card) := by rw [Nat.mul_comm]
    _ = (3 ^ 4) ^ n.primeFactors.card := by rw [pow_mul]
    _ = 81 ^ n.primeFactors.card := by norm_num

/-- Fourth-power bound for the exact squarefree interval energy. -/
theorem ltwSquarefreeIntervalEnergy_pow_four_le
    (a L x : ℕ) (hx : 3 ≤ x) (hax : a + L ≤ x) :
    ltwSquarefreeIntervalEnergy a L ^ 4 ≤
      (L : ℝ) ^ 3 *
        ((x : ℝ) * (2 * Real.log (x : ℝ)) ^ 80) := by
  let s : Finset ℕ := (caichIntervalSupport a L).filter Squarefree
  have hsx : s ⊆ Finset.Ioc 0 x := by
    exact (Finset.filter_subset _ _).trans
      (caichIntervalSupport_subset_Ioc hax)
  have hpower := pow_sum_le_card_mul_sum_pow
    (s := s) (f := fun n ↦ (orderedDivisorCount 3 n : ℝ))
    (fun n hn ↦ by positivity) 3
  have hsumEq :
      (∑ n ∈ s, (orderedDivisorCount 3 n : ℝ) ^ 4) =
        ∑ n ∈ s, (orderedDivisorCount 81 n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact orderedDivisorCount_three_pow_four_eq_eightyOne
      (Finset.mem_filter.mp hn).2
  rw [hsumEq] at hpower
  have hcard : (s.card : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (calc
      s.card ≤ (caichIntervalSupport a L).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = L := card_caichIntervalSupport a L)
  have hsum :
      (∑ n ∈ s, (orderedDivisorCount 81 n : ℝ)) ≤
        (x : ℝ) * (2 * Real.log (x : ℝ)) ^ 80 := by
    have hnat := sum_orderedDivisorCount_le_two_log
      81 x s (by norm_num) hx hsx
    have hcast :
        (∑ n ∈ s, (orderedDivisorCount 81 n : ℝ)) =
          ((∑ n ∈ s, orderedDivisorCount 81 n : ℕ) : ℝ) := by
      norm_cast
    rw [hcast]
    simpa using! hnat
  have hcardPow : (s.card : ℝ) ^ 3 ≤ (L : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcard 3
  unfold ltwSquarefreeIntervalEnergy
  change (∑ n ∈ s, (orderedDivisorCount 3 n : ℝ)) ^ 4 ≤ _
  calc
    (∑ n ∈ s, (orderedDivisorCount 3 n : ℝ)) ^ 4 ≤
        (s.card : ℝ) ^ 3 *
          ∑ n ∈ s, (orderedDivisorCount 81 n : ℝ) := hpower
    _ ≤ (L : ℝ) ^ 3 *
          ((x : ℝ) * (2 * Real.log (x : ℝ)) ^ 80) := by
      exact mul_le_mul hcardPow hsum (by positivity) (by positivity)

/-- Coarse but length-sensitive fourth moment.  This is an unconditional
replacement for the external LTW moment estimate in the Rademacher model. -/
theorem integral_abs_fIntervalSum_pow_four_le_ltwBudget
    (a L x : ℕ) (hx : 3 ≤ x) (hax : a + L ≤ x) :
    (∫ omega, |fIntervalSum omega a L| ^ 4 ∂μ) ≤
      Real.sqrt
        ((L : ℝ) ^ 3 *
          ((x : ℝ) * (2 * Real.log (x : ℝ)) ^ 80)) := by
  let I : ℝ := ∫ omega, |fIntervalSum omega a L| ^ 4 ∂μ
  let E : ℝ := ltwSquarefreeIntervalEnergy a L
  have hI : 0 ≤ I := integral_nonneg fun omega ↦ by positivity
  have hIE : I ≤ E ^ 2 := by
    simpa only [I, E] using!
      integral_abs_fIntervalSum_pow_four_le_energy_sq a L x hax
  have hsq : I ^ 2 ≤ E ^ 4 := by
    calc
      I ^ 2 ≤ (E ^ 2) ^ 2 := pow_le_pow_left₀ hI hIE 2
      _ = E ^ 4 := by ring
  have hbudget := ltwSquarefreeIntervalEnergy_pow_four_le a L x hx hax
  exact Real.le_sqrt_of_sq_le (hsq.trans (by simpa only [E] using! hbudget))

/-- Markov form of the length-sensitive fourth-moment estimate. -/
theorem measureReal_abs_fIntervalSum_gt_le_ltwBudget
    (a L x : ℕ) (hx : 3 ≤ x) (hax : a + L ≤ x)
    {u : ℝ} (hu : 0 < u) :
    μ.real {omega | u < |fIntervalSum omega a L|} ≤
      Real.sqrt
          ((L : ℝ) ^ 3 *
            ((x : ℝ) * (2 * Real.log (x : ℝ)) ^ 80)) /
        u ^ 4 := by
  exact measureReal_lt_le_natMoment
    (q := 4) (Y := fun omega ↦ |fIntervalSum omega a L|)
    (by norm_num) (fun omega ↦ abs_nonneg _) hu
    (by simpa only [show 4 = 2 * 2 by norm_num] using!
      integrable_abs_fIntervalSum_pow 2 a L)
    (integral_abs_fIntervalSum_pow_four_le_ltwBudget a L x hx hax)

end Problem520
end Erdos
