import ErdosProblems.Erdos67b.MRMaskedDistance
import ErdosProblems.Erdos67b.MRMultiplicativeEuler
import ErdosProblems.Erdos67b.MRHalaszOrdinaryBands

/-!
# Euler suppression retaining the deleted small-prime mass

The exact Euler deficit keeps nearly the full reciprocal weight of
deleted primes far below the product scale. The global distance term
still uses its proved `exp(-1)` factor.
-/

open scoped BigOperators ComplexConjugate
open Finset Filter

namespace Erdos67b

open MRHalaszBands MRMultiplicativeEuler MRHalaszEuler EulerResidue EulerQuantitative

noncomputable section

def mrRemovedPrimeEulerMass (P : ℕ → Prop) [DecidablePred P] (s : ℂ) (X : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE X, if P p then 0 else ‖(p : ℂ) ^ (-s)‖

theorem mrEulerDeficit_mask_lower
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] (s : ℂ) (X : ℕ)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1 / 2) :
    lam * finiteMultiplicativeEulerDeficit f s X +
        (1 - 2 * lam) * mrRemovedPrimeEulerMass P s X ≤
      finiteMultiplicativeEulerDeficit (primeBandCoefficient f P) s X := by
  unfold finiteMultiplicativeEulerDeficit mrRemovedPrimeEulerMass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (Nat.mem_primesLE.mp hp).2
  have hnonneg := multiplicativeEulerDeficit_nonneg hbound s hprime
  by_cases hP : P p
  · simp only [hP, ↓reduceIte, mul_zero, add_zero]
    have heq : multiplicativeEulerDeficit (primeBandCoefficient f P) s p =
        multiplicativeEulerDeficit f s p := by
      unfold multiplicativeEulerDeficit
      rw [primeBandCoefficient_at_prime f P hprime, if_pos hP]
    rw [heq]
    nlinarith
  · simp only [hP, ↓reduceIte]
    have hnorm : ‖f p * (p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-s)‖ := by
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hbound p hprime.pos) (norm_nonneg _)
    have hre := neg_le_of_abs_le (Complex.abs_re_le_norm (f p * (p : ℂ) ^ (-s)))
    have hupper : multiplicativeEulerDeficit f s p ≤ 2 * ‖(p : ℂ) ^ (-s)‖ := by
      unfold multiplicativeEulerDeficit
      linarith
    have hh := mul_le_mul_of_nonneg_left hupper hlam0
    unfold multiplicativeEulerDeficit at hh ⊢
    rw [primeBandCoefficient_at_prime f P hprime, if_neg hP]
    simp only [zero_mul, Complex.zero_re, sub_zero]
    nlinarith

theorem mrPrimeEulerWeight_ge_exp_div
    {p X : ℕ} (hp : 0 < p) (hX : 1 < X) {theta : ℝ}
    (hlogp : Real.log (p : ℝ) ≤ theta * Real.log (X : ℝ)) (t : ℝ) :
    Real.exp (-theta) / (p : ℝ) ≤ ‖(p : ℂ) ^ (-halaszPoint X t)‖ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hratio : Real.log (p : ℝ) / Real.log (X : ℝ) ≤ theta :=
    (div_le_iff₀ hlogX).mpr hlogp
  rw [halaszPoint, HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp,
    Real.rpow_def_of_pos hp0]
  calc
    _ = Real.exp (-theta - Real.log (p : ℝ)) := by rw [Real.exp_sub, Real.exp_log hp0]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold taoExponent
      rw [div_eq_mul_inv] at hratio
      nlinarith

theorem mrRemovedPrimeEulerMass_ge_small_prime_mass
    (P : ℕ → Prop) [DecidablePred P] {X : ℕ} (hX : 1 < X)
    (hsmall : ∀ p ∈ primesUpTo X, ¬ P p → Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (t : ℝ) :
    (15 / 16 : ℝ) * mrRemovedPrimeMass P X ≤ mrRemovedPrimeEulerMass P (halaszPoint X t) X := by
  have hsets : Nat.primesLE X = primesUpTo X := by
    ext p
    rw [Nat.mem_primesLE, mem_primesUpTo]
    tauto
  unfold mrRemovedPrimeMass mrRemovedPrimeEulerMass
  rw [hsets, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  by_cases hP : P p
  · simp [hP]
  · simp only [hP, ↓reduceIte]
    have hweight := mrPrimeEulerWeight_ge_exp_div (mem_primesUpTo.mp hp).1.pos hX
      (theta := 1 / 16) (by simpa only [one_div, inv_mul_eq_div] using hsmall p hp hP) t
    have he : (15 / 16 : ℝ) ≤ Real.exp (-(1 / 16 : ℝ)) := by
      linarith [Real.add_one_le_exp (-(1 / 16 : ℝ))]
    have hh := div_le_div_of_nonneg_right he (show (0 : ℝ) ≤ p by positivity)
    have heq : (15 / 16 : ℝ) * (1 / (p : ℝ)) = (15 / 16 : ℝ) / p := by ring
    rw [heq]
    exact hh.trans hweight

theorem mrEulerDeficit_mask_ge_distance_add_mass
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] {X : ℕ} (hX : 1 < X)
    (hsmall : ∀ p ∈ primesUpTo X, ¬ P p → Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (t : ℝ) :
    Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X +
        (3 / 4 : ℝ) * mrRemovedPrimeMass P X ≤
      finiteMultiplicativeEulerDeficit (primeBandCoefficient f P) (halaszPoint X t) X := by
  have hmask := mrEulerDeficit_mask_lower hbound P (halaszPoint X t) X
    (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) ≤ 1 / 2)
  have hdist := exp_neg_one_mul_pretentiousDistSq_le_finiteMultiplicativeEulerDeficit hbound hX t
  have hmass := mrRemovedPrimeEulerMass_ge_small_prime_mass P hX hsmall t
  have hm0 : 0 ≤ mrRemovedPrimeMass P X := by
    unfold mrRemovedPrimeMass
    apply Finset.sum_nonneg
    intro p hp
    split_ifs <;> positivity
  nlinarith

/-- Retain the finite deficit when passing from finite Euler products
to the actual L-series. -/
theorem mrNorm_LSeries_halaszPoint_le_finiteDeficit
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {X : ℕ} (hX : 1 < X) (t : ℝ) :
    ‖LSeries f (halaszPoint X t)‖ ≤
      Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re -
        finiteMultiplicativeEulerDeficit f (halaszPoint X t) X + 3 * primeQuadraticConstant) := by
  let E : ℝ := (∑' p : Nat.Primes, ‖(p : ℂ) ^ (-halaszPoint X t)‖) -
    finiteMultiplicativeEulerDeficit f (halaszPoint X t) X +
    3 * ∑' p : Nat.Primes, ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2
  have hlim := (tendsto_multiplicative_eulerProduct hmul hbound
    (s := halaszPoint X t) (by rw [halaszPoint_re]; exact one_lt_taoExponent hX)).norm
  have hfinite : ∀ᶠ N : ℕ in atTop,
      ‖∏ p ∈ N.primesBelow, ∑' e : ℕ, f (p ^ e) * ((p : ℂ) ^ (-halaszPoint X t)) ^ e‖ ≤ Real.exp E := by
    filter_upwards [eventually_gt_atTop X] with N hN
    exact norm_finiteMultiplicativeEulerProduct_halaszPoint_le hmul hbound hX hN t
  have hbase : ‖LSeries f (halaszPoint X t)‖ ≤ Real.exp E := le_of_tendsto hlim hfinite
  apply hbase.trans
  apply Real.exp_le_exp.mpr
  have hprime := tsum_primeCpowNorm_halaszPoint_le_logZeta hX t
  have hsquare := tsum_primeCpowNorm_sq_halaszPoint_le_constant hX t
  dsimp only [E]
  linarith

theorem mrNorm_masked_LSeries_le_distance_add_mass
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] {X : ℕ} (hX : 1 < X)
    (hsmall : ∀ p ∈ primesUpTo X, ¬ P p → Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (t : ℝ) :
    ‖LSeries (primeBandCoefficient f P) (halaszPoint X t)‖ ≤
      Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re + 3 * primeQuadraticConstant -
        Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X -
        (3 / 4 : ℝ) * mrRemovedPrimeMass P X) := by
  have hbase := mrNorm_LSeries_halaszPoint_le_finiteDeficit
    (primeBandCoefficient_isMultiplicativeOnPositiveNat hmul P)
    (fun n hn ↦ norm_primeBandCoefficient_le_one hbound P hn) hX t
  have hdef := mrEulerDeficit_mask_ge_distance_add_mass hbound P hX hsmall t
  exact hbase.trans (Real.exp_le_exp.mpr (by linarith))

end

end Erdos67b
