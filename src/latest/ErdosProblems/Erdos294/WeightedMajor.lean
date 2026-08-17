/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos294.PrescribedFourier
import ErdosProblems.Erdos297.FourierPhase

/-!
# The prescribed-target weighted major arc for Erdős Problem 294

The linear phase in the prescribed Fourier coefficient is cancelled by the
exact expectation identity.  On the central arc a relative cubic Taylor
estimate keeps the resulting product in the right half-plane; on the rest
of the major arc the standard quadratic norm bound is used.
-/

open scoped BigOperators

namespace Erdos294.WeightedMajor

open Complex Finset Real
open UnitFractions
open Erdos297
open Erdos294.PrescribedFourier

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Product of mean-centred Bernoulli factors. -/
def centeredProduct (A : Finset ℕ) (p t : ℕ → ℝ) : ℂ :=
  ∏ n ∈ A, centeredBernoulliFactor (p n) (t n)

/-- The positive quadratic product used to normalize the Taylor expansion. -/
def quadraticProduct (A : Finset ℕ) (p t : ℕ → ℝ) : ℝ :=
  ∏ n ∈ A, (1 - p n * (1 - p n) * (t n) ^ 2 / 2)

lemma quadraticFactor_ge_half {p t : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1) :
    (1 / 2 : ℝ) ≤ 1 - p * (1 - p) * t ^ 2 / 2 := by
  have hpvar : p * (1 - p) ≤ 1 := by
    nlinarith [sq_nonneg (p - 1 / 2)]
  have ht2 : t ^ 2 ≤ 1 := by
    have hpow := pow_le_pow_left₀ (abs_nonneg t) ht 2
    simpa [sq_abs] using hpow
  have hmul : p * (1 - p) * t ^ 2 ≤ 1 := by
    calc
      p * (1 - p) * t ^ 2 ≤ 1 * t ^ 2 :=
        mul_le_mul_of_nonneg_right hpvar (sq_nonneg t)
      _ ≤ 1 := by simpa using ht2
  linarith

lemma normalized_centeredFactor_sub_one
    {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1) :
    ‖centeredBernoulliFactor p t /
          (1 - p * (1 - p) * t ^ 2 / 2 : ℝ) - 1‖
      ≤ 2 * |t| ^ 3 := by
  let b : ℝ := 1 - p * (1 - p) * t ^ 2 / 2
  have hbhalf : (1 / 2 : ℝ) ≤ b := quadraticFactor_ge_half hp0 hp1 ht
  have hbpos : 0 < b := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hbhalf
  have htaylor :
      ‖centeredBernoulliFactor p t - (b : ℂ)‖ ≤ |t| ^ 3 := by
    simpa [b] using centeredBernoulliFactor_local_quadratic hp0 hp1 ht
  have hbne : (b : ℂ) ≠ 0 := by exact_mod_cast hbpos.ne'
  change ‖centeredBernoulliFactor p t / (b : ℂ) - 1‖ ≤ _
  rw [div_sub_one hbne, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hbpos]
  calc
    ‖centeredBernoulliFactor p t - (b : ℂ)‖ / b
        ≤ |t| ^ 3 / b := div_le_div_of_nonneg_right htaylor hbpos.le
    _ ≤ |t| ^ 3 / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) _)
        (by norm_num) hbhalf
    _ = 2 * |t| ^ 3 := by ring

lemma norm_prod_one_add_sub_one_le_one_sixth
    (A : Finset ℕ) (u : ℕ → ℂ)
    (hbudget : ∑ n ∈ A, ‖u n‖ ≤ (1 / 7 : ℝ)) :
    ‖(∏ n ∈ A, (1 + u n)) - 1‖ ≤ (1 / 6 : ℝ) := by
  calc
    ‖(∏ n ∈ A, (1 + u n)) - 1‖
        ≤ Real.exp (∑ n ∈ A, ‖u n‖) - 1 :=
      Finset.norm_prod_one_add_sub_one_le A u
    _ ≤ Real.exp (1 / 7 : ℝ) - 1 := by gcongr
    _ ≤ 1 / (1 - (1 / 7 : ℝ)) - 1 := by
      gcongr
      exact Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    _ = 1 / 6 := by norm_num

/-- The central product has nonnegative real part under the cubic budget. -/
theorem central_centeredProduct_re_nonneg
    (A : Finset ℕ) (p t : ℕ → ℝ)
    (hp0 : ∀ n ∈ A, 0 ≤ p n) (hp1 : ∀ n ∈ A, p n ≤ 1)
    (ht : ∀ n ∈ A, |t n| ≤ 1)
    (hcubic : 2 * ∑ n ∈ A, |t n| ^ 3 ≤ (1 / 7 : ℝ)) :
    0 ≤ (centeredProduct A p t).re := by
  let b : ℕ → ℝ := fun n ↦ 1 - p n * (1 - p n) * (t n) ^ 2 / 2
  let u : ℕ → ℂ := fun n ↦ centeredBernoulliFactor (p n) (t n) / b n - 1
  have hbhalf : ∀ n ∈ A, (1 / 2 : ℝ) ≤ b n := by
    intro n hn
    exact quadraticFactor_ge_half (hp0 n hn) (hp1 n hn) (ht n hn)
  have hbpos : ∀ n ∈ A, 0 < b n := by
    intro n hn
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hbhalf n hn)
  have hubound : ∀ n ∈ A, ‖u n‖ ≤ 2 * |t n| ^ 3 := by
    intro n hn
    exact normalized_centeredFactor_sub_one
      (hp0 n hn) (hp1 n hn) (ht n hn)
  have husum : ∑ n ∈ A, ‖u n‖ ≤ (1 / 7 : ℝ) := by
    calc
      ∑ n ∈ A, ‖u n‖ ≤ ∑ n ∈ A, 2 * |t n| ^ 3 :=
        Finset.sum_le_sum fun n hn ↦ hubound n hn
      _ = 2 * ∑ n ∈ A, |t n| ^ 3 := by rw [Finset.mul_sum]
      _ ≤ 1 / 7 := hcubic
  have hprod := norm_prod_one_add_sub_one_le_one_sixth A u husum
  have hprodRe : (5 / 6 : ℝ) ≤ (∏ n ∈ A, (1 + u n)).re := by
    have hreabs : |((∏ n ∈ A, (1 + u n)) - 1).re| ≤ (1 / 6 : ℝ) :=
      (Complex.abs_re_le_norm _).trans hprod
    have hre := (abs_le.mp hreabs).1
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hfactor (n : ℕ) (hn : n ∈ A) :
      centeredBernoulliFactor (p n) (t n) =
        (b n : ℂ) * (1 + u n) := by
    dsimp [u]
    have hbne : (b n : ℂ) ≠ 0 := by exact_mod_cast (hbpos n hn).ne'
    field_simp
    ring
  have hcentered : centeredProduct A p t =
      ((∏ n ∈ A, b n : ℝ) : ℂ) * ∏ n ∈ A, (1 + u n) := by
    unfold centeredProduct
    calc
      ∏ n ∈ A, centeredBernoulliFactor (p n) (t n) =
          ∏ n ∈ A, ((b n : ℂ) * (1 + u n)) := by
        apply Finset.prod_congr rfl
        intro n hn
        exact hfactor n hn
      _ = ((∏ n ∈ A, b n : ℝ) : ℂ) * ∏ n ∈ A, (1 + u n) := by
        rw [Finset.prod_mul_distrib, Complex.ofReal_prod]
  have hbprod0 : 0 ≤ ∏ n ∈ A, b n :=
    Finset.prod_nonneg fun n hn ↦ (hbpos n hn).le
  rw [hcentered, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg hbprod0 (le_trans (by norm_num) hprodRe)

lemma fourierPhase_eq_e (x : ℝ) : fourierPhase x = UnitFractions.e x := by
  unfold fourierPhase UnitFractions.e
  apply congrArg Complex.exp
  push_cast
  ring

/-- The uncentred product after removing its exact linear mean phase. -/
def expectationCenteredTerm (A : Finset ℕ) (p t : ℕ → ℝ) : ℂ :=
  Complex.exp (((-(∑ n ∈ A, p n * t n) : ℝ) : ℂ) * Complex.I) *
    ∏ n ∈ A,
      (((1 - p n : ℝ) : ℂ) +
        (p n : ℂ) * Complex.exp (((t n : ℝ) : ℂ) * Complex.I))

lemma expectationCenteredTerm_eq_centeredProduct
    (A : Finset ℕ) (p t : ℕ → ℝ) :
    expectationCenteredTerm A p t = centeredProduct A p t := by
  unfold expectationCenteredTerm centeredProduct centeredBernoulliFactor
  rw [Finset.prod_mul_distrib]
  have hexp :
      ∏ n ∈ A, Complex.exp (((-(p n * t n) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((-(∑ n ∈ A, p n * t n) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 2
    push_cast
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  congr 1
  congr 1
  simpa using hexp.symm

/-- Exact expectation cancellation for the integer-frequency formula. -/
lemma twistedProduct_eq_centered
    (A : Finset ℕ) (p : ℕ → ℝ) (h : ℤ) (y : ℝ)
    (hmean : ∑ n ∈ A, p n / n = y) :
    UnitFractions.e (-(h : ℝ) * y) *
        ∏ n ∈ A, ((1 - p n : ℝ) + p n * UnitFractions.e ((h : ℝ) / n)) =
      centeredProduct A p (fun n ↦ 2 * Real.pi * (h : ℝ) / n) := by
  let t : ℕ → ℝ := fun n ↦ 2 * Real.pi * (h : ℝ) / n
  have hsum : ∑ n ∈ A, p n * t n = (2 * Real.pi * (h : ℝ)) * y := by
    calc
      ∑ n ∈ A, p n * t n =
          (2 * Real.pi * (h : ℝ)) * ∑ n ∈ A, p n / n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [t]
        ring
      _ = (2 * Real.pi * (h : ℝ)) * y := by rw [hmean]
  have hphase :
      UnitFractions.e (-(h : ℝ) * y) =
        Complex.exp (((-(∑ n ∈ A, p n * t n) : ℝ) : ℂ) * Complex.I) := by
    unfold UnitFractions.e
    apply congrArg Complex.exp
    rw [hsum]
    push_cast
    ring
  have hprod :
      ∏ n ∈ A, ((1 - p n : ℝ) + p n * UnitFractions.e ((h : ℝ) / n)) =
        ∏ n ∈ A,
          (((1 - p n : ℝ) : ℂ) +
            (p n : ℂ) * Complex.exp (((t n : ℝ) : ℂ) * Complex.I)) := by
    apply Finset.prod_congr rfl
    intro n hn
    rw [← fourierPhase_eq_e]
    unfold fourierPhase
    dsimp [t]
    congr 2
    push_cast
    ring
  rw [hphase, hprod]
  exact expectationCenteredTerm_eq_centeredProduct A p t

/-- A central prescribed Fourier coefficient has nonnegative real part. -/
theorem central_twistedProduct_re_nonneg
    (A : Finset ℕ) (p : ℕ → ℝ) (h : ℤ) (y : ℝ)
    (hp0 : ∀ n ∈ A, 0 ≤ p n) (hp1 : ∀ n ∈ A, p n ≤ 1)
    (hmean : ∑ n ∈ A, p n / n = y)
    (hangle : ∀ n ∈ A, |2 * Real.pi * (h : ℝ) / n| ≤ 1)
    (hcubic : 2 * ∑ n ∈ A, |2 * Real.pi * (h : ℝ) / n| ^ 3 ≤
      (1 / 7 : ℝ)) :
    0 ≤ (UnitFractions.e (-(h : ℝ) * y) *
      ∏ n ∈ A, ((1 - p n : ℝ) + p n * UnitFractions.e ((h : ℝ) / n))).re := by
  rw [twistedProduct_eq_centered A p h y hmean]
  exact central_centeredProduct_re_nonneg A p
    (fun n ↦ 2 * Real.pi * (h : ℝ) / n) hp0 hp1 hangle hcubic

/-- The target twist has norm one and hence does not affect quadratic decay. -/
theorem norm_twistedProduct_le_exp
    (A : Finset ℕ) (p : ℕ → ℝ) (h : ℤ) (y : ℝ)
    (hp0 : ∀ n ∈ A, 0 ≤ p n) (hp1 : ∀ n ∈ A, p n ≤ 1) :
    ‖UnitFractions.e (-(h : ℝ) * y) *
      ∏ n ∈ A, ((1 - p n : ℝ) + p n * UnitFractions.e ((h : ℝ) / n))‖ ≤
      Real.exp (-(8 * ∑ n ∈ A,
        p n * (1 - p n) * circleDistance ((h : ℝ) / n) ^ 2)) := by
  rw [norm_mul, UnitFractions.norm_e, one_mul]
  have heq :
      ∏ n ∈ A, ((1 - p n : ℝ) + p n * UnitFractions.e ((h : ℝ) / n)) =
        ∏ n ∈ A, bernoulliFactor (p n) ((h : ℝ) / n) := by
    apply Finset.prod_congr rfl
    intro n hn
    unfold bernoulliFactor
    rw [fourierPhase_eq_e]
  rw [heq]
  exact bernoulliFactor_prod_norm_le_exp A p
    (fun n ↦ (h : ℝ) / n) hp0 hp1

lemma circleDistance_eq_abs_of_abs_le_half {x : ℝ} (hx : |x| ≤ 1 / 2) :
    circleDistance x = |x| := by
  unfold circleDistance
  exact (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (by norm_num)).2 (by simpa using hx)

end

end Erdos294.WeightedMajor
