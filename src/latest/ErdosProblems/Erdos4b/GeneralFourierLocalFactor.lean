/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Complex local factors for the doubled Selberg kernel

The pair polynomial is the exact contribution from a prime in the left
coefficient, the right coefficient, or both.  Its rational comparison
factor is the local factor of the zeta quotient.  All bounds below are
uniform on the closed complex unit disk.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def selbergPairPolynomial (X Y : ℂ) : ℂ := -X - Y + X * Y

def selbergPairZetaFactor (p : ℝ) (X Y : ℂ) : ℂ :=
  (1 - X / p) * (1 - Y / p) / (1 - X * Y / p)

theorem selbergPairPolynomial_add_one (X Y : ℂ) :
    selbergPairPolynomial X Y + 1 = (1 - X) * (1 - Y) := by
  unfold selbergPairPolynomial
  ring

theorem norm_selbergPairPolynomial_le_three {X Y : ℂ}
    (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    ‖selbergPairPolynomial X Y‖ ≤ 3 := by
  calc
    _ ≤ ‖-X - Y‖ + ‖X * Y‖ := norm_add_le _ _
    _ ≤ (‖X‖ + ‖Y‖) + ‖X‖ * ‖Y‖ := by
      rw [norm_mul]
      exact add_le_add
        (by simpa only [norm_neg] using norm_sub_le (-X) Y) le_rfl
    _ ≤ (1 + 1) + 1 * 1 := by gcongr
    _ = 3 := by norm_num

theorem norm_one_sub_complex_le_two {X : ℂ} (hX : ‖X‖ ≤ 1) :
    ‖1 - X‖ ≤ 2 := by
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖X‖ := norm_sub_le _ _
    _ ≤ 2 := by simpa only [norm_one] using (by linarith : 1 + ‖X‖ ≤ 2)

theorem norm_selbergPairPolynomial_add_one_le {X Y : ℂ} (hY : ‖Y‖ ≤ 1) :
    ‖selbergPairPolynomial X Y + 1‖ ≤ 2 * ‖X - 1‖ := by
  rw [selbergPairPolynomial_add_one, norm_mul, norm_sub_rev (1 : ℂ) X]
  calc
    _ ≤ ‖X - 1‖ * 2 :=
      mul_le_mul_of_nonneg_left (norm_one_sub_complex_le_two hY) (norm_nonneg _)
    _ = _ := by ring

theorem norm_complex_div_le_inv {p : ℝ} (hp : 0 < p)
    {X : ℂ} (hX : ‖X‖ ≤ 1) : ‖X / (p : ℂ)‖ ≤ 1 / p := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  exact div_le_div_of_nonneg_right hX hp.le

theorem half_le_norm_one_sub_complex_div {p : ℝ} (hp : 2 ≤ p)
    {X : ℂ} (hX : ‖X‖ ≤ 1) :
    (1 / 2 : ℝ) ≤ ‖1 - X / (p : ℂ)‖ := by
  have hp0 : 0 < p := by linarith
  have hdiv : ‖X / (p : ℂ)‖ ≤ 1 / 2 :=
    (norm_complex_div_le_inv hp0 hX).trans
      (one_div_le_one_div_of_le (by norm_num) hp)
  have h := norm_sub_norm_le (1 : ℂ) (X / (p : ℂ))
  rw [norm_one] at h
  linarith

theorem selbergPairZetaFactor_identity {p : ℝ} (hp : p ≠ 0)
    {X Y : ℂ} (hden : 1 - X * Y / (p : ℂ) ≠ 0) :
    selbergPairZetaFactor p X Y = 1 + selbergPairPolynomial X Y / p +
      X * Y * (1 - X) * (1 - Y) /
        ((p : ℂ) ^ 2 * (1 - X * Y / p)) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hden' : (p : ℂ) - X * Y ≠ 0 := by
    intro h
    apply hden
    rw [← sub_eq_zero.mp h, div_self hpC]
    ring
  unfold selbergPairZetaFactor selbergPairPolynomial
  field_simp [hpC, hden, hden']
  ring

theorem norm_selbergPairZetaFactor_error_le {p : ℝ} (hp : 2 ≤ p)
    {X Y : ℂ} (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    ‖selbergPairZetaFactor p X Y -
      (1 + selbergPairPolynomial X Y / p)‖ ≤ 8 / p ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hXY : ‖X * Y‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg X, norm_nonneg Y]
  have hden := half_le_norm_one_sub_complex_div hp hXY
  have hden0 : 1 - X * Y / (p : ℂ) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hden
    norm_num at hden
  rw [selbergPairZetaFactor_identity hp0.ne' hden0, add_sub_cancel_left]
  rw [norm_div, norm_mul ((p : ℂ) ^ 2), norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hp0]
  have hnum : ‖X * Y * (1 - X) * (1 - Y)‖ ≤ 4 := by
    rw [norm_mul, norm_mul]
    have hX2 := norm_one_sub_complex_le_two hX
    have hY2 := norm_one_sub_complex_le_two hY
    calc
      ‖X * Y‖ * ‖1 - X‖ * ‖1 - Y‖ ≤ 1 * 2 * 2 := by gcongr
      _ = 4 := by norm_num
  calc
    _ ≤ 4 / (p ^ 2 * (1 / 2)) := by
      apply div_le_div₀ (by positivity) hnum (by positivity)
      exact mul_le_mul_of_nonneg_left hden (sq_nonneg p)
    _ = 8 / p ^ 2 := by ring

theorem norm_selbergPairZetaFactor_sub_one_le {p : ℝ} (hp : 2 ≤ p)
    {X Y : ℂ} (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    ‖selbergPairZetaFactor p X Y - 1‖ ≤ 7 / p := by
  have hp0 : 0 < p := by linarith
  calc
    _ ≤ ‖selbergPairZetaFactor p X Y -
        (1 + selbergPairPolynomial X Y / p)‖ +
        ‖(1 + selbergPairPolynomial X Y / (p : ℂ)) - 1‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 8 / p ^ 2 + 3 / p := by
      apply add_le_add (norm_selbergPairZetaFactor_error_le hp hX hY)
      rw [add_sub_cancel_left, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hp0]
      exact div_le_div_of_nonneg_right
        (norm_selbergPairPolynomial_le_three hX hY) hp0.le
    _ ≤ 7 / p := by
      field_simp
      nlinarith

theorem one_sixth_le_norm_selbergPairZetaFactor {p : ℝ} (hp : 2 ≤ p)
    {X Y : ℂ} (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    (1 / 6 : ℝ) ≤ ‖selbergPairZetaFactor p X Y‖ := by
  have hp0 : 0 < p := by linarith
  have hXY : ‖X * Y‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg X, norm_nonneg Y]
  have hdenlow := half_le_norm_one_sub_complex_div hp hXY
  have hdenup : ‖1 - X * Y / (p : ℂ)‖ ≤ 3 / 2 := by
    have hdiv : ‖X * Y / (p : ℂ)‖ ≤ 1 / 2 :=
      (norm_complex_div_le_inv hp0 hXY).trans
        (one_div_le_one_div_of_le (by norm_num) hp)
    have h := norm_sub_le (1 : ℂ) (X * Y / (p : ℂ))
    rw [norm_one] at h
    linarith
  have hnum : (1 / 2 : ℝ) * (1 / 2) ≤
      ‖1 - X / (p : ℂ)‖ * ‖1 - Y / (p : ℂ)‖ :=
    mul_le_mul (half_le_norm_one_sub_complex_div hp hX)
      (half_le_norm_one_sub_complex_div hp hY) (by norm_num) (norm_nonneg _)
  rw [selbergPairZetaFactor, norm_div, norm_mul]
  calc
    (1 / 6 : ℝ) = ((1 / 2) * (1 / 2)) / (3 / 2) := by norm_num
    _ ≤ _ := div_le_div₀ (by positivity) hnum (by linarith) hdenup

theorem selbergPairZetaFactor_ne_zero {p : ℝ} (hp : 2 ≤ p)
    {X Y : ℂ} (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    selbergPairZetaFactor p X Y ≠ 0 := by
  have h := one_sixth_le_norm_selbergPairZetaFactor hp hX hY
  intro hz
  rw [hz, norm_zero] at h
  norm_num at h

theorem selbergPairZetaFactor_at_zero_exponents {p : ℝ} (hp : 2 ≤ p) :
    selbergPairZetaFactor p 1 1 = 1 - 1 / (p : ℂ) := by
  have hden : 1 - 1 / (p : ℂ) ≠ 0 := by
    have h := half_le_norm_one_sub_complex_div hp (X := 1) (by simp)
    intro hz
    rw [hz, norm_zero] at h
    norm_num at h
  simp only [selbergPairZetaFactor, one_mul]
  exact mul_div_cancel_right₀ _ hden

/-- The complex product error inequality used for all uniform local errors. -/
theorem norm_prod_one_add_error_le {ι : Type*} (s : Finset ι) (e : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + e i)) - 1‖ ≤
      Real.exp (∑ i ∈ s, ‖e i‖) - 1 :=
  s.norm_prod_one_add_sub_one_le e

/-- The exponential is Lipschitz with constant one along a segment in
the closed left half-plane starting at zero. -/
theorem norm_complex_exp_sub_one_le_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) :
    ‖Complex.exp z - 1‖ ≤ ‖z‖ := by
  have hderiv (t : ℝ) :
      HasDerivAt (fun t : ℝ ↦ Complex.exp ((t : ℂ) * z))
        (Complex.exp ((t : ℂ) * z) * z) t := by
    simpa only [Function.comp_def, id_eq, mul_one, one_mul] using!
      ((Complex.hasDerivAt_exp ((t : ℂ) * z)).comp (t : ℂ)
        ((hasDerivAt_id (t : ℂ)).mul_const z)).comp_ofReal
  have hbound (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      ‖Complex.exp ((t : ℂ) * z) * z‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_exp]
    have hre : ((t : ℂ) * z).re ≤ 0 := by
      simpa using mul_nonpos_of_nonneg_of_nonpos ht.1 hz
    have he : Real.exp (((t : ℂ) * z).re) ≤ 1 := by
      simpa using Real.exp_le_exp.mpr hre
    simpa using mul_le_mul_of_nonneg_right he (norm_nonneg z)
  simpa using norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ ↦ (hderiv t).hasDerivWithinAt) hbound

def primeFourierPower (p : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-(s * (Real.log p : ℂ)))

theorem norm_primeFourierPower_le_one {p : ℝ} (hp : 1 ≤ p)
    {s : ℂ} (hs : 0 ≤ s.re) : ‖primeFourierPower p s‖ ≤ 1 := by
  rw [primeFourierPower, Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact neg_nonpos.mpr (mul_nonneg hs (Real.log_nonneg hp))

theorem norm_primeFourierPower_sub_one_le {p : ℝ} (hp : 1 ≤ p)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖primeFourierPower p s - 1‖ ≤ ‖s‖ * Real.log p := by
  have hre : (-(s * (Real.log p : ℂ))).re ≤ 0 := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    exact neg_nonpos.mpr (mul_nonneg hs (Real.log_nonneg hp))
  simpa only [primeFourierPower, norm_neg, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hp)] using
    norm_complex_exp_sub_one_le_of_re_nonpos hre

theorem norm_selbergPairPolynomial_primeFourierPowers_add_one_le
    {p σ : ℝ} (hp : 1 ≤ p) {s t : ℂ}
    (hs : 0 ≤ s.re) (ht : 0 ≤ t.re) (hσ : ‖s‖ ≤ σ) :
    ‖selbergPairPolynomial (primeFourierPower p s) (primeFourierPower p t) + 1‖ ≤
      2 * σ * Real.log p := by
  calc
    _ ≤ 2 * ‖primeFourierPower p s - 1‖ :=
      norm_selbergPairPolynomial_add_one_le (norm_primeFourierPower_le_one hp ht)
    _ ≤ 2 * (‖s‖ * Real.log p) :=
      mul_le_mul_of_nonneg_left (norm_primeFourierPower_sub_one_le hp hs) (by norm_num)
    _ ≤ 2 * (σ * Real.log p) := by
      gcongr
      exact Real.log_nonneg hp
    _ = _ := by ring

/-- Varying finite prime sets cause no problem once their total local
norm error tends to zero. -/
theorem tendsto_prod_one_add_of_sum_norm_tendsto_zero
    {α ι : Type*} {l : Filter α} (s : α → Finset ι) (e : α → ι → ℂ)
    (h : Filter.Tendsto (fun a ↦ ∑ i ∈ s a, ‖e a i‖) l (nhds 0)) :
    Filter.Tendsto (fun a ↦ ∏ i ∈ s a, (1 + e a i)) l (nhds 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun a ↦ norm_nonneg _)
    (fun a ↦ norm_prod_one_add_error_le (s a) (e a))
  simpa using ((Real.continuous_exp.tendsto 0).comp h).sub_const 1

/-- The quadratic remainder in a finite complex product, with its
linear terms removed exactly. -/
theorem norm_prod_one_add_sub_one_sub_sum_le_exp
    {ι : Type*} (s : Finset ι) (e : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + e i)) - 1 - ∑ i ∈ s, e i‖ ≤
      Real.exp (∑ i ∈ s, ‖e i‖) - 1 - ∑ i ∈ s, ‖e i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    have hid : (1 + e a) * (∏ i ∈ s, (1 + e i)) - 1 -
        (e a + ∑ i ∈ s, e i) =
        (1 + e a) * ((∏ i ∈ s, (1 + e i)) - 1 - ∑ i ∈ s, e i) +
          e a * ∑ i ∈ s, e i := by ring
    rw [hid]
    have hlinear : ‖1 + e a‖ ≤ 1 + ‖e a‖ := by
      simpa using norm_add_le (1 : ℂ) (e a)
    have hexp : 0 ≤ Real.exp (∑ i ∈ s, ‖e i‖) - 1 -
        ∑ i ∈ s, ‖e i‖ := by
      linarith [Real.add_one_le_exp (∑ i ∈ s, ‖e i‖)]
    calc
      _ ≤ ‖1 + e a‖ * ‖(∏ i ∈ s, (1 + e i)) - 1 - ∑ i ∈ s, e i‖ +
          ‖e a‖ * ‖∑ i ∈ s, e i‖ := by
        simpa only [norm_mul] using norm_add_le
          ((1 + e a) * ((∏ i ∈ s, (1 + e i)) - 1 - ∑ i ∈ s, e i))
          (e a * ∑ i ∈ s, e i)
      _ ≤ (1 + ‖e a‖) * (Real.exp (∑ i ∈ s, ‖e i‖) - 1 -
          ∑ i ∈ s, ‖e i‖) + ‖e a‖ * ∑ i ∈ s, ‖e i‖ := by
        exact add_le_add
          (mul_le_mul hlinear ih (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left (norm_sum_le s e) (norm_nonneg _))
      _ = (1 + ‖e a‖) * Real.exp (∑ i ∈ s, ‖e i‖) - 1 -
          (‖e a‖ + ∑ i ∈ s, ‖e i‖) := by ring
      _ ≤ _ := by
        rw [Real.exp_add]
        gcongr
        simpa only [add_comm] using Real.add_one_le_exp ‖e a‖

theorem norm_prod_one_add_sub_one_sub_sum_le_sq
    {ι : Type*} (s : Finset ι) (e : ι → ℂ)
    (hsmall : (∑ i ∈ s, ‖e i‖) ≤ 1) :
    ‖(∏ i ∈ s, (1 + e i)) - 1 - ∑ i ∈ s, e i‖ ≤
      (∑ i ∈ s, ‖e i‖) ^ 2 := by
  have hnonneg : 0 ≤ ∑ i ∈ s, ‖e i‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  calc
    _ ≤ Real.exp (∑ i ∈ s, ‖e i‖) - 1 - ∑ i ∈ s, ‖e i‖ :=
      norm_prod_one_add_sub_one_sub_sum_le_exp s e
    _ ≤ ‖Real.exp (∑ i ∈ s, ‖e i‖) - 1 - ∑ i ∈ s, ‖e i‖‖ :=
      Real.le_norm_self _
    _ ≤ _ := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
        Real.norm_exp_sub_one_sub_id_le (x := ∑ i ∈ s, ‖e i‖)
          (by simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hsmall)

/-- A finite product of pair zeta factors has the sum of the pair
polynomials as its exact first-order term.  The explicit constant depends
only on the number of pairs, not on their Fourier variables. -/
theorem norm_prod_selbergPairZetaFactor_error_le
    {ι : Type*} (s : Finset ι) (X Y : ι → ℂ) {p : ℝ}
    (hp : 2 ≤ p) (hcard : 7 * (s.card : ℝ) ≤ p)
    (hX : ∀ i ∈ s, ‖X i‖ ≤ 1) (hY : ∀ i ∈ s, ‖Y i‖ ≤ 1) :
    ‖(∏ i ∈ s, selbergPairZetaFactor p (X i) (Y i)) -
        (1 + (∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) / p)‖ ≤
      ((7 * (s.card : ℝ)) ^ 2 + 8 * s.card) / p ^ 2 := by
  let e : ι → ℂ := fun i ↦ selbergPairZetaFactor p (X i) (Y i) - 1
  have hp0 : 0 < p := by linarith
  have hsum : (∑ i ∈ s, ‖e i‖) ≤ 7 * (s.card : ℝ) / p := by
    calc
      _ ≤ ∑ _i ∈ s, 7 / p := Finset.sum_le_sum fun i hi ↦
        norm_selbergPairZetaFactor_sub_one_le hp (hX i hi) (hY i hi)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hsmall : (∑ i ∈ s, ‖e i‖) ≤ 1 :=
    hsum.trans ((div_le_one hp0).mpr hcard)
  have hrem := norm_prod_one_add_sub_one_sub_sum_le_sq s e hsmall
  have hprod : (∏ i ∈ s, selbergPairZetaFactor p (X i) (Y i)) =
      ∏ i ∈ s, (1 + e i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [e]
  have hlinear :
      ‖(∑ i ∈ s, e i) - (∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) / p‖ ≤
        8 * (s.card : ℝ) / p ^ 2 := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ s, ‖e i - selbergPairPolynomial (X i) (Y i) / (p : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, 8 / p ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have heq : e i - selbergPairPolynomial (X i) (Y i) / (p : ℂ) =
            selbergPairZetaFactor p (X i) (Y i) -
              (1 + selbergPairPolynomial (X i) (Y i) / p) := by
          dsimp [e]
          ring
        rw [heq]
        exact norm_selbergPairZetaFactor_error_le hp (hX i hi) (hY i hi)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hprod]
  have hid : (∏ i ∈ s, (1 + e i)) -
      (1 + (∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) / (p : ℂ)) =
      ((∏ i ∈ s, (1 + e i)) - 1 - ∑ i ∈ s, e i) +
      ((∑ i ∈ s, e i) - (∑ i ∈ s, selbergPairPolynomial (X i) (Y i)) / p) := by
    ring
  rw [hid]
  calc
    _ ≤ (∑ i ∈ s, ‖e i‖) ^ 2 + 8 * (s.card : ℝ) / p ^ 2 :=
      (norm_add_le _ _).trans (add_le_add hrem hlinear)
    _ ≤ (7 * (s.card : ℝ) / p) ^ 2 + 8 * (s.card : ℝ) / p ^ 2 := by
      gcongr
    _ = _ := by ring

theorem pow_one_sixth_le_norm_prod_selbergPairZetaFactor
    {ι : Type*} (s : Finset ι) (X Y : ι → ℂ) {p : ℝ} (hp : 2 ≤ p)
    (hX : ∀ i ∈ s, ‖X i‖ ≤ 1) (hY : ∀ i ∈ s, ‖Y i‖ ≤ 1) :
    (1 / 6 : ℝ) ^ s.card ≤
      ‖∏ i ∈ s, selbergPairZetaFactor p (X i) (Y i)‖ := by
  rw [norm_prod]
  calc
    (1 / 6 : ℝ) ^ s.card = ∏ _i ∈ s, (1 / 6 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (by intro i hi; norm_num)
      (fun i hi ↦ one_sixth_le_norm_selbergPairZetaFactor hp (hX i hi) (hY i hi))

/-- Exact comparison identity separating a shared linear perturbation
from the two quadratic remainders. -/
theorem quotient_linear_comparison_identity
    (a b₀ g e r : ℂ) (hb₀ : b₀ ≠ 0) (hb : b₀ + g + r ≠ 0) :
    (a + g + e) / (b₀ + g + r) - a / b₀ =
      ((b₀ - a) * g + b₀ * e - a * r) / ((b₀ + g + r) * b₀) := by
  field_simp
  ring

theorem norm_quotient_linear_comparison_le
    (a b₀ g e r : ℂ) (hb₀ : b₀ ≠ 0) (hb : b₀ + g + r ≠ 0) :
    ‖(a + g + e) / (b₀ + g + r) - a / b₀‖ ≤
      (‖b₀ - a‖ * ‖g‖ + ‖b₀‖ * ‖e‖ + ‖a‖ * ‖r‖) /
        (‖b₀ + g + r‖ * ‖b₀‖) := by
  rw [quotient_linear_comparison_identity a b₀ g e r hb₀ hb, norm_div,
    norm_mul (b₀ + g + r) b₀]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ‖(b₀ - a) * g + b₀ * e‖ + ‖a * r‖ := norm_sub_le _ _
    _ ≤ (‖(b₀ - a) * g‖ + ‖b₀ * e‖) + ‖a * r‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by simp only [norm_mul]

end

end Erdos4b
