import ErdosProblems.Erdos520.HarperCharacteristic
import ErdosProblems.Erdos520.HarperCubicTail

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate

namespace Erdos
namespace Problem520

/-!
# Gaussian characteristic approximation for a finite tilted prime block

The one-prime characteristic estimate in `HarperCharacteristic` is first
accumulated with a finite-product perturbation lemma.  A second perturbation
replaces each factor `1 - q_p` by `exp (-q_p)`.  The product of the latter
factors is exactly the Gaussian characteristic function with the block
variance from `HarperPrimeBlocks`.
-/

/-! ## Deterministic finite-product estimates -/

/-- A telescoping perturbation bound for finite products in `ℂ`.  If both
families lie in the closed unit disk, the product error is at most the sum
of the coordinate errors. -/
theorem norm_prod_sub_prod_le_sum_norm_sub
    {ι : Type*} (S : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ 1)
    (hg : ∀ i ∈ S, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤
      ∑ i ∈ S, ‖f i - g i‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hfa : ‖f a‖ ≤ 1 := hf a (Finset.mem_insert_self a S)
      have hga : ‖g a‖ ≤ 1 := hg a (Finset.mem_insert_self a S)
      have hfS : ∀ i ∈ S, ‖f i‖ ≤ 1 := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hgS : ∀ i ∈ S, ‖g i‖ ≤ 1 := by
        intro i hi
        exact hg i (Finset.mem_insert_of_mem hi)
      have hprodF : ‖∏ i ∈ S, f i‖ ≤ 1 := by
        rw [Complex.norm_prod]
        exact Finset.prod_le_one
          (fun i hi ↦ norm_nonneg (f i)) hfS
      have htail := ih hfS hgS
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.sum_insert ha]
      calc
        ‖f a * (∏ i ∈ S, f i) - g a * ∏ i ∈ S, g i‖ =
            ‖(f a - g a) * (∏ i ∈ S, f i) +
              g a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)‖ := by
          congr 1
          ring
        _ ≤ ‖f a - g a‖ * ‖∏ i ∈ S, f i‖ +
              ‖g a‖ * ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ := by
          exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
        _ ≤ ‖f a - g a‖ * 1 + 1 *
              (∑ i ∈ S, ‖f i - g i‖) := by
          gcongr
        _ = ‖f a - g a‖ + ∑ i ∈ S, ‖f i - g i‖ := by ring

/-- The first-order exponential approximation on `[0,1]`, in the complex
norm needed by the product perturbation argument. -/
theorem norm_one_sub_sub_exp_neg_le_sq
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖((1 : ℂ) - (q : ℂ)) - Complex.exp (-(q : ℂ))‖ ≤ q ^ 2 := by
  have hnorm : ‖-(q : ℂ)‖ ≤ 1 := by
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hq0]
    exact hq1
  have hExp := Complex.norm_exp_sub_one_sub_id_le hnorm
  calc
    ‖((1 : ℂ) - (q : ℂ)) - Complex.exp (-(q : ℂ))‖ =
        ‖Complex.exp (-(q : ℂ)) - 1 - (-(q : ℂ))‖ := by
      rw [← norm_neg]
      congr 1
      ring
    _ ≤ ‖-(q : ℂ)‖ ^ 2 := hExp
    _ = q ^ 2 := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]

/-! ## Prime quadratic factors -/

/-- The nonnegative quadratic Gaussian exponent contributed by one prime. -/
noncomputable def harperPrimeGaussianQuadratic
    (p : ℕ) (t u v : ℝ) : ℝ :=
  v ^ 2 * harperCenteredLinearPrimeVariance p t u / 2

theorem harperCenteredLinearPrimeVariance_nonneg
    (p : ℕ) (t u : ℝ) :
    0 ≤ harperCenteredLinearPrimeVariance p t u := by
  rw [← integral_harperCenteredLinearPrimeIncrement_sq]
  exact integral_nonneg fun b ↦ sq_nonneg _

theorem harperPrimeGaussianQuadratic_nonneg
    (p : ℕ) (t u v : ℝ) :
    0 ≤ harperPrimeGaussianQuadratic p t u v := by
  unfold harperPrimeGaussianQuadratic
  exact div_nonneg
    (mul_nonneg (sq_nonneg v)
      (harperCenteredLinearPrimeVariance_nonneg p t u))
    (by norm_num)

/-- The sum of the one-prime quadratic exponents is exactly half `v²`
times the block variance already computed in `HarperPrimeBlocks`. -/
theorem sum_harperPrimeGaussianQuadratic
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u v : ℝ) :
    (∑ p ∈ S, harperPrimeGaussianQuadratic p.1 t u v) =
      v ^ 2 * harperLinearBlockVariance y S t u / 2 := by
  unfold harperPrimeGaussianQuadratic harperLinearBlockVariance
    harperLinearPrimeCenteredVariance harperCenteredLinearPrimeVariance
  rw [← Finset.sum_div, ← Finset.mul_sum]

/-- Every one-prime characteristic function lies in the closed unit disk. -/
theorem norm_harperTiltedLinearPrimeCharacteristic_le_one
    (p : ℕ) (t u v : ℝ) :
    ‖harperTiltedLinearPrimeCharacteristic p t u v‖ ≤ 1 := by
  unfold harperTiltedLinearPrimeCharacteristic
  calc
    ‖∫ b, Complex.exp (harperCharacteristicExponent p t u v b)
        ∂harperTiltedCoin p t‖ ≤
        ∫ b, ‖Complex.exp (harperCharacteristicExponent p t u v b)‖
          ∂harperTiltedCoin p t :=
      norm_integral_le_integral_norm _
    _ = ∫ _b : Bool, (1 : ℝ) ∂harperTiltedCoin p t := by
      apply integral_congr_ae
      exact ae_of_all _ fun b ↦ by
        unfold harperCharacteristicExponent
        change ‖Complex.exp
          (((v * harperCenteredLinearPrimeIncrement p t u b : ℝ) : ℂ) *
            Complex.I)‖ = 1
        exact Complex.norm_exp_ofReal_mul_I _
    _ = 1 := by
      rw [integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem norm_one_sub_harperPrimeGaussianQuadratic_le_one
    {p : ℕ} {t u v : ℝ}
    (hq : harperPrimeGaussianQuadratic p t u v ≤ 1) :
    ‖(1 : ℂ) - (harperPrimeGaussianQuadratic p t u v : ℂ)‖ ≤ 1 := by
  have hq0 := harperPrimeGaussianQuadratic_nonneg p t u v
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hq)]
  linarith

theorem norm_exp_neg_harperPrimeGaussianQuadratic_le_one
    (p : ℕ) (t u v : ℝ) :
    ‖Complex.exp (-(harperPrimeGaussianQuadratic p t u v : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  exact Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (harperPrimeGaussianQuadratic_nonneg p t u v))

/-- Product of the one-prime Gaussian factors is the Gaussian factor for
the sum of their exponents. -/
theorem prod_exp_neg_harperPrimeGaussianQuadratic
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u v : ℝ) :
    (∏ p ∈ S,
        Complex.exp (-(harperPrimeGaussianQuadratic p.1 t u v : ℂ))) =
      Complex.exp
        (-((v ^ 2 * harperLinearBlockVariance y S t u / 2 : ℝ) : ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [← sum_harperPrimeGaussianQuadratic y S t u v]
  push_cast
  rw [Finset.sum_neg_distrib]

/-! ## Block characteristic versus Gaussian -/

/-- Quantitative Gaussian comparison for an arbitrary finite prime block.
The first sum is the accumulated cubic characteristic error; the second is
the accumulated error in replacing `1-q_p` by `exp(-q_p)`. -/
theorem norm_harperTiltedLinearPrimeBlockCharacteristic_sub_gaussian_le
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (h4 : ∀ p ∈ S, 4 ≤ p.1)
    (t u v : ℝ)
    (hsmall : ∀ p ∈ S,
      |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) ≤ 1)
    (hquad : ∀ p ∈ S,
      harperPrimeGaussianQuadratic p.1 t u v ≤ 1 / 2) :
    ‖harperTiltedLinearPrimeBlockCharacteristic y S t u v -
        Complex.exp
          (-((v ^ 2 * harperLinearBlockVariance y S t u / 2 : ℝ) : ℂ))‖ ≤
      (∑ p ∈ S,
        8 * |v| ^ 3 * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) +
      ∑ p ∈ S, harperPrimeGaussianQuadratic p.1 t u v ^ 2 := by
  let phi : HarperPrimeIndex y → ℂ :=
    fun p ↦ harperTiltedLinearPrimeCharacteristic p.1 t u v
  let linearGaussian : HarperPrimeIndex y → ℂ :=
    fun p ↦ (1 : ℂ) - (harperPrimeGaussianQuadratic p.1 t u v : ℂ)
  let exactGaussian : HarperPrimeIndex y → ℂ :=
    fun p ↦ Complex.exp (-(harperPrimeGaussianQuadratic p.1 t u v : ℂ))
  have hphi : ∀ p ∈ S, ‖phi p‖ ≤ 1 := by
    intro p hp
    exact norm_harperTiltedLinearPrimeCharacteristic_le_one p.1 t u v
  have hlinear : ∀ p ∈ S, ‖linearGaussian p‖ ≤ 1 := by
    intro p hp
    apply norm_one_sub_harperPrimeGaussianQuadratic_le_one
    linarith [hquad p hp]
  have hexact : ∀ p ∈ S, ‖exactGaussian p‖ ≤ 1 := by
    intro p hp
    exact norm_exp_neg_harperPrimeGaussianQuadratic_le_one p.1 t u v
  have hfirst := norm_prod_sub_prod_le_sum_norm_sub S phi linearGaussian
    hphi hlinear
  have hsecond := norm_prod_sub_prod_le_sum_norm_sub S linearGaussian exactGaussian
    hlinear hexact
  have hfirstBound :
      ‖(∏ p ∈ S, phi p) - ∏ p ∈ S, linearGaussian p‖ ≤
        ∑ p ∈ S,
          8 * |v| ^ 3 * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3 := by
    exact hfirst.trans (Finset.sum_le_sum fun p hp ↦ by
      simpa only [phi, linearGaussian, harperPrimeGaussianQuadratic] using!
        norm_harperTiltedLinearPrimeCharacteristic_sub_quadratic_le
          (h4 p hp) t u v (hsmall p hp))
  have hsecondBound :
      ‖(∏ p ∈ S, linearGaussian p) - ∏ p ∈ S, exactGaussian p‖ ≤
        ∑ p ∈ S, harperPrimeGaussianQuadratic p.1 t u v ^ 2 := by
    exact hsecond.trans (Finset.sum_le_sum fun p hp ↦ by
      simpa only [linearGaussian, exactGaussian] using!
        norm_one_sub_sub_exp_neg_le_sq
          (harperPrimeGaussianQuadratic_nonneg p.1 t u v)
          (by linarith [hquad p hp] :
            harperPrimeGaussianQuadratic p.1 t u v ≤ 1))
  rw [harperTiltedLinearPrimeBlockCharacteristic_eq_prod,
    ← prod_exp_neg_harperPrimeGaussianQuadratic y S t u v]
  calc
    ‖(∏ p ∈ S, phi p) - ∏ p ∈ S, exactGaussian p‖ ≤
        ‖(∏ p ∈ S, phi p) - ∏ p ∈ S, linearGaussian p‖ +
          ‖(∏ p ∈ S, linearGaussian p) - ∏ p ∈ S, exactGaussian p‖ := by
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (∑ p ∈ S,
          8 * |v| ^ 3 * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) +
        ∑ p ∈ S, harperPrimeGaussianQuadratic p.1 t u v ^ 2 :=
      add_le_add hfirstBound hsecondBound

/-- The cubic part of the preceding arbitrary-block estimate is exactly
`12 |v|³` times the logarithmic cubic budget from `HarperPrimeBlocks`. -/
theorem sum_characteristicCubic_eq_blockCubicRemainder
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (v : ℝ) :
    (∑ p ∈ S, 8 * |v| ^ 3 * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) =
      12 * |v| ^ 3 * harperBlockCubicRemainder y S := by
  unfold harperBlockCubicRemainder
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Scheduled-block form: the explicit cubic characteristic budget is
bounded by the inverse square root of the block's lower endpoint. -/
theorem norm_harperScheduledBlockCharacteristic_sub_gaussian_le
    (y j : ℕ) (t u v : ℝ)
    (hsmall : ∀ p ∈ harperScheduledPrimeBlock y j,
      |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) ≤ 1)
    (hquad : ∀ p ∈ harperScheduledPrimeBlock y j,
      harperPrimeGaussianQuadratic p.1 t u v ≤ 1 / 2) :
    ‖harperTiltedLinearPrimeBlockCharacteristic y
          (harperScheduledPrimeBlock y j) t u v -
        Complex.exp
          (-((v ^ 2 * harperLinearBlockVariance y
            (harperScheduledPrimeBlock y j) t u / 2 : ℝ) : ℂ))‖ ≤
      16 * |v| ^ 3 *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ +
        ∑ p ∈ harperScheduledPrimeBlock y j,
          harperPrimeGaussianQuadratic p.1 t u v ^ 2 := by
  let S := harperScheduledPrimeBlock y j
  have hgeneral :=
    norm_harperTiltedLinearPrimeBlockCharacteristic_sub_gaussian_le
      y S (fun p hp ↦ four_le_prime_of_mem_harperScheduledPrimeBlock hp)
      t u v hsmall hquad
  rw [sum_characteristicCubic_eq_blockCubicRemainder] at hgeneral
  have hcubic := harperBlockCubicRemainder_scheduled_le y j
  calc
    ‖harperTiltedLinearPrimeBlockCharacteristic y S t u v -
        Complex.exp
          (-((v ^ 2 * harperLinearBlockVariance y S t u / 2 : ℝ) : ℂ))‖ ≤
        12 * |v| ^ 3 * harperBlockCubicRemainder y S +
          ∑ p ∈ S, harperPrimeGaussianQuadratic p.1 t u v ^ 2 := hgeneral
    _ ≤ 12 * |v| ^ 3 *
          ((4 / 3 : ℝ) *
            (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) +
          ∑ p ∈ S, harperPrimeGaussianQuadratic p.1 t u v ^ 2 := by
      gcongr
    _ = 16 * |v| ^ 3 *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ +
          ∑ p ∈ S, harperPrimeGaussianQuadratic p.1 t u v ^ 2 := by ring

end Problem520
end Erdos
