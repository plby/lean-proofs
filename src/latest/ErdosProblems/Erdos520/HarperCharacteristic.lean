import ErdosProblems.Erdos520.HarperTiltedBounds
import Mathlib.Analysis.Complex.Exponential

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate

namespace Erdos
namespace Problem520

/-!
# Characteristic function of one tilted prime coordinate

For the linearized logarithmic increment at a fixed prime, this file centers
the coordinate by its exact tilted mean and expands its characteristic
function through second order.  The error is controlled explicitly by the
cubic absolute-moment envelope from `HarperTiltedBounds`.
-/

/-- The linearized one-prime increment centered by its exact tilted mean. -/
noncomputable def harperCenteredLinearPrimeIncrement
    (p : ℕ) (t u : ℝ) (b : Bool) : ℝ :=
  harperLinearPrimeIncrement p u b -
    harperTiltBias p t *
      (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ))

/-- The exact second moment (and variance) of the centered one-prime
linearized increment. -/
noncomputable def harperCenteredLinearPrimeVariance
    (p : ℕ) (t u : ℝ) : ℝ :=
  (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ)) ^ 2 *
    (1 - harperTiltBias p t ^ 2)

/-- The centered coordinate has mean zero under its tilted coin. -/
theorem integral_harperCenteredLinearPrimeIncrement
    (p : ℕ) (t u : ℝ) :
    (∫ b, harperCenteredLinearPrimeIncrement p t u b
        ∂harperTiltedCoin p t) = 0 := by
  rw [integral_harperTiltedCoin]
  have hlin := integral_harperLinearPrimeIncrement p t u
  rw [integral_harperTiltedCoin] at hlin
  have hsum := harperTiltedCoinWeight_false_add_true p t
  unfold harperCenteredLinearPrimeIncrement
  calc
    harperTiltedCoinWeight p t false *
          (harperLinearPrimeIncrement p u false -
            harperTiltBias p t *
              (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ))) +
        harperTiltedCoinWeight p t true *
          (harperLinearPrimeIncrement p u true -
            harperTiltBias p t *
              (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ))) =
        (harperTiltedCoinWeight p t false *
            harperLinearPrimeIncrement p u false +
          harperTiltedCoinWeight p t true *
            harperLinearPrimeIncrement p u true) -
          (harperTiltedCoinWeight p t false +
            harperTiltedCoinWeight p t true) *
            (harperTiltBias p t *
              (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ))) := by ring
    _ = 0 := by rw [hlin, hsum, one_mul, sub_self]

/-- Exact second moment of the centered coordinate. -/
theorem integral_harperCenteredLinearPrimeIncrement_sq
    (p : ℕ) (t u : ℝ) :
    (∫ b, harperCenteredLinearPrimeIncrement p t u b ^ 2
        ∂harperTiltedCoin p t) =
      harperCenteredLinearPrimeVariance p t u := by
  simpa only [harperCenteredLinearPrimeIncrement,
    harperCenteredLinearPrimeVariance] using!
      integral_harperLinearPrimeIncrement_sub_mean_sq p t u

/-- Cubic absolute moment inherited from the uniform pointwise envelope. -/
theorem integral_abs_harperCenteredLinearPrimeIncrement_pow_three_le
    {p : ℕ} (hp : 4 ≤ p) (t u : ℝ) :
    (∫ b, |harperCenteredLinearPrimeIncrement p t u b| ^ 3
        ∂harperTiltedCoin p t) ≤
      8 * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  simpa only [harperCenteredLinearPrimeIncrement] using!
    integral_abs_harperLinearPrimeIncrement_sub_mean_pow_three_le hp t u

/-- The purely imaginary exponent used in the one-coordinate
characteristic function. -/
noncomputable def harperCharacteristicExponent
    (p : ℕ) (t u v : ℝ) (b : Bool) : ℂ :=
  ((v * harperCenteredLinearPrimeIncrement p t u b : ℝ) : ℂ) * Complex.I

/-- Exact norm of the characteristic exponent. -/
theorem norm_harperCharacteristicExponent
    (p : ℕ) (t u v : ℝ) (b : Bool) :
    ‖harperCharacteristicExponent p t u v b‖ =
      |v| * |harperCenteredLinearPrimeIncrement p t u b| := by
  rw [harperCharacteristicExponent, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, abs_mul]

/-- A prime-scale smallness condition puts every characteristic exponent in
the unit ball where the explicit complex exponential Taylor bound applies. -/
theorem norm_harperCharacteristicExponent_le_one
    {p : ℕ} (hp : 4 ≤ p) (t u v : ℝ)
    (hsmall : |v| * (2 * (Real.sqrt (p : ℝ))⁻¹) ≤ 1)
    (b : Bool) :
    ‖harperCharacteristicExponent p t u v b‖ ≤ 1 := by
  rw [norm_harperCharacteristicExponent]
  exact (mul_le_mul_of_nonneg_left
      (abs_harperLinearPrimeIncrement_sub_mean_le hp t u b)
      (abs_nonneg v)).trans hsmall

/-- Second-order Taylor polynomial of the complex exponential. -/
noncomputable def harperCharacteristicQuadratic
    (p : ℕ) (t u v : ℝ) (b : Bool) : ℂ :=
  1 + harperCharacteristicExponent p t u v b +
    harperCharacteristicExponent p t u v b ^ 2 / 2

/-- Pointwise cubic remainder for the characteristic exponential.  The
constant `1` is a convenient enlargement of Mathlib's sharper `2/9` bound
for the order-three tail in the unit ball. -/
theorem norm_exp_harperCharacteristicExponent_sub_quadratic_le
    {p : ℕ} (hp : 4 ≤ p) (t u v : ℝ)
    (hsmall : |v| * (2 * (Real.sqrt (p : ℝ))⁻¹) ≤ 1)
    (b : Bool) :
    ‖Complex.exp (harperCharacteristicExponent p t u v b) -
        harperCharacteristicQuadratic p t u v b‖ ≤
      |v| ^ 3 * |harperCenteredLinearPrimeIncrement p t u b| ^ 3 := by
  let z := harperCharacteristicExponent p t u v b
  have hz : ‖z‖ ≤ 1 :=
    norm_harperCharacteristicExponent_le_one hp t u v hsmall b
  have hExp := Complex.exp_bound hz (n := 3) (by decide)
  have hpoly :
      (∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℂ)) =
        harperCharacteristicQuadratic p t u v b := by
    dsimp [harperCharacteristicQuadratic, z]
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hpoly] at hExp
  calc
    ‖Complex.exp z - harperCharacteristicQuadratic p t u v b‖ ≤
        ‖z‖ ^ 3 *
          ((Nat.succ 3 : ℝ) * ((Nat.factorial 3) * (3 : ℕ) : ℝ)⁻¹) := hExp
    _ ≤ ‖z‖ ^ 3 := by
      have hzpow : 0 ≤ ‖z‖ ^ 3 := by positivity
      norm_num [Nat.factorial]
      linarith
    _ = |v| ^ 3 *
        |harperCenteredLinearPrimeIncrement p t u b| ^ 3 := by
      rw [norm_harperCharacteristicExponent]
      ring

/-- The tilted one-coordinate characteristic function. -/
noncomputable def harperTiltedLinearPrimeCharacteristic
    (p : ℕ) (t u v : ℝ) : ℂ :=
  ∫ b, Complex.exp (harperCharacteristicExponent p t u v b)
    ∂harperTiltedCoin p t

/-- The first complex moment of the characteristic exponent vanishes. -/
theorem integral_harperCharacteristicExponent
    (p : ℕ) (t u v : ℝ) :
    (∫ b, harperCharacteristicExponent p t u v b
        ∂harperTiltedCoin p t) = 0 := by
  unfold harperCharacteristicExponent
  calc
    (∫ b,
        ((v * harperCenteredLinearPrimeIncrement p t u b : ℝ) : ℂ) *
          Complex.I ∂harperTiltedCoin p t) =
        (∫ b,
          ((v * harperCenteredLinearPrimeIncrement p t u b : ℝ) : ℂ)
          ∂harperTiltedCoin p t) * Complex.I :=
      integral_mul_const Complex.I _
    _ =
        ((∫ b, v * harperCenteredLinearPrimeIncrement p t u b
            ∂harperTiltedCoin p t : ℝ) : ℂ) * Complex.I := by
      have hcast :
          (∫ b,
              ((v * harperCenteredLinearPrimeIncrement p t u b : ℝ) : ℂ)
              ∂harperTiltedCoin p t) =
            ((∫ b, v * harperCenteredLinearPrimeIncrement p t u b
                ∂harperTiltedCoin p t : ℝ) : ℂ) :=
        integral_ofReal
      exact congrArg (fun z : ℂ ↦ z * Complex.I) hcast
    _ = 0 := by
      rw [integral_const_mul,
        integral_harperCenteredLinearPrimeIncrement]
      simp

/-- The second complex moment of the characteristic exponent is minus
`v²` times the real centered variance. -/
theorem integral_harperCharacteristicExponent_sq
    (p : ℕ) (t u v : ℝ) :
    (∫ b, harperCharacteristicExponent p t u v b ^ 2
        ∂harperTiltedCoin p t) =
      -((v ^ 2 * harperCenteredLinearPrimeVariance p t u : ℝ) : ℂ) := by
  have hpoint (b : Bool) :
      harperCharacteristicExponent p t u v b ^ 2 =
        -((v ^ 2 * harperCenteredLinearPrimeIncrement p t u b ^ 2 : ℝ) : ℂ) := by
    unfold harperCharacteristicExponent
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  simp_rw [hpoint]
  rw [integral_neg]
  have hcast :
      (∫ b,
          ((v ^ 2 * harperCenteredLinearPrimeIncrement p t u b ^ 2 : ℝ) : ℂ)
          ∂harperTiltedCoin p t) =
        ((∫ b, v ^ 2 * harperCenteredLinearPrimeIncrement p t u b ^ 2
            ∂harperTiltedCoin p t : ℝ) : ℂ) :=
    integral_ofReal
  rw [hcast]
  rw [integral_const_mul,
    integral_harperCenteredLinearPrimeIncrement_sq]

/-- The tilted expectation of the pointwise quadratic characteristic
polynomial is exactly `1 - v² Var(X)/2`. -/
theorem integral_harperCharacteristicQuadratic
    (p : ℕ) (t u v : ℝ) :
    (∫ b, harperCharacteristicQuadratic p t u v b
        ∂harperTiltedCoin p t) =
      1 - ((v ^ 2 * harperCenteredLinearPrimeVariance p t u / 2 : ℝ) : ℂ) := by
  have hone :
      (∫ _b : Bool, (1 : ℂ) ∂harperTiltedCoin p t) = 1 := by
    rw [integral_const, probReal_univ, one_smul]
  have hdiv :
      (∫ b, harperCharacteristicExponent p t u v b ^ 2 / 2
          ∂harperTiltedCoin p t) =
        -((v ^ 2 * harperCenteredLinearPrimeVariance p t u : ℝ) : ℂ) / 2 := by
    calc
      (∫ b, harperCharacteristicExponent p t u v b ^ 2 / 2
          ∂harperTiltedCoin p t) =
          (∫ b, harperCharacteristicExponent p t u v b ^ 2
            ∂harperTiltedCoin p t) / 2 :=
        integral_div 2 _
      _ = -((v ^ 2 * harperCenteredLinearPrimeVariance p t u : ℝ) : ℂ) / 2 := by
        rw [integral_harperCharacteristicExponent_sq]
  unfold harperCharacteristicQuadratic
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite,
    hone, integral_harperCharacteristicExponent, hdiv]
  push_cast
  ring

/-- Explicit one-coordinate characteristic-function expansion.  On the
prime-scale unit window, the error after the Gaussian quadratic term is at
most the cubic moment envelope. -/
theorem norm_harperTiltedLinearPrimeCharacteristic_sub_quadratic_le
    {p : ℕ} (hp : 4 ≤ p) (t u v : ℝ)
    (hsmall : |v| * (2 * (Real.sqrt (p : ℝ))⁻¹) ≤ 1) :
    ‖harperTiltedLinearPrimeCharacteristic p t u v -
        (1 - ((v ^ 2 * harperCenteredLinearPrimeVariance p t u / 2 : ℝ) : ℂ))‖ ≤
      8 * |v| ^ 3 * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  let R : Bool → ℂ := fun b ↦
    Complex.exp (harperCharacteristicExponent p t u v b) -
      harperCharacteristicQuadratic p t u v b
  have hidentity :
      harperTiltedLinearPrimeCharacteristic p t u v -
          (1 - ((v ^ 2 * harperCenteredLinearPrimeVariance p t u / 2 : ℝ) : ℂ)) =
        ∫ b, R b ∂harperTiltedCoin p t := by
    rw [← integral_harperCharacteristicQuadratic p t u v]
    exact (integral_sub Integrable.of_finite Integrable.of_finite).symm
  rw [hidentity]
  calc
    ‖∫ b, R b ∂harperTiltedCoin p t‖ ≤
        ∫ b, ‖R b‖ ∂harperTiltedCoin p t :=
      norm_integral_le_integral_norm R
    _ ≤ ∫ b,
        |v| ^ 3 * |harperCenteredLinearPrimeIncrement p t u b| ^ 3
        ∂harperTiltedCoin p t := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      exact fun b ↦
        norm_exp_harperCharacteristicExponent_sub_quadratic_le
          hp t u v hsmall b
    _ = |v| ^ 3 *
        ∫ b, |harperCenteredLinearPrimeIncrement p t u b| ^ 3
          ∂harperTiltedCoin p t := by
      rw [integral_const_mul]
    _ ≤ |v| ^ 3 * (8 * (Real.sqrt (p : ℝ))⁻¹ ^ 3) := by
      exact mul_le_mul_of_nonneg_left
        (integral_abs_harperCenteredLinearPrimeIncrement_pow_three_le hp t u)
        (by positivity)
    _ = 8 * |v| ^ 3 * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by ring

/-! ## Finite-block product factorization -/

/-- Sum of centered linearized coordinates over an arbitrary finite set of
prime coordinates in the cube through `y`. -/
noncomputable def harperCenteredLinearPrimeBlockSum
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (t u : ℝ) (eta : HarperPrimeCube y) : ℝ :=
  ∑ p ∈ S, harperCenteredLinearPrimeIncrement p.1 t u (eta p)

/-- Purely imaginary exponent of a centered finite prime block. -/
noncomputable def harperCharacteristicBlockExponent
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (t u v : ℝ) (eta : HarperPrimeCube y) : ℂ :=
  ((v * harperCenteredLinearPrimeBlockSum y S t u eta : ℝ) : ℂ) * Complex.I

/-- The exponent of a block is the sum of its one-coordinate exponents. -/
theorem harperCharacteristicBlockExponent_eq_sum
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (t u v : ℝ) (eta : HarperPrimeCube y) :
    harperCharacteristicBlockExponent y S t u v eta =
      ∑ p ∈ S, harperCharacteristicExponent p.1 t u v (eta p) := by
  unfold harperCharacteristicBlockExponent harperCenteredLinearPrimeBlockSum
    harperCharacteristicExponent
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

/-- The exponential of the centered block is the product of the
one-coordinate characteristic factors. -/
theorem exp_harperCharacteristicBlockExponent_eq_prod
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (t u v : ℝ) (eta : HarperPrimeCube y) :
    Complex.exp (harperCharacteristicBlockExponent y S t u v eta) =
      ∏ p ∈ S,
        Complex.exp (harperCharacteristicExponent p.1 t u v (eta p)) := by
  rw [harperCharacteristicBlockExponent_eq_sum, Complex.exp_sum]

/-- Characteristic function of a centered finite prime block under the
tilted product law. -/
noncomputable def harperTiltedLinearPrimeBlockCharacteristic
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (t u v : ℝ) : ℂ :=
  ∫ eta, Complex.exp (harperCharacteristicBlockExponent y S t u v eta)
    ∂harperTiltedCubeLaw y t

/-- Complex-valued marginal integration for one coordinate of the tilted
cube. -/
theorem integral_harperTiltedCube_eval_complex
    (y : ℕ) (t : ℝ) (p : HarperPrimeIndex y) (g : Bool → ℂ) :
    (∫ eta, g (eta p) ∂harperTiltedCubeLaw y t) =
      ∫ b, g b ∂harperTiltedCoin p.1 t := by
  have hmp := measurePreserving_harperTiltedCube_eval y t p
  calc
    (∫ eta, g (eta p) ∂harperTiltedCubeLaw y t) =
        ∫ b, g b ∂Measure.map
          (fun eta : HarperPrimeCube y ↦ eta p)
          (harperTiltedCubeLaw y t) := by
      symm
      exact integral_map hmp.measurable.aemeasurable
        (measurable_of_finite g).aestronglyMeasurable
    _ = ∫ b, g b ∂harperTiltedCoin p.1 t := by
      rw [hmp.map_eq]

/-- Exact product factorization of the characteristic function of any
finite centered prime block. -/
theorem harperTiltedLinearPrimeBlockCharacteristic_eq_prod
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (t u v : ℝ) :
    harperTiltedLinearPrimeBlockCharacteristic y S t u v =
      ∏ p ∈ S, harperTiltedLinearPrimeCharacteristic p.1 t u v := by
  let coord : S → HarperPrimeCube y → Bool :=
    fun p eta ↦ eta p.1
  let g : (p : S) → Bool → ℂ :=
    fun p b ↦ Complex.exp (harperCharacteristicExponent p.1.1 t u v b)
  have hcoord : iIndepFun coord (harperTiltedCubeLaw y t) := by
    exact iIndepFun.precomp Subtype.val_injective
      (iIndepFun_harperTiltedCube_coordinates y t)
  have hfunctions : iIndepFun
      (fun p : S ↦ g p ∘ coord p) (harperTiltedCubeLaw y t) :=
    hcoord.comp g (fun _ ↦ measurable_of_finite _)
  have hprod := hfunctions.integral_fun_prod_eq_prod_integral
    (fun p ↦ (measurable_of_finite (g p ∘ coord p)).aestronglyMeasurable)
  calc
    harperTiltedLinearPrimeBlockCharacteristic y S t u v =
        ∫ eta, ∏ p ∈ S,
          Complex.exp (harperCharacteristicExponent p.1 t u v (eta p))
          ∂harperTiltedCubeLaw y t := by
      apply integral_congr_ae
      exact ae_of_all _ fun eta ↦
        exp_harperCharacteristicBlockExponent_eq_prod y S t u v eta
    _ = ∫ eta, ∏ p : S,
          Complex.exp
            (harperCharacteristicExponent p.1.1 t u v (eta p.1))
          ∂harperTiltedCubeLaw y t := by
      congr 1
      funext eta
      exact (Finset.prod_coe_sort S
        (fun p ↦ Complex.exp
          (harperCharacteristicExponent p.1 t u v (eta p)))).symm
    _ = ∏ p : S,
        ∫ eta,
          Complex.exp
            (harperCharacteristicExponent p.1.1 t u v (eta p.1))
          ∂harperTiltedCubeLaw y t := by
      simpa only [g, coord, Function.comp_apply] using! hprod
    _ = ∏ p : S,
        harperTiltedLinearPrimeCharacteristic p.1.1 t u v := by
      apply Finset.prod_congr rfl
      intro p hp
      exact integral_harperTiltedCube_eval_complex y t p.1
        (fun b ↦ Complex.exp
          (harperCharacteristicExponent p.1.1 t u v b))
    _ = ∏ p ∈ S,
        harperTiltedLinearPrimeCharacteristic p.1 t u v :=
      Finset.prod_coe_sort S
        (fun p ↦ harperTiltedLinearPrimeCharacteristic p.1 t u v)

end Problem520
end Erdos
