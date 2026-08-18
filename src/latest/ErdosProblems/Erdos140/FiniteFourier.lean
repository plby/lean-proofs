import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Data.Complex.BigOperators

/-!
# Normalized Fourier analysis on a finite abelian group

This file contains the elementary finite Fourier identities used in the proof of
Erdős Problem 140.  Both the Fourier transform and convolution are normalized
with respect to the uniform probability measure on the ambient group.
-/

noncomputable section

open AddChar Finset Fintype Function RCLike
open scoped BigOperators ComplexConjugate

namespace Erdos140.FiniteFourier

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The normalized Fourier coefficient
`E_x conj (χ x) * f x` of a complex-valued function on a finite abelian group. -/
def coeff (f : G → ℂ) (χ : AddChar G ℂ) : ℂ := ⟪(χ : G → ℂ), f⟫ₙ_[ℂ]

@[simp] lemma coeff_zero (χ : AddChar G ℂ) : coeff (0 : G → ℂ) χ = 0 := by
  simp [coeff]

lemma coeff_add (f g : G → ℂ) (χ : AddChar G ℂ) :
    coeff (f + g) χ = coeff f χ + coeff g χ := by
  simp [coeff, wInner_add_right]

lemma coeff_smul (c : ℂ) (f : G → ℂ) (χ : AddChar G ℂ) :
    coeff (c • f) χ = c * coeff f χ := by
  simp [coeff, wInner_smul_right]

/-- Orthogonality of two normalized complex characters. -/
lemma character_orthogonality (χ ψ : AddChar G ℂ) :
    ⟪(χ : G → ℂ), ψ⟫ₙ_[ℂ] = if χ = ψ then 1 else 0 :=
  AddChar.wInner_cWeight_eq_boole χ ψ

/-- Orthogonality in the dual variable. -/
lemma dual_orthogonality [DecidableEq G] (a : G) :
    𝔼 χ : AddChar G ℂ, χ a = if a = 0 then 1 else 0 := by
  classical
  simpa using AddChar.expect_apply_eq_ite a

/-- Parseval--Plancherel for the normalized Fourier coefficients. -/
lemma parseval (f g : G → ℂ) :
    ∑ χ : AddChar G ℂ, conj (coeff f χ) * coeff g χ =
      𝔼 x : G, conj (f x) * g x := by
  classical
  unfold coeff
  simp_rw [wInner_cWeight_eq_expect, inner_apply', map_expect, map_mul,
    starRingEnd_self_apply, expect_mul, mul_expect, ← expect_sum_comm,
    mul_mul_mul_comm _ (conj <| f _), ← sum_mul, ← AddChar.inv_apply_eq_conj,
    ← map_neg_eq_inv, ← map_add_eq_mul, AddChar.sum_apply_eq_ite]
  simp [add_neg_eq_zero, card_univ, Fintype.card_ne_zero, NNRat.smul_def]

/-- Fourier inversion, with normalized coefficients and an unnormalized sum over the dual. -/
lemma inversion (f : G → ℂ) (a : G) :
    ∑ χ : AddChar G ℂ, coeff f χ * χ a = f a := by
  classical
  simp_rw [coeff, wInner_cWeight_eq_expect, inner_apply', expect_mul,
    ← expect_sum_comm, mul_right_comm _ (f _), ← sum_mul,
    ← AddChar.inv_apply_eq_conj, inv_mul_eq_div, ← map_sub_eq_div,
    AddChar.sum_apply_eq_ite, sub_eq_zero, ite_mul, zero_mul, Fintype.expect_ite_eq]
  simp [NNRat.smul_def (K := ℂ), Fintype.card_ne_zero]

/-- The normalized additive convolution `E_y f y * g (x-y)`. -/
def convolution (f g : G → ℂ) (x : G) : ℂ :=
  𝔼 y : G, f y * g (x - y)

/-- The normalized difference convolution `E_y f (x+y) * conj (g y)`.

For real-valued functions this is the usual additive-combinatorial difference
convolution.  The conjugation makes autocorrelation positive on the Fourier side.
-/
def differenceConvolution (f g : G → ℂ) (x : G) : ℂ :=
  𝔼 y : G, f (x + y) * conj (g y)

lemma coeff_convolution (f g : G → ℂ) (χ : AddChar G ℂ) :
    coeff (convolution f g) χ = coeff f χ * coeff g χ := by
  classical
  simp_rw [coeff, wInner_cWeight_eq_expect, inner_apply, convolution,
    mul_expect, expect_mul, ← expect_product', univ_product_univ]
  refine Fintype.expect_equiv ((Equiv.prodComm _ _).trans <|
    ((Equiv.refl _).prodShear Equiv.subRight).trans <| Equiv.prodComm _ _) _ _ fun (a, b) ↦ ?_
  simp [mul_mul_mul_comm, ← map_mul, ← map_add_eq_mul]

lemma coeff_conjneg (f : G → ℂ) (χ : AddChar G ℂ) :
    coeff (fun x ↦ conj (f (-x))) χ = conj (coeff f χ) := by
  classical
  simp only [coeff, wInner_cWeight_eq_expect, inner_apply, map_expect, map_mul,
    RCLike.conj_conj]
  refine Fintype.expect_equiv (Equiv.neg _) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, ← inv_apply_eq_conj, ← inv_apply', inv_apply]

lemma differenceConvolution_eq_convolution (f g : G → ℂ) :
    differenceConvolution f g = convolution f (fun x ↦ conj (g (-x))) := by
  funext x
  simp only [differenceConvolution, convolution]
  refine Fintype.expect_equiv (Equiv.addLeft x) _ _ fun y ↦ ?_
  simp

lemma coeff_differenceConvolution (f g : G → ℂ) (χ : AddChar G ℂ) :
    coeff (differenceConvolution f g) χ = coeff f χ * conj (coeff g χ) := by
  rw [differenceConvolution_eq_convolution, coeff_convolution, coeff_conjneg]

/-- The Fourier coefficient of an autocorrelation is a squared absolute value. -/
lemma coeff_autocorrelation (f : G → ℂ) (χ : AddChar G ℂ) :
    coeff (differenceConvolution f f) χ = (Complex.normSq (coeff f χ) : ℂ) := by
  rw [coeff_differenceConvolution]
  exact Complex.mul_conj _

/-- Spectral positivity of an autocorrelation. -/
lemma coeff_autocorrelation_re_nonneg (f : G → ℂ) (χ : AddChar G ℂ) :
    0 ≤ (coeff (differenceConvolution f f) χ).re := by
  rw [coeff_autocorrelation]
  simpa using Complex.normSq_nonneg (coeff f χ)

/-- Fourier inversion specialized to an autocorrelation: every spectral weight is nonnegative. -/
lemma autocorrelation_spectral_expansion (f : G → ℂ) (x : G) :
    ∑ χ : AddChar G ℂ, (Complex.normSq (coeff f χ) : ℂ) * χ x =
      differenceConvolution f f x := by
  simpa only [coeff_autocorrelation] using inversion (differenceConvolution f f) x

/-- The normalized second moment equals the sum of squared Fourier magnitudes. -/
lemma second_moment (f : G → ℂ) :
    𝔼 x : G, ‖f x‖ ^ 2 = ∑ χ : AddChar G ℂ, ‖coeff f χ‖ ^ 2 := by
  have h := parseval f f
  have h' : ∑ χ : AddChar G ℂ, (Complex.normSq (coeff f χ) : ℂ) =
      𝔼 x : G, (Complex.normSq (f x) : ℂ) := by
    simpa only [Complex.normSq_eq_conj_mul_self] using h
  have hre := congrArg Complex.re h'
  simpa only [Complex.re_sum, Complex.re_expect, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] using hre.symm

/-- The second moment of a convolution is its corresponding spectral fourth moment. -/
lemma convolution_second_moment (f g : G → ℂ) :
    𝔼 x : G, ‖convolution f g x‖ ^ 2 =
      ∑ χ : AddChar G ℂ, ‖coeff f χ * coeff g χ‖ ^ 2 := by
  simpa only [coeff_convolution] using second_moment (convolution f g)

/-- The additive energy identity: the second moment of an autocorrelation is the fourth
moment of the Fourier magnitudes. -/
lemma autocorrelation_second_moment (f : G → ℂ) :
    𝔼 x : G, ‖differenceConvolution f f x‖ ^ 2 =
      ∑ χ : AddChar G ℂ, (Complex.normSq (coeff f χ)) ^ 2 := by
  rw [second_moment]
  congr 1 with χ
  rw [coeff_autocorrelation, Complex.norm_real,
    Real.norm_of_nonneg (Complex.normSq_nonneg _)]

/-- Evaluation of an autocorrelation at zero is the normalized second moment. -/
lemma autocorrelation_zero (f : G → ℂ) :
    differenceConvolution f f 0 = (𝔼 x : G, (‖f x‖ ^ 2 : ℝ)) := by
  rw [differenceConvolution]
  push_cast
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The zero-frequency coefficient is the normalized mean. -/
lemma coeff_zero_character (f : G → ℂ) :
    coeff f 0 = 𝔼 x : G, f x := by
  simp [coeff, wInner_cWeight_eq_expect, inner_apply]

/-- The mean of a normalized convolution is the product of the means. -/
lemma mean_convolution (f g : G → ℂ) :
    (𝔼 x : G, convolution f g x) = (𝔼 x : G, f x) * (𝔼 x : G, g x) := by
  simpa [coeff_zero_character] using coeff_convolution f g 0

#print axioms Erdos140.FiniteFourier.inversion
#print axioms Erdos140.FiniteFourier.parseval
#print axioms Erdos140.FiniteFourier.coeff_differenceConvolution

end Erdos140.FiniteFourier
