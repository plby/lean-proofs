import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The finite Fourier reduction in Tao's proof of the Erdős discrepancy theorem

This file proves the vector-valued finite Fourier identities used in Section 2 of Tao's
proof.  We deliberately index Fourier coefficients by the full Pontryagin dual
`AddChar G ℂ`; this avoids choosing coordinates or a noncanonical self-duality of the finite
abelian group `G`.

The transform is left unnormalised.  Thus, if `F : G → E` takes values on the unit sphere and
`N = Fintype.card G`, the quantities `‖rawCoeff F ψ‖² / N²` are probability weights.  The last
theorem below is exactly the spectral identity needed to turn an average of translated vector
sums into the second moment of a random character sum.
-/

open Finset
open scoped BigOperators ComplexConjugate NNReal ENNReal

namespace Erdos67

noncomputable section

section FiniteFourier

variable {G E : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The unnormalised Fourier coefficient of a vector-valued function on a finite abelian group. -/
def rawCoeff (F : G → E) (psi : AddChar G ℂ) : E :=
  ∑ x : G, conj (psi x) • F x

private lemma char_mul_conj (psi : AddChar G ℂ) (x y : G) :
    psi x * conj (psi y) = psi (x - y) := by
  calc
    psi x * conj (psi y) = psi x * (psi y)⁻¹ := by rw [psi.inv_apply_eq_conj]
    _ = psi x * psi (-y) := by rw [psi.map_neg_eq_inv]
    _ = psi (x + -y) := (psi.map_add_eq_mul x (-y)).symm
    _ = psi (x - y) := by rw [sub_eq_add_neg]

private lemma sum_char_mul_conj (x y : G) :
    ∑ psi : AddChar G ℂ, psi x * conj (psi y) =
      if x = y then (Fintype.card G : ℂ) else 0 := by
  simp_rw [char_mul_conj]
  simpa only [sub_eq_zero] using (AddChar.sum_apply_eq_ite (a := x - y))

/-- Polarised Parseval identity for the unnormalised transform. -/
theorem rawCoeff_inner_expansion (F K : G → E) :
    ∑ psi : AddChar G ℂ, inner ℂ (rawCoeff F psi) (rawCoeff K psi) =
      ∑ x : G, ∑ y : G,
        (∑ psi : AddChar G ℂ, psi x * conj (psi y)) * inner ℂ (F x) (K y) := by
  classical
  simp only [rawCoeff, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_star]
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ psi : AddChar G ℂ, ∑ y : G, ∑ x : G,
        star (psi y) * (psi x * inner ℂ (F x) (K y))) =
      ∑ y : G, ∑ psi : AddChar G ℂ, ∑ x : G,
        star (psi y) * (psi x * inner ℂ (F x) (K y)) := Finset.sum_comm
    _ = ∑ y : G, ∑ x : G, ∑ psi : AddChar G ℂ,
        star (psi y) * (psi x * inner ℂ (F x) (K y)) := by
      apply Finset.sum_congr rfl
      intro y _
      exact Finset.sum_comm
    _ = ∑ x : G, ∑ y : G, ∑ psi : AddChar G ℂ,
        star (psi y) * (psi x * inner ℂ (F x) (K y)) := Finset.sum_comm
    _ = ∑ x : G, ∑ y : G, ∑ psi : AddChar G ℂ,
        psi x * star (psi y) * inner ℂ (F x) (K y) := by
      simp only [mul_assoc, mul_left_comm, mul_comm]

/-- Polarised Parseval identity for the unnormalised transform. -/
theorem sum_inner_rawCoeff (F K : G → E) :
    ∑ psi : AddChar G ℂ, inner ℂ (rawCoeff F psi) (rawCoeff K psi) =
      (Fintype.card G : ℂ) * ∑ x : G, inner ℂ (F x) (K x) := by
  rw [rawCoeff_inner_expansion]
  simp_rw [sum_char_mul_conj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hyx
    simp [hyx.symm]
  · simp

/-- Parseval in squared-norm form. -/
theorem sum_sq_norm_rawCoeff (F : G → E) :
    ∑ psi : AddChar G ℂ, ‖rawCoeff F psi‖ ^ 2 =
      (Fintype.card G : ℝ) * ∑ x : G, ‖F x‖ ^ 2 := by
  have h := sum_inner_rawCoeff F F
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  simpa [pow_two, Complex.mul_re] using congrArg Complex.re h

/-- A translate by `v` multiplies an unnormalised Fourier coefficient by `ψ(v)`. -/
theorem rawCoeff_translate (F : G → E) (v : G) (psi : AddChar G ℂ) :
    rawCoeff (fun x ↦ F (x + v)) psi = psi v • rawCoeff F psi := by
  classical
  unfold rawCoeff
  calc
    (∑ x : G, conj (psi x) • F (x + v)) =
        ∑ y : G, conj (psi (y - v)) • F y := by
      apply Fintype.sum_equiv (Equiv.addRight v)
      intro x
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
    _ = ∑ y : G, (psi v * conj (psi y)) • F y := by
      congr 1
      funext y
      rw [psi.map_sub_eq_div, map_div₀, ← psi.inv_apply_eq_conj y,
        ← psi.inv_apply_eq_conj v, div_inv_eq_mul, mul_comm]
    _ = psi v • ∑ y : G, conj (psi y) • F y := by
      simp only [mul_smul, Finset.smul_sum]

/-- The sum of translates used in the finite Fourier reduction. -/
def translateSum {I : Type*} (s : Finset I) (v : I → G) (F : G → E) (x : G) : E :=
  ∑ i ∈ s, F (x + v i)

/-- Fourier coefficient of a finite sum of translates. -/
theorem rawCoeff_translateSum {I : Type*} (s : Finset I) (v : I → G) (F : G → E)
    (psi : AddChar G ℂ) :
    rawCoeff (translateSum s v F) psi =
      (∑ i ∈ s, psi (v i)) • rawCoeff F psi := by
  calc
    rawCoeff (translateSum s v F) psi =
        ∑ i ∈ s, rawCoeff (fun x ↦ F (x + v i)) psi := by
      classical
      simp only [rawCoeff, translateSum, Finset.smul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i ∈ s, psi (v i) • rawCoeff F psi := by
      simp_rw [rawCoeff_translate]
    _ = (∑ i ∈ s, psi (v i)) • rawCoeff F psi := Finset.sum_smul.symm

/-- Spectral identity for the energy of a finite sum of translates.

The transform and the counting measure on `G` are both unnormalised. -/
theorem spectral_energy_identity {I : Type*} (s : Finset I) (v : I → G) (F : G → E) :
    (Fintype.card G : ℝ) * ∑ x : G, ‖translateSum s v F x‖ ^ 2 =
      ∑ psi : AddChar G ℂ,
        ‖∑ i ∈ s, psi (v i)‖ ^ 2 * ‖rawCoeff F psi‖ ^ 2 := by
  rw [← sum_sq_norm_rawCoeff (translateSum s v F)]
  apply Finset.sum_congr rfl
  intro psi _
  rw [rawCoeff_translateSum, norm_smul, mul_pow]

/-- For a unit-vector-valued function, the squared Fourier masses have total mass `N²`. -/
theorem sum_sq_norm_rawCoeff_of_unit (F : G → E) (hF : ∀ x, ‖F x‖ = 1) :
    ∑ psi : AddChar G ℂ, ‖rawCoeff F psi‖ ^ 2 = (Fintype.card G : ℝ) ^ 2 := by
  rw [sum_sq_norm_rawCoeff]
  simp_rw [hF, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  norm_num [pow_two]

/-- The normalised squared Fourier masses of a unit-vector-valued function sum to one. -/
theorem sum_normalized_sq_norm_rawCoeff_of_unit (F : G → E) (hF : ∀ x, ‖F x‖ = 1) :
    ∑ psi : AddChar G ℂ,
      ‖rawCoeff F psi‖ ^ 2 / (Fintype.card G : ℝ) ^ 2 = 1 := by
  rw [← Finset.sum_div, sum_sq_norm_rawCoeff_of_unit F hF]
  exact div_self (pow_ne_zero 2 (by exact_mod_cast Fintype.card_ne_zero))

/-- The Fourier mass as a nonnegative real number. -/
def spectralWeight (F : G → E) (psi : AddChar G ℂ) : ℝ≥0 :=
  ‖rawCoeff F psi‖₊ ^ 2 / (Fintype.card G : ℝ≥0) ^ 2

theorem sum_spectralWeight_of_unit (F : G → E) (hF : ∀ x, ‖F x‖ = 1) :
    ∑ psi : AddChar G ℂ, spectralWeight F psi = 1 := by
  apply NNReal.eq
  simpa [spectralWeight] using sum_normalized_sq_norm_rawCoeff_of_unit F hF

/-- The probability mass function on the dual obtained from the squared Fourier masses. -/
def spectralPMF (F : G → E) (hF : ∀ x, ‖F x‖ = 1) : PMF (AddChar G ℂ) :=
  PMF.ofFintype (fun psi ↦ (spectralWeight F psi : ℝ≥0∞)) (by
    exact_mod_cast sum_spectralWeight_of_unit F hF)

@[simp]
theorem spectralPMF_apply (F : G → E) (hF : ∀ x, ‖F x‖ = 1) (psi : AddChar G ℂ) :
    spectralPMF F hF psi = spectralWeight F psi := rfl

/-- Normalised spectral identity in the probability-weight form used by Tao.

The left side is the expectation of the scalar character energy for the probability weights
`w(ψ) = ‖rawCoeff F ψ‖² / |G|²`; the right side is the uniform average of the vector energy.
-/
theorem spectral_probability_identity {I : Type*} (s : Finset I) (v : I → G) (F : G → E) :
    ∑ psi : AddChar G ℂ,
        (‖rawCoeff F psi‖ ^ 2 / (Fintype.card G : ℝ) ^ 2) *
          ‖∑ i ∈ s, psi (v i)‖ ^ 2 =
      (∑ x : G, ‖translateSum s v F x‖ ^ 2) / Fintype.card G := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  calc
    (∑ psi : AddChar G ℂ,
          ‖rawCoeff F psi‖ ^ 2 * ‖∑ i ∈ s, psi (v i)‖ ^ 2) /
        (Fintype.card G : ℝ) ^ 2 =
        ((Fintype.card G : ℝ) *
          ∑ x : G, ‖translateSum s v F x‖ ^ 2) /
            (Fintype.card G : ℝ) ^ 2 := by
      congr 1
      simpa only [mul_comm] using (spectral_energy_identity s v F).symm
    _ = (∑ x : G, ‖translateSum s v F x‖ ^ 2) / Fintype.card G := by
      field_simp

/-- The spectral identity written literally as an expectation with respect to `spectralPMF`. -/
theorem spectralPMF_expectation {I : Type*} (s : Finset I) (v : I → G) (F : G → E)
    (hF : ∀ x, ‖F x‖ = 1) :
    ∑ psi : AddChar G ℂ, (spectralPMF F hF psi).toReal *
        ‖∑ i ∈ s, psi (v i)‖ ^ 2 =
      (∑ x : G, ‖translateSum s v F x‖ ^ 2) / Fintype.card G := by
  simpa [spectralWeight] using spectral_probability_identity s v F

end FiniteFourier

end

end Erdos67
