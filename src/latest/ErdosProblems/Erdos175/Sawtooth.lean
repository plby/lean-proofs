/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# The finite Fourier step in Granville--Ramaré, Section 7

This file isolates the finite-dimensional part of the argument leading to
equation (7.2).  The analytic input is expressed by a pair of pointwise
trigonometric majorants and by an `ℓ¹` bound for their coefficients.  The
lemmas below prove, without any asymptotic or measure-theoretic argument, how
these data control a nonnegative weighted sawtooth sum and how the constants
`43 / 6` and `11 / 8` follow from the degree-ten coefficient bound `86 / 99`.
-/

namespace Erdos175.Sawtooth

open scoped BigOperators

/-- The centered sawtooth function used in the Kummer detector.  Following
Granville--Ramaré's convention, its value at an integer is `0` rather than
the right-limit value `-1 / 2`. -/
noncomputable def psi (x : ℝ) : ℝ :=
  if x = (⌊x⌋ : ℝ) then 0 else Int.fract x - 1 / 2

/-- The standard additive character `e(x) = exp(2 π i x)`. -/
noncomputable def e (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

@[simp] lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  simp [e, Complex.norm_exp]

/-- Nonzero integral frequencies of absolute value at most `R`. -/
noncomputable def frequencies (R : ℕ) : Finset ℤ :=
  (Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0

/-- A finite trigonometric polynomial on the real line. -/
noncomputable def fourierPolynomial
    (F : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ r ∈ F, a r * e ((r : ℝ) * x)

/-- The coefficients in Granville--Ramaré, Lemma 7.1.  The parameter
`sign` is `1` for the upper majorant of `psi` and `-1` for the upper
majorant of `-psi`.  Only nonzero `r` are used. -/
noncomputable def grCoefficient (R : ℕ) (sign : ℝ) (r : ℤ) : ℂ :=
  (Complex.I / (((2 * Real.pi * ((R + 1 : ℕ) : ℝ) : ℝ) : ℂ))) *
      (((Real.pi *
        (1 - (r.natAbs : ℝ) / ((R + 1 : ℕ) : ℝ)) *
        (Real.cos (Real.pi * (r : ℝ) / ((R + 1 : ℕ) : ℝ)) /
          Real.sin (Real.pi * (r : ℝ) / ((R + 1 : ℕ) : ℝ))) +
        (r.natAbs : ℝ) / (r : ℝ) : ℝ) : ℂ)) +
    (((sign / ((2 * R + 2 : ℕ) : ℝ)) *
        (1 - (r.natAbs : ℝ) / ((R + 1 : ℕ) : ℝ)) : ℝ) : ℂ)

/-- Degree-ten upper-majorant coefficients. -/
noncomputable def degreeTenPlusCoefficient (r : ℤ) : ℂ :=
  grCoefficient 10 1 r

/-- Negatives of the degree-ten lower-majorant coefficients, hence upper
majorant coefficients for `-psi`. -/
noncomputable def degreeTenMinusCoefficient (r : ℤ) : ℂ :=
  -grCoefficient 10 (-1) r

/-- A pointwise upper Fourier majorant for a real-valued function. -/
def IsUpperMajorant
    (F : Finset ℤ) (f : ℝ → ℝ) (c : ℝ) (a : ℤ → ℂ) : Prop :=
  ∀ x, f x ≤ c + (fourierPolynomial F a x).re

/-- The exact degree-ten numerical input from Lemma 7.1.  Separating this
record from its finite-sum consumer makes the very tight coefficient check
(`0.86809... < 86/99`) explicit in theorem types. -/
def DegreeTenVaalerData : Prop :=
  IsUpperMajorant (frequencies 10) psi (1 / 22)
      degreeTenPlusCoefficient ∧
    IsUpperMajorant (frequencies 10) (fun x ↦ -psi x) (1 / 22)
      degreeTenMinusCoefficient ∧
    (∑ r ∈ frequencies 10, ‖degreeTenPlusCoefficient r‖) ≤ 86 / 99 ∧
    (∑ r ∈ frequencies 10, ‖degreeTenMinusCoefficient r‖) ≤ 86 / 99

/-- Weighted exponential sum at frequency `r`. -/
noncomputable def weightedPhaseSum { ι : Type* }
    (s : Finset ι) (w : ι → ℝ) (t : ι → ℝ) (r : ℤ) : ℂ :=
  ∑ i ∈ s, (w i : ℂ) * e ((r : ℝ) * t i)

/-- Distribute a weighted sum through a finite Fourier polynomial. -/
lemma weighted_fourierPolynomial_eq { ι : Type* }
    (s : Finset ι) (w : ι → ℝ) (t : ι → ℝ)
    (F : Finset ℤ) (a : ℤ → ℂ) :
    ∑ i ∈ s, (w i : ℂ) * fourierPolynomial F a (t i) =
      ∑ r ∈ F, a r * weightedPhaseSum s w t r := by
  simp only [fourierPolynomial, weightedPhaseSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Real-part version of `weighted_fourierPolynomial_eq`. -/
lemma weighted_fourierPolynomial_re_eq { ι : Type* }
    (s : Finset ι) (w : ι → ℝ) (t : ι → ℝ)
    (F : Finset ℤ) (a : ℤ → ℂ) :
    ∑ i ∈ s, w i * (fourierPolynomial F a (t i)).re =
      (∑ r ∈ F, a r * weightedPhaseSum s w t r).re := by
  rw [← weighted_fourierPolynomial_eq]
  simp

/-- A pointwise Fourier majorant gives a bound for every finite nonnegative
weighted sum.  This is the first displayed inequality after Lemma 7.1 in the
paper, stated in a form which does not assume a particular choice of phases. -/
lemma weighted_sum_le_of_upperMajorant { ι : Type* }
    (s : Finset ι) (w : ι → ℝ) (t : ι → ℝ)
    (F : Finset ℤ) (f : ℝ → ℝ) (c A M : ℝ) (a : ℤ → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmajor : IsUpperMajorant F f c a)
    (hphase : ∀ r ∈ F, ‖weightedPhaseSum s w t r‖ ≤ M)
    (hcoeff : ∑ r ∈ F, ‖a r‖ ≤ A)
    (hM : 0 ≤ M) :
    ∑ i ∈ s, w i * f (t i) ≤
      c * ∑ i ∈ s, w i + A * M := by
  have hpoint : ∑ i ∈ s, w i * f (t i) ≤
      ∑ i ∈ s, w i * (c + (fourierPolynomial F a (t i)).re) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hmajor (t i)) (hw i hi)
  have hrearrange :
      ∑ i ∈ s, w i * (c + (fourierPolynomial F a (t i)).re) =
        c * ∑ i ∈ s, w i +
          (∑ r ∈ F, a r * weightedPhaseSum s w t r).re := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [weighted_fourierPolynomial_re_eq]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hrearrange] at hpoint
  have hfourier :
    (∑ r ∈ F, a r * weightedPhaseSum s w t r).re
        ≤ A * M := by
      calc
        (∑ r ∈ F, a r * weightedPhaseSum s w t r).re
            ≤ ‖∑ r ∈ F, a r * weightedPhaseSum s w t r‖ := Complex.re_le_norm _
        _ ≤ ∑ r ∈ F, ‖a r * weightedPhaseSum s w t r‖ :=
          norm_sum_le _ _
        _ = ∑ r ∈ F, ‖a r‖ * ‖weightedPhaseSum s w t r‖ := by
          simp only [norm_mul]
        _ ≤ ∑ r ∈ F, ‖a r‖ * M := by
          apply Finset.sum_le_sum
          intro r hr
          exact mul_le_mul_of_nonneg_left (hphase r hr) (norm_nonneg _)
        _ = (∑ r ∈ F, ‖a r‖) * M := by rw [Finset.sum_mul]
        _ ≤ A * M := mul_le_mul_of_nonneg_right hcoeff hM
  linarith

/-- Applying upper majorants to both `f` and `-f` bounds the absolute value
of the weighted sum. -/
lemma abs_weighted_sum_le_of_majorants { ι : Type* }
    (s : Finset ι) (w : ι → ℝ) (t : ι → ℝ)
    (F : Finset ℤ) (f : ℝ → ℝ) (c A M : ℝ)
    (aPlus aMinus : ℤ → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hplus : IsUpperMajorant F f c aPlus)
    (hminus : IsUpperMajorant F (fun x ↦ -f x) c aMinus)
    (hphase : ∀ r ∈ F, ‖weightedPhaseSum s w t r‖ ≤ M)
    (hcoeffPlus : ∑ r ∈ F, ‖aPlus r‖ ≤ A)
    (hcoeffMinus : ∑ r ∈ F, ‖aMinus r‖ ≤ A)
    (hM : 0 ≤ M) :
    |∑ i ∈ s, w i * f (t i)| ≤
      c * ∑ i ∈ s, w i + A * M := by
  rw [abs_le]
  constructor
  · have h := weighted_sum_le_of_upperMajorant s w t F (fun x ↦ -f x)
      c A M aMinus hw hminus hphase hcoeffMinus hM
    simpa only [mul_neg, Finset.sum_neg_distrib, neg_le] using h
  · exact weighted_sum_le_of_upperMajorant s w t F f c A M aPlus hw hplus
      hphase hcoeffPlus hM

/-- The degree-ten specialization of the weighted Vaaler estimate. -/
lemma degreeTen_abs_weighted_psi_le { ι : Type* }
    (hVaaler : DegreeTenVaalerData)
    (s : Finset ι) (w : ι → ℝ) (t : ι → ℝ) (M : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hphase : ∀ r ∈ frequencies 10, ‖weightedPhaseSum s w t r‖ ≤ M)
    (hM : 0 ≤ M) :
    |∑ i ∈ s, w i * psi (t i)| ≤
      (1 / 22) * ∑ i ∈ s, w i + (86 / 99) * M := by
  rcases hVaaler with ⟨hplus, hminus, hcoeffPlus, hcoeffMinus⟩
  exact abs_weighted_sum_le_of_majorants s w t (frequencies 10) psi
    (1 / 22) (86 / 99) M degreeTenPlusCoefficient degreeTenMinusCoefficient
    hw hplus hminus hphase hcoeffPlus hcoeffMinus hM

/-- Pure constant calculation behind Granville--Ramaré (7.2).

Each of the two sawtooth sums is bounded by
`S / 22 + (86 / 99) M`.  Combining those bounds with the Kummer detector
`(S - bad) / 2 ≤ U + 2 V` gives exactly
`S ≤ (43 / 6) M + (11 / 8) bad`. -/
lemma constants_43_over_6_and_11_over_8
    {S bad U V M : ℝ}
    (hdetector : (S - bad) / 2 ≤ U + 2 * V)
    (hU : U ≤ S / 22 + (86 / 99) * M)
    (hV : V ≤ S / 22 + (86 / 99) * M) :
    S ≤ (43 / 6) * M + (11 / 8) * bad := by
  linarith

/-- Equation (7.2), with the arithmetic and Fourier inputs made explicit.
This version is convenient when `U` and `V` have already been named as the
absolute values of the two weighted sawtooth sums. -/
lemma equation_7_2
    {S bad U V M L : ℝ}
    (hdetector : (S - bad) / 2 ≤ U + 2 * V)
    (hU : U ≤ (1 / 22) * S + (86 / 99) * M)
    (hV : V ≤ (1 / 22) * S + (86 / 99) * M)
    (hbad : bad ≤ L) :
    S ≤ (43 / 6) * M + (11 / 8) * L := by
  have hU' : U ≤ S / 22 + (86 / 99) * M := by
    linarith
  have hV' : V ≤ S / 22 + (86 / 99) * M := by
    linarith
  have h := constants_43_over_6_and_11_over_8 hdetector hU' hV'
  linarith

/-- The complete finite Fourier deduction of (7.2) from Lemma 7.1 and the
Kummer detector (7.1).  In applications `w d = Λ(d)`, `t₁ d = 2n/d`,
`t₂ d = n/d`, and `L = log n`. -/
lemma equation_7_2_of_degreeTen { ι : Type* }
    (hVaaler : DegreeTenVaalerData)
    (s : Finset ι) (w : ι → ℝ) (t₁ t₂ : ι → ℝ)
    (bad M L : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hphase₁ : ∀ r ∈ frequencies 10,
      ‖weightedPhaseSum s w t₁ r‖ ≤ M)
    (hphase₂ : ∀ r ∈ frequencies 10,
      ‖weightedPhaseSum s w t₂ r‖ ≤ M)
    (hM : 0 ≤ M)
    (hdetector :
      ((∑ i ∈ s, w i) - bad) / 2 ≤
        |∑ i ∈ s, w i * psi (t₁ i)| +
          2 * |∑ i ∈ s, w i * psi (t₂ i)|)
    (hbad : bad ≤ L) :
    ∑ i ∈ s, w i ≤ (43 / 6) * M + (11 / 8) * L := by
  have h₁ := degreeTen_abs_weighted_psi_le hVaaler s w t₁ M hw hphase₁ hM
  have h₂ := degreeTen_abs_weighted_psi_le hVaaler s w t₂ M hw hphase₂ hM
  exact equation_7_2 hdetector h₁ h₂ hbad

end Erdos175.Sawtooth
