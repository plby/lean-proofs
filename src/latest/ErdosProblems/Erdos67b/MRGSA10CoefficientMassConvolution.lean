import ErdosProblems.Erdos67b.MRGSA10TailoredCoefficient
import ErdosProblems.Erdos67b.MRGSA10LambdaWindowMass

/-!
# Absolute Perron masses of Dirichlet convolutions

The coefficient-mass error in the GS A.10 Perron formula factorizes across
Dirichlet convolution.  This file records that general inequality and the
exact behavior under the real coefficient shifts used by the tailored
four-factor coefficient.
-/

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Absolute real-line L-series mass is submultiplicative under Dirichlet
convolution. -/
theorem dirichletPerronCoefficientMass_mul_le
    (a b : ArithmeticFunction ℂ) (sigma : ℝ)
    (ha : LSeriesSummable a (sigma : ℂ))
    (hb : LSeriesSummable b (sigma : ℂ)) :
    dirichletPerronCoefficientMass
        ((a * b : ArithmeticFunction ℂ) : ℕ → ℂ) sigma ≤
      dirichletPerronCoefficientMass a sigma *
        dirichletPerronCoefficientMass b sigma := by
  let fa : ℕ → ℝ := fun n ↦ ‖LSeries.term a (sigma : ℂ) n‖
  let fb : ℕ → ℝ := fun n ↦ ‖LSeries.term b (sigma : ℂ) n‖
  let prod : ℕ × ℕ → ℝ := fun p ↦ fa p.1 * fb p.2
  let fiber : ℕ → ℝ := fun n ↦
    ∑' p : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n}, prod p
  have hfa : Summable fa := ha.norm
  have hfb : Summable fb := hb.norm
  have hfaNorm : Summable fun n ↦ ‖fa n‖ := by
    simpa only [fa, Real.norm_eq_abs, abs_norm] using hfa
  have hfbNorm : Summable fun n ↦ ‖fb n‖ := by
    simpa only [fb, Real.norm_eq_abs, abs_norm] using hfb
  have hprod : Summable prod := by
    exact summable_mul_of_summable_norm hfaNorm hfbNorm
  have hfiber : HasSum fiber (∑' p : ℕ × ℕ, prod p) := by
    simpa only [fiber] using
      hprod.hasSum.tsum_fiberwise (fun p : ℕ × ℕ ↦ p.1 * p.2)
  have hpoint (n : ℕ) :
      ‖LSeries.term ((a * b : ArithmeticFunction ℂ) : ℕ → ℂ)
          (sigma : ℂ) n‖ ≤ fiber n := by
    rw [← ArithmeticFunction.coe_mul]
    rw [LSeries.term_convolution']
    change
      ‖∑' p : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n},
          LSeries.term a (sigma : ℂ) (p : ℕ × ℕ).1 *
            LSeries.term b (sigma : ℂ) (p : ℕ × ℕ).2‖ ≤
        ∑' p : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n},
          ‖LSeries.term a (sigma : ℂ) (p : ℕ × ℕ).1‖ *
            ‖LSeries.term b (sigma : ℂ) (p : ℕ × ℕ).2‖
    have hnorm : Summable fun
        p : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n} ↦
          ‖LSeries.term a (sigma : ℂ) (p : ℕ × ℕ).1 *
            LSeries.term b (sigma : ℂ) (p : ℕ × ℕ).2‖ := by
      have hsub := hprod.subtype
        (fun p : ℕ × ℕ ↦ p ∈
          ((fun q : ℕ × ℕ ↦ q.1 * q.2) ⁻¹' {n}))
      refine hsub.congr ?_
      intro p
      simp only [prod, fa, fb, Function.comp_apply, norm_mul]
    calc
      ‖∑' p : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n},
          LSeries.term a (sigma : ℂ) (p : ℕ × ℕ).1 *
            LSeries.term b (sigma : ℂ) (p : ℕ × ℕ).2‖ ≤
        ∑' p : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n},
          ‖LSeries.term a (sigma : ℂ) (p : ℕ × ℕ).1 *
            LSeries.term b (sigma : ℂ) (p : ℕ × ℕ).2‖ :=
        norm_tsum_le_tsum_norm hnorm
      _ = _ := by
        apply tsum_congr
        intro p
        rw [norm_mul]
  have hleft : Summable fun n ↦
      ‖LSeries.term ((a * b : ArithmeticFunction ℂ) : ℕ → ℂ)
          (sigma : ℂ) n‖ := by
    have hab : LSeriesSummable
        ((a * b : ArithmeticFunction ℂ) : ℕ → ℂ) (sigma : ℂ) := by
      rw [← ArithmeticFunction.coe_mul]
      exact ha.convolution hb
    exact hab.norm
  unfold dirichletPerronCoefficientMass
  calc
    (∑' n : ℕ, ‖LSeries.term
        ((a * b : ArithmeticFunction ℂ) : ℕ → ℂ) (sigma : ℂ) n‖) ≤
        ∑' n : ℕ, fiber n :=
      hleft.tsum_le_tsum hpoint hfiber.summable
    _ = ∑' p : ℕ × ℕ, prod p := hfiber.tsum_eq
    _ = (∑' n : ℕ, fa n) * ∑' n : ℕ, fb n := by
      symm
      exact tsum_mul_tsum_of_summable_norm hfaNorm hfbNorm
    _ = (∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖) *
        ∑' n : ℕ, ‖LSeries.term b (sigma : ℂ) n‖ := rfl

/-- A real coefficient shift simply translates the real line on which the
absolute L-series mass is evaluated. -/
theorem dirichletPerronCoefficientMass_gsRealShift
    (rho : ℝ) (a : ArithmeticFunction ℂ) (sigma : ℝ) :
    dirichletPerronCoefficientMass (gsRealShift rho a) sigma =
      dirichletPerronCoefficientMass a (sigma + rho) := by
  unfold dirichletPerronCoefficientMass
  apply tsum_congr
  intro n
  rw [LSeries_term_gsRealShift]
  simp only [Complex.ofReal_add]

private theorem dirichletPerronCoefficientMass_four_mul_le
    (a b c d : ArithmeticFunction ℂ) (sigma : ℝ)
    (ha : LSeriesSummable a (sigma : ℂ))
    (hb : LSeriesSummable b (sigma : ℂ))
    (hc : LSeriesSummable c (sigma : ℂ))
    (hd : LSeriesSummable d (sigma : ℂ)) :
    dirichletPerronCoefficientMass
        (((a * b) * (c * d) : ArithmeticFunction ℂ) : ℕ → ℂ) sigma ≤
      (dirichletPerronCoefficientMass a sigma *
        dirichletPerronCoefficientMass b sigma) *
      (dirichletPerronCoefficientMass c sigma *
        dirichletPerronCoefficientMass d sigma) := by
  have hab : LSeriesSummable
      (((a * b : ArithmeticFunction ℂ)) : ℕ → ℂ) (sigma : ℂ) := by
    rw [← ArithmeticFunction.coe_mul]
    exact ha.convolution hb
  have hcd : LSeriesSummable
      (((c * d : ArithmeticFunction ℂ)) : ℕ → ℂ) (sigma : ℂ) := by
    rw [← ArithmeticFunction.coe_mul]
    exact hc.convolution hd
  have houter := dirichletPerronCoefficientMass_mul_le
    (a * b) (c * d) sigma hab hcd
  have hleft := dirichletPerronCoefficientMass_mul_le a b sigma ha hb
  have hright := dirichletPerronCoefficientMass_mul_le c d sigma hc hd
  exact houter.trans (mul_le_mul hleft hright
    (by unfold dirichletPerronCoefficientMass; positivity)
    (mul_nonneg
      (by unfold dirichletPerronCoefficientMass; positivity)
      (by unfold dirichletPerronCoefficientMass; positivity)))

/-- The absolute Perron mass of the tailored A.10 coefficient splits into
the masses of its four Dirichlet factors.  Keeping the four real lines
visible is essential: after putting `sigma = c - alpha - beta`, the two
finite Mangoldt windows lie on `c - beta` and `c + beta`, respectively. -/
theorem dirichletPerronCoefficientMass_gsA10TailoredCoefficient_le
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (alpha beta sigma : ℝ)
    (hlow : LSeriesSummable low (sigma : ℂ))
    (hhigh : LSeriesSummable high
      ((sigma + alpha + 2 * beta : ℝ) : ℂ)) :
    dirichletPerronCoefficientMass
        (gsA10TailoredCoefficient low high lambda y X alpha beta) sigma ≤
      (dirichletPerronCoefficientMass low sigma *
        dirichletPerronCoefficientMass high (sigma + alpha + 2 * beta)) *
      (dirichletPerronCoefficientMass (gsA10LambdaWindow lambda y X)
          (sigma + alpha) *
        dirichletPerronCoefficientMass (gsA10LambdaWindow lambda y X)
          (sigma + alpha + 2 * beta)) := by
  let W : ArithmeticFunction ℂ := gsA10LambdaWindow lambda y X
  have hhigh' : LSeriesSummable
      (gsRealShift (alpha + 2 * beta) high) (sigma : ℂ) := by
    apply (gsRealShift_LSeriesSummable_iff _ _ _).2
    simpa only [Complex.ofReal_add, add_assoc] using hhigh
  have hWalpha : LSeriesSummable (gsRealShift alpha W) (sigma : ℂ) := by
    apply (gsRealShift_LSeriesSummable_iff _ _ _).2
    exact gsA10LambdaWindow_LSeriesSummable lambda y X _
  have hWbeta : LSeriesSummable
      (gsRealShift (alpha + 2 * beta) W) (sigma : ℂ) := by
    apply (gsRealShift_LSeriesSummable_iff _ _ _).2
    exact gsA10LambdaWindow_LSeriesSummable lambda y X _
  have hfour := dirichletPerronCoefficientMass_four_mul_le
    low (gsRealShift (alpha + 2 * beta) high)
    (gsRealShift alpha W) (gsRealShift (alpha + 2 * beta) W)
    sigma hlow hhigh' hWalpha hWbeta
  simpa only [gsA10TailoredCoefficient, W,
    dirichletPerronCoefficientMass_gsRealShift, add_assoc] using hfour

/-- Source-line form of the four-factor bound.  The Perron line is
`c - alpha - beta`; hence the high factor and the second finite window
both land on `c + beta`, while the first finite window lands on
`c - beta`. -/
theorem dirichletPerronCoefficientMass_gsA10TailoredCoefficient_sourceLines_le
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (c alpha beta : ℝ)
    (hlow : LSeriesSummable low ((c - alpha - beta : ℝ) : ℂ))
    (hhigh : LSeriesSummable high ((c + beta : ℝ) : ℂ)) :
    dirichletPerronCoefficientMass
        (gsA10TailoredCoefficient low high lambda y X alpha beta)
        (c - alpha - beta) ≤
      (dirichletPerronCoefficientMass low (c - alpha - beta) *
        dirichletPerronCoefficientMass high (c + beta)) *
      (dirichletPerronCoefficientMass (gsA10LambdaWindow lambda y X)
          (c - beta) *
        dirichletPerronCoefficientMass (gsA10LambdaWindow lambda y X)
          (c + beta)) := by
  have hlineHigh : (c - alpha - beta) + alpha + 2 * beta = c + beta := by
    ring
  have hlineLow : (c - alpha - beta) + alpha = c - beta := by
    ring
  have hlineAfter : c - beta + 2 * beta = c + beta := by
    ring
  have hhigh' : LSeriesSummable high
      ((((c - alpha - beta) + alpha + 2 * beta : ℝ)) : ℂ) := by
    rw [hlineHigh]
    exact hhigh
  have hbase := dirichletPerronCoefficientMass_gsA10TailoredCoefficient_le
    low high lambda y X alpha beta (c - alpha - beta) hlow hhigh'
  simpa only [hlineHigh, hlineLow, hlineAfter] using hbase

end

end Erdos67b.MRHalaszBands
