import Wikipedia.HopfProblem.AnalyticGermsFactorialPreparationPolynomial
import Wikipedia.HopfProblem.AnalyticGermsFactorialPreparationUnit
import Wikipedia.HopfProblem.AnalyticGermsFactorialPreparationCylinder
import Wikipedia.HopfProblem.AnalyticGermsFactorialPreparationGerms

/-!
# Convergent preparation in the genuine two-variable analytic-germ ring

For an analytic function with nonzero second-axis germ, the actual contour
moments construct a monic polynomial with analytic first-variable
coefficients. The explicit Cauchy quotient is a jointly analytic unit, and
the original actual germ is their product. No formal-adic completeness,
analytic division theorem, or factoriality premise is used.
-/

noncomputable section

open Set Metric Filter Topology Polynomial
open Wikipedia.HopfProblem.CuspNormalization.Germs
open Wikipedia.HopfProblem.CuspNormalization.Germs.CoordinateDivision
open Wikipedia.HopfProblem.CuspNormalization.Germs.PolynomialGerms

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.Preparation

variable {f : ℂ × ℂ → ℂ} {r R : ℝ}

/-- On a smaller parameter disc, the reconstructed preparation polynomial
has an actual jointly analytic and invertible Cauchy quotient. -/
theorem actual_cauchy_unit (hr : 0 < r) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r ×ˢ closedBall 0 R))
    (hf0 : ∀ p ∈ closedBall 0 r ×ˢ sphere 0 R, f p ≠ 0) :
    AnalyticAt ℂ (NormalIntegral.cauchyQuotient f (PreparationPolynomial.function f R) R) 0 ∧
      NormalIntegral.cauchyQuotient f (PreparationPolynomial.function f R) R 0 ≠ 0 ∧
      f =ᶠ[𝓝 (0 : ℂ × ℂ)] (fun p => PreparationPolynomial.function f R p *
        NormalIntegral.cauchyQuotient f (PreparationPolynomial.function f R) R p) := by
  have hrhalf : 0 < r / 2 := half_pos hr
  have hsmall : closedBall (0 : ℂ) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (half_lt_self hr)
  have hclosed : closedBall (0 : ℂ) (r / 2) ⊆ closedBall 0 r :=
    hsmall.trans ball_subset_closedBall
  apply PreparationUnit.cauchyQuotient_unit_germ hrhalf hR
    (hf.mono (Set.prod_mono hclosed (subset_refl _)))
  · exact (PreparationPolynomial.function_analyticOnNhd hr hR hf hf0).mono
      (Set.prod_mono hsmall (subset_univ _))
  · intro p hp
    exact PreparationPolynomial.function_boundary_ne_zero hr hR hf hf0 (hsmall hp.1) hp.2
  · intro z hz
    obtain ⟨g, hg, hg0, hfg⟩ :=
      PreparationPolynomial.exists_slice_factor hr hR hf hf0 (hsmall hz)
    exact ⟨g, hg, hg0, fun w hw => hfg w⟩

/-- Genuine convergent preparation: an actual regular analytic germ is a
monic polynomial in the second coordinate, with actual one-variable germ
coefficients, multiplied by a unit of the actual two-variable local ring. -/
theorem exists_monic_polynomial_mul_unit (hf : AnalyticAt ℂ f 0)
    (hline : ¬ (fun w : ℂ => f (0, w)) =ᶠ[𝓝 0] 0) :
    ∃ P : Polynomial O₁, P.Monic ∧ ∃ u : O₂ˣ,
      ofAnalytic f hf = polynomialGerm P * (u : O₂) := by
  obtain ⟨r, hr, R, hR, hfdisc, hf0, haxis⟩ :=
    PreparationCylinder.exists_preparation_cylinder hf hline
  let c : ℕ → ℂ → ℂ := PreparationPolynomial.coefficient f R
  have hc (j : ℕ) : AnalyticAt ℂ (c j) 0 :=
    PreparationPolynomial.coefficient_analyticOnNhd hr hR hfdisc hf0 j 0 (mem_ball_self hr)
  let d : ℕ := PreparationPolynomial.degree f R
  let P : Polynomial O₁ := Newton.descendingPolynomial (fun j => ofAnalytic (c j) (hc j)) d
  have hP : P.Monic := by
    apply Newton.descendingPolynomial_monic
    exact ofAnalytic_eq_one_of_forall_eq_one _ _ (PreparationPolynomial.coefficient_zero f R)
  obtain ⟨hu, hu0, hfu⟩ := actual_cauchy_unit hr hR hfdisc hf0
  let u : O₂ˣ := unitOfAnalytic
    (NormalIntegral.cauchyQuotient f (PreparationPolynomial.function f R) R) hu hu0
  refine ⟨P, hP, u, ?_⟩
  have hpoly := polynomialGerm_descending c hc d
  rw [hpoly]
  change ofAnalytic f hf = ofAnalytic
    ((fun p : ℂ × ℂ => ∑ j ∈ Finset.range (d + 1), c j p.1 * p.2 ^ (d - j)) *
      NormalIntegral.cauchyQuotient f (PreparationPolynomial.function f R) R)
    ((descendingFunction_analyticAt c hc d).mul hu)
  apply (ofAnalytic_eq_iff _ _ _ _).mpr
  filter_upwards [hfu] with p hp
  convert hp using 1
  simp only [PreparationPolynomial.function, PreparationPolynomial.slicePolynomial,
    Newton.polynomial_eval, PreparationPolynomial.coefficient, c, d, Pi.mul_apply]

end Wikipedia.HopfProblem.AnalyticGermsFactorial.Preparation
