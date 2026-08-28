import Wikipedia.HopfProblem.AnalyticGermsFactorialPolynomialCoefficients
import Wikipedia.HopfProblem.AnalyticGermsFactorialPolynomialGerms

/-!
# Analytic polynomial families and their actual germs

Taking the genuine germ of an analytic finite polynomial family commutes
with the actual polynomial-germ homomorphism. This supplies the bridge from
contour reconstruction to algebra in the local ring.
-/

noncomputable section

open Set Filter Topology Polynomial
open Wikipedia.HopfProblem.CuspNormalization.Germs
open Wikipedia.HopfProblem.CuspNormalization.Germs.CoordinateDivision
open Wikipedia.HopfProblem.CuspNormalization.Germs.PolynomialGerms

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.Preparation

theorem descendingFunction_analyticAt (c : ℕ → ℂ → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (d : ℕ) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ => ∑ j ∈ Finset.range (d + 1), c j p.1 * p.2 ^ (d - j)) 0 := by
  apply Finset.analyticAt_fun_sum
  intro j hj
  have hj' : AnalyticAt ℂ (fun p : ℂ × ℂ => c j p.1) 0 :=
    (hc j).comp_of_eq (analyticAt_fst (p := (0 : ℂ × ℂ))) rfl
  exact hj'.mul (analyticAt_snd.pow (d - j))

/-- Actual germ formation commutes with evaluation of a polynomial whose
coefficients are actual one-variable analytic germs. -/
theorem polynomialGerm_descending (c : ℕ → ℂ → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (d : ℕ) :
    polynomialGerm (Newton.descendingPolynomial (fun j => ofAnalytic (c j) (hc j)) d) =
      ofAnalytic
        (fun p : ℂ × ℂ => ∑ j ∈ Finset.range (d + 1), c j p.1 * p.2 ^ (d - j))
        (descendingFunction_analyticAt c hc d) := by
  simp only [Newton.descendingPolynomial, map_sum, map_mul, map_pow,
    polynomialGerm_C, polynomialGerm_X]
  apply Wikipedia.HopfProblem.CuspNormalization.Germs.ext
  change (analyticSubring (0 : ℂ × ℂ)).subtype
      (∑ j ∈ Finset.range (d + 1), fstPullback (ofAnalytic (c j) (hc j)) *
        secondCoordinateGerm ^ (d - j)) = _
  simp only [map_sum, map_mul, map_pow, fstPullback_ofAnalytic]
  change (∑ j ∈ Finset.range (d + 1),
      (Filter.Germ.coeRingHom (𝓝 (0 : ℂ × ℂ)))
        (fun p : ℂ × ℂ => c j p.1 * p.2 ^ (d - j))) = _
  rw [← map_sum]
  apply Filter.Germ.coe_eq.mpr
  exact Eventually.of_forall (fun p => by simp only [Finset.sum_apply])

/-- A coefficient identically equal to one has literal unit germ. -/
theorem ofAnalytic_eq_one_of_forall_eq_one (c : ℂ → ℂ)
    (hc : AnalyticAt ℂ c 0) (hone : ∀ z, c z = 1) : ofAnalytic c hc = 1 := by
  apply (ofAnalytic_eq_iff c (fun _ => 1) hc analyticAt_const).mpr
  exact Eventually.of_forall hone

end Wikipedia.HopfProblem.AnalyticGermsFactorial.Preparation
