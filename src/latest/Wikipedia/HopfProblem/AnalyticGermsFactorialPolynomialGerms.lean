import Wikipedia.HopfProblem.AnalyticGermsFactorialCoordinateDivisionAlgebra
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomials as actual analytic germs

A polynomial in the second coordinate with one-variable analytic-germ
coefficients has a canonical image in the actual two-variable germ ring.
Its restriction to the second coordinate axis is the scalar polynomial
obtained by evaluating the coefficients at zero.  Scalar polynomials embed
in actual one-variable germs because a neighbourhood has infinitely many
points, whereas a nonzero polynomial has only finitely many roots.
-/

open Set Filter Topology
open Wikipedia.HopfProblem.CuspNormalization.Germs.CoordinateDivision

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.PolynomialGerms

/-- Scalar polynomial evaluation is analytic at the origin. -/
theorem complexPolynomial_analyticAt (P : Polynomial ℂ) :
    AnalyticAt ℂ (fun w : ℂ => P.eval w) 0 :=
  (AnalyticOnNhd.eval_polynomial P) 0 (mem_univ 0)

/-- The actual neighbourhood germ of a scalar polynomial. -/
noncomputable def complexPolynomialGerm : Polynomial ℂ →+* O₁ where
  toFun P := ofAnalytic (fun w : ℂ => P.eval w) (complexPolynomial_analyticAt P)
  map_zero' := by
    apply (ofAnalytic_eq_iff _ _ (complexPolynomial_analyticAt 0)
      (analyticAt_const (x := (0 : ℂ)))).mpr
    exact Eventually.of_forall fun w => by simp
  map_one' := by
    apply (ofAnalytic_eq_iff _ _ (complexPolynomial_analyticAt 1)
      (analyticAt_const (x := (0 : ℂ)))).mpr
    exact Eventually.of_forall fun w => by simp
  map_add' P Q := by
    apply (ofAnalytic_eq_iff _ _ (complexPolynomial_analyticAt (P + Q))
      ((complexPolynomial_analyticAt P).add (complexPolynomial_analyticAt Q))).mpr
    exact Eventually.of_forall fun w => by simp
  map_mul' P Q := by
    apply (ofAnalytic_eq_iff _ _ (complexPolynomial_analyticAt (P * Q))
      ((complexPolynomial_analyticAt P).mul (complexPolynomial_analyticAt Q))).mpr
    exact Eventually.of_forall fun w => by simp

theorem complexPolynomialGerm_apply (P : Polynomial ℂ) :
    complexPolynomialGerm P =
      ofAnalytic (fun w : ℂ => P.eval w) (complexPolynomial_analyticAt P) := rfl

@[simp] theorem complexPolynomialGerm_C (c : ℂ) :
    complexPolynomialGerm (Polynomial.C c) = constant (0 : ℂ) c := by
  apply (ofAnalytic_eq_iff _ _ (complexPolynomial_analyticAt (Polynomial.C c))
    analyticAt_const).mpr
  exact Eventually.of_forall fun w => by simp

@[simp] theorem complexPolynomialGerm_X :
    complexPolynomialGerm Polynomial.X = centeredCoordinateGerm (0 : ℂ) := by
  apply (ofAnalytic_eq_iff _ _ (complexPolynomial_analyticAt Polynomial.X)
    (analyticAt_id.sub analyticAt_const)).mpr
  exact Eventually.of_forall fun w => by simp

/-- A scalar polynomial is determined by its actual germ at zero. -/
theorem complexPolynomialGerm_injective : Function.Injective complexPolynomialGerm := by
  intro P Q h
  have he : (fun w : ℂ => P.eval w) =ᶠ[𝓝 (0 : ℂ)] (fun w => Q.eval w) :=
    (ofAnalytic_eq_iff _ _ (complexPolynomial_analyticAt P)
      (complexPolynomial_analyticAt Q)).mp h
  exact P.eq_of_infinite_eval_eq Q (infinite_of_mem_nhds (0 : ℂ) he)

@[simp] theorem complexPolynomialGerm_eq_zero_iff (P : Polynomial ℂ) :
    complexPolynomialGerm P = 0 ↔ P = 0 := by
  constructor
  · intro h
    apply complexPolynomialGerm_injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

/-- One-variable coefficient germs pulled back along the first projection. -/
noncomputable def fstPullback : O₁ →+* O₂ :=
  pullbackAt (Prod.fst : ℂ × ℂ → ℂ) analyticAt_fst rfl

@[simp] theorem fstPullback_ofAnalytic (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    fstPullback (ofAnalytic f hf) =
      ofAnalytic (fun p : ℂ × ℂ => f p.1) (hf.comp_of_eq analyticAt_fst rfl) := rfl

theorem fstPullback_injective : Function.Injective fstPullback := by
  have hleft : Function.LeftInverse
      (pullbackAt (fun z : ℂ => (z, 0)) (analyticAt_id.prod analyticAt_const) rfl)
      fstPullback := by
    intro φ
    obtain ⟨f, hf, rfl⟩ := exists_representative φ
    rfl
  exact hleft.injective

@[simp] theorem axisRestriction_fstPullback (φ : O₁) :
    axisRestriction (fstPullback φ) = constant (0 : ℂ) (eval (0 : ℂ) φ) := by
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rfl

@[simp] theorem fstPullback_centeredCoordinateGerm :
    fstPullback (centeredCoordinateGerm (0 : ℂ)) = firstCoordinateGerm := by
  apply ext
  apply Filter.Germ.coe_eq.mpr
  exact Eventually.of_forall fun p : ℂ × ℂ => sub_zero p.1

/-- The actual germ of the second coordinate. -/
noncomputable def secondCoordinateGerm : O₂ := ofAnalytic Prod.snd analyticAt_snd

@[simp] theorem axisRestriction_secondCoordinateGerm :
    axisRestriction secondCoordinateGerm = centeredCoordinateGerm (0 : ℂ) := by
  apply ext
  apply Filter.Germ.coe_eq.mpr
  exact Eventually.of_forall fun w : ℂ => (sub_zero w).symm

/-- Evaluate polynomial coefficients in the first coordinate and the
polynomial variable in the second coordinate, as actual analytic germs. -/
noncomputable def polynomialGerm : Polynomial O₁ →+* O₂ :=
  Polynomial.eval₂RingHom fstPullback secondCoordinateGerm

@[simp] theorem polynomialGerm_C (φ : O₁) :
    polynomialGerm (Polynomial.C φ) = fstPullback φ := by
  simp [polynomialGerm]

@[simp] theorem polynomialGerm_X :
    polynomialGerm Polynomial.X = secondCoordinateGerm := by
  simp [polynomialGerm]

/-- Restriction commutes with actual polynomial evaluation. -/
theorem axisRestriction_comp_polynomialGerm :
    axisRestriction.comp polynomialGerm =
      complexPolynomialGerm.comp (Polynomial.mapRingHom (eval (0 : ℂ))) := by
  apply Polynomial.ringHom_ext
  · intro φ
    simp
  · simp

/-- The restricted germ is exactly the scalar polynomial whose
coefficients are the values at zero of the original coefficient germs. -/
theorem axisRestriction_polynomialGerm (P : Polynomial O₁) :
    axisRestriction (polynomialGerm P) =
      complexPolynomialGerm (P.map (eval (0 : ℂ))) :=
  RingHom.congr_fun axisRestriction_comp_polynomialGerm P

/-- Coordinate divisibility is detected exactly by coefficient reduction. -/
theorem firstCoordinateGerm_dvd_polynomialGerm_iff (P : Polynomial O₁) :
    firstCoordinateGerm ∣ polynomialGerm P ↔ P.map (eval (0 : ℂ)) = 0 := by
  rw [← axisRestriction_eq_zero_iff_dvd, axisRestriction_polynomialGerm,
    complexPolynomialGerm_eq_zero_iff]

/-- A unit leading coefficient survives reduction to the axis, so the
first coordinate cannot divide the resulting actual polynomial germ. -/
theorem firstCoordinateGerm_not_dvd_polynomialGerm_of_isUnit_leadingCoeff
    (P : Polynomial O₁) (hP : IsUnit P.leadingCoeff) :
    ¬ firstCoordinateGerm ∣ polynomialGerm P := by
  rw [firstCoordinateGerm_dvd_polynomialGerm_iff]
  intro hzero
  have hcoeff := congrArg (fun Q : Polynomial ℂ => Q.coeff P.natDegree) hzero
  have hlc : eval (0 : ℂ) P.leadingCoeff = 0 := by
    simpa only [Polynomial.coeff_map, Polynomial.coeff_natDegree, Polynomial.coeff_zero]
      using hcoeff
  exact (hP.map (eval (0 : ℂ))).ne_zero hlc

/-- In particular, a monic polynomial germ has no first-coordinate divisor. -/
theorem firstCoordinateGerm_not_dvd_polynomialGerm_of_monic
    (P : Polynomial O₁) (hP : P.Monic) :
    ¬ firstCoordinateGerm ∣ polynomialGerm P :=
  firstCoordinateGerm_not_dvd_polynomialGerm_of_isUnit_leadingCoeff P
    (hP ▸ isUnit_one)

end Wikipedia.HopfProblem.CuspNormalization.Germs.PolynomialGerms
