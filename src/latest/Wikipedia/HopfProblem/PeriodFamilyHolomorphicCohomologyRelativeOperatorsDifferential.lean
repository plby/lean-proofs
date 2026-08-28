import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperatorsBasic

/-!
# The three actual scalar relative differential operators

The base operator has the usual antiholomorphic normalization `1/2`.
The two vertical operators are in the first two marked period-coordinate
forms, so their coefficients involve the original holomorphic period
entries and have no extra factor `1/2`.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators

open FourierParameter PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*} [Fintype d]

/-- The actual antiholomorphic base derivative in the fixed real torus coordinates. -/
def d0 (f : SmoothFamily U d) : SmoothFamily U d :=
  constMul (2 : ℂ)⁻¹ (add (f.baseDerivative 1) (constMul Complex.I (f.baseDerivative Complex.I)))

@[simp] theorem d0_apply (f : SmoothFamily U d) (x : U × UnitAddTorus d) :
    d0 f x = (f.baseDerivative 1 x + Complex.I * f.baseDerivative Complex.I x) / 2 := by
  simp only [d0, constMul_apply, add_apply, div_eq_mul_inv, mul_comm (2 : ℂ)⁻¹]

/-- Its lift is the literal antiholomorphic part of the actual joint derivative. -/
theorem ambientLift_d0 (f : SmoothFamily U d) (x : ℂ × (d → ℝ))
    (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    ambientLift (d0 f) x =
      (fderiv ℝ (ambientLift f) x (1, 0) +
        Complex.I * fderiv ℝ (ambientLift f) x (Complex.I, 0)) / 2 := by
  rw [d0, ambientLift_constMul _ _ x hx, ambientLift_add _ _ x hx,
    ambientLift_constMul _ _ x hx, f.ambientLift_baseDerivative 1 x hx,
    f.ambientLift_baseDerivative Complex.I x hx]
  ring

variable (P : HolomorphicPeriodMap ℂ U)

/-- The first genuine vertical operator in the marked relative frame. -/
def d1 (f : SmoothFamily U (Fin 4)) : SmoothFamily U (Fin 4) :=
  (f.verticalDerivative (Pi.single 0 1)).sub
    (add (baseMultiply (fun z => 6 * Smooth.muValue P z)
      (contDiffOn_const.mul (Smooth.muValue_contDiffOn_real P))
      (f.verticalDerivative (Pi.single 2 1)))
    (baseMultiply (Smooth.betaValue P) (Smooth.betaValue_contDiffOn_real P)
      (f.verticalDerivative (Pi.single 3 1))))

/-- The second genuine vertical operator in the marked relative frame. -/
def d2 (f : SmoothFamily U (Fin 4)) : SmoothFamily U (Fin 4) :=
  (f.verticalDerivative (Pi.single 1 1)).sub
    (add (baseMultiply (Smooth.tauValue P) (Smooth.tauValue_contDiffOn_real P)
      (f.verticalDerivative (Pi.single 2 1)))
    (baseMultiply (Smooth.muValue P) (Smooth.muValue_contDiffOn_real P)
      (f.verticalDerivative (Pi.single 3 1))))

@[simp] theorem d1_apply (f : SmoothFamily U (Fin 4)) (b : U)
    (t : UnitAddTorus (Fin 4)) :
    d1 P f (b, t) = f.verticalDerivative (Pi.single 0 1) (b, t) -
      (6 * (P.point b).val.μ * f.verticalDerivative (Pi.single 2 1) (b, t) +
        (P.point b).val.β * f.verticalDerivative (Pi.single 3 1) (b, t)) := by
  simp only [d1, SmoothFamily.sub_apply, add_apply, baseMultiply_apply,
    Smooth.muValue_apply, Smooth.betaValue_apply]

@[simp] theorem d2_apply (f : SmoothFamily U (Fin 4)) (b : U)
    (t : UnitAddTorus (Fin 4)) :
    d2 P f (b, t) = f.verticalDerivative (Pi.single 1 1) (b, t) -
      ((P.point b).val.τ * f.verticalDerivative (Pi.single 2 1) (b, t) +
        (P.point b).val.μ * f.verticalDerivative (Pi.single 3 1) (b, t)) := by
  simp only [d2, SmoothFamily.sub_apply, add_apply, baseMultiply_apply,
    Smooth.tauValue_apply, Smooth.muValue_apply]

/-- The first operator is literally the indicated combination of actual joint derivatives. -/
theorem ambientLift_d1 (f : SmoothFamily U (Fin 4)) (x : ℂ × (Fin 4 → ℝ))
    (hx : x ∈ Smooth.baseProductDomain U (Fin 4 → ℝ)) :
    ambientLift (d1 P f) x = fderiv ℝ (ambientLift f) x (0, Pi.single 0 1) -
      (6 * Smooth.muValue P x.1 * fderiv ℝ (ambientLift f) x (0, Pi.single 2 1) +
        Smooth.betaValue P x.1 * fderiv ℝ (ambientLift f) x (0, Pi.single 3 1)) := by
  rw [d1, ambientLift_sub _ _ x hx, ambientLift_add _ _ x hx,
    ambientLift_baseMultiply _ _ _ x hx, ambientLift_baseMultiply _ _ _ x hx,
    ambientLift_verticalDerivative _ _ x hx, ambientLift_verticalDerivative _ _ x hx,
    ambientLift_verticalDerivative _ _ x hx]

/-- The second operator is literally the indicated combination of actual joint derivatives. -/
theorem ambientLift_d2 (f : SmoothFamily U (Fin 4)) (x : ℂ × (Fin 4 → ℝ))
    (hx : x ∈ Smooth.baseProductDomain U (Fin 4 → ℝ)) :
    ambientLift (d2 P f) x = fderiv ℝ (ambientLift f) x (0, Pi.single 1 1) -
      (Smooth.tauValue P x.1 * fderiv ℝ (ambientLift f) x (0, Pi.single 2 1) +
        Smooth.muValue P x.1 * fderiv ℝ (ambientLift f) x (0, Pi.single 3 1)) := by
  rw [d2, ambientLift_sub _ _ x hx, ambientLift_add _ _ x hx,
    ambientLift_baseMultiply _ _ _ x hx, ambientLift_baseMultiply _ _ _ x hx,
    ambientLift_verticalDerivative _ _ x hx, ambientLift_verticalDerivative _ _ x hx,
    ambientLift_verticalDerivative _ _ x hx]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators
