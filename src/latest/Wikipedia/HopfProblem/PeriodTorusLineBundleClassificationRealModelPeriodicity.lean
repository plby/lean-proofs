import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationRealModelReduction
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationRealModelObstruction

/-!
# Periodicity derived from the actual logarithmic cocycle

The derivative identities follow from the actual entire factor logarithms
and the exact real model. A smooth primitive of the constructed additive
cocycle therefore yields periodic corrected coefficients and forces type
`(1,1)`. The primitive is constructed by the lattice-cochain theorem in
the subsequent existence wrapper.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex PeriodTorusAppellHumbert PeriodTorusTypeOneOne
open scoped ContDiff

theorem dbarCoordinate_realModelLog (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l : p.lattice) (i : Fin 2) (z : ComplexPlane₂) :
    dbarCoordinate (realModelLog p E l) i z =
      (Real.pi : ℂ) * I * realFormDbarLinear (tangentForm p E) i l := by
  have hB : DifferentiableAt ℝ (fun x => (tangentForm p E x l : ℂ)) z :=
    (Complex.ofRealCLM.comp ((tangentForm p E).flip l).toContinuousLinearMap).differentiableAt
  change dbarCoordinate (fun x =>
    (Real.pi : ℂ) * I * (coordinateQuadratic E (p.latticeEquiv l) : ℂ) +
      (Real.pi : ℂ) * I * (tangentForm p E x l : ℂ)) i z = _
  rw [dbarCoordinate_add (differentiableAt_const _) (hB.const_mul _),
    dbarCoordinate_const, zero_add, dbarCoordinate_const_mul hB,
    dbarCoordinate_realForm_eval]

theorem dbarCoordinate_realModelCocycle {p : PeriodDomain} (F : FactorOfAutomorphy p)
    (l : p.lattice) (i : Fin 2) (z : ComplexPlane₂) :
    dbarCoordinate (realModelCocycle F l) i z =
      -((Real.pi : ℂ) * I *
        realFormDbarLinear (tangentForm p (factorIntegralCoefficients F)) i l) := by
  have hlog : ContDiff ℝ ∞ (factorLog F l) :=
    ((factorLog_holomorphic F l).of_le le_top).restrict_scalars ℝ
  have hmodel := realModelLog_contDiff p (factorIntegralCoefficients F) l
  change dbarCoordinate (fun x => factorLog F l x -
    realModelLog p (factorIntegralCoefficients F) l x -
      (factorIntegerAdjustment F l : ℂ) * (2 * (Real.pi : ℂ) * I)) i z = _
  rw [dbarCoordinate_sub ((hlog.sub hmodel).differentiable (by simp) z)
      (differentiableAt_const _),
    dbarCoordinate_sub (hlog.differentiable (by simp) z) (hmodel.differentiable (by simp) z),
    dbarCoordinate_zero_of_differentiableAt
      ((factorLog_holomorphic F l).differentiable (by simp) z),
    dbarCoordinate_realModelLog, dbarCoordinate_const, sub_zero, zero_sub]

theorem realFormCorrectedDbar_periodic_of_primitive {p : PeriodDomain}
    (F : FactorOfAutomorphy p) {u : ComplexPlane₂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hshift : ∀ l : p.lattice, ∀ z, u (z + l) - u z = realModelCocycle F l z)
    (i : Fin 2) (z : ComplexPlane₂) (l : p.lattice) :
    realFormCorrectedDbar (tangentForm p (factorIntegralCoefficients F)) u i (z + l) =
      realFormCorrectedDbar (tangentForm p (factorIntegralCoefficients F)) u i z := by
  have he : (fun x => u (x + l) - u x) = realModelCocycle F l := funext (hshift l)
  have hd := congrArg (fun v : ComplexPlane₂ → ℂ => dbarCoordinate v i z) he
  have ht : DifferentiableAt ℝ (fun x => u (x + l)) z :=
    (hu.differentiable (by simp) (z + l)).comp z (differentiableAt_id.add_const _)
  rw [dbarCoordinate_sub ht (hu.differentiable (by simp) z),
    dbarCoordinate_translate (hu.differentiable (by simp) (z + l)),
    dbarCoordinate_realModelCocycle] at hd
  dsimp only [realFormCorrectedDbar]
  rw [map_add]
  linear_combination hd

theorem factor_typeOneOne_of_realModel_primitive {p : PeriodDomain}
    (F : FactorOfAutomorphy p) {u : ComplexPlane₂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hshift : ∀ l : p.lattice, ∀ z, u (z + l) - u z = realModelCocycle F l z) :
    IsTypeOneOne (tangentForm p (factorIntegralCoefficients F)) :=
  isTypeOneOne_of_periodic_correctedDbar p _ (tangentForm_self p _) hu
    (realFormCorrectedDbar_periodic_of_primitive F hu hshift)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
