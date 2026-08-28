import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyOne
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyTwo

/-!
# The literal constant representatives of the fixed Haar markings

The actual native Dolbeault classes of constant coefficient pairs and
constant top coefficients coincide with the original cohomology
classes. The verification uses the already proved original Haar-mean
formulas; it does not choose a different marking or change a sign.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup

open PeriodTorusHolomorphicCohomology

variable (p : PeriodDomain)

/-- The original degree-one constant class is its literal native closed coefficient pair. -/
theorem nativeH1Class_constant (a : Fin 2 → ℂ) :
    nativeH1Class p (GlobalFourier.constantPairSection p a)
      (GlobalFourier.top_constantPairSection p a) = h1Constant p a := by
  apply (h1Equiv p).injective
  rw [h1Equiv_nativeClass, GlobalFourier.pairMean_constant, h1Equiv_constant]

/-- The original degree-two constant class is its literal native top coefficient. -/
theorem nativeH2Class_constant (a : ℂ) :
    nativeH2Class p (ContMDiffMap.const a) = h2Constant p a := by
  apply (h2Equiv p).injective
  rw [h2Equiv_nativeClass, GlobalFourier.mean_constant, h2Equiv_constant]

/-- The literal coefficient product has exactly the original coordinate order. -/
theorem constantPair_wedge (a b : Fin 2 → ℂ) :
    (GlobalFourier.constantPairSection p a).1 *
        (GlobalFourier.constantPairSection p b).2 -
      (GlobalFourier.constantPairSection p a).2 *
        (GlobalFourier.constantPairSection p b).1 =
      (ContMDiffMap.const (a 0 * b 1 - a 1 * b 0) : Dolbeault.SmoothSection p ⊤) := by
  ext x
  rfl

/-- Every original degree-one class has its actual constant Haar-mean representative. -/
theorem h1Constant_marked (a : H p 1) : h1Constant p (h1Equiv p a) = a := by
  apply (h1Equiv p).injective
  rw [h1Equiv_constant]

/-- The original marked top class is genuinely nonzero. -/
theorem h2Constant_one_ne_zero : h2Constant p 1 ≠ 0 := by
  intro h
  have he := congrArg (h2Equiv p) h
  rw [h2Equiv_constant, map_zero] at he
  exact one_ne_zero he

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup
