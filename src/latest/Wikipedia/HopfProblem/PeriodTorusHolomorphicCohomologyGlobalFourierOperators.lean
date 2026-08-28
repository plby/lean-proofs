import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyGlobalFourierPairs
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultGlobal

/-!
# The native global Dolbeault arrows agree with the actual Fourier arrows

Every equality is proved after the original quotient pullback, using
the already established genuine coordinate derivative formulas.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.GlobalFourier

open FourierLinear PeriodTorusLineBundleClassification

/-- The actual native coordinate derivative agrees with the actual Fourier derivative. -/
theorem sectionEquiv_derivative (p : PeriodDomain) (i : Fin 2)
    (s : Dolbeault.SmoothSection p ⊤) :
    sectionEquiv p (Dolbeault.derivativeSection p i ⊤ s) =
      dbarLinear p i (sectionEquiv p s) := by
  apply periodLift_injective p
  funext z
  change periodTorusLift p (toFourier p (Dolbeault.derivativeSection p i ⊤ s)) z =
    periodTorusLift p (torusDbar p (toFourier p s) i) z
  rw [lift_toFourier, Dolbeault.globalLift_derivativeSection,
    ← dbarCoordinate_periodTorusLift, lift_toFourier]

/-- The entire first differential is preserved, with the original two coordinate labels. -/
theorem pairSectionEquiv_differential (p : PeriodDomain)
    (s : Dolbeault.SmoothSection p ⊤) :
    pairSectionEquiv p (Dolbeault.differentialSection p ⊤ s) =
      differential p (sectionEquiv p s) := by
  funext i
  fin_cases i
  · exact sectionEquiv_derivative p 0 s
  · exact sectionEquiv_derivative p 1 s

/-- The actual top derivative retains exactly the native sign and coordinate order. -/
theorem sectionEquiv_top (p : PeriodDomain) (s : Dolbeault.PairSection p ⊤) :
    sectionEquiv p (Dolbeault.topSection p ⊤ s) = top p (pairSectionEquiv p s) := by
  change sectionEquiv p
    (Dolbeault.derivativeSection p 0 ⊤ s.2 - Dolbeault.derivativeSection p 1 ⊤ s.1) = _
  rw [map_sub, sectionEquiv_derivative, sectionEquiv_derivative]
  rfl

@[simp] theorem mean_derivative (p : PeriodDomain) (i : Fin 2)
    (s : Dolbeault.SmoothSection p ⊤) : mean p (Dolbeault.derivativeSection p i ⊤ s) = 0 := by
  change meanLinear (sectionEquiv p (Dolbeault.derivativeSection p i ⊤ s)) = 0
  rw [sectionEquiv_derivative, mean_dbar]

@[simp] theorem pairMean_differential (p : PeriodDomain)
    (s : Dolbeault.SmoothSection p ⊤) : pairMean p (Dolbeault.differentialSection p ⊤ s) = 0 := by
  change FourierLinear.pairMean
    (pairSectionEquiv p (Dolbeault.differentialSection p ⊤ s)) = 0
  rw [pairSectionEquiv_differential, FourierLinear.pairMean_differential]

@[simp] theorem mean_top (p : PeriodDomain) (s : Dolbeault.PairSection p ⊤) :
    mean p (Dolbeault.topSection p ⊤ s) = 0 := by
  change meanLinear (sectionEquiv p (Dolbeault.topSection p ⊤ s)) = 0
  rw [sectionEquiv_top, FourierLinear.mean_top]

/-- Literal constant native coefficient pairs are genuine closed forms. -/
theorem top_constantPairSection (p : PeriodDomain) (c : Fin 2 → ℂ) :
    Dolbeault.topSection p ⊤ (constantPairSection p c) = 0 := by
  apply (sectionEquiv p).injective
  rw [sectionEquiv_top, pairSectionEquiv_constant, top_constantPair, map_zero]

/-- Literal constant native functions are killed by the genuine first differential. -/
theorem differential_constant (p : PeriodDomain) (c : ℂ) :
    Dolbeault.differentialSection p ⊤ (ContMDiffMap.const c) = 0 := by
  apply (pairSectionEquiv p).injective
  rw [pairSectionEquiv_differential, sectionEquiv_constant, map_zero]
  funext i
  exact dbar_constant p c i

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.GlobalFourier
