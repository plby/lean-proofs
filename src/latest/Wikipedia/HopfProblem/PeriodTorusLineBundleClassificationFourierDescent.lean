import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDescentBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierPeriod

/-!
# Actual descent through the period lattice

The integer-periodic descent construction is applied using the actual real
period equivalence. The descended smooth torus function is proved to lift
back to the given smooth lattice-periodic function on the complex plane.
-/

noncomputable section

open Function UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusTypeOneOne

variable (p : PeriodDomain)

theorem period_coordinate_integerPeriodic (u : ComplexPlane₂ → ℂ)
    (hper : ∀ z : ComplexPlane₂, ∀ l : p.lattice, u (z + l) = u z)
    (x : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    u (periodEquiv p (x + (fun i => (k i : ℝ)))) = u (periodEquiv p x) := by
  rw [map_add, periodEquiv_integer_eq_periodVector]
  simpa only [PeriodDomain.periodLatticeEquiv_coe] using
    hper (periodEquiv p x) (p.periodLatticeEquiv k)

/-- Descent through the actual period lattice, with no chosen torus lift in
the hypotheses. -/
def smoothTorusOfLatticePeriodic (u : ComplexPlane₂ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : ∀ z : ComplexPlane₂, ∀ l : p.lattice, u (z + l) = u z) :
    SmoothTorusFunction (Fin 4) :=
  smoothTorusOfPeriodic (u ∘ periodEquiv p)
    (hu.comp (periodEquiv p).toContinuousLinearEquiv.contDiff)
    (period_coordinate_integerPeriodic p u hper)

@[simp]
theorem periodTorusLift_smoothTorusOfLatticePeriodic (u : ComplexPlane₂ → ℂ)
    (hu : ContDiff ℝ ∞ u)
    (hper : ∀ z : ComplexPlane₂, ∀ l : p.lattice, u (z + l) = u z)
    (z : ComplexPlane₂) :
    periodTorusLift p (smoothTorusOfLatticePeriodic p u hu hper) z = u z := by
  rw [periodTorusLift, smoothTorusOfLatticePeriodic, smoothTorusOfPeriodic_lift]
  simp only [Function.comp_apply, LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
