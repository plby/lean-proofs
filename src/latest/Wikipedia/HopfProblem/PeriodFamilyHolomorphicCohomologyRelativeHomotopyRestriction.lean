import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperators

/-!
# Literal restrictions to smaller ambient base opens

For an inclusion of original open subsets of the complex plane, restrict
the period functions and the genuine smooth unit-torus family by their
literal inclusion. Their original values and Haar coefficients are
unchanged. The inherited open atlases are used throughout.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierParameter

variable {U V : Opens ℂ}

/-- The original period functions composed with the actual smaller-open inclusion. -/
def restrictPeriods (P : HolomorphicPeriodMap ℂ U) (hVU : V ≤ U) :
    HolomorphicPeriodMap ℂ V where
  point b := P.point (Set.inclusion hVU b)
  holomorphic_tau := P.holomorphic_tau.comp (contMDiff_inclusion hVU)
  holomorphic_mu := P.holomorphic_mu.comp (contMDiff_inclusion hVU)
  holomorphic_beta := P.holomorphic_beta.comp (contMDiff_inclusion hVU)

@[simp] theorem restrictPeriods_point (P : HolomorphicPeriodMap ℂ U) (hVU : V ≤ U)
    (b : V) : (restrictPeriods P hVU).point b = P.point (Set.inclusion hVU b) := rfl

/-- Literal restriction of the original smooth family, retaining its smooth lift. -/
def restrictFamily (hVU : V ≤ U) (f : SmoothFamily U (Fin 4)) :
    SmoothFamily V (Fin 4) where
  toFun x := f (Set.inclusion hVU x.1, x.2)
  smooth_lift := by
    apply (f.smooth_lift.mono (fun x hx => hVU hx)).congr
    intro x hx
    change x.1 ∈ V at hx
    simp only [ambientLift, dif_pos hx, dif_pos (hVU hx)]

@[simp] theorem restrictFamily_apply (hVU : V ≤ U) (f : SmoothFamily U (Fin 4))
    (b : V) (t : UnitAddTorus (Fin 4)) :
    restrictFamily hVU f (b, t) = f (Set.inclusion hVU b, t) := rfl

/-- Original normalized Haar coefficients are unchanged by this literal base restriction. -/
theorem coefficientValue_restrictFamily (hVU : V ≤ U) (f : SmoothFamily U (Fin 4))
    (b : V) (k : Fin 4 → ℤ) :
    (restrictFamily hVU f).coefficientValue k (b : ℂ) = f.coefficientValue k (b : ℂ) := by
  rw [SmoothFamily.coefficientValue_apply,
    SmoothFamily.coefficientValue_apply f k (Set.inclusion hVU b)]
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
