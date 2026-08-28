import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterElliptic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeFamily

/-!
# Elementary operations on actual smooth families

These are pointwise operations on the original open base times the unit
torus. Their smoothness is proved for the literal quotient lifts. A base
multiplier is used only on the original open set; no extension across its
boundary is required.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators

open FourierParameter PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*} [Fintype d]

/-- Pointwise addition of the original jointly smooth families. -/
def add (f g : SmoothFamily U d) : SmoothFamily U d where
  toFun x := f x + g x
  smooth_lift := (f.smooth_lift.add g.smooth_lift).congr (fun x hx => by
    change x.1 ∈ U at hx
    simp only [ambientLift, dif_pos hx])

@[simp] theorem add_apply (f g : SmoothFamily U d) (x : U × UnitAddTorus d) :
    add f g x = f x + g x := rfl

/-- Multiplication by a genuine constant complex scalar. -/
def constMul (a : ℂ) (f : SmoothFamily U d) : SmoothFamily U d where
  toFun x := a * f x
  smooth_lift := ((contDiffOn_const (c := a)).mul f.smooth_lift).congr (fun x hx => by
    change x.1 ∈ U at hx
    simp only [ambientLift, dif_pos hx])

@[simp] theorem constMul_apply (a : ℂ) (f : SmoothFamily U d)
    (x : U × UnitAddTorus d) : constMul a f x = a * f x := rfl

/-- A smooth base function acts by actual pointwise multiplication. -/
def baseMultiply (g : ℂ → ℂ) (hg : ContDiffOn ℝ ∞ g U)
    (f : SmoothFamily U d) : SmoothFamily U d where
  toFun x := g (x.1 : ℂ) * f x
  smooth_lift := ((hg.comp contDiffOn_fst (fun _ hx => hx)).mul f.smooth_lift).congr
    (fun x hx => by
      change x.1 ∈ U at hx
      simp only [ambientLift, dif_pos hx, Function.comp_def])

@[simp] theorem baseMultiply_apply (g : ℂ → ℂ) (hg : ContDiffOn ℝ ∞ g U)
    (f : SmoothFamily U d) (x : U × UnitAddTorus d) :
    baseMultiply g hg f x = g (x.1 : ℂ) * f x := rfl

theorem ambientLift_add (f g : SmoothFamily U d) (x : ℂ × (d → ℝ))
    (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    ambientLift (add f g) x = ambientLift f x + ambientLift g x := by
  change x.1 ∈ U at hx
  simp only [ambientLift, dif_pos hx, add_apply]

theorem ambientLift_sub (f g : SmoothFamily U d) (x : ℂ × (d → ℝ))
    (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    ambientLift (f.sub g) x = ambientLift f x - ambientLift g x := by
  change x.1 ∈ U at hx
  simp only [ambientLift, dif_pos hx, SmoothFamily.sub_apply]

theorem ambientLift_constMul (a : ℂ) (f : SmoothFamily U d) (x : ℂ × (d → ℝ))
    (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    ambientLift (constMul a f) x = a * ambientLift f x := by
  change x.1 ∈ U at hx
  simp only [ambientLift, dif_pos hx, constMul_apply]

theorem ambientLift_baseMultiply (g : ℂ → ℂ) (hg : ContDiffOn ℝ ∞ g U)
    (f : SmoothFamily U d) (x : ℂ × (d → ℝ))
    (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    ambientLift (baseMultiply g hg f) x = g x.1 * ambientLift f x := by
  change x.1 ∈ U at hx
  simp only [ambientLift, dif_pos hx, baseMultiply_apply]

/-- The existing descended vertical operator has the actual full-lift derivative. -/
theorem ambientLift_verticalDerivative (f : SmoothFamily U d) (v : d → ℝ)
    (x : ℂ × (d → ℝ)) (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    ambientLift (f.verticalDerivative v) x = fderiv ℝ (ambientLift f) x (0, v) :=
  f.ambientLift_verticalValue v x hx

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators
