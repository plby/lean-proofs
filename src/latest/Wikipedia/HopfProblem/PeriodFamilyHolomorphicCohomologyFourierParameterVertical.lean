import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterBasic

/-!
# Actual vertical differentiation preserves jointly smooth torus families

The derivative of each slice agrees with the derivative of the genuine
joint lift in the direction `(0,v)`. Smoothness on the original open base
therefore proves joint smoothness of the descended derivative family. The
operator on every fibre is exactly the existing torus directional derivative.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter

open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*} [Fintype d]

namespace SmoothFamily

variable (f : SmoothFamily U d)

/-- The actual vertical derivative of the original joint lift. -/
def jointVerticalValue (v : d → ℝ) (x : ℂ × (d → ℝ)) : ℂ :=
  fderiv ℝ (ambientLift f) x (0, v)

/-- No derivative-regularity premise is needed: it follows from joint smoothness. -/
theorem jointVerticalValue_contDiffOn (v : d → ℝ) :
    ContDiffOn ℝ ∞ (f.jointVerticalValue v) (Smooth.baseProductDomain U (d → ℝ)) :=
  ((contDiffOn_infty_iff_fderiv_of_isOpen
    (Smooth.baseProductDomain_isOpen U (d → ℝ))).mp f.smooth_lift).2.clm_apply
      contDiffOn_const

/-- The derivative of the genuine slice is the vertical part of the joint derivative. -/
theorem slice_fderiv_apply (b : U) (x v : d → ℝ) :
    fderiv ℝ (torusLift (f.slice b)) x v = f.jointVerticalValue v ((b : ℂ), x) := by
  have hAt : DifferentiableAt ℝ (ambientLift f) ((b : ℂ), x) :=
    ((f.smooth_lift ((b : ℂ), x) b.property).contDiffAt
      ((Smooth.baseProductDomain_isOpen U (d → ℝ)).mem_nhds b.property)).differentiableAt
        (by simp)
  have hpair := (hasFDerivAt_const (𝕜 := ℝ) (b : ℂ) x).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) x)
  have hcomp := hAt.hasFDerivAt.comp x hpair
  have hfun : (fun y : d → ℝ => ambientLift f ((b : ℂ), y)) =
      torusLift (f.slice b) := by
    funext y
    exact (f.slice_lift b y).symm
  change HasFDerivAt (fun y : d → ℝ => ambientLift f ((b : ℂ), y)) _ x at hcomp
  rw [hfun] at hcomp
  simpa [jointVerticalValue] using congrArg (fun L => L v) hcomp.fderiv

/-- The original fibrewise directional derivative as an actual parameterized function. -/
def verticalValue (v : d → ℝ) (x : U × UnitAddTorus d) : ℂ :=
  torusDirectionalDerivative (f.slice x.1) v x.2

/-- Its lift is the genuine vertical derivative of the original joint lift. -/
theorem ambientLift_verticalValue (v : d → ℝ) (x : ℂ × (d → ℝ))
    (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    ambientLift (f.verticalValue v) x = f.jointVerticalValue v x := by
  let b : U := ⟨x.1, hx⟩
  calc
    ambientLift (f.verticalValue v) x =
        torusLift (torusDirectionalDerivative (f.slice b) v) x.2 :=
      ambientLift_apply (f.verticalValue v) b x.2
    _ = fderiv ℝ (torusLift (f.slice b)) x.2 v := torusDirectionalDerivative_lift _ _ _
    _ = f.jointVerticalValue v x := f.slice_fderiv_apply b x.2 v

/-- The actual descended vertical derivative is again a genuinely jointly smooth family. -/
def verticalDerivative (v : d → ℝ) : SmoothFamily U d where
  toFun := f.verticalValue v
  smooth_lift := (f.jointVerticalValue_contDiffOn v).congr
    (fun x hx => f.ambientLift_verticalValue v x hx)

@[simp] theorem verticalDerivative_apply (v : d → ℝ) (b : U) (t : UnitAddTorus d) :
    f.verticalDerivative v (b, t) = torusDirectionalDerivative (f.slice b) v t := rfl

/-- On every fibre this is literally the previously defined torus differential operator. -/
@[simp] theorem verticalDerivative_slice (v : d → ℝ) (b : U) :
    (f.verticalDerivative v).slice b = torusDirectionalDerivative (f.slice b) v := rfl

end SmoothFamily

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter
