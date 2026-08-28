import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeFamilyBasic

/-!
# Actual base derivatives preserve genuine smooth torus families

Every joint directional derivative descends to a genuinely jointly smooth
family. In particular, the base directional derivative is the evaluation
of the actual continuous base differential. The ambient-value endpoint
identifies this differential with the real Fréchet derivative in the
original complex base variable, at every point of the open base.
-/

noncomputable section

open Function TopologicalSpace
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter

open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*} [Fintype d]

namespace SmoothFamily

variable (f : SmoothFamily U d)

/-- The descended full differential evaluates to the actual derivative of the joint lift. -/
theorem ambientLift_jointDifferential_apply (w : ℂ × (d → ℝ)) (x : ℂ × (d → ℝ))
    (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    ambientLift (fun p => f.jointDifferential p w) x = fderiv ℝ (ambientLift f) x w := by
  let b : U := ⟨x.1, hx⟩
  calc
    ambientLift (fun p => f.jointDifferential p w) x =
        f.jointDifferential (b, torusQuotient x.2) w :=
      ambientLift_apply (fun p => f.jointDifferential p w) b x.2
    _ = fderiv ℝ (ambientLift f) x w := by rw [jointDifferential_lift]

/-- Differentiation in any fixed joint real direction preserves actual joint smoothness. -/
def jointDerivative (w : ℂ × (d → ℝ)) : SmoothFamily U d where
  toFun p := f.jointDifferential p w
  smooth_lift := (f.jointLift_fderiv_contDiffOn.clm_apply contDiffOn_const).congr
    (fun x hx => f.ambientLift_jointDifferential_apply w x hx)

@[simp] theorem jointDerivative_apply (w : ℂ × (d → ℝ)) (p : U × UnitAddTorus d) :
    f.jointDerivative w p = f.jointDifferential p w := rfl

/-- The actual scalar derivative in a fixed real base direction. -/
def baseDerivative (v : ℂ) : SmoothFamily U d := f.jointDerivative (v, 0)

@[simp] theorem baseDerivative_apply (v : ℂ) (p : U × UnitAddTorus d) :
    f.baseDerivative v p = f.baseDifferential p v := rfl

/-- Its lift is the genuine derivative of the original joint lift in the direction `(v,0)`. -/
theorem ambientLift_baseDerivative (v : ℂ) (x : ℂ × (d → ℝ))
    (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    ambientLift (f.baseDerivative v) x = fderiv ℝ (ambientLift f) x (v, 0) :=
  f.ambientLift_jointDifferential_apply (v, 0) x hx

/-- The original smoothness supplies the joint Fréchet derivative at each native point. -/
theorem jointLift_hasFDerivAt (b : U) (x : d → ℝ) :
    HasFDerivAt (ambientLift f) (fderiv ℝ (ambientLift f) ((b : ℂ), x)) ((b : ℂ), x) :=
  (((f.smooth_lift ((b : ℂ), x) b.property).contDiffAt
    ((Smooth.baseProductDomain_isOpen U (d → ℝ)).mem_nhds b.property)).differentiableAt
      (by simp)).hasFDerivAt

/-- The genuine base differential is the real derivative in the original ambient base variable. -/
theorem ambientValue_hasFDerivAt (b : U) (t : UnitAddTorus d) :
    HasFDerivAt (fun z : ℂ => ambientValue f (z, t))
      (f.baseDifferential (b, t)) (b : ℂ) := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective t
  rw [f.baseDifferential_lift b x]
  have hbase := (f.jointLift_hasFDerivAt b x).comp (b : ℂ)
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) (b : ℂ) x)
  simpa only [Function.comp_def, ambientLift_eq_ambientValue] using hbase

/-- Each native fibre of the ambient-value representative is continuous on the actual torus. -/
theorem ambientValue_continuous_fibre (b : U) :
    Continuous (fun t : UnitAddTorus d => ambientValue f ((b : ℂ), t)) := by
  have h : Continuous (fun t : UnitAddTorus d => f (b, t)) :=
    f.continuous.comp (continuous_const.prodMk continuous_id)
  simpa only [ambientValue_apply] using h

end SmoothFamily

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter
