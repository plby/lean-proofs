import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeBasePrimitiveBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperatorsDifferential

/-!
# The actual torus-constant family associated to a scalar base primitive

A real-smooth scalar function on the original open base gives a genuine
smooth family constant in the torus variable. Every real vertical
derivative vanishes. The base operator is exactly the scalar
antiholomorphic derivative, with its original factor `1/2`.
-/

noncomputable section

open TopologicalSpace Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeBasePrimitive

open FourierParameter PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*} [Fintype d]

/-- The literal family whose value depends only on the original base coordinate. -/
def constantFamily (u : ℂ → ℂ) (hu : ContDiffOn ℝ ∞ u U) : SmoothFamily U d where
  toFun x := u (x.1 : ℂ)
  smooth_lift := (hu.comp contDiffOn_fst (fun _ hx => hx)).congr (fun x hx => by
    change x.1 ∈ U at hx
    simp only [ambientLift, dif_pos hx, Function.comp_def])

@[simp] theorem constantFamily_apply (u : ℂ → ℂ) (hu : ContDiffOn ℝ ∞ u U)
    (x : U × UnitAddTorus d) : constantFamily u hu x = u (x.1 : ℂ) := rfl

theorem ambientLift_constantFamily (u : ℂ → ℂ) (hu : ContDiffOn ℝ ∞ u U)
    (x : ℂ × (d → ℝ)) (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    ambientLift (constantFamily u hu) x = u x.1 := by
  change x.1 ∈ U at hx
  simp only [ambientLift, dif_pos hx, constantFamily_apply]

/-- Every actual real vertical derivative vanishes, in every direction and at every torus point. -/
@[simp] theorem constantFamily_verticalDerivative (u : ℂ → ℂ)
    (hu : ContDiffOn ℝ ∞ u U) (v : d → ℝ) (b : U) (t : UnitAddTorus d) :
    (constantFamily u hu).verticalDerivative v (b, t) = 0 := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective t
  rw [SmoothFamily.verticalDerivative_apply]
  change torusLift (torusDirectionalDerivative ((constantFamily u hu).slice b) v) x = 0
  rw [torusDirectionalDerivative_lift]
  change fderiv ℝ (fun _ : d → ℝ => u (b : ℂ)) x v = 0
  simp only [fderiv_const_apply, zero_apply]

/-- The actual base derivative of the family is the derivative of the original scalar function. -/
theorem constantFamily_baseDerivative (u : ℂ → ℂ) (hu : ContDiffOn ℝ ∞ u U)
    (v : ℂ) (b : U) (t : UnitAddTorus d) :
    (constantFamily u hu).baseDerivative v (b, t) = fderiv ℝ u (b : ℂ) v := by
  have huAt : DifferentiableAt ℝ u (b : ℂ) :=
    ((hu (b : ℂ) b.property).contDiffAt (U.isOpen.mem_nhds b.property)).differentiableAt
      (by simp)
  have he : (fun z : ℂ => ambientValue (constantFamily u hu) (z, t)) =ᶠ[𝓝 (b : ℂ)] u := by
    filter_upwards [U.isOpen.mem_nhds b.property] with z hz
    exact ambientValue_apply (constantFamily u hu) ⟨z, hz⟩ t
  have hder := huAt.hasFDerivAt.congr_of_eventuallyEq he
  change (constantFamily u hu).baseDifferential (b, t) v = _
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    (((constantFamily u hu).ambientValue_hasFDerivAt b t).unique hder)

/-- The genuine family base operator has exactly the scalar Cauchy--Green normalization. -/
theorem constantFamily_d0 (u : ℂ → ℂ) (hu : ContDiffOn ℝ ∞ u U)
    (b : U) (t : UnitAddTorus d) :
    RelativeOperators.d0 (constantFamily u hu) (b, t) =
      (fderiv ℝ u (b : ℂ) 1 + Complex.I * fderiv ℝ u (b : ℂ) Complex.I) / 2 := by
  rw [RelativeOperators.d0_apply, constantFamily_baseDerivative, constantFamily_baseDerivative]

/-- The original mean admits a genuine local smooth-family primitive, with every vertical
derivative zero and actual torus-independent values. No period map is required. -/
theorem exists_local_constant_family_primitive (f : SmoothFamily U d) (b₀ : U) :
    ∃ V : Opens ℂ, V ≤ U ∧ (b₀ : ℂ) ∈ V ∧ ∃ g : SmoothFamily V d,
      (∀ b : V, ∀ t : UnitAddTorus d,
        RelativeOperators.d0 g (b, t) = f.coefficientValue 0 (b : ℂ)) ∧
      (∀ v : d → ℝ, ∀ b : V, ∀ t : UnitAddTorus d,
        g.verticalDerivative v (b, t) = 0) ∧
      (∀ b : V, ∀ s t : UnitAddTorus d, g (b, s) = g (b, t)) := by
  obtain ⟨V, hVU, hbV, u, hu, he⟩ := exists_local_mean_primitive f b₀
  refine ⟨V, hVU, hbV, constantFamily u hu.contDiffOn, ?_, ?_, ?_⟩
  · intro b t
    rw [constantFamily_d0]
    exact he b
  · intro v b t
    exact constantFamily_verticalDerivative u hu.contDiffOn v b t
  · intro b s t
    rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeBasePrimitive
