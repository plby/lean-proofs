import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspLogCover
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspChart
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspExponential

/-!
# The native logarithmic pullback in the actual reference toric chart

The reference exponential lands in the genuine full reference-chart
domain. Its map to the global threefold is the original logarithmic
cusp map. The actual extended-chart equation computes its manifold
derivative, and functoriality of genuine holomorphic-form pullback gives
the complete coefficient comparison.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open ToricCharts ToricFan CuspUniformization HolomorphicDifferentialForms

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃
local notation "EL" => ℂ × ComplexPlane₂
local notation "IL" => modelWithCornersSelf ℂ EL

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The original reference exponential, codrestricted to its genuine open tube domain. -/
def refExpInto (x : LogDomain) : referenceDomain :=
  ⟨refExp x.val, by
    rw [mem_referenceDomain, time_refExp]
    exact (mem_logDomain CuspGeometry.data.radius x.val).mp x.property⟩

@[simp] theorem refExpInto_val (x : LogDomain) :
    (refExpInto x : E₃) = refExp x.val := rfl

theorem refExpInto_holomorphic : ContMDiff IL I₃ ω refExpInto := by
  have h : ContMDiff IL I₃ ω (fun x : LogDomain => refExp x.val) :=
    refExp_holomorphic.contMDiff.comp contMDiff_subtype_val
  intro x
  have he : ContMDiffAt IL I₃ ω (Subtype.val ∘ refExpInto) x ↔
      ContMDiffAt IL I₃ ω refExpInto x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (h x)

/-- In the unchanged native charts the coordinate expression is exactly `refExp`. -/
theorem refExpInto_extChart_eq (x : LogDomain) :
    extChartAt I₃ (refExpInto x) ∘ refExpInto = refExp ∘ extChartAt IL x := by
  funext y
  rfl

theorem refExp_mfderiv (x : EL) :
    (mfderiv IL I₃ refExp x : EL →L[ℂ] E₃) = refExpDerivative x :=
  (refExp_hasFDerivAt x).hasMFDerivAt.mfderiv

/-- The manifold derivative equals the already computed exact complex Jacobian. -/
theorem refExpInto_mfderiv (x : LogDomain) :
    (mfderiv IL I₃ refExpInto x : EL →L[ℂ] E₃) = refExpDerivative x.val := by
  have hf := refExpInto_holomorphic.mdifferentiable (by simp) x
  have hs : MDifferentiableAt IL IL (extChartAt IL x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source EL x)
  have ht : MDifferentiableAt I₃ I₃ (extChartAt I₃ (refExpInto x)) (refExpInto x) :=
    mdifferentiableAt_extChartAt (mem_chart_source E₃ (refExpInto x))
  have hg : MDifferentiableAt IL I₃ refExp (extChartAt IL x x) :=
    (refExp_holomorphic.contMDiff.mdifferentiable (by simp)) _
  have h := mfderiv_congr (I := IL) (I' := I₃) (x := x) (refExpInto_extChart_eq x)
  rw [mfderiv_comp x ht hf, mfderiv_comp x hg hs,
    mfderiv_extChartAt_self, mfderiv_extChartAt_self, refExp_mfderiv] at h
  ext v
  exact congrArg (fun L : EL →L[ℂ] E₃ => L v) h

/-- Equality already holds in the original toric tube, before taking any quotient. -/
theorem referenceLift_refExpInto (x : LogDomain) :
    referenceLift (refExpInto x) = totalExponentialLift CuspGeometry.data.radius x := by
  apply Subtype.ext
  change ToricSpace.inclusion ToricSpace.referenceTriangle (refExp x.val) =
    ToricSpace.inclusion ToricSpace.referenceTriangle
      (monomial ToricSpace.referenceTriangle.dual (totalExponentialCoordinates x.val))
  rw [monomial_reference_dual_totalExponential]

/-- The actual quotient maps have the same value, not merely the same base parameter. -/
theorem referenceQuotient_refExpInto (x : LogDomain) :
    referenceQuotient (refExpInto x) = localLogMap x :=
  congrArg (fun y : ToricSpace.Tube (CuspQuotient.disc CuspGeometry.data.radius) =>
    (CuspQuotient.quotientMap CuspGeometry.data.correction CuspGeometry.data.radius y :
      CuspGeometry.LocalSpace)) (referenceLift_refExpInto x)

theorem referenceMap_refExpInto (x : LogDomain) :
    referenceMap (refExpInto x) = globalLogMap x :=
  congrArg CuspGeometry.inclusion (referenceQuotient_refExpInto x)

theorem referenceMap_comp_refExpInto : referenceMap ∘ refExpInto = globalLogMap :=
  funext referenceMap_refExpInto

/-- Functoriality compares the actual native holomorphic forms on the full logarithmic cover. -/
theorem logPullback_eq_referencePullback {p : ℕ} (θ : Form EL Threefold.Space p) :
    logPullback θ = pullback refExpInto refExpInto_holomorphic (referencePullback θ) := by
  change pullback globalLogMap globalLogMap_holomorphic θ =
    pullback refExpInto refExpInto_holomorphic (pullback referenceMap referenceMap_holomorphic θ)
  rw [← pullback_comp]
  exact congrArg (fun L => L θ)
    (pullback_congr globalLogMap_holomorphic
      (referenceMap_holomorphic.comp refExpInto_holomorphic) referenceMap_comp_refExpInto.symm)

/-- The complete scalar coefficient comparison uses the actual derivative computed above. -/
theorem logCoefficients_refExp {p : ℕ} (θ : Form EL Threefold.Space p)
    (x : LogDomain) (v : Fin p → EL) :
    logCoefficients θ x v =
      referenceCoefficient θ (fun j => refExpDerivative x.val (v j)) (refExpInto x) := by
  have hv : (fun j => mfderiv IL I₃ refExpInto x (v j)) =
      (fun j => refExpDerivative x.val (v j)) := by
    funext j
    exact congrArg (fun L : EL →L[ℂ] E₃ => L (v j)) (refExpInto_mfderiv x)
  calc
    logCoefficients θ x v =
        referencePullback θ (refExpInto x) (fun j => mfderiv IL I₃ refExpInto x (v j)) := by
      rw [logCoefficients_apply, logPullback_eq_referencePullback]
      rfl
    _ = referencePullback θ (refExpInto x) (fun j => refExpDerivative x.val (v j)) :=
      congrArg (referencePullback θ (refExpInto x)) hv
    _ = referenceCoefficient θ (fun j => refExpDerivative x.val (v j)) (refExpInto x) :=
      (referenceCoefficient_eq θ _ (refExpInto x)).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
