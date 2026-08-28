import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsCoordinates
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic

/-!
# The actual inverse-period pullback and its real chain rule

The source is the unchanged complex covering model. The target of the
coordinate map is only a real normed space: the original complex base and
the four original real lattice coordinates. No complex structure is imposed
on this real coordinate product.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback

open HolomorphicDolbeaultThree

/-- The original base and real lattice-coordinate model, used only for real calculus. -/
abbrev RealModel := ℂ × RealPlane₄

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The original base together with the actual inverse real period coordinates. -/
def inverseGraph (q : Model) : RealModel :=
  (q.1, Smooth.inversePeriodCoordinates P q)

@[simp] theorem inverseGraph_apply (b : U) (z : ComplexPlane₂) :
    inverseGraph P ((b : ℂ), z) = ((b : ℂ), (P.periodEquiv b).symm z) := by
  simp only [inverseGraph, Smooth.inversePeriodCoordinates_apply]

/-- Joint real smoothness of the actual inverse-coordinate map. -/
theorem inverseGraph_contDiffOn :
    ContDiffOn ℝ ∞ (inverseGraph P) (Smooth.baseProductDomain U ComplexPlane₂) :=
  contDiffOn_fst.prodMk (Smooth.inversePeriodCoordinates_contDiffOn P)

/-- The original smooth inverse coordinates have their actual real Fréchet derivative. -/
theorem inverseCoordinates_hasFDerivAt (q : Model)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    HasFDerivAt (Smooth.inversePeriodCoordinates P)
      (fderiv ℝ (Smooth.inversePeriodCoordinates P) q) q :=
  (((Smooth.inversePeriodCoordinates_contDiffOn P).contDiffAt
    ((Smooth.baseProductDomain_isOpen U ComplexPlane₂).mem_nhds hq)).differentiableAt
      (by simp)).hasFDerivAt

/-- The derivative of the actual graph keeps the original base projection
and the actual derivative of its inverse real coordinates. -/
theorem inverseGraph_hasFDerivAt (q : Model)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    HasFDerivAt (inverseGraph P)
      ((ContinuousLinearMap.fst ℝ ℂ ComplexPlane₂).prod
        (fderiv ℝ (Smooth.inversePeriodCoordinates P) q)) q :=
  hasFDerivAt_fst.prodMk (inverseCoordinates_hasFDerivAt P q hq)

/-- Pullback along the actual original inverse-period coordinate map. -/
def ambientPullback (f : RealModel → ℂ) : Model → ℂ := f ∘ inverseGraph P

@[simp] theorem ambientPullback_apply (f : RealModel → ℂ) (q : Model) :
    ambientPullback P f q = f (q.1, Smooth.inversePeriodCoordinates P q) := rfl

/-- A smooth function in the original real coordinates has a genuinely
jointly smooth pullback in the unchanged complex covering coordinates. -/
theorem ambientPullback_contDiffOn {f : RealModel → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Smooth.baseProductDomain U RealPlane₄)) :
    ContDiffOn ℝ ∞ (ambientPullback P f) (Smooth.baseProductDomain U ComplexPlane₂) :=
  hf.comp (inverseGraph_contDiffOn P) (fun _ hq => hq)

/-- The real chain rule for the literal pullback, before any antiholomorphic projection. -/
theorem ambientPullback_fderiv {f : RealModel → ℂ} (q : Model)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂)
    (hf : DifferentiableAt ℝ f (inverseGraph P q)) :
    fderiv ℝ (ambientPullback P f) q =
      (fderiv ℝ f (inverseGraph P q)).comp
        ((ContinuousLinearMap.fst ℝ ℂ ComplexPlane₂).prod
          (fderiv ℝ (Smooth.inversePeriodCoordinates P) q)) :=
  (hf.hasFDerivAt.comp q (inverseGraph_hasFDerivAt P q hq)).fderiv

/-- The full real derivative of each embedded real coordinate is obtained
by projection from the actual derivative of the inverse-coordinate map. -/
theorem coordinate_fderiv_eq_projection (j : Fin 4) (q : Model)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    fderiv ℝ (coordinate P j) q =
      Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp
        (fderiv ℝ (Smooth.inversePeriodCoordinates P) q)) := by
  let L : RealPlane₄ →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)
  change fderiv ℝ (L ∘ Smooth.inversePeriodCoordinates P) q = _
  rw [(L.hasFDerivAt.comp q (inverseCoordinates_hasFDerivAt P q hq)).fderiv]
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback
