import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsPullbackBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsPullbackLinear
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsDifferential
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsFrame

/-!
# The full antiholomorphic chain rule in the original period frame

The real chain rule is projected onto actual antiholomorphic covectors.
The four genuine real-coordinate derivatives are then reduced using the
proved full period-coordinate identities. The resulting three coefficients
are explicit evaluations of the original real Fréchet derivative.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff BigOperators Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback

open HolomorphicDolbeaultThree

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The actual chain rule before reduction to the first two marked real
coordinates. All four terms come from the genuine real differential. -/
theorem ambientPullback_dbar_four {f : RealModel → ℂ} (q : Model)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂)
    (hf : DifferentiableAt ℝ f (inverseGraph P q)) :
    dbar (ambientPullback P f) q =
      baseCoefficient (fderiv ℝ f (inverseGraph P q)) • baseCovector.val +
        ∑ j : Fin 4, realCoefficient (fderiv ℝ f (inverseGraph P q)) j •
          dbar (coordinate P j) q := by
  rw [dbar, ambientPullback_fderiv P q hq hf, antiPart_comp_graph]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [dbar, coordinate_fderiv_eq_projection P j q hq]

/-- Literal three coefficients of the original real derivative after
the two genuine full period-coordinate identities are used. -/
def reducedCoefficients (τ μ β : ℂ) (L : RealModel →L[ℝ] ℂ) : Model :=
  (baseCoefficient L,
    ![realCoefficient L 0 -
        (6 * μ * realCoefficient L 2 + β * realCoefficient L 3),
      realCoefficient L 1 -
        (τ * realCoefficient L 2 + μ * realCoefficient L 3)])

/-- The full antiholomorphic derivative of an actual smooth ambient
function, pulled back by the original inverse period coordinates. -/
theorem ambientPullback_dbar {f : RealModel → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Smooth.baseProductDomain U RealPlane₄))
    (q : Model) (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    let L := fderiv ℝ f (inverseGraph P q)
    dbar (ambientPullback P f) q = baseCoefficient L • baseCovector.val +
      (realCoefficient L 0 -
        (6 * Smooth.muValue P q.1 * realCoefficient L 2 +
          Smooth.betaValue P q.1 * realCoefficient L 3)) • dbar (coordinate P 0) q +
      (realCoefficient L 1 -
        (Smooth.tauValue P q.1 * realCoefficient L 2 +
          Smooth.muValue P q.1 * realCoefficient L 3)) • dbar (coordinate P 1) q := by
  dsimp only
  have hd : DifferentiableAt ℝ f (inverseGraph P q) :=
    (hf.contDiffAt ((Smooth.baseProductDomain_isOpen U RealPlane₄).mem_nhds hq)).differentiableAt
      (by simp)
  rw [ambientPullback_dbar_four P q hq hd, Fin.sum_univ_four,
    dbar_coordinate_two P q hq, dbar_coordinate_three P q hq]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

/-- At a native base point the formula uses the literal original period
entries and the actual inverse of its original real period isomorphism. -/
theorem ambientPullback_dbar_at {f : RealModel → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Smooth.baseProductDomain U RealPlane₄))
    (b : U) (z : ComplexPlane₂) :
    let L := fderiv ℝ f ((b : ℂ), (P.periodEquiv b).symm z)
    dbar (ambientPullback P f) ((b : ℂ), z) = baseCoefficient L • baseCovector.val +
      (realCoefficient L 0 -
        (6 * (P.point b).val.μ * realCoefficient L 2 +
          (P.point b).val.β * realCoefficient L 3)) •
            dbar (coordinate P 0) ((b : ℂ), z) +
      (realCoefficient L 1 -
        ((P.point b).val.τ * realCoefficient L 2 +
          (P.point b).val.μ * realCoefficient L 3)) •
            dbar (coordinate P 1) ((b : ℂ), z) := by
  simpa only [inverseGraph_apply, Smooth.muValue_apply, Smooth.betaValue_apply,
    Smooth.tauValue_apply] using ambientPullback_dbar P hf ((b : ℂ), z) b.property

/-- The actual full pullback differential is the genuine native frame
applied to these explicitly computed real-derivative coefficients. -/
theorem ambientPullback_dbar_eq_frame {f : RealModel → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Smooth.baseProductDomain U RealPlane₄))
    (b : U) (z : ComplexPlane₂) :
    dbar (ambientPullback P f) ((b : ℂ), z) =
      (frameEquiv P b z (reducedCoefficients (P.point b).val.τ (P.point b).val.μ
        (P.point b).val.β (fderiv ℝ f ((b : ℂ), (P.periodEquiv b).symm z)))).val := by
  exact ambientPullback_dbar_at P hf b z

/-- These are the coefficients in the already proved genuine frame,
not coefficients introduced by defining a replacement differential. -/
theorem ambientPullback_frame_inverse {f : RealModel → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Smooth.baseProductDomain U RealPlane₄))
    (b : U) (z : ComplexPlane₂) :
    (frameEquiv P b z).symm
      ⟨dbar (ambientPullback P f) ((b : ℂ), z), dbar_mem _ _⟩ =
      reducedCoefficients (P.point b).val.τ (P.point b).val.μ (P.point b).val.β
        (fderiv ℝ f ((b : ℂ), (P.periodEquiv b).symm z)) := by
  apply (frameEquiv P b z).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact ambientPullback_dbar_eq_frame P hf b z

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback
