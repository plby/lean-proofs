import Wikipedia.HopfProblem.SpecialPeriodsThreefoldChosenBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegular
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCoverSphere
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupOuterMeridian

/-!
# A genuine peripheral circle inside the chosen cusp patch

The finite coordinate used for the jointly based planar meridians is
the actual normalized sphere uniformization.  Compactness at its infinity
therefore places every sufficiently large outer-circle core in the
specific cusp disc used in the threefold gluing.  The based vertical tail
is not asserted to stay in that disc.
-/

noncomputable section

open Set
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspPeripheral

open Triangle

attribute [local instance] triangleCompactifiedChartedSpace triangleRegularQuotientChartedSpace

/-- The actual finite uniformization, with target the literal regular base patch. -/
def planeToRegularBase : TwicePuncturedPlane → regularPatch :=
  regularBiholomorph ∘ triangleRegularPlaneHomeomorph.symm

theorem planeToRegularBase_continuous : Continuous planeToRegularBase :=
  regularBiholomorph.continuous.comp triangleRegularPlaneHomeomorph.symm.continuous

/-- This finite coordinate is the same one used by the actual compact
sphere uniformization, not an independently marked planar model. -/
theorem planeToRegularBase_eq_finiteInverse (z : TwicePuncturedPlane) :
    (planeToRegularBase z : TriangleCompactifiedOrbitSpace) =
      MuTorsor.Cover.finiteInverse triangleSphereUniformization (z : ℂ) := by
  apply triangleSphereUniformization.injective
  have hfinite : triangleSphereUniformization
      (planeToRegularBase z : TriangleCompactifiedOrbitSpace) = ((z : ℂ) : RiemannSphere) := by
    change ((triangleRegularPlaneHomeomorph
      (triangleRegularPlaneHomeomorph.symm z) : ℂ) : RiemannSphere) = ((z : ℂ) : RiemannSphere)
    rw [triangleRegularPlaneHomeomorph.apply_symm_apply]
  exact hfinite.trans
    (MuTorsor.Cover.apply_finiteInverse triangleSphereUniformization (z : ℂ)).symm

/-- The genuine selected cusp filling patch contains all sufficiently
large finite regular coordinates. -/
theorem exists_cusp_exterior_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ z : TwicePuncturedPlane, A ≤ ‖(z : ℂ)‖ →
      (planeToRegularBase z : TriangleCompactifiedOrbitSpace) ∈
        specialBaseCover.fillingPatch none := by
  obtain ⟨A, hA, hmem⟩ := MuTorsor.Cover.finitePullback_contains_exterior
    triangleSphereUniformization triangleSphereUniformization_cusp
    (specialBaseCover.fillingPatch none) (specialBaseCover.point_mem_fillingPatch none)
  refine ⟨A, hA, fun z hz => ?_⟩
  rw [planeToRegularBase_eq_finiteInverse]
  apply hmem
  simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz

/-- There is an actual explicit outer circle whose whole core lies in
the chosen cusp patch.  Its basepoint remains the bottom of that circle. -/
theorem exists_outerCircle_in_cusp :
    ∃ R : ℝ, ∃ hR : 2 ≤ R, ∀ t : unitInterval,
      (planeToRegularBase (outerPositiveCircle R hR t) : TriangleCompactifiedOrbitSpace) ∈
        specialBaseCover.fillingPatch none := by
  obtain ⟨A, _, hA⟩ := exists_cusp_exterior_bound
  let R : ℝ := max 2 (A + 1)
  have hR : 2 ≤ R := le_max_left _ _
  refine ⟨R, hR, fun t => hA _ ?_⟩
  have hnorm := outerPositiveCircle_norm_lower_bound R hR t
  have hlarge : A + 1 ≤ R := le_max_right _ _
  linarith

/-- A chosen radius for that concrete outer circle. -/
def outerRadius : ℝ := exists_outerCircle_in_cusp.choose

theorem outerRadius_ge_two : 2 ≤ outerRadius :=
  exists_outerCircle_in_cusp.choose_spec.choose

/-- The literal regular-base image of the chosen outer-circle core. -/
def outerRegularCircle :
    Path (planeToRegularBase (outerCircleBasepoint outerRadius outerRadius_ge_two))
      (planeToRegularBase (outerCircleBasepoint outerRadius outerRadius_ge_two)) :=
  (outerPositiveCircle outerRadius outerRadius_ge_two).map planeToRegularBase_continuous

theorem outerRegularCircle_mem_cusp (t : unitInterval) :
    (outerRegularCircle t : TriangleCompactifiedOrbitSpace) ∈
      specialBaseCover.fillingPatch none :=
  exists_outerCircle_in_cusp.choose_spec.choose_spec t

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspPeripheral
