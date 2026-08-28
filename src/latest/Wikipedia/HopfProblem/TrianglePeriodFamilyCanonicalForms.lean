import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalBundle
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalGeneratorBase

/-!
# Pullback of the actual canonical form by triangle generators

The pullbacks below use `mfderiv` of the actual triangle action on the
varying lattice quotient.  Thus these are identities of genuine
alternating covectors on the tangent spaces, not assigned formal
characters.  The full three-form has multiplier `g'(z) det R_g(z)`;
the two factors are separately derived from the actual base action and
the actual fibre matrices.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical

open SpecialPeriods

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

section General

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold I₁ ω B] [MulAction TriangleGroup B]

theorem familyMap_holomorphic (D : Data ℂ B) (g : TriangleGroup) :
    letI := D.periods.totalChartedSpace
    ContMDiff I₃ I₃ ω (familyMap D g) := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  exact D.totalAction_holomorphic g

/-- The derivative used here is the genuine manifold derivative of the
actual quotient-family action, in its preferred tangent coordinates. -/
theorem familyMap_mfderiv (D : Data ℂ B) (g : TriangleGroup) (x : D.TotalSpace) :
    letI := D.periods.totalChartedSpace
    mfderiv I₃ I₃ (familyMap D g) x =
      fderiv ℂ (familyActionCoordinate D g x (familyMap D g x))
        (familyChart D.periods x x) := by
  let := D.periods.totalChartedSpace
  have hf : MDifferentiableAt I₃ I₃ (familyMap D g) x :=
    ((familyMap_holomorphic D g).mdifferentiable (by simp)) x
  simp only [mfderiv, hf, writtenInExtChartAt, mfld_simps, fderivWithin_univ]
  rfl

variable (coordinate : B → ℂ) (hcoordinate : ∀ a x : B, chartAt ℂ a x = coordinate x)

include hcoordinate in
/-- The full intrinsic canonical covector pulls back by the exact
base-derivative times fibre-determinant factor. -/
theorem familyCanonicalVolume_pullback (D : Data ℂ B) (g : TriangleGroup)
    (x : D.TotalSpace) :
    letI := D.periods.totalChartedSpace
    (familyCanonicalIntrinsicEquiv D.periods (familyMap D g x)
      (familyCanonicalVolume D.periods (familyMap D g x))).compContinuousLinearMap
        (mfderiv I₃ I₃ (familyMap D g) x) =
      (deriv (baseActionCoordinate coordinate D g (familyRepresentative D.periods x).1)
        (coordinate x.1) * D.determinantFactor g x.1) •
          familyCanonicalIntrinsicEquiv D.periods x (familyCanonicalVolume D.periods x) := by
  let := D.periods.totalChartedSpace
  rw [familyCanonicalIntrinsicEquiv_volume, familyCanonicalIntrinsicEquiv_volume,
    familyMap_mfderiv]
  change volume.compContinuousLinearMap
      (fderiv ℂ (familyActionCoordinate D g x (familyMap D g x))
        (familyChart D.periods x x)) =
    (deriv (baseActionCoordinate coordinate D g (familyRepresentative D.periods x).1)
      (coordinate x.1) * D.determinantFactor g x.1) • volume
  have hx : x ∈ (familyChart D.periods x).source := mem_chart_source Model x
  have hy : familyMap D g ((familyChart D.periods x).symm (familyChart D.periods x x)) ∈
      (familyChart D.periods (familyMap D g x)).source := by
    rw [(familyChart D.periods x).left_inv hx]
    exact mem_chart_source Model (familyMap D g x)
  rw [familyActionCoordinate_volume coordinate hcoordinate D g x (familyMap D g x)
    ((familyChart D.periods x).map_source hx) hy,
    familyChart_inverse_base D.periods x x hx,
    familyChart_first_coordinate coordinate hcoordinate D.periods x x hx]
  rfl

end General

section Regular

variable (D : Data ℂ TriangleRegularPoint)

/-- The first triangle generator's actual full three-form multiplier. -/
theorem familyCanonicalVolume_pullback_generator₁ (x : D.TotalSpace) :
    letI := D.periods.totalChartedSpace
    (familyCanonicalIntrinsicEquiv D.periods (familyMap D triangleGenerator₁ x)
      (familyCanonicalVolume D.periods (familyMap D triangleGenerator₁ x))).compContinuousLinearMap
        (mfderiv I₃ I₃ (familyMap D triangleGenerator₁) x) =
      (((((x.1.val : ℂ) + 1) ^ 2)⁻¹) * (-1 / (D.periods.point x.1).val.τ)) •
        familyCanonicalIntrinsicEquiv D.periods x (familyCanonicalVolume D.periods x) := by
  let := D.periods.totalChartedSpace
  rw [familyCanonicalVolume_pullback (fun z : TriangleRegularPoint => (z.val : ℂ))
    regularPoint_chart_apply]
  have hx : x ∈ (familyChart D.periods x).source := mem_chart_source Model x
  have hz := (familyChart_target_subset D.periods x ((familyChart D.periods x).map_source hx)).1
  rw [familyChart_first_coordinate (fun z : TriangleRegularPoint => (z.val : ℂ))
    regularPoint_chart_apply D.periods x x hx] at hz
  rw [regularPoint_generator₁_deriv D _ hz, D.determinantFactor_generator₁]

/-- The second generator has the opposite fibre-determinant sign from
the first, while both base derivatives are positive inverse squares. -/
theorem familyCanonicalVolume_pullback_generator₂ (x : D.TotalSpace) :
    letI := D.periods.totalChartedSpace
    (familyCanonicalIntrinsicEquiv D.periods (familyMap D triangleGenerator₂ x)
      (familyCanonicalVolume D.periods (familyMap D triangleGenerator₂ x))).compContinuousLinearMap
        (mfderiv I₃ I₃ (familyMap D triangleGenerator₂) x) =
      (((((x.1.val : ℂ) + (Triangle.width : ℂ)) ^ 2)⁻¹) *
        (1 / (D.periods.point x.1).val.τ)) •
        familyCanonicalIntrinsicEquiv D.periods x (familyCanonicalVolume D.periods x) := by
  let := D.periods.totalChartedSpace
  rw [familyCanonicalVolume_pullback (fun z : TriangleRegularPoint => (z.val : ℂ))
    regularPoint_chart_apply]
  have hx : x ∈ (familyChart D.periods x).source := mem_chart_source Model x
  have hz := (familyChart_target_subset D.periods x ((familyChart D.periods x).map_source hx)).1
  rw [familyChart_first_coordinate (fun z : TriangleRegularPoint => (z.val : ℂ))
    regularPoint_chart_apply D.periods x x hx] at hz
  rw [regularPoint_generator₂_deriv D _ hz, D.determinantFactor_generator₂]

/-- The actual cusp translation preserves the genuine full volume form. -/
theorem familyCanonicalVolume_pullback_cusp (x : D.TotalSpace) :
    letI := D.periods.totalChartedSpace
    (familyCanonicalIntrinsicEquiv D.periods (familyMap D triangleCuspGenerator x)
      (familyCanonicalVolume D.periods
        (familyMap D triangleCuspGenerator x))).compContinuousLinearMap
        (mfderiv I₃ I₃ (familyMap D triangleCuspGenerator) x) =
      familyCanonicalIntrinsicEquiv D.periods x (familyCanonicalVolume D.periods x) := by
  let := D.periods.totalChartedSpace
  rw [familyCanonicalVolume_pullback (fun z : TriangleRegularPoint => (z.val : ℂ))
    regularPoint_chart_apply]
  have hx : x ∈ (familyChart D.periods x).source := mem_chart_source Model x
  have hz := (familyChart_target_subset D.periods x ((familyChart D.periods x).map_source hx)).1
  rw [familyChart_first_coordinate (fun z : TriangleRegularPoint => (z.val : ℂ))
    regularPoint_chart_apply D.periods x x hx] at hz
  rw [regularPoint_cusp_deriv D _ hz, D.determinantFactor_cusp, mul_one, one_smul]

end Regular

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical
