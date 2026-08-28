import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegularCocycle
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullback

/-!
# Genuine weighted three-forms on the actual regular period family

A function on the native regular upper-half-plane locus multiplies the
actual globally defined volume of the varying lattice quotient.  Its
pullback is calculated from the actual manifold derivative of the
triangle action, including both the base derivative and the true fibre
matrix determinant.  These calculations will be applied to `dt/F`.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular

open TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

local instance weightedUpstairsChartedSpace : ChartedSpace Model SpecialRegularUpstairs :=
  specialRegularData.periods.totalChartedSpace

local instance weightedUpstairsManifold : IsManifold I₃ ω SpecialRegularUpstairs :=
  specialRegularData.periods.totalSpace_isManifold

/-- The actual base-action derivative in a specified native source chart. -/
def baseActionDerivative (g : TriangleGroup) (a z : TriangleRegularPoint) : ℂ :=
  deriv (baseActionCoordinate (fun w : TriangleRegularPoint => (w.val : ℂ))
    specialRegularData g a) (z.val : ℂ)

/-- The native source chart used by the actual period-family chart is
valid at the original base point. -/
theorem representative_base_chart_target (x : SpecialRegularUpstairs) :
    (x.1.val : ℂ) ∈ (chartAt ℂ (familyRepresentative specialRegularData.periods x).1).target := by
  have hx : x ∈ (familyChart specialRegularData.periods x).source := mem_chart_source Model x
  have hz := (familyChart_target_subset specialRegularData.periods x
    ((familyChart specialRegularData.periods x).map_source hx)).1
  rw [familyChart_first_coordinate (fun z : TriangleRegularPoint => (z.val : ℂ))
    regularPoint_chart_apply specialRegularData.periods x x hx] at hz
  exact hz

/-- The determinant is calculated from the genuine native `mfderiv`. -/
theorem familyMap_det_mfderiv (g : TriangleGroup) (x : SpecialRegularUpstairs) :
    LinearMap.det (mfderiv I₃ I₃ (familyMap specialRegularData g) x).toLinearMap =
      baseActionDerivative g (familyRepresentative specialRegularData.periods x).1 x.1 *
        specialRegularData.determinantFactor g x.1 := by
  have hx : x ∈ (familyChart specialRegularData.periods x).source := mem_chart_source Model x
  have hy : familyMap specialRegularData g
      ((familyChart specialRegularData.periods x).symm
        (familyChart specialRegularData.periods x x)) ∈
      (familyChart specialRegularData.periods (familyMap specialRegularData g x)).source := by
    rw [(familyChart specialRegularData.periods x).left_inv hx]
    exact mem_chart_source Model (familyMap specialRegularData g x)
  have h := familyActionCoordinate_det_fderiv (fun z : TriangleRegularPoint => (z.val : ℂ))
    regularPoint_chart_apply specialRegularData g x (familyMap specialRegularData g x)
    ((familyChart specialRegularData.periods x).map_source hx) hy
  rw [familyChart_inverse_base specialRegularData.periods x x hx,
    familyChart_first_coordinate (fun z : TriangleRegularPoint => (z.val : ℂ))
      regularPoint_chart_apply specialRegularData.periods x x hx] at h
  exact (congrArg (fun A : Model →L[ℂ] Model => LinearMap.det A.toLinearMap)
    (familyMap_mfderiv specialRegularData g x)).trans h

/-- A genuine weighted section of the original upstairs canonical bundle. -/
def upstairsWeightedSection (C : TriangleRegularPoint → ℂ) (x : SpecialRegularUpstairs) :
    specialUpstairsCanonicalBundle.Fiber x := C x.1 • specialUpstairsCanonicalVolume x

def upstairsWeightedSectionMap (C : TriangleRegularPoint → ℂ)
    (x : SpecialRegularUpstairs) : specialUpstairsCanonicalBundle.TotalSpace :=
  ⟨x, upstairsWeightedSection C x⟩

@[simp] theorem upstairsWeightedSectionMap_proj (C : TriangleRegularPoint → ℂ)
    (x : SpecialRegularUpstairs) : (upstairsWeightedSectionMap C x).proj = x := rfl

theorem upstairsWeightedSection_ne_zero_iff (C : TriangleRegularPoint → ℂ)
    (x : SpecialRegularUpstairs) : upstairsWeightedSection C x ≠ 0 ↔ C x.1 ≠ 0 := by
  change C x.1 * 1 ≠ 0 ↔ C x.1 ≠ 0
  rw [mul_one]

/-- Holomorphicity is measured in the existing canonical-bundle total space. -/
theorem upstairsWeightedSectionMap_holomorphic (C : TriangleRegularPoint → ℂ)
    (hC : ContMDiff I₁ I₁ ω C) : ContMDiff I₃ ((I₃).prod I₁) ω
      (upstairsWeightedSectionMap C) := by
  have hc : ContMDiff I₃ I₁ ω (fun x : SpecialRegularUpstairs => C x.1) :=
    hC.comp specialRegularData.periods.projection_holomorphic
  have h := specialUpstairsCanonicalTrivialization.symm.contMDiff.comp
    (contMDiff_id.prodMk hc)
  have he : upstairsWeightedSectionMap C = specialUpstairsCanonicalTrivialization.symm ∘
      (fun x : SpecialRegularUpstairs => (x, C x.1)) := by
    funext x
    change (⟨x, C x.1 * 1⟩ : specialUpstairsCanonicalBundle.TotalSpace) = ⟨x, C x.1⟩
    exact congrArg (fun c : ℂ => (⟨x, c⟩ : specialUpstairsCanonicalBundle.TotalSpace))
      (mul_one (C x.1))
  rw [he]
  exact h

def upstairsWeightedHolomorphicSection (C : TriangleRegularPoint → ℂ)
    (hC : ContMDiff I₁ I₁ ω C) :
    ContMDiffSection I₃ ℂ ω specialUpstairsCanonicalBundle.Fiber where
  toFun := upstairsWeightedSection C
  contMDiff_toFun := upstairsWeightedSectionMap_holomorphic C hC

@[simp] theorem upstairsWeightedHolomorphicSection_apply (C : TriangleRegularPoint → ℂ)
    (hC : ContMDiff I₁ I₁ ω C) (x : SpecialRegularUpstairs) :
    upstairsWeightedHolomorphicSection C hC x = upstairsWeightedSection C x := rfl

/-- The exact differential-pullback formula for the actual three-form. -/
theorem upstairsWeightedSection_pullback (C : TriangleRegularPoint → ℂ)
    (g : TriangleGroup) (x : SpecialRegularUpstairs) :
    Pullback.pullbackLinear (familyMap specialRegularData g) x
      (upstairsWeightedSection C (familyMap specialRegularData g x)) =
        (C (g • x.1) *
          (baseActionDerivative g (familyRepresentative specialRegularData.periods x).1 x.1 *
            specialRegularData.determinantFactor g x.1)) • specialUpstairsCanonicalVolume x := by
  change id (α := ℂ) (Pullback.pullbackLinear (familyMap specialRegularData g) x
    (upstairsWeightedSection C (familyMap specialRegularData g x))) =
      (C (g • x.1) *
        (baseActionDerivative g (familyRepresentative specialRegularData.periods x).1 x.1 *
          specialRegularData.determinantFactor g x.1)) * 1
  rw [Pullback.pullbackLinear_preferred_coefficient, familyMap_det_mfderiv]
  change (_ * _) * (C (g • x.1) * 1) = (C (g • x.1) * (_ * _)) * 1
  ring

/-- The coefficient identity implies invariance of the genuine canonical section. -/
theorem upstairsWeightedSection_invariant (C : TriangleRegularPoint → ℂ)
    (hC : ∀ (g : TriangleGroup) (a z : TriangleRegularPoint),
      (z.val : ℂ) ∈ (chartAt ℂ a).target →
        C (g • z) * (baseActionDerivative g a z *
          specialRegularData.determinantFactor g z) = C z)
    (g : TriangleGroup) (x : SpecialRegularUpstairs) :
    Pullback.pullbackLinear (familyMap specialRegularData g) x
      (upstairsWeightedSection C (familyMap specialRegularData g x)) =
        upstairsWeightedSection C x := by
  rw [upstairsWeightedSection_pullback,
    hC g (familyRepresentative specialRegularData.periods x).1 x.1
      (representative_base_chart_target x)]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular
