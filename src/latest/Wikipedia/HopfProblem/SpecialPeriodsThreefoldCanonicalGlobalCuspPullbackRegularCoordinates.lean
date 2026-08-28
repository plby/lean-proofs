import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspComparisonDerivative
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalBundle

/-!
# Genuine regular volume pullback from logarithmic cusp coordinates

The period-vector projection is locally a lattice shear in its original
covering charts. Its actual manifold derivative therefore preserves the
base-first alternating three-volume. The unchanged logarithmic comparison
scales only the base coordinate, by the actual triangle cusp width.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback

open TrianglePeriodFamily.Canonical
open HolomorphicForms.Cusp

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ Model

section PeriodQuotient

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold I₁ ω B]

local instance coverProductChartedSpace : ChartedSpace Model (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (B × ComplexPlane₂))

local instance coverProductManifold : IsManifold I₃ ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) B ComplexPlane₂

/-- The original quotient map written in its original preferred source and target charts. -/
def periodQuotientCoordinate (P : HolomorphicPeriodMap ℂ B) (x : B × ComplexPlane₂) :
    Model → Model :=
  familyChart P (P.quotientMap x) ∘ P.quotientMap ∘ (chartAt Model x).symm

variable (coordinate : B → ℂ) (hcoordinate : ∀ a x : B, chartAt ℂ a x = coordinate x)

include hcoordinate in
omit [IsManifold I₁ ω B] in
/-- The quotient's actual chart expression agrees near the point with one fixed lattice shear. -/
theorem periodQuotientCoordinate_eventually_shear (P : HolomorphicPeriodMap ℂ B)
    (x : B × ComplexPlane₂) :
    ∃ g : Multiplicative standardLattice,
      periodQuotientCoordinate P x =ᶠ[𝓝 (chartAt Model x x)]
        shearMap (periodDisplacement P x.1 g.toAdd) := by
  let := P.coveringAction
  let := P.totalChartedSpace
  let b := familyRepresentative P (P.quotientMap x)
  have hx : P.quotientMap x ∈ (familyChart P (P.quotientMap x)).source :=
    mem_chart_source Model (P.quotientMap x)
  obtain ⟨g, _, hg⟩ := CoveringQuotient.localInverse_eventually_deck P.quotientCoveringMap
    (fun g => (P.coveringAction_holomorphic g).continuous) b x hx.1
  have ht : Tendsto (chartAt Model x).symm (𝓝 (chartAt Model x x)) (𝓝 x) := by
    have hi := (chartAt Model x).symm.continuousAt
      ((chartAt Model x).map_source (mem_chart_source Model x))
    change Tendsto (chartAt Model x).symm (𝓝 (chartAt Model x x))
      (𝓝 ((chartAt Model x).symm (chartAt Model x x))) at hi
    rwa [(chartAt Model x).left_inv (mem_chart_source Model x)] at hi
  refine ⟨g, ?_⟩
  have he := (hg.comp_tendsto ht).fun_comp (chartAt Model b)
  exact he.trans (coveringAction_coordinate_eventually coordinate hcoordinate P x b g
    ((chartAt Model x).map_source (mem_chart_source Model x)))

include hcoordinate in
/-- The genuine chart derivative of the original lattice quotient has determinant one. -/
theorem periodQuotientCoordinate_det (P : HolomorphicPeriodMap ℂ B)
    (x : B × ComplexPlane₂) :
    LinearMap.det (fderiv ℂ (periodQuotientCoordinate P x)
      (chartAt Model x x)).toLinearMap = 1 := by
  obtain ⟨g, hg⟩ := periodQuotientCoordinate_eventually_shear coordinate hcoordinate P x
  rw [hg.fderiv_eq]
  exact det_fderiv_shearMap x.2
    ((periodDisplacement_contDiffAt P x.1 g.toAdd
      ((chartAt ℂ x.1).map_source (mem_chart_source ℂ x.1))).differentiableAt
        (by simp)).hasDerivAt

include hcoordinate in
/-- The actual manifold derivative preserves the native alternating three-volume. -/
theorem periodQuotient_volume_pullback (P : HolomorphicPeriodMap ℂ B)
    (x : B × ComplexPlane₂) :
    letI := P.totalChartedSpace
    volume.compContinuousLinearMap (mfderiv I₃ I₃ P.quotientMap x) = volume := by
  let := P.totalChartedSpace
  have hf := P.quotientMap_holomorphic.mdifferentiable (by simp) x
  have hm : mfderiv I₃ I₃ P.quotientMap x =
      fderiv ℂ (periodQuotientCoordinate P x) (chartAt Model x x) := by
    simp only [mfderiv, hf, writtenInExtChartAt, mfld_simps, fderivWithin_univ]
    rfl
  rw [hm]
  change volume.compContinuousLinearMap
    (fderiv ℂ (periodQuotientCoordinate P x) (chartAt Model x x) : Model →L[ℂ] Model) = volume
  rw [volume_pullback, periodQuotientCoordinate_det coordinate hcoordinate, one_smul]

include hcoordinate in
/-- Pullback of the genuine family canonical section, not a formal determinant label. -/
theorem familyVolume_periodQuotient_pullback (P : HolomorphicPeriodMap ℂ B)
    (x : B × ComplexPlane₂) :
    letI := P.totalChartedSpace
    (familyCanonicalIntrinsicEquiv P (P.quotientMap x)
      (familyCanonicalVolume P (P.quotientMap x))).compContinuousLinearMap
        (mfderiv I₃ I₃ P.quotientMap x) = volume := by
  let := P.totalChartedSpace
  rw [familyCanonicalIntrinsicEquiv_volume]
  exact periodQuotient_volume_pullback coordinate hcoordinate P x

end PeriodQuotient

attribute [local instance] HolomorphicForms.RegularCover.coverChartedSpace
  HolomorphicForms.RegularCover.cover_isManifold

/-- Base-width scaling has the asserted coefficient on the actual base-first top covector. -/
theorem baseWidthLinear_volume_coefficient :
    coefficient (volume.compContinuousLinearMap baseWidthLinear) = (Triangle.width : ℂ) := by
  change volume (fun i => baseWidthLinear (basis i)) = _
  rw [volume_apply]
  have hm : Matrix.of (fun i => coordinateEquiv (baseWidthLinear (basis i))) =
      !![(Triangle.width : ℂ), 0, 0; 0, 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [basis, baseWidthLinear_apply, Pi.basisFun_apply]
  rw [hm]
  simp [Matrix.det_fin_three]

/-- Genuine pullback of the regular cover's standard three-volume by the comparison derivative. -/
theorem toRegularCover_volume_pullback (x : LogDomain) :
    volume.compContinuousLinearMap (mfderiv I₃ I₃ toRegularCover x) =
      (Triangle.width : ℂ) • volume := by
  rw [toRegularCover_mfderiv]
  exact (eq_coefficient_smul_volume _).trans
    (congrArg (fun c : ℂ => c • volume) baseWidthLinear_volume_coefficient)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback
