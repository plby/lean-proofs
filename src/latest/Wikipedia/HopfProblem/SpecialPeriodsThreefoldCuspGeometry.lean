import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Wikipedia.HopfProblem.CuspStrata

/-!
# The genuine cusp neighborhood inside the glued threefold

The full constructed cusp quotient is identified with the full inverse
image of the chosen compact-base cusp patch.  Its original three-coordinate
complex atlas agrees analytically with the actual glued atlas, through
the proved identity model change and full patch biholomorphism.  The cusp
coordinate of the global sphere projection is exactly the original toric
quotient parameter, including on its central fibre.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry

open ToricCharts Triangle

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual global cusp correction restricted to the already chosen
positive filling radius. -/
abbrev data : CuspFamily.Data :=
  CuspPiece.restrictedData specialCuspData specialBaseCover specialCuspRadius_le

/-- The full original cusp quotient, not an abstract local model. -/
abbrev LocalSpace := SpecialCuspPiece

/-- The native three-coordinate quotient atlas of the actual cusp piece. -/
@[instance_reducible] def nativeChartedSpace : ChartedSpace (CoordinateSpace 3) LocalSpace :=
  CuspPiece.nativeChartedSpace specialCuspData specialBaseCover specialCuspRadius_le

attribute [local instance] nativeChartedSpace Threefold.chartedSpace
  specialCuspPieceChartedSpace triangleCompactifiedChartedSpace

theorem native_isManifold : IsManifold I₃ ω LocalSpace :=
  CuspPiece.native_isManifold specialCuspData specialBaseCover specialCuspRadius_le

/-- The original, unmodified toric parameter on the full cusp quotient. -/
def parameter : LocalSpace → ℂ := CuspQuotient.projection data.correction data.radius

theorem parameter_continuous : Continuous parameter :=
  CuspQuotient.projection_continuous data.correction data.radius

theorem parameter_holomorphic : ContMDiff I₃ 𝓘(ℂ) ω parameter :=
  CuspQuotient.projection_holomorphic data.correction data.radius data.radius_pos
    data.radius_lt_one data.holomorphic data.smallDrift

theorem parameter_mem_ball (x : LocalSpace) : parameter x ∈ Metric.ball 0 data.radius :=
  CuspQuotient.projection_mem_disc data.correction data.radius x

/-- The actual inclusion of the full cusp piece into the glued manifold. -/
def inclusion : LocalSpace → Threefold.Space := Threefold.inclusion (some none)

theorem inclusion_openEmbedding : IsOpenEmbedding inclusion :=
  Threefold.inclusion_openEmbedding (some none)

theorem inclusion_injective : Injective inclusion := inclusion_openEmbedding.injective

theorem inclusion_continuous : Continuous inclusion := inclusion_openEmbedding.continuous

theorem inclusion_range : range inclusion = Threefold.projection ⁻¹'
    (specialBaseCover.fillingPatch none : Set TriangleCompactifiedOrbitSpace) :=
  Threefold.inclusion_range (some none)

/-- The full patch biholomorphism starts with the original cusp atlas;
the model reindexing is the already proved identity biholomorphism. -/
def nativePatchBiholomorph :
    Diffeomorph I₃ IF LocalSpace (Threefold.liftedPatch (some none)) ω :=
  (CuspPiece.nativeToCommon specialCuspData specialBaseCover specialCuspRadius_le).trans
    (Threefold.patchBiholomorph (some none))

@[simp] theorem nativePatchBiholomorph_val (x : LocalSpace) :
    (nativePatchBiholomorph x : Threefold.Space) = inclusion x := rfl

theorem liftedPatch_nonempty : Nonempty (Threefold.liftedPatch (some none)) :=
  specialCuspPiece_nonempty.map nativePatchBiholomorph

/-- The actual ambient cusp parametrization, with its full source and
full global cusp-patch target, for the unchanged native and glued atlases. -/
def nativeParametrization : PartialDiffeomorph I₃ IF LocalSpace Threefold.Space ω :=
  nativePatchBiholomorph.toPartialDiffeomorph.trans
    (opensInclusionPartialDiffeomorph IF (Threefold.liftedPatch (some none))
      liftedPatch_nonempty)

@[simp] theorem nativeParametrization_source : nativeParametrization.source = univ := by
  simp [nativeParametrization, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph,
    opensInclusionPartialDiffeomorph]

@[simp] theorem nativeParametrization_target :
    nativeParametrization.target = (Threefold.liftedPatch (some none) : Set Threefold.Space) := by
  simp [nativeParametrization, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph,
    opensInclusionPartialDiffeomorph]

@[simp] theorem nativeParametrization_apply (x : LocalSpace) :
    nativeParametrization x = inclusion x := rfl

theorem inclusion_isLocalDiffeomorph : IsLocalDiffeomorph I₃ IF ω inclusion := by
  intro x
  apply nativeParametrization.isLocalDiffeomorphAt _ _ _
  rw [nativeParametrization_source]
  trivial

/-- Native cusp holomorphy holds into the actual glued complex manifold,
not only for the reindexed common-model cusp atlas. -/
theorem inclusion_holomorphic : ContMDiff I₃ IF ω inclusion :=
  inclusion_isLocalDiffeomorph.contMDiff

@[simp] theorem projection_inclusion (x : LocalSpace) :
    Threefold.projection (inclusion x) = specialCuspPieceProjectionToBase x :=
  Threefold.projection_inclusion (some none) x

theorem projection_inclusion_eq_cusp_iff (x : LocalSpace) :
    Threefold.projection (inclusion x) = triangleCuspPoint ↔ parameter x = 0 := by
  rw [projection_inclusion]
  exact CuspPiece.projectionToBase_eq_cusp_iff specialCuspData specialBaseCover x

/-- The literal sphere fibre at infinity is exactly the central cusp
fibre on every actual cusp representative. -/
theorem projectionSphere_inclusion_eq_infty_iff (x : LocalSpace) :
    Threefold.projectionSphere (inclusion x) = (∞ : RiemannSphere) ↔ parameter x = 0 := by
  change triangleSphereUniformization (Threefold.projection (inclusion x)) =
    (∞ : RiemannSphere) ↔ _
  rw [← triangleSphereUniformization_cusp]
  exact triangleSphereUniformization.injective.eq_iff.trans (projection_inclusion_eq_cusp_iff x)

/-- The actual filled cusp coordinate of the global compact-base map. -/
def cuspCoordinate : Threefold.Space → ℂ :=
  cuspFullChart width le_rfl ∘ Threefold.projection

@[simp] theorem cuspCoordinate_inclusion (x : LocalSpace) :
    cuspCoordinate (inclusion x) = parameter x := by
  change punctureChart none (Threefold.projection (inclusion x)) = parameter x
  rw [projection_inclusion]
  exact specialBaseCover.punctureChart_fillingEmbedding none
    (CuspPiece.coordinate specialCuspData specialBaseCover x)

/-- The genuine sphere chart obtained from the original compactified
cusp chart by the constructed global sphere biholomorphism. -/
def sphereChart : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) RiemannSphere ℂ ω :=
  triangleSphereUniformization.symm.toPartialDiffeomorph.trans (puncturePartial none)

@[simp] theorem sphereChart_projectionSphere (y : Threefold.Space) :
    sphereChart (Threefold.projectionSphere y) = cuspCoordinate y := by
  change punctureChart none
    (triangleSphereUniformization.symm (triangleSphereUniformization (Threefold.projection y))) = _
  rw [Diffeomorph.symm_apply_apply]
  rfl

@[simp] theorem sphereChart_infty : sphereChart (∞ : RiemannSphere) = 0 := by
  rw [← triangleSphereUniformization_cusp]
  change punctureChart none
    (triangleSphereUniformization.symm (triangleSphereUniformization triangleCuspPoint)) = 0
  rw [Diffeomorph.symm_apply_apply]
  exact punctureChart_point none

theorem projection_inclusion_mem_chart (x : LocalSpace) :
    Threefold.projection (inclusion x) ∈ (punctureChart none).source := by
  rw [projection_inclusion]
  exact specialBaseCover.fillingPatch_subset_chart none (specialCuspPieceProjection x).property

theorem projectionSphere_inclusion_mem_sphereChart_source (x : LocalSpace) :
    Threefold.projectionSphere (inclusion x) ∈ sphereChart.source := by
  change Threefold.projectionSphere (inclusion x) ∈ univ ∧
    triangleSphereUniformization.symm (triangleSphereUniformization
      (Threefold.projection (inclusion x))) ∈ (punctureChart none).source
  rw [Diffeomorph.symm_apply_apply]
  exact ⟨mem_univ _, projection_inclusion_mem_chart x⟩

/-- The sphere chart is locally biholomorphic at every base point of
the full actual cusp piece. -/
theorem sphereChart_isLocalDiffeomorphAt_inclusion (x : LocalSpace) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω sphereChart
      (Threefold.projectionSphere (inclusion x)) :=
  sphereChart.isLocalDiffeomorphAt _ _ _
    (projectionSphere_inclusion_mem_sphereChart_source x)

@[simp] theorem sphereChart_projectionSphere_inclusion (x : LocalSpace) :
    sphereChart (Threefold.projectionSphere (inclusion x)) = parameter x := by
  rw [sphereChart_projectionSphere, cuspCoordinate_inclusion]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry
