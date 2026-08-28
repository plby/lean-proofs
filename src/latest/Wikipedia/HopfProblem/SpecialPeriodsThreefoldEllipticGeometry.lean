import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Wikipedia.HopfProblem.EllipticEquivariantCentralSpecial

/-!
# The genuine elliptic neighborhoods in the constructed threefold

The two small elliptic pieces carry the open-submanifold atlases of the
actual varying-period fillings. Their full patch identifications are
biholomorphic for these unchanged atlases. In the original quotient
coordinate on the sphere base, the global projection agrees exactly
with the original filling parameter, including on the central surface.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open EllipticFilling Triangle

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The original small elliptic piece, as an open subset of the actual
full equivariant filling. -/
abbrev LocalSpace (j : Elliptic.Kind) := SpecialEllipticPiece j

attribute [local instance] specialEllipticPieceChartedSpace
  specialFullFillingChartedSpace Threefold.chartedSpace triangleCompactifiedChartedSpace

theorem native_isManifold (j : Elliptic.Kind) : IsManifold IF ω (LocalSpace j) :=
  specialEllipticPiece_isManifold j

/-- The unchanged disc coordinate on the actual filling piece. -/
def parameter (j : Elliptic.Kind) (x : LocalSpace j) : ℂ :=
  specialFullFillingProjection j x.val

theorem parameter_continuous (j : Elliptic.Kind) : Continuous (parameter j) := by
  change Continuous ((Subtype.val : coordinateBall (specialBaseCover.radius (some j)) → ℂ) ∘
    pieceCoordinate specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j)
  exact continuous_subtype_val.comp
    (pieceCoordinate_continuous specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j)

theorem parameter_holomorphic (j : Elliptic.Kind) :
    ContMDiff IF 𝓘(ℂ) ω (parameter j) := by
  change ContMDiff IF 𝓘(ℂ) ω
    ((Subtype.val : coordinateBall (specialBaseCover.radius (some j)) → ℂ) ∘
      pieceCoordinate specialPeriodMap specialPeriodMap_generator₁
        specialPeriodMap_generator₂ specialBaseCover j)
  exact contMDiff_subtype_val.comp
    (pieceCoordinate_holomorphic specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j)

theorem parameter_mem_ball (j : Elliptic.Kind) (x : LocalSpace j) :
    parameter j x ∈ Metric.ball 0 (specialBaseCover.radius (some j)) := by
  rw [Metric.mem_ball, dist_zero_right]
  exact x.property

/-- The actual inclusion of the entire small elliptic piece into the
glued manifold. -/
def inclusion (j : Elliptic.Kind) : LocalSpace j → Threefold.Space :=
  Threefold.inclusion (some (some j))

theorem inclusion_openEmbedding (j : Elliptic.Kind) : IsOpenEmbedding (inclusion j) :=
  Threefold.inclusion_openEmbedding (some (some j))

theorem inclusion_injective (j : Elliptic.Kind) : Injective (inclusion j) :=
  (inclusion_openEmbedding j).injective

theorem inclusion_continuous (j : Elliptic.Kind) : Continuous (inclusion j) :=
  (inclusion_openEmbedding j).continuous

theorem inclusion_range (j : Elliptic.Kind) :
    range (inclusion j) = Threefold.projection ⁻¹'
      (specialBaseCover.fillingPatch (some j) : Set TriangleCompactifiedOrbitSpace) :=
  Threefold.inclusion_range (some (some j))

/-- The original elliptic atlas identifies analytically with the full
inverse image of its chosen base patch. No replacement atlas is used. -/
def nativePatchBiholomorph (j : Elliptic.Kind) :
    Diffeomorph IF IF (LocalSpace j) (Threefold.liftedPatch (some (some j))) ω :=
  Threefold.patchBiholomorph (some (some j))

@[simp] theorem nativePatchBiholomorph_val (j : Elliptic.Kind) (x : LocalSpace j) :
    (nativePatchBiholomorph j x : Threefold.Space) = inclusion j x := rfl

theorem liftedPatch_nonempty (j : Elliptic.Kind) :
    Nonempty (Threefold.liftedPatch (some (some j))) :=
  (specialEllipticPiece_nonempty j).map (nativePatchBiholomorph j)

/-- The native parametrization into the whole glued ambient manifold. -/
def nativeParametrization (j : Elliptic.Kind) :
    PartialDiffeomorph IF IF (LocalSpace j) Threefold.Space ω :=
  (nativePatchBiholomorph j).toPartialDiffeomorph.trans
    (opensInclusionPartialDiffeomorph IF (Threefold.liftedPatch (some (some j)))
      (liftedPatch_nonempty j))

@[simp] theorem nativeParametrization_source (j : Elliptic.Kind) :
    (nativeParametrization j).source = univ := by
  simp [nativeParametrization, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph,
    opensInclusionPartialDiffeomorph]

@[simp] theorem nativeParametrization_target (j : Elliptic.Kind) :
    (nativeParametrization j).target =
      (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) := by
  simp [nativeParametrization, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph,
    opensInclusionPartialDiffeomorph]

@[simp] theorem nativeParametrization_apply (j : Elliptic.Kind) (x : LocalSpace j) :
    nativeParametrization j x = inclusion j x := rfl

theorem inclusion_isLocalDiffeomorph (j : Elliptic.Kind) :
    IsLocalDiffeomorph IF IF ω (inclusion j) := by
  intro x
  apply (nativeParametrization j).isLocalDiffeomorphAt _ _ _
  rw [nativeParametrization_source]
  trivial

theorem inclusion_holomorphic (j : Elliptic.Kind) :
    ContMDiff IF IF ω (inclusion j) :=
  (inclusion_isLocalDiffeomorph j).contMDiff

@[simp] theorem projection_inclusion (j : Elliptic.Kind) (x : LocalSpace j) :
    Threefold.projection (inclusion j x) = specialEllipticPieceProjectionToBase j x :=
  Threefold.projection_inclusion (some (some j)) x

theorem projection_inclusion_eq_point_iff (j : Elliptic.Kind) (x : LocalSpace j) :
    Threefold.projection (inclusion j x) = puncturePoint (some j) ↔ parameter j x = 0 := by
  rw [projection_inclusion]
  exact specialBaseCover.fillingEmbedding_eq_point_iff (some j)
    (pieceCoordinate specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j x)

/-- The two normalized values of the actual sphere projection. -/
def sphereValue (j : Elliptic.Kind) : RiemannSphere :=
  triangleSphereUniformization (puncturePoint (some j))

@[simp] theorem sphereValue_three : sphereValue .three = ((0 : ℂ) : RiemannSphere) :=
  triangleSphereUniformization_centerOne

@[simp] theorem sphereValue_four : sphereValue .four = ((1 : ℂ) : RiemannSphere) :=
  triangleSphereUniformization_centerTwo

/-- The actual elliptic sphere fibre is exactly the central filling
fibre on every representative of the entire original piece. -/
theorem projectionSphere_inclusion_eq_value_iff (j : Elliptic.Kind) (x : LocalSpace j) :
    Threefold.projectionSphere (inclusion j x) = sphereValue j ↔ parameter j x = 0 :=
  triangleSphereUniformization.injective.eq_iff.trans
    (projection_inclusion_eq_point_iff j x)

/-- The original filled elliptic coordinate of the global base map. -/
def ellipticCoordinate (j : Elliptic.Kind) : Threefold.Space → ℂ :=
  punctureChart (some j) ∘ Threefold.projection

@[simp] theorem ellipticCoordinate_inclusion (j : Elliptic.Kind) (x : LocalSpace j) :
    ellipticCoordinate j (inclusion j x) = parameter j x := by
  change punctureChart (some j) (Threefold.projection (inclusion j x)) = parameter j x
  rw [projection_inclusion]
  exact specialBaseCover.punctureChart_fillingEmbedding (some j)
    (pieceCoordinate specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j x)

/-- The genuine elliptic quotient chart on the normalized sphere. -/
def sphereChart (j : Elliptic.Kind) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) RiemannSphere ℂ ω :=
  triangleSphereUniformization.symm.toPartialDiffeomorph.trans (puncturePartial (some j))

@[simp] theorem sphereChart_projectionSphere (j : Elliptic.Kind) (y : Threefold.Space) :
    sphereChart j (Threefold.projectionSphere y) = ellipticCoordinate j y := by
  change punctureChart (some j)
    (triangleSphereUniformization.symm (triangleSphereUniformization (Threefold.projection y))) = _
  rw [Diffeomorph.symm_apply_apply]
  rfl

@[simp] theorem sphereChart_value (j : Elliptic.Kind) :
    sphereChart j (sphereValue j) = 0 := by
  change punctureChart (some j)
    (triangleSphereUniformization.symm
      (triangleSphereUniformization (puncturePoint (some j)))) = 0
  rw [Diffeomorph.symm_apply_apply]
  exact punctureChart_point (some j)

theorem projection_inclusion_mem_chart (j : Elliptic.Kind) (x : LocalSpace j) :
    Threefold.projection (inclusion j x) ∈ (punctureChart (some j)).source := by
  rw [projection_inclusion]
  exact specialBaseCover.fillingPatch_subset_chart (some j)
    (specialEllipticPieceProjection j x).property

theorem projectionSphere_inclusion_mem_sphereChart_source (j : Elliptic.Kind)
    (x : LocalSpace j) :
    Threefold.projectionSphere (inclusion j x) ∈ (sphereChart j).source := by
  change Threefold.projectionSphere (inclusion j x) ∈ univ ∧
    triangleSphereUniformization.symm (triangleSphereUniformization
      (Threefold.projection (inclusion j x))) ∈ (punctureChart (some j)).source
  rw [Diffeomorph.symm_apply_apply]
  exact ⟨mem_univ _, projection_inclusion_mem_chart j x⟩

theorem sphereChart_isLocalDiffeomorphAt_inclusion (j : Elliptic.Kind) (x : LocalSpace j) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (sphereChart j)
      (Threefold.projectionSphere (inclusion j x)) :=
  (sphereChart j).isLocalDiffeomorphAt _ _ _
    (projectionSphere_inclusion_mem_sphereChart_source j x)

@[simp] theorem sphereChart_projectionSphere_inclusion (j : Elliptic.Kind)
    (x : LocalSpace j) :
    sphereChart j (Threefold.projectionSphere (inclusion j x)) = parameter j x := by
  rw [sphereChart_projectionSphere, ellipticCoordinate_inclusion]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
