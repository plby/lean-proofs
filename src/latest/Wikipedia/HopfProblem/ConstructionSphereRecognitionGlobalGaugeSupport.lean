import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeSupportBase
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyLocalizedBoundary
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticGeometry

/-!
# Closed support for the native elliptic cap isotopies

The original inverse elliptic chart sends a closed coordinate disc to a
compact subset strictly inside the selected filling patch.  Its full
inverse image under the actual proper threefold projection is a compact,
closed support.  On the native cap this is exactly the original squared
root-radius bound.  Every localized collar slice, and its literal inverse,
is the identity outside this one support, independently of phase and time.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge

open Elliptic SpecialPeriods SpecialPeriods.EllipticFilling SpecialPeriods.Threefold
open TrianglePeriodFamily.Boundary GaugeIsotopy

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace

/-- The actual outer root radius already used in the supported cap isotopy. -/
def ellipticSupportRadius (j : Kind) : ℝ :=
  largerRadius (nativeBoundaryRootRadius j)

theorem ellipticSupportRadius_pos (j : Kind) : 0 < ellipticSupportRadius j :=
  largerRadius_pos (nativeBoundaryRootRadius j)

/-- Its quotient-coordinate radius is strictly inside the original selected base disc. -/
theorem ellipticSupportRadius_pow_lt (j : Kind) :
    ellipticSupportRadius j ^ j.order < specialBaseCover.radius (some j) :=
  nativeLocalizedCollar_outer_radius j

/-- The closed disc uses the original inverse elliptic quotient coordinate. -/
def ellipticBaseSupport (j : Kind) : Set TriangleCompactifiedOrbitSpace :=
  coordinateClosedSupport specialBaseCover (some j) (ellipticSupportRadius j ^ j.order)

theorem ellipticBaseSupport_isCompact (j : Kind) : IsCompact (ellipticBaseSupport j) :=
  coordinateClosedSupport_isCompact specialBaseCover (some j)
    (ellipticSupportRadius j ^ j.order) (ellipticSupportRadius_pow_lt j)

theorem ellipticBaseSupport_isClosed (j : Kind) : IsClosed (ellipticBaseSupport j) :=
  (ellipticBaseSupport_isCompact j).isClosed

theorem ellipticBaseSupport_subset_fillingPatch (j : Kind) :
    ellipticBaseSupport j ⊆
      (specialBaseCover.fillingPatch (some j) : Set TriangleCompactifiedOrbitSpace) :=
  coordinateClosedSupport_subset_fillingPatch specialBaseCover (some j)
    (ellipticSupportRadius j ^ j.order) (ellipticSupportRadius_pow_lt j)

/-- The support is a full base preimage in the unchanged global threefold. -/
def ellipticSupport (j : Kind) : Set Threefold.Space :=
  Threefold.projection ⁻¹' ellipticBaseSupport j

/-- Properness of the actual projection makes this support compact. -/
theorem ellipticSupport_isCompact (j : Kind) : IsCompact (ellipticSupport j) :=
  Threefold.projection_proper.isCompact_preimage (ellipticBaseSupport_isCompact j)

theorem ellipticSupport_isClosed (j : Kind) : IsClosed (ellipticSupport j) :=
  (ellipticBaseSupport_isClosed j).preimage Threefold.projection_continuous

/-- The closed support stays inside the original full elliptic gluing patch. -/
theorem ellipticSupport_subset_patch (j : Kind) :
    ellipticSupport j ⊆ (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) := by
  intro y hy
  change Threefold.projection y ∈ specialBaseCover.fillingPatch (some j)
  exact ellipticBaseSupport_subset_fillingPatch j hy

/-- Global membership retains both the original chart source and its literal coordinate bound. -/
theorem ellipticSupport_mem_iff (j : Kind) (y : Threefold.Space) :
    y ∈ ellipticSupport j ↔
      Threefold.projection y ∈ (punctureChart (some j)).source ∧
        ‖EllipticGeometry.ellipticCoordinate j y‖ ≤ ellipticSupportRadius j ^ j.order :=
  mem_coordinateClosedSupport specialBaseCover (some j)
    (ellipticSupportRadius j ^ j.order) (ellipticSupportRadius_pow_lt j)
    (Threefold.projection y)

/-- On the actual included cap, support membership is the native filling-parameter bound. -/
theorem ellipticSupport_inclusion_iff_parameter (j : Kind) (y : SpecialEllipticPiece j) :
    EllipticGeometry.inclusion j y ∈ ellipticSupport j ↔
      ‖EllipticGeometry.parameter j y‖ ≤ ellipticSupportRadius j ^ j.order := by
  rw [ellipticSupport_mem_iff, EllipticGeometry.ellipticCoordinate_inclusion]
  exact and_iff_right (EllipticGeometry.projection_inclusion_mem_chart j y)

/-- The unchanged quotient parameter and the unchanged squared root radius give the same bound. -/
theorem parameter_norm_le_supportRadius_pow_iff (j : Kind) (y : SpecialEllipticPiece j) :
    ‖EllipticGeometry.parameter j y‖ ≤ ellipticSupportRadius j ^ j.order ↔
      smallRootSquared j y ≤ ellipticSupportRadius j ^ 2 := by
  change ‖(specialFullFillingProjection j y.val : ℂ)‖ ≤
      ellipticSupportRadius j ^ j.order ↔
    ‖((EllipticFullProduct.specialFillingProductHomeomorph j y.val).1 : ℂ)‖ ^ 2 ≤
      ellipticSupportRadius j ^ 2
  rw [← EllipticSmallProduct.fullProduct_norm_pow j y.val]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (ellipticSupportRadius_pos j).le
    (Nat.ne_of_gt j.order_pos)).trans
      (sq_le_sq₀ (norm_nonneg _) (ellipticSupportRadius_pos j).le).symm

/-- Exact membership in the global support, in the original small-cap radius. -/
theorem ellipticSupport_inclusion_iff (j : Kind) (y : SpecialEllipticPiece j) :
    EllipticGeometry.inclusion j y ∈ ellipticSupport j ↔
      smallRootSquared j y ≤ ellipticSupportRadius j ^ 2 :=
  (ellipticSupport_inclusion_iff_parameter j y).trans
    (parameter_norm_le_supportRadius_pow_iff j y)

/-- Original quotient representatives have exactly the declared root-radius support. -/
theorem ellipticSupport_inclusion_smallQuotient_iff (j : Kind)
    (z : EllipticSmallProduct.RootBall j) (x : RealTorus₄) :
    EllipticGeometry.inclusion j (EllipticSmallProduct.smallQuotient j z x) ∈
        ellipticSupport j ↔ ‖((z : Disc) : ℂ)‖ ≤ ellipticSupportRadius j := by
  rw [ellipticSupport_inclusion_iff]
  change capRootSquared (specialLocalData j)
      ((specialLocalData j).quotient j.twist (mainTwist_admissible j) (z.val, x)) ≤
        ellipticSupportRadius j ^ 2 ↔ _
  rw [capRootSquared_quotient]
  exact sq_le_sq₀ (norm_nonneg _) (ellipticSupportRadius_pos j).le

/-- Every actual collar slice fixes all cap points outside this global closed support. -/
theorem nativeLocalizedCollar_eq_self_of_not_mem_support (j : Kind) (τ s : ℝ)
    (y : SpecialEllipticPiece j)
    (hy : EllipticGeometry.inclusion j y ∉ ellipticSupport j) :
    nativeLocalizedCollarDiffeomorph j τ s y = y := by
  apply nativeLocalizedCollar_eq_self_outer j τ s y
  exact (lt_of_not_ge (fun h => hy ((ellipticSupport_inclusion_iff j y).mpr h))).le

/-- The explicit inverse has the same support, for all phases and all real times. -/
theorem nativeLocalizedCollar_symm_eq_self_of_not_mem_support (j : Kind) (τ s : ℝ)
    (y : SpecialEllipticPiece j)
    (hy : EllipticGeometry.inclusion j y ∉ ellipticSupport j) :
    (nativeLocalizedCollarDiffeomorph j τ s).symm y = y :=
  nativeLocalizedCollar_eq_self_of_not_mem_support j τ (-s) y hy

theorem nativeLocalizedCollar_ne_self_mem_support (j : Kind) (τ s : ℝ)
    (y : SpecialEllipticPiece j) (hy : nativeLocalizedCollarDiffeomorph j τ s y ≠ y) :
    EllipticGeometry.inclusion j y ∈ ellipticSupport j := by
  by_contra h
  exact hy (nativeLocalizedCollar_eq_self_of_not_mem_support j τ s y h)

/-- Outside the closed support, a whole original global neighborhood misses it. -/
theorem ellipticSupport_compl_mem_nhds (j : Kind) {y : Threefold.Space}
    (hy : y ∉ ellipticSupport j) : (ellipticSupport j)ᶜ ∈ 𝓝 y :=
  (ellipticSupport_isClosed j).isOpen_compl.mem_nhds hy

/-- The same neighborhood is fixed by every cap slice wherever its points lie in the cap. -/
theorem nativeLocalizedCollar_eventually_eq_self_of_not_mem_support (j : Kind)
    {y : Threefold.Space} (hy : y ∉ ellipticSupport j) :
    ∀ᶠ y' in 𝓝 y, ∀ (τ s : ℝ) (x : SpecialEllipticPiece j),
      EllipticGeometry.inclusion j x = y' → nativeLocalizedCollarDiffeomorph j τ s x = x := by
  filter_upwards [ellipticSupport_compl_mem_nhds j hy] with y' hy' τ s x hx
  apply nativeLocalizedCollar_eq_self_of_not_mem_support j τ s x
  rwa [hx]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge
