import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingBasic
import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingComparison

/-!
# The actual cusp gluing identifies the two genuine zero sections

All periods, radii, and overlap maps below are the unconditional ones
used to construct the threefold.  The identity on logarithmic vector
zero specializes to the native cusp map, survives the identity change
of model, and gives equality after the actual gluing inclusions.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching

open Triangle CuspFamily

attribute [local instance] triangleCompactifiedChartedSpace triangleRegularQuotientChartedSpace
  specialRegularFamilyChartedSpace specialCuspPieceChartedSpace

/-- The actual chosen radius lies in the original full cusp chart. -/
theorem radius_le_cuspChart : radius ≤ cuspRadius width :=
  specialBaseCover_cusp_radius_bounds.2.2.le

/-- The two actual period families agree on their original logarithmic base. -/
theorem period_agreement (s : LogBase radius) :
    regularData.periods.point (logBaseToRegular radius radius_le_cuspChart s) =
      data.periods.point s :=
  CuspGlobalOverlap.spherePeriod_agreement triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo radius (specialBaseCover.radius_pos none)
    specialCuspRadius_le radius_le_cuspChart s

theorem regularZeroSection_projection_eq (x : SpecialRegularFamily) :
    regularZeroSection (specialRegularFamilyProjection x) =
      regularData.zeroSection (regularData.projection x) := by
  change regularData.zeroSection
    (regularBiholomorph.symm (regularBiholomorph (regularData.projection x))) = _
  exact congrArg regularData.zeroSection
    (regularBiholomorph.symm_apply_apply (regularData.projection x))

/-- The actual common-model overlap preserves the genuine zero section
at every nonzero point of the chosen cusp disc. -/
theorem overlap_cuspZeroSection (t : Disc) (ht : (t : ℂ) ≠ 0) :
    specialCuspOverlap (cuspZeroSection t) = regularZeroSection (regularBase t ht) := by
  have hzero := CuspGlobalOverlap.cuspToRegularPartial_zeroSection
    data regularData radius_le_cuspChart period_agreement t ht
  change specialCuspOverlap (cuspZeroSection t) =
    regularData.zeroSection (regularData.projection
      (specialCuspOverlap (cuspZeroSection t))) at hzero
  calc
    specialCuspOverlap (cuspZeroSection t) =
        regularData.zeroSection (regularData.projection
          (specialCuspOverlap (cuspZeroSection t))) := hzero
    _ = regularZeroSection
        (specialRegularFamilyProjection (specialCuspOverlap (cuspZeroSection t))) :=
      (regularZeroSection_projection_eq _).symm
    _ = regularZeroSection (regularBase t ht) :=
      congrArg regularZeroSection (overlap_cuspZeroSection_projection t ht)

/-- The same equality for the native cusp coordinate model. -/
theorem nativeOverlap_cuspZeroSection (t : Disc) (ht : (t : ℂ) ≠ 0) :
    specialCuspNativeOverlap (cuspZeroSection t) = regularZeroSection (regularBase t ht) :=
  overlap_cuspZeroSection t ht

/-- The inverse actual overlap sends regular vector zero to the toric section. -/
theorem overlap_symm_regularZeroSection (t : Disc) (ht : (t : ℂ) ≠ 0) :
    specialCuspOverlap.symm (regularZeroSection (regularBase t ht)) = cuspZeroSection t := by
  rw [← overlap_cuspZeroSection t ht]
  exact specialCuspOverlap.left_inv (cuspZeroSection_mem_overlap t ht)

/-- The two sections represent literally the same point of the actual glued space. -/
theorem inclusion_cuspZeroSection (t : Disc) (ht : (t : ℂ) ≠ 0) :
    inclusion (some none) (cuspZeroSection t) =
      inclusion none (regularZeroSection (regularBase t ht)) := by
  apply (gluingData.inclusion_eq_iff (some none) none _ _).mpr
  exact ⟨cuspZeroSection_mem_overlap t ht, overlap_cuspZeroSection t ht⟩

theorem overlap_regularZeroSection_inverse (b : OverlapBase) :
    specialCuspOverlap.symm (regularZeroSection b.val) =
      cuspZeroSection (overlapCoordinate b) := by
  simpa only [regularBase_overlapCoordinate] using
    overlap_symm_regularZeroSection (overlapCoordinate b) (overlapCoordinate_ne_zero b)

/-- The toric section extended across the central fibre in the actual threefold. -/
def extendedSection : Disc → Space := inclusion (some none) ∘ cuspZeroSection

theorem extendedSection_continuous : Continuous extendedSection :=
  (inclusion_openEmbedding (some none)).continuous.comp cuspZeroSection_continuous

/-- The actual regular zero section included in the constructed total space. -/
def regularSection : regularPatch → Space := inclusion none ∘ regularZeroSection

theorem regularSection_continuous : Continuous regularSection :=
  (inclusion_openEmbedding none).continuous.comp regularZeroSection_continuous

/-- Restriction of that regular section to the full actual cusp overlap. -/
def attachedRegularSection : OverlapBase → Space := regularSection ∘ Subtype.val

theorem attachedRegularSection_continuous : Continuous attachedRegularSection :=
  regularSection_continuous.comp continuous_subtype_val

/-- The actual regular section on the overlap is the restriction of the
genuine section extending over the full cusp disc. -/
theorem attachedRegularSection_eq_extended (b : OverlapBase) :
    attachedRegularSection b = extendedSection (overlapCoordinate b) := by
  have h := inclusion_cuspZeroSection (overlapCoordinate b) (overlapCoordinate_ne_zero b)
  rw [regularBase_overlapCoordinate] at h
  exact h.symm

theorem extendedSection_mem_cuspPatch (t : Disc) :
    extendedSection t ∈ liftedPatch (some none) := by
  change extendedSection t ∈ projection ⁻¹'
    (specialBaseCover.patch (some none) : Set TriangleCompactifiedOrbitSpace)
  rw [← inclusion_range (some none)]
  exact mem_range_self (cuspZeroSection t)

theorem extendedSection_projection (t : Disc) :
    projection (extendedSection t) = specialBaseCover.fillingEmbedding none t := by
  exact (gluingData.projection_inclusion (some none) (cuspZeroSection t)).trans
    (cuspZeroSection_projection t)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching
