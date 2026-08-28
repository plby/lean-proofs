import Wikipedia.HopfProblem.SpecialPeriodsThreefold
import Wikipedia.HopfProblem.CuspSectionHomotopy

/-!
# The actual sections and base maps on the cusp attaching region

The small cusp filling uses the already chosen radius and unchanged
correction matrix.  Its genuine toric section and the regular family's
zero section are kept as separate maps until the actual overlap is proved
to identify them.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching

open Triangle

attribute [local instance] triangleCompactifiedChartedSpace

/-- The actual common radius used in the cusp gluing. -/
abbrev radius : ℝ := specialBaseCover.radius none

/-- The full coordinate disc, including its central point. -/
abbrev Disc := CuspQuotient.disc radius

/-- The genuine cusp data at the actual common radius. -/
abbrev data : CuspFamily.Data :=
  specialCuspData.shrink radius (specialBaseCover.radius_pos none) specialCuspRadius_le

/-- The genuine unchanged regular family data. -/
abbrev regularData : TrianglePeriodFamily.Data ℂ TriangleRegularPoint :=
  regularFamilyData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The actual toric section through the smooth part of the central fibre. -/
def cuspZeroSection : Disc → SpecialCuspPiece :=
  CuspQuotient.zeroSection specialCuspData.correction radius

theorem cuspZeroSection_continuous : Continuous cuspZeroSection :=
  CuspQuotient.zeroSection_continuous specialCuspData.correction radius

/-- The actual zero section of the regular quotient family. -/
def regularZeroSection : regularPatch → SpecialRegularFamily :=
  regularFamilyZeroSection specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

theorem regularZeroSection_continuous : Continuous regularZeroSection :=
  regularFamilyZeroSection_continuous specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂

@[simp] theorem regularZeroSection_projection (b : regularPatch) :
    specialRegularFamilyProjection (regularZeroSection b) = b :=
  regularFamilyProjection_zeroSection specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ b

/-- The punctured cusp disc as a subset of the actual regular base. -/
def regularBase (t : Disc) (ht : (t : ℂ) ≠ 0) : regularPatch :=
  ⟨specialBaseCover.fillingEmbedding none t,
    (specialBaseCover.fillingEmbedding_mem_regular_iff none t).mpr ht⟩

@[simp] theorem regularBase_val (t : Disc) (ht : (t : ℂ) ≠ 0) :
    (regularBase t ht : TriangleCompactifiedOrbitSpace) =
      specialBaseCover.fillingEmbedding none t := rfl

theorem cuspZeroSection_projection (t : Disc) :
    specialCuspPieceProjectionToBase (cuspZeroSection t) =
      specialBaseCover.fillingEmbedding none t := by
  change (punctureChart none).symm
    (CuspQuotient.projection specialCuspData.correction radius
      (CuspQuotient.zeroSection specialCuspData.correction radius t)) = _
  rw [CuspQuotient.projection_zeroSection]
  rfl

theorem cuspZeroSection_mem_overlap (t : Disc) (ht : (t : ℂ) ≠ 0) :
    cuspZeroSection t ∈ specialCuspOverlap.source := by
  rw [specialCuspOverlap_source]
  change specialCuspPieceProjectionToBase (cuspZeroSection t) ∈ regularPatch
  rw [cuspZeroSection_projection]
  exact (regularBase t ht).property

theorem cuspZeroSection_mem_nativeOverlap (t : Disc) (ht : (t : ℂ) ≠ 0) :
    cuspZeroSection t ∈ specialCuspNativeOverlap.source := by
  rw [specialCuspNativeOverlap_source_iff]
  exact (CuspQuotient.projection_zeroSection specialCuspData.correction radius t) ▸ ht

/-- The overlap already has the correct exact base value on the toric section. -/
theorem overlap_cuspZeroSection_projection (t : Disc) (ht : (t : ℂ) ≠ 0) :
    specialRegularFamilyProjection (specialCuspOverlap (cuspZeroSection t)) =
      regularBase t ht := by
  apply Subtype.ext
  exact (specialCuspOverlap_base _ (cuspZeroSection_mem_overlap t ht)).trans
    (cuspZeroSection_projection t)

/-- Points in the regular base whose images lie in the actual cusp filling patch. -/
abbrev OverlapBase :=
  {b : regularPatch // (b : TriangleCompactifiedOrbitSpace) ∈
    specialBaseCover.fillingPatch none}

/-- The original cusp chart as a map from the full actual overlap to its disc. -/
def overlapCoordinate (b : OverlapBase) : Disc :=
  specialBaseCover.fillingChart none ⟨b.val, b.property⟩

theorem overlapCoordinate_continuous : Continuous overlapCoordinate :=
  (specialBaseCover.fillingChart none).continuous.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

theorem overlapCoordinate_ne_zero (b : OverlapBase) : (overlapCoordinate b : ℂ) ≠ 0 :=
  (specialBaseCover.fillingPatch_regular_iff_coordinate_ne_zero none b.property).mp b.val.property

@[simp] theorem regularBase_overlapCoordinate (b : OverlapBase) :
    regularBase (overlapCoordinate b) (overlapCoordinate_ne_zero b) = b.val := by
  apply Subtype.ext
  change ((specialBaseCover.fillingChart none).symm
    (specialBaseCover.fillingChart none ⟨b.val, b.property⟩)).val = b.val.val
  exact congrArg Subtype.val ((specialBaseCover.fillingChart none).symm_apply_apply
    ⟨b.val, b.property⟩)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching
