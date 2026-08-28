import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetectionDensityCusp
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetectionDensityElliptic

/-!
# Density of the actual regular locus in the glued threefold

The noncentral points are dense in the original full cusp quotient and
in each original small elliptic filling. Their inclusions take precisely
these points into the actual regular locus. Continuity of the genuine
piece inclusions and their joint surjectivity prove density in the
actual glued topology, with no global density assumption.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

namespace HolomorphicForms.DetectionDensity

/-- Each original elliptic parameter detects exactly the overlap with
the actual regular base patch. -/
theorem elliptic_inclusion_mem_regular_iff (j : Elliptic.Kind)
    (x : EllipticGeometry.LocalSpace j) :
    EllipticGeometry.inclusion j x ∈ regularLocus ↔ EllipticGeometry.parameter j x ≠ 0 := by
  rw [mem_regularLocus, EllipticGeometry.projection_inclusion]
  exact EllipticFilling.pieceProjectionToBase_mem_regular_iff
    specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂ specialBaseCover j x

theorem elliptic_regular_preimage_dense (j : Elliptic.Kind) :
    Dense (EllipticGeometry.inclusion j ⁻¹' (regularLocus : Set Space)) := by
  have he : EllipticGeometry.inclusion j ⁻¹' (regularLocus : Set Space) =
      {x : EllipticGeometry.LocalSpace j | EllipticGeometry.parameter j x ≠ 0} :=
    Set.ext (elliptic_inclusion_mem_regular_iff j)
  rw [he]
  exact elliptic_parameter_ne_zero_dense j

/-- The regular locus is dense on every member of the actual four-piece cover. -/
theorem local_regular_preimage_dense (i : Index) :
    Dense (inclusion i ⁻¹' (regularLocus : Set Space)) := by
  cases i with
  | none =>
      have he : inclusion none ⁻¹' (regularLocus : Set Space) = univ := by
        apply Set.eq_univ_of_forall
        intro x
        change projection (inclusion none x) ∈ regularPatch
        rw [projection_inclusion]
        exact localProjectionToBase_mem none x
      rw [he]
      exact dense_univ
  | some i =>
      cases i with
      | none => exact cusp_regular_preimage_dense
      | some j => exact elliptic_regular_preimage_dense j

end HolomorphicForms.DetectionDensity

/-- The full regular locus is dense in the genuine glued threefold.
This includes approximation of every cusp and elliptic central-fibre point. -/
theorem regularLocus_dense : Dense (regularLocus : Set Space) := by
  intro y
  obtain ⟨i, x, rfl⟩ := gluingData.inclusion_jointly_surjective y
  have hx := HolomorphicForms.DetectionDensity.local_regular_preimage_dense i x
  have him := mem_closure_image ((inclusion_openEmbedding i).continuous.continuousAt) hx
  exact closure_mono (Set.image_preimage_subset (inclusion i) (regularLocus : Set Space)) him

/-- The original regular-family inclusion has dense range in the actual threefold. -/
theorem regularFamilyInclusion_denseRange : DenseRange regularFamilyInclusion := by
  change Dense (range regularFamilyInclusion)
  rw [range_regularFamilyInclusion]
  exact regularLocus_dense

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
