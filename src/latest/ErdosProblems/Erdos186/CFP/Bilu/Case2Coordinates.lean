/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.OrthogonalTransport
import ErdosProblems.Erdos186.CFP.Bilu.ProjectionVolumeCoarse

/-!
# Canonical coordinates for Bilu Section 8.3, Case 2

The separating vector in Case 2 is normal to a codimension-one subspace.
This file constructs the resulting orthogonal coordinate isometry, including
the ordinary-product measurable equivalence used by the Fubini estimates.
-/

namespace Erdos186.CFP.Bilu.Case2Coordinates

open MeasureTheory Set Module Submodule
open scoped ENNReal RealInnerProductSpace
open ProjectionVolumeCoarse VolumeSections

variable {n d : ℕ}

/-- The unit vector pointing in the direction of a nonzero normal. -/
noncomputable def unitNormal (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  ‖u‖⁻¹ • u

@[simp]
theorem norm_unitNormal {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) :
    ‖unitNormal u‖ = 1 := by
  simp [unitNormal, norm_smul, hu]

theorem unitNormal_ne_zero {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) :
    unitNormal u ≠ 0 := by
  intro h
  have := congrArg norm h
  simpa [norm_unitNormal hu] using this

/-- A nonzero vector in the orthogonal complement of a codimension-one
subspace spans that complement. -/
theorem span_unitNormal_eq_orthogonal
    {W : Submodule ℝ (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n)}
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0) :
    ℝ ∙ unitNormal u = Wᗮ := by
  have hle : ℝ ∙ unitNormal u ≤ Wᗮ :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (by
      exact (Wᗮ).smul_mem (‖u‖⁻¹) huW)
  have horthRank : finrank ℝ Wᗮ = 1 := by
    have hsum := W.finrank_add_finrank_orthogonal
    omega
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_singleton (unitNormal_ne_zero hu0), horthRank]

/-- Isometric parametrization of the one-dimensional normal space, oriented
so that the coordinate `1` is the unit vector in the direction of `u`. -/
noncomputable def normalLineEquiv
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0) :
    ℝ ≃ₗᵢ[ℝ] Wᗮ :=
  (LinearIsometryEquiv.toSpanUnitSingleton (unitNormal u)
    (norm_unitNormal hu0)).trans
      (LinearIsometryEquiv.ofEq _ _
        (span_unitNormal_eq_orthogonal hcodim huW hu0))

@[simp]
theorem normalLineEquiv_apply
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0) (t : ℝ) :
    ((normalLineEquiv W u hcodim huW hu0 t : Wᗮ) :
        EuclideanSpace ℝ (Fin n)) = t • unitNormal u := by
  rfl

/-- Orthogonal Case-2 coordinates.  The first coordinate is the projected
hyperplane `W`, and the second coordinate is the oriented normal line. -/
noncomputable def normalCoordinateEquiv
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0) :
    WithLp 2 (Base d × ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (LinearIsometryEquiv.withLpProdCongr 2 q
      (normalLineEquiv W u hcodim huW hu0)).trans
    W.orthogonalDecomposition.symm

@[simp]
theorem normalCoordinateEquiv_apply
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0)
    (x : Base d) (t : ℝ) :
    normalCoordinateEquiv W u q hcodim huW hu0 (WithLp.toLp 2 (x, t)) =
      (q x : EuclideanSpace ℝ (Fin n)) + t • unitNormal u := by
  simp [normalCoordinateEquiv, Submodule.coe_orthogonalDecomposition_symm]

/-- The same coordinate change as a measurable equivalence from the
ordinary product.  This is the representation used by `volume.prod volume`.
-/
noncomputable def normalCoordinateMeasurableEquiv
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0) :
    (Base d × ℝ) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
  (MeasurableEquiv.toLp 2 (Base d × ℝ)).trans
    (normalCoordinateEquiv W u q hcodim huW hu0).toMeasurableEquiv

/-- The linear-equivalence spelling of `normalCoordinateMeasurableEquiv`.
The ordinary product and its `L²` wrapper have the same underlying module.
-/
noncomputable def normalCoordinateLinearEquiv
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0) :
    (Base d × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Base d × ℝ)).symm.trans
    (normalCoordinateEquiv W u q hcodim huW hu0).toLinearEquiv

theorem normalCoordinateLinearEquiv_apply
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0)
    (z : Base d × ℝ) :
    normalCoordinateLinearEquiv W u q hcodim huW hu0 z =
      normalCoordinateMeasurableEquiv W u q hcodim huW hu0 z := by
  rfl

@[simp]
theorem normalCoordinateMeasurableEquiv_apply
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0)
    (z : Base d × ℝ) :
    normalCoordinateMeasurableEquiv W u q hcodim huW hu0 z =
      (q z.1 : EuclideanSpace ℝ (Fin n)) + z.2 • unitNormal u := by
  rcases z with ⟨x, t⟩
  exact normalCoordinateEquiv_apply W u q hcodim huW hu0 x t

/-- The ordinary-product Case-2 coordinates preserve Euclidean volume. -/
theorem normalCoordinate_measurePreserving
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0) :
    MeasurePreserving
      (normalCoordinateMeasurableEquiv W u q hcodim huW hu0) := by
  exact (WithLp.volume_preserving_toLp (Base d) ℝ).trans
    (normalCoordinateEquiv W u q hcodim huW hu0).measurePreserving

/-- Pulling a measurable body back to the Case-2 product coordinates leaves
its volume unchanged. -/
theorem volume_preimage_normalCoordinate
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    (volume.prod volume)
        ((normalCoordinateMeasurableEquiv W u q hcodim huW hu0) ⁻¹' B) =
      volume B := by
  rw [← Measure.volume_eq_prod]
  exact (normalCoordinate_measurePreserving W u q hcodim huW hu0).measure_preimage
    hB.nullMeasurableSet

/-- Convexity is preserved by the Case-2 coordinate pullback. -/
theorem convex_preimage_normalCoordinate
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : Convex ℝ B) :
    Convex ℝ
      ((normalCoordinateMeasurableEquiv W u q hcodim huW hu0) ⁻¹' B) := by
  intro x hx y hy a b ha hb hab
  let e := normalCoordinateLinearEquiv W u q hcodim huW hu0
  change normalCoordinateMeasurableEquiv W u q hcodim huW hu0 x ∈ B at hx
  change normalCoordinateMeasurableEquiv W u q hcodim huW hu0 y ∈ B at hy
  have hx' : e x ∈ B := by
    rw [show e x = normalCoordinateMeasurableEquiv W u q hcodim huW hu0 x by
      exact normalCoordinateLinearEquiv_apply W u q hcodim huW hu0 x]
    exact hx
  have hy' : e y ∈ B := by
    rw [show e y = normalCoordinateMeasurableEquiv W u q hcodim huW hu0 y by
      exact normalCoordinateLinearEquiv_apply W u q hcodim huW hu0 y]
    exact hy
  have hxy := hB hx' hy' ha hb hab
  change normalCoordinateMeasurableEquiv W u q hcodim huW hu0
    (a • x + b • y) ∈ B
  rw [← normalCoordinateLinearEquiv_apply]
  simpa only [map_add, map_smul] using hxy

/-- In normal coordinates, the first-coordinate projection is exactly the
orthogonal projection to the hyperplane `W`. -/
theorem image_baseProjection_preimage_normalCoordinate
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0)
    (B : Set (EuclideanSpace ℝ (Fin n))) :
    (fun x : Base d ↦ q x) ''
        baseProjection
          ((normalCoordinateMeasurableEquiv W u q hcodim huW hu0) ⁻¹' B) =
      W.orthogonalProjectionOnto '' B := by
  let e := normalCoordinateMeasurableEquiv W u q hcodim huW hu0
  have hunitW : unitNormal u ∈ Wᗮ := (Wᗮ).smul_mem _ huW
  ext z
  constructor
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    rcases p with ⟨y, t⟩
    change e (y, t) ∈ B at hp
    have hxy : y = x := hpx
    subst y
    refine ⟨e (x, t), hp, ?_⟩
    rw [normalCoordinateMeasurableEquiv_apply]
    simp [hunitW]
  · rintro ⟨b, hb, rfl⟩
    let p : Base d × ℝ := e.symm b
    refine ⟨p.1, ?_, ?_⟩
    · refine ⟨p, ?_, rfl⟩
      change e p ∈ B
      simpa [p] using hb
    · have hbcoord : b =
          (q p.1 : EuclideanSpace ℝ (Fin n)) + p.2 • unitNormal u := by
        rw [← e.apply_symm_apply b]
        exact (normalCoordinateMeasurableEquiv_apply
          W u q hcodim huW hu0 p).symm
      rw [hbcoord]
      simp [hunitW]

/-- A centered ambient inball gives the same-radius inball in the projected
base of the normal-coordinate pullback. -/
theorem closedBall_subset_baseProjection_preimage_normalCoordinate
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0)
    {B : Set (EuclideanSpace ℝ (Fin n))} {rho : ℝ}
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) rho ⊆ B) :
    Metric.closedBall (0 : Base d) rho ⊆
      baseProjection
        ((normalCoordinateMeasurableEquiv W u q hcodim huW hu0) ⁻¹' B) := by
  intro x hx
  refine ⟨(x, 0), ?_, rfl⟩
  change normalCoordinateMeasurableEquiv W u q hcodim huW hu0 (x, 0) ∈ B
  apply hball
  rw [Metric.mem_closedBall, dist_zero_right,
    normalCoordinateMeasurableEquiv_apply]
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  simpa only [zero_smul, add_zero, Submodule.norm_coe,
    LinearIsometryEquiv.norm_map] using hx

/-- A centered segment in the direction of `u` becomes the vertical segment
required by the product-volume estimate. -/
theorem vertical_segment_mem_preimage_normalCoordinate
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n))
    (q : Base d ≃ₗᵢ[ℝ] W)
    (hcodim : finrank ℝ W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (huW : u ∈ Wᗮ) (hu0 : u ≠ 0)
    {B : Set (EuclideanSpace ℝ (Fin n))} {a b : ℝ}
    (hsegment : ∀ t ∈ Icc a b, t • unitNormal u ∈ B) :
    ∀ t ∈ Icc a b,
      ((0 : Base d), t) ∈
        (normalCoordinateMeasurableEquiv W u q hcodim huW hu0) ⁻¹' B := by
  intro t ht
  change normalCoordinateMeasurableEquiv W u q hcodim huW hu0 (0, t) ∈ B
  simpa using hsegment t ht

end Erdos186.CFP.Bilu.Case2Coordinates

#print axioms Erdos186.CFP.Bilu.Case2Coordinates.span_unitNormal_eq_orthogonal
#print axioms Erdos186.CFP.Bilu.Case2Coordinates.normalCoordinate_measurePreserving
#print axioms Erdos186.CFP.Bilu.Case2Coordinates.volume_preimage_normalCoordinate
#print axioms Erdos186.CFP.Bilu.Case2Coordinates.convex_preimage_normalCoordinate
#print axioms Erdos186.CFP.Bilu.Case2Coordinates.image_baseProjection_preimage_normalCoordinate
#print axioms Erdos186.CFP.Bilu.Case2Coordinates.closedBall_subset_baseProjection_preimage_normalCoordinate
