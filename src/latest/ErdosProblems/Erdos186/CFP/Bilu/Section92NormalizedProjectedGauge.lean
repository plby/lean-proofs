/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92ProjectedComplementCoordinates
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Complement-lattice normalized primitive quotients

The orthogonal quotient used in the projection estimate is normalized here
by the integral complement basis, rather than by an arbitrary orthonormal
basis.  Consequently the reduced lattice is literally `ℤ^(n-1)`.  This
file proves exact unit-ball preservation for all old integral lifts and
records the covolume factor relating these coordinates to the orthonormal
projected volume.
-/

namespace Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep

open scoped ENNReal Topology
open Module Submodule Set MeasureTheory Filter
open Mahler MinkowskiUpper SubspaceLattice

noncomputable section

variable {n : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
  {phi : IntegralPoint n →+ ℤ} {T : ℝ}

variable (S : PrimitiveKernelStep p phi T)

/-- Change from the analytic orthonormal quotient chart to the chart in
which the projected complement lattice is standard. -/
def orthonormalToComplementEquiv :
    EuclideanSpace ℝ (Fin S.quotient.complementRank) ≃ₗ[ℝ]
      (Fin S.quotient.complementRank → ℝ) :=
  (Section92ProjectedGauge.PrimitiveKernelStep.projectedEquiv S).symm.toLinearEquiv.trans
    S.projectedComplementEquiv

/-- The old unit ball, projected away from the primitive kernel direction
and expressed in integral complement coordinates. -/
def coordinateProjectedBody :
    Set (Fin S.quotient.complementRank → ℝ) :=
  S.projectedComplementEquiv ''
    (S.projectedSpace.orthogonalProjectionOnto ''
      Section92ProjectedGauge.PrimitiveKernelStep.euclideanUnitBall S)

/-- The coordinate-normalized body is the image of the orthonormally
normalized projected body under the change of basis. -/
theorem coordinateProjectedBody_eq_image :
    S.coordinateProjectedBody =
      S.orthonormalToComplementEquiv ''
        Section92ProjectedGauge.PrimitiveKernelStep.projectedBody S := by
  ext x
  simp only [coordinateProjectedBody, orthonormalToComplementEquiv,
    Section92ProjectedGauge.PrimitiveKernelStep.projectedBody,
    Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Section92ProjectedGauge.PrimitiveKernelStep.projectedEquiv S
      (S.projectedSpace.orthogonalProjectionOnto z), ?_, ?_⟩
    · exact ⟨S.projectedSpace.orthogonalProjectionOnto z, ⟨z, hz, rfl⟩, rfl⟩
    · simp
  · rintro ⟨y, ⟨w, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    refine ⟨S.projectedSpace.orthogonalProjectionOnto z, ⟨z, hz, rfl⟩, ?_⟩
    exact congrArg S.projectedComplementEquiv
      ((Section92ProjectedGauge.PrimitiveKernelStep.projectedEquiv S).symm_apply_apply
        (S.projectedSpace.orthogonalProjectionOnto z)).symm

theorem isCompact_coordinateProjectedBody (hp : IsDefinite p) :
    IsCompact S.coordinateProjectedBody := by
  rw [S.coordinateProjectedBody_eq_image]
  exact
    (Section92ProjectedGauge.PrimitiveKernelStep.isCompact_projectedBody S hp).image
      S.orthonormalToComplementEquiv.toLinearMap.continuous_of_finiteDimensional

theorem coordinateProjectedBody_mem_nhds_zero (hp : IsDefinite p) :
    S.coordinateProjectedBody ∈ 𝓝 0 := by
  rw [S.coordinateProjectedBody_eq_image]
  have hopen : IsOpenMap S.orthonormalToComplementEquiv :=
    S.orthonormalToComplementEquiv.toLinearMap.isOpenMap_of_finiteDimensional
      S.orthonormalToComplementEquiv.surjective
  simpa only [map_zero] using
    hopen.image_mem_nhds
      (Section92ProjectedGauge.PrimitiveKernelStep.projectedBody_mem_nhds_zero
        S hp)

/-- The normalized projected body has positive finite real volume. -/
theorem coordinateProjectedBody_volumeReal_pos (hp : IsDefinite p) :
    0 < volume.real S.coordinateProjectedBody := by
  exact ENNReal.toReal_pos
    (Measure.measure_pos_of_mem_nhds volume
      (S.coordinateProjectedBody_mem_nhds_zero hp)).ne'
    (S.isCompact_coordinateProjectedBody hp).measure_lt_top.ne

/-! ## The exact projected-lattice covolume factor -/

/-- The projected complement basis in the orthonormal analytic chart. -/
def orthonormalProjectedComplementBasis :
    Basis (Fin S.quotient.complementRank) ℝ
      (EuclideanSpace ℝ (Fin S.quotient.complementRank)) :=
  S.projectedComplementBasis.map
    (Section92ProjectedGauge.PrimitiveKernelStep.projectedEquiv S).toLinearEquiv

/-- The projected complement lattice in the orthonormal analytic chart. -/
def projectedComplementLattice :
    Submodule ℤ (EuclideanSpace ℝ (Fin S.quotient.complementRank)) :=
  Submodule.span ℤ (Set.range S.orthonormalProjectedComplementBasis)

instance instDiscreteTopologyProjectedComplementLattice :
    DiscreteTopology S.projectedComplementLattice := by
  change DiscreteTopology
    (Submodule.span ℤ (Set.range S.orthonormalProjectedComplementBasis))
  infer_instance

instance instIsZLatticeProjectedComplementLattice :
    IsZLattice ℝ S.projectedComplementLattice := by
  change IsZLattice ℝ
    (Submodule.span ℤ (Set.range S.orthonormalProjectedComplementBasis))
  infer_instance

/-- Its canonical integral basis, induced by the chosen complement basis. -/
def projectedComplementLatticeBasis :
    Basis (Fin S.quotient.complementRank) ℤ S.projectedComplementLattice :=
  S.orthonormalProjectedComplementBasis.restrictScalars ℤ

theorem orthonormalToComplementEquiv_eq_equivFun :
    S.orthonormalToComplementEquiv =
      S.orthonormalProjectedComplementBasis.equivFun := by
  have hmaps : S.orthonormalToComplementEquiv.toLinearMap =
      S.orthonormalProjectedComplementBasis.equivFun.toLinearMap := by
    apply S.orthonormalProjectedComplementBasis.ext
    intro i
    simp [orthonormalToComplementEquiv, orthonormalProjectedComplementBasis,
      projectedComplementBasis_apply]
    rw [← S.projectedComplementBasis_apply i]
    simp only [Basis.equivFun_apply, Basis.repr_self]
    ext j
    by_cases hji : j = i
    · subst j
      simp [Pi.single]
    · simp [Pi.single, hji, Ne.symm hji]
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun hmaps x

theorem projectedComplementLatticeBasis_ofZLatticeBasis :
    S.projectedComplementLatticeBasis.ofZLatticeBasis ℝ
        S.projectedComplementLattice =
      S.orthonormalProjectedComplementBasis := by
  apply DFunLike.coe_injective
  funext i
  rw [S.projectedComplementLatticeBasis.ofZLatticeBasis_apply ℝ
    S.projectedComplementLattice]
  exact S.orthonormalProjectedComplementBasis.restrictScalars_apply ℤ i

/-- Exact cancellation identity: passing from the orthonormal quotient
chart to standard complement-lattice coordinates divides volume by the
projected lattice covolume. -/
theorem volume_coordinateProjectedBody_eq_div_covolume
    (hp : IsDefinite p) :
    volume S.coordinateProjectedBody =
      volume
          (Section92ProjectedGauge.PrimitiveKernelStep.projectedBody S) /
        ENNReal.ofReal (ZLattice.covolume S.projectedComplementLattice) := by
  have h := ZLattice.volume_image_eq_volume_div_covolume'
    S.projectedComplementLattice S.projectedComplementLatticeBasis
    (Section92ProjectedGauge.PrimitiveKernelStep.isCompact_projectedBody S hp
      |>.measurableSet.nullMeasurableSet)
  rw [S.projectedComplementLatticeBasis_ofZLatticeBasis,
    ← S.orthonormalToComplementEquiv_eq_equivFun,
    ← S.coordinateProjectedBody_eq_image] at h
  exact h

theorem covolume_mul_volume_coordinateProjectedBody
    (hp : IsDefinite p) :
    ENNReal.ofReal (ZLattice.covolume S.projectedComplementLattice) *
        volume S.coordinateProjectedBody =
      volume
        (Section92ProjectedGauge.PrimitiveKernelStep.projectedBody S) := by
  rw [S.volume_coordinateProjectedBody_eq_div_covolume hp]
  exact ENNReal.mul_div_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr
      (ZLattice.covolume_pos S.projectedComplementLattice volume))
    ENNReal.ofReal_ne_top

/-- Sharp covolume-cancelled projection inequality in standard complement
coordinates. -/
theorem coordinateProjectedBody_volume_bound (hn : 0 < n)
    (hp : IsDefinite p) :
    (2 : ENNReal) * ENNReal.ofReal ‖S.primitiveReal‖ *
        ENNReal.ofReal (ZLattice.covolume S.projectedComplementLattice) *
        volume S.coordinateProjectedBody ≤
      (n : ENNReal) * ENNReal.ofReal
          (p (integralEmbed S.short.vector)) * volume (unitBall p) := by
  have h :=
    Section92ProjectedGauge.PrimitiveKernelStep.projectedBody_volume_bound
      hn S hp
  rw [← S.covolume_mul_volume_coordinateProjectedBody hp] at h
  simpa only [mul_assoc] using h

/-- Coarse covolume-cancelled form using the defining short-vector bound. -/
theorem coordinateProjectedBody_volume_bound_two_mul (hn : 0 < n)
    (hp : IsDefinite p) :
    (2 : ENNReal) * ENNReal.ofReal ‖S.primitiveReal‖ *
        ENNReal.ofReal (ZLattice.covolume S.projectedComplementLattice) *
        volume S.coordinateProjectedBody ≤
      (n : ENNReal) * ENNReal.ofReal (2 * T) * volume (unitBall p) := by
  have h :=
    Section92ProjectedGauge.PrimitiveKernelStep.projectedBody_volume_bound_two_mul
      hn S hp
  rw [← S.covolume_mul_volume_coordinateProjectedBody hp] at h
  simpa only [mul_assoc] using h

/-- The projected gauge pulled back to literal integral-complement
coordinates. -/
def coordinateProjectedSeminorm (hp : IsDefinite p) :
    Seminorm ℝ (Fin S.quotient.complementRank → ℝ) :=
  (Section92ProjectedGauge.PrimitiveKernelStep.projectedSeminorm S hp).comp
    S.orthonormalToComplementEquiv.symm.toLinearMap

/-- Exact unit ball of the coordinate-normalized projected seminorm. -/
theorem unitBall_coordinateProjectedSeminorm (hp : IsDefinite p) :
    {x | S.coordinateProjectedSeminorm hp x ≤ 1} =
      S.coordinateProjectedBody := by
  rw [S.coordinateProjectedBody_eq_image]
  ext x
  change
    Section92ProjectedGauge.PrimitiveKernelStep.projectedSeminorm S hp
        (S.orthonormalToComplementEquiv.symm x) ≤ 1 ↔ _
  rw [show
      Section92ProjectedGauge.PrimitiveKernelStep.projectedSeminorm S hp
          (S.orthonormalToComplementEquiv.symm x) ≤ 1 ↔
        S.orthonormalToComplementEquiv.symm x ∈
          Section92ProjectedGauge.PrimitiveKernelStep.projectedBody S by
    have h := Set.ext_iff.mp
      (Section92ProjectedGauge.PrimitiveKernelStep.unitBall_projectedSeminorm
        S hp) (S.orthonormalToComplementEquiv.symm x)
    exact h]
  constructor
  · intro hx
    exact ⟨S.orthonormalToComplementEquiv.symm x, hx,
      S.orthonormalToComplementEquiv.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/-- The coordinate-normalized projected seminorm is definite. -/
theorem isDefinite_coordinateProjectedSeminorm (hp : IsDefinite p) :
    IsDefinite (S.coordinateProjectedSeminorm hp) := by
  intro x hx
  have hzero : S.orthonormalToComplementEquiv.symm x = 0 :=
    Section92ProjectedGauge.PrimitiveKernelStep.isDefinite_projectedSeminorm
      S hp _ hx
  apply S.orthonormalToComplementEquiv.symm.injective
  simpa using hzero

/-- Every old integral unit-ball point survives in the literal standard
lattice of the rank-decreased presentation. -/
theorem coordinateProjectedSeminorm_complementCoordinates_le_one
    (hp : IsDefinite p) (x : IntegralPoint n)
    (hx : p (integralEmbed x) ≤ 1) :
    S.coordinateProjectedSeminorm hp
        (integralEmbed (S.quotient.complementCoordinates x)) ≤ 1 := by
  rw [show S.coordinateProjectedSeminorm hp
          (integralEmbed (S.quotient.complementCoordinates x)) ≤ 1 ↔
        integralEmbed (S.quotient.complementCoordinates x) ∈
          S.coordinateProjectedBody by
    have h := Set.ext_iff.mp (S.unitBall_coordinateProjectedSeminorm hp)
      (integralEmbed (S.quotient.complementCoordinates x))
    exact h]
  refine ⟨S.projectedSpace.orthogonalProjectionOnto (integralReal x), ?_, ?_⟩
  · refine ⟨integralReal x, ?_, rfl⟩
    rw [Section92ProjectedGauge.PrimitiveKernelStep.euclideanUnitBall,
      Seminorm.mem_closedBall]
    simp only [sub_zero]
    change p ((EuclideanSpace.equiv (Fin n) ℝ) (integralReal x)) ≤ 1
    rw [show (EuclideanSpace.equiv (Fin n) ℝ) (integralReal x) =
        integralEmbed x by
      ext i
      rfl]
    exact hx
  · exact S.projectedIntegralCoordinates_eq_integralEmbed x

end

end Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep

#print axioms Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep.unitBall_coordinateProjectedSeminorm
#print axioms Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep.coordinateProjectedSeminorm_complementCoordinates_le_one
