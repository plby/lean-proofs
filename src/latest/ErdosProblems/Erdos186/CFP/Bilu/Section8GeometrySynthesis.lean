/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.ProjectionVolumeCoarse
import ErdosProblems.Erdos186.CFP.Bilu.VolumeSections

/-!
# Geometric synthesis for Bilu Section 8.3, Case 2

This file supplies the two geometric inequalities in the final Case 2
cancellation.  Equation (8.8) follows from the proved midpoint/Fubini
projection estimate.  Equation (8.9) follows from the proved sharp cone
chain.  The last theorem inserts both into the division-free
`combine_equations_8_7_to_8_10_ennreal` calculation.
-/

namespace Erdos186.CFP.Bilu.Section8GeometrySynthesis

open scoped ENNReal
open MeasureTheory Set
open ProjectionVolumeCoarse VolumeSections

/-- The intrinsic volume of the half-scaled projection is the expected
power of `1/2` times the projection volume. -/
theorem volume_halfBaseProjection {d : ℕ}
    (B : Set (Base d × ℝ)) :
    volume (halfBaseProjection B) =
      ‖(2 : ℝ)⁻¹‖₊ ^ d * volume (baseProjection B) := by
  rw [halfBaseProjection]
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    (V := Base d)]
  rw [Measure.euclideanHausdorffMeasure_smul₀
    (Module.finrank ℝ (Base d)) (by norm_num : (2 : ℝ)⁻¹ ≠ 0)]
  rw [show Module.finrank ℝ (Base d) = d by simp [Base]]
  rfl

/-- Coarse, dimension-only form of equation (8.8), obtained directly
from `half_projection_volume_le_prod_volume`.

`volumeFactor * V` is any previously established upper bound for the
ambient volume of `Omega`. -/
theorem equation88_of_half_projection {d : ℕ}
    {Omega : Set (Base d × ℝ)} {normW gaugeW : ℝ}
    {volumeFactor V : ℝ≥0∞}
    (hnormW : 0 ≤ normW) (hgaugeW : 0 < gaugeW)
    (hOmega : MeasurableSet Omega)
    (hhalf : MeasurableSet (halfBaseProjection Omega))
    (hconv : Convex ℝ Omega)
    (hsegment : ∀ t ∈ Set.Icc (-(normW / gaugeW)) (normW / gaugeW),
      ((0 : Base d), t) ∈ Omega)
    (hvolume : (volume.prod volume) Omega ≤ volumeFactor * V) :
    ENNReal.ofReal normW * volume (baseProjection Omega) ≤
      ((‖(2 : ℝ)⁻¹‖₊ : ℝ≥0∞) ^ d)⁻¹ * volumeFactor *
        ENNReal.ofReal gaugeW * V := by
  let scale : ℝ≥0∞ := ‖(2 : ℝ)⁻¹‖₊ ^ d
  have hscale0 : scale ≠ 0 := by
    dsimp only [scale]
    exact pow_ne_zero _ (by norm_num)
  have hscaletop : scale ≠ ∞ := by
    dsimp only [scale]
    finiteness
  have hquot : 0 ≤ normW / gaugeW := div_nonneg hnormW hgaugeW.le
  have hproj := half_projection_volume_le_prod_volume
    hquot hOmega hhalf hconv hsegment
  rw [volume_halfBaseProjection] at hproj
  change ENNReal.ofReal (normW / gaugeW) *
      (scale * volume (baseProjection Omega)) ≤
        (volume.prod volume) Omega at hproj
  have hgauge0 : ENNReal.ofReal gaugeW ≠ 0 := by
    intro hzero
    rw [ENNReal.ofReal_eq_zero] at hzero
    exact (not_le.mpr hgaugeW) hzero
  have hofReal_cancel :
      ENNReal.ofReal gaugeW * ENNReal.ofReal (normW / gaugeW) =
        ENNReal.ofReal normW := by
    rw [← ENNReal.ofReal_mul hgaugeW.le]
    congr 1
    field_simp
  have hcross :
      scale * (ENNReal.ofReal normW * volume (baseProjection Omega)) ≤
        ENNReal.ofReal gaugeW * (volumeFactor * V) := by
    calc
      scale * (ENNReal.ofReal normW * volume (baseProjection Omega)) =
          ENNReal.ofReal normW *
            (scale * volume (baseProjection Omega)) := by ac_rfl
      _ = (ENNReal.ofReal gaugeW * ENNReal.ofReal (normW / gaugeW)) *
            (scale * volume (baseProjection Omega)) := by
        rw [hofReal_cancel]
      _ =
          ENNReal.ofReal gaugeW *
            (ENNReal.ofReal (normW / gaugeW) *
              (scale * volume (baseProjection Omega))) := by
        ac_rfl
      _ ≤ ENNReal.ofReal gaugeW * (volume.prod volume) Omega := by
        gcongr
      _ ≤ ENNReal.ofReal gaugeW * (volumeFactor * V) := by
        gcongr
  have hresult : ENNReal.ofReal normW * volume (baseProjection Omega) ≤
      scale⁻¹ * volumeFactor * ENNReal.ofReal gaugeW * V := by
    calc
    ENNReal.ofReal normW * volume (baseProjection Omega) =
        scale⁻¹ *
          (scale * (ENNReal.ofReal normW * volume (baseProjection Omega))) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hscale0 hscaletop, one_mul]
    _ ≤ scale⁻¹ * (ENNReal.ofReal gaugeW * (volumeFactor * V)) := by
      gcongr
    _ = scale⁻¹ * volumeFactor * ENNReal.ofReal gaugeW * V := by
      ac_rfl
  simpa only [scale] using hresult

/-- Solve the cross-multiplied sharp cone-chain estimate for the initial
section volume. -/
theorem initial_volume_le_of_coordinateConeChain {d k : ℕ} {ρ : ℝ}
    {S : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (d + i)))}
    (hchain : CoordinateConeChain d k ρ S) :
    intrinsicVolume d (S 0) ≤
      (((d.factorial : ℝ≥0∞) * ENNReal.ofReal (ρ ^ k))⁻¹ *
        ((d + k).factorial : ℝ≥0∞)) * intrinsicVolume (d + k) (S k) := by
  let scale : ℝ≥0∞ :=
    (d.factorial : ℝ≥0∞) * ENNReal.ofReal (ρ ^ k)
  have hρ : 0 < ρ := hchain.1
  have hscale0 : scale ≠ 0 := by
    dsimp only [scale]
    apply mul_ne_zero
    · exact_mod_cast Nat.factorial_ne_zero d
    · intro hzero
      rw [ENNReal.ofReal_eq_zero] at hzero
      exact (not_le.mpr (pow_pos hρ k)) hzero
  have hscaletop : scale ≠ ∞ := by
    dsimp only [scale]
    finiteness
  have hcone := coordinate_cone_chain_factorial_bound hchain
  change scale * intrinsicVolume d (S 0) ≤
      ((d + k).factorial : ℝ≥0∞) * intrinsicVolume (d + k) (S k) at hcone
  calc
    intrinsicVolume d (S 0) = scale⁻¹ * (scale * intrinsicVolume d (S 0)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hscale0 hscaletop, one_mul]
    _ ≤ scale⁻¹ *
        (((d + k).factorial : ℝ≥0∞) * intrinsicVolume (d + k) (S k)) := by
      gcongr
    _ = (scale⁻¹ * ((d + k).factorial : ℝ≥0∞)) *
        intrinsicVolume (d + k) (S k) := by rw [mul_assoc]

/-- Concrete synthesis of (8.8), (8.9), and the final Case 2
cancellation.  Equations (8.7) and (8.10) enter in precisely the
division-free forms produced by polar separation and the projection
determinant theorem. -/
theorem combine_case2_with_projection_and_cone
    {d k : ℕ} {ρ normW gaugeW : ℝ}
    {Omega : Set (Base (d + k) × ℝ)}
    {S : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (d + i)))}
    {C innerAbs volB V volumeFactor : ℝ≥0∞} {normL : ℝ}
    (hnormW : 0 ≤ normW) (hgaugeW : 0 < gaugeW)
    (hOmega : MeasurableSet Omega)
    (hhalf : MeasurableSet (halfBaseProjection Omega))
    (hconv : Convex ℝ Omega)
    (hsegment : ∀ t ∈ Set.Icc (-(normW / gaugeW)) (normW / gaugeW),
      ((0 : Base (d + k)), t) ∈ Omega)
    (hOmegaVolume : (volume.prod volume) Omega ≤ volumeFactor * V)
    (hchain : CoordinateConeChain d k ρ S)
    (hfinal : S k = baseProjection Omega)
    (h87 : 2 * C * ENNReal.ofReal gaugeW ≤ innerAbs)
    (h810 : innerAbs * volB ≤
      ENNReal.ofReal normW * ENNReal.ofReal normL * intrinsicVolume d (S 0)) :
    2 * C * volB ≤
      ((‖(2 : ℝ)⁻¹‖₊ : ℝ≥0∞) ^ (d + k))⁻¹ * volumeFactor *
        ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (ρ ^ k))⁻¹ *
          ((d + k).factorial : ℝ≥0∞) *
        ENNReal.ofReal normL * V := by
  let c82 : ℝ≥0∞ :=
    ((‖(2 : ℝ)⁻¹‖₊ : ℝ≥0∞) ^ (d + k))⁻¹ * volumeFactor
  let c83 : ℝ≥0∞ :=
    ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (ρ ^ k))⁻¹ *
      ((d + k).factorial : ℝ≥0∞)
  have h88 : ENNReal.ofReal normW * intrinsicVolume (d + k) (S k) ≤
      c82 * ENNReal.ofReal gaugeW * V := by
    rw [hfinal]
    rw [show intrinsicVolume (d + k) (baseProjection Omega) =
        volume (baseProjection Omega) by
      simp only [intrinsicVolume]
      have hm :
          (MeasureTheory.Measure.euclideanHausdorffMeasure (d + k) :
              Measure (Base (d + k))) = volume := by
        simpa using
          (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
            (V := Base (d + k)))
      rw [hm]]
    exact equation88_of_half_projection hnormW hgaugeW hOmega hhalf hconv
      hsegment hOmegaVolume
  have h89 : intrinsicVolume d (S 0) ≤
      c83 * intrinsicVolume (d + k) (S k) := by
    exact initial_volume_le_of_coordinateConeChain hchain
  have hgauge0 : ENNReal.ofReal gaugeW ≠ 0 :=
    by
      intro hzero
      rw [ENNReal.ofReal_eq_zero] at hzero
      exact (not_le.mpr hgaugeW) hzero
  have hgaugetop : ENNReal.ofReal gaugeW ≠ ∞ := ENNReal.ofReal_ne_top
  have h87' : (2 * C * ENNReal.ofReal gaugeW) * volB ≤
      innerAbs * volB := by
    gcongr
  have h89' : ENNReal.ofReal normW * ENNReal.ofReal normL *
      intrinsicVolume d (S 0) ≤
        ENNReal.ofReal normW * ENNReal.ofReal normL *
          (c83 * intrinsicVolume (d + k) (S k)) := by
    gcongr
  have h88' : (ENNReal.ofReal normL * c83) *
      (ENNReal.ofReal normW * intrinsicVolume (d + k) (S k)) ≤
        (ENNReal.ofReal normL * c83) *
          (c82 * ENNReal.ofReal gaugeW * V) := by
    gcongr
  have hproduct : (2 * C * volB) * ENNReal.ofReal gaugeW ≤
      (c82 * c83 * ENNReal.ofReal normL * V) *
        ENNReal.ofReal gaugeW := by
    calc
      (2 * C * volB) * ENNReal.ofReal gaugeW =
          (2 * C * ENNReal.ofReal gaugeW) * volB := by ac_rfl
      _ ≤ innerAbs * volB := h87'
      _ ≤ ENNReal.ofReal normW * ENNReal.ofReal normL *
          intrinsicVolume d (S 0) := h810
      _ ≤ ENNReal.ofReal normW * ENNReal.ofReal normL *
          (c83 * intrinsicVolume (d + k) (S k)) := h89'
      _ = (ENNReal.ofReal normL * c83) *
          (ENNReal.ofReal normW * intrinsicVolume (d + k) (S k)) := by ac_rfl
      _ ≤ (ENNReal.ofReal normL * c83) *
          (c82 * ENNReal.ofReal gaugeW * V) := h88'
      _ = (c82 * c83 * ENNReal.ofReal normL * V) *
          ENNReal.ofReal gaugeW := by ac_rfl
  have hcombine : 2 * C * volB ≤
      c82 * c83 * ENNReal.ofReal normL * V :=
    (ENNReal.mul_le_mul_iff_left hgauge0 hgaugetop).mp hproduct
  simpa only [c82, c83, mul_assoc] using hcombine

end Erdos186.CFP.Bilu.Section8GeometrySynthesis

#print axioms Erdos186.CFP.Bilu.Section8GeometrySynthesis.equation88_of_half_projection
#print axioms Erdos186.CFP.Bilu.Section8GeometrySynthesis.combine_case2_with_projection_and_cone
