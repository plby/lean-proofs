/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.DiscreteJohnMahler

/-!
# A quantitative volume bound for the Mahler discrete-John certificate

This isolates the continuous-volume consequence of the unconditional
discrete-John construction.  In the full-rank branch, all successive minima
are at most one, so the inner Mahler box controls the continuous body volume.
-/

namespace Erdos186
namespace DiscreteJohn
namespace MahlerExtraction

open scoped BigOperators
open Module CFP.Bilu.Mahler CFP.Bilu.MinkowskiSecond
open CFP.Bilu.MahlerBox

variable {d : ℕ}

/-- The specific certificate produced by the Mahler extraction in positive
dimension. -/
noncomputable def mahlerCertificate
    (hd : 0 < d) (p : Seminorm ℝ (Fin d → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin d) ℤ (LatticePoint d)) (hb : IsMahlerBasis p b)
    (points : Finset (LatticePoint d))
    (hpoints : ∀ z, z ∈ points ↔ p (integralEmbed z) ≤ 1) :
    Certificate points d (johnFactor d) :=
  certificateOfFullRankMinimaData p b
    (fullRankMinimaData hd p hp b hb) points hpoints

/-- In the full-lattice-rank (`λ_i ≤ 1`) branch, the outer volume of the
specific Mahler certificate is at most a dimension-only multiple of the
continuous body volume. -/
theorem mahlerCertificate_outer_volume_le
    (hd : 0 < d) (p : Seminorm ℝ (Fin d → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin d) ℤ (LatticePoint d)) (hb : IsMahlerBasis p b)
    (hthick : ∀ i, successiveMinimum p i ≤ 1)
    (points : Finset (LatticePoint d))
    (hpoints : ∀ z, z ∈ points ↔ p (integralEmbed z) ≤ 1) :
    ((mahlerCertificate hd p hp b hb points hpoints).outer.volume : ℝ) ≤
      (((2 * johnFactor d + 1) ^ d * d.factorial * 3 ^ d : ℕ) : ℝ) *
        MeasureTheory.volume.real (CFP.Bilu.MinkowskiUpper.unitBall p) := by
  let C := mahlerCertificate hd p hp b hb points hpoints
  have houterNat := C.outer_volume_le
  have houter : (C.outer.volume : ℝ) ≤
      (((2 * johnFactor d + 1) ^ d : ℕ) : ℝ) * (C.inner.volume : ℝ) := by
    exact_mod_cast houterNat
  have hwidth := innerRadius_width_le hd p hp hthick
  have henn := centeredBasisGAP_volume_mul_minkowskiFactor_le
    hd p hp b (innerRadius p) hwidth
  have hball_ne_top :
      MeasureTheory.volume (CFP.Bilu.MinkowskiUpper.unitBall p) ≠ ⊤ :=
    (CFP.Bilu.MinkowskiUpper.isBounded_unitBall p hp).measure_lt_top.ne
  have hrhs_ne_top :
      ENNReal.ofReal ((3 : ℝ) ^ d) *
          MeasureTheory.volume (CFP.Bilu.MinkowskiUpper.unitBall p) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hball_ne_top
  have hreal := ENNReal.toReal_mono hrhs_ne_top henn
  have hinnerEq : C.inner.volume =
      (centeredBasisGAP b (innerRadius p)).volume := by
    simp [C, mahlerCertificate, Certificate.inner,
      certificateOfFullRankMinimaData, fullRankMinimaData,
      johnRadius_div hd]
  have hinner : (C.inner.volume : ℝ) ≤
      (d.factorial : ℝ) * (3 : ℝ) ^ d *
        MeasureTheory.volume.real (CFP.Bilu.MinkowskiUpper.unitBall p) := by
    have hreal' :
        ((centeredBasisGAP b (innerRadius p)).volume : ℝ) *
            ((2 : ℝ) ^ d / (d.factorial : ℝ)) ≤
          (3 : ℝ) ^ d *
            MeasureTheory.volume.real (CFP.Bilu.MinkowskiUpper.unitBall p) := by
      simpa [MeasureTheory.measureReal_def, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤
          ((centeredBasisGAP b (innerRadius p)).volume : ℝ)),
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤
          (2 : ℝ) ^ d / (d.factorial : ℝ)),
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d)]
        using hreal
    rw [← hinnerEq] at hreal'
    have hfac : (0 : ℝ) < d.factorial := by positivity
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hweak : (C.inner.volume : ℝ) / (d.factorial : ℝ) ≤
        (3 : ℝ) ^ d *
          MeasureTheory.volume.real (CFP.Bilu.MinkowskiUpper.unitBall p) := by
      calc
        (C.inner.volume : ℝ) / (d.factorial : ℝ) =
            (C.inner.volume : ℝ) *
              (1 / (d.factorial : ℝ)) := by ring
        _ ≤ (C.inner.volume : ℝ) *
              ((2 : ℝ) ^ d / (d.factorial : ℝ)) := by
          gcongr
        _ ≤ _ := hreal'
    have hmul := (div_le_iff₀ hfac).mp hweak
    calc
      (C.inner.volume : ℝ) ≤
          ((3 : ℝ) ^ d *
              MeasureTheory.volume.real (CFP.Bilu.MinkowskiUpper.unitBall p)) *
            (d.factorial : ℝ) := hmul
      _ = _ := by ring
  calc
    (C.outer.volume : ℝ) ≤
        (((2 * johnFactor d + 1) ^ d : ℕ) : ℝ) *
          (C.inner.volume : ℝ) := houter
    _ ≤ (((2 * johnFactor d + 1) ^ d : ℕ) : ℝ) *
        ((d.factorial : ℝ) * (3 : ℝ) ^ d *
          MeasureTheory.volume.real (CFP.Bilu.MinkowskiUpper.unitBall p)) := by
      gcongr
    _ = (((2 * johnFactor d + 1) ^ d * d.factorial * 3 ^ d : ℕ) : ℝ) *
        MeasureTheory.volume.real (CFP.Bilu.MinkowskiUpper.unitBall p) := by
      push_cast
      ring

end MahlerExtraction
end DiscreteJohn
end Erdos186
