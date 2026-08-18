/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.PreprocessingBilu

/-!
# Uniform preprocessing numerics for a prescribed no-carry dilation

The preprocessing hierarchy already dominates the coefficient needed for
unit properness.  Multiplying that hierarchy by a prescribed dilation scale
gives the exact arbitrary-scale numerical inequality used by the final
centered map-back.
-/

namespace Erdos186.CFP.PreprocessingBilu

noncomputable section

/-- The dimension-uniform coefficient controlling a prescribed canonical
bounding-box dilation. -/
def preprocessingNoCarryIndexBound (D scaleDen : ℕ) : ℕ :=
  4 * (6 * scaleDen) ^ D * (4 * scaleDen) ^ D

theorem preprocessingNoCarryIndexBound_pos
    {D scaleDen : ℕ} (hscaleDen : 0 < scaleDen) :
    0 < preprocessingNoCarryIndexBound D scaleDen := by
  simp only [preprocessingNoCarryIndexBound]
  positivity

/-- Arbitrary-dilation version of
`boundingBox_proper_numeric_of_preprocessing_large`. -/
theorem boundingBox_dilate_numeric_of_preprocessing_large
    {scaleDen D e h q : ℕ}
    (hscaleDen : 0 < scaleDen) (he : 0 < e) (heD : e ≤ D)
    (hh : 0 < h)
    (hlarge : preprocessingNoCarryIndexBound D scaleDen * q ≤ h) :
    (2 * scaleDen) ^ e *
        (e * q * (h + 1) ^ (e - 1)) < h ^ e := by
  by_cases hq : q = 0
  · subst q
    simp only [mul_zero, zero_mul]
    positivity
  · have hqPos : 0 < q := Nat.pos_of_ne_zero hq
    let a := 4 * scaleDen
    let b := 6 * scaleDen
    have haPos : 0 < a := by dsimp only [a]; positivity
    have hbPos : 0 < b := by dsimp only [b]; positivity
    have hDPos : 0 < D := he.trans_le heD
    have hDTwo : D ≤ 2 ^ D := self_le_two_pow D
    have htwoB : 2 ≤ b := by dsimp only [b]; omega
    have hpowBase : 2 ^ D ≤ b ^ D := Nat.pow_le_pow_left htwoB _
    have hDle : D ≤ b ^ D := hDTwo.trans hpowBase
    have hbPowPos : 0 < b ^ D := pow_pos hbPos _
    have hDlt : D < 4 * b ^ D := by nlinarith
    have haMono : a ^ e ≤ a ^ D :=
      Nat.pow_le_pow_right haPos heD
    have hcoeff : e * a ^ e < 4 * b ^ D * a ^ D := by
      calc
        e * a ^ e ≤ D * a ^ D := Nat.mul_le_mul heD haMono
        _ < (4 * b ^ D) * a ^ D :=
          Nat.mul_lt_mul_of_pos_right hDlt (pow_pos haPos _)
    have hcoeffQ : e * a ^ e * q < h := by
      calc
        e * a ^ e * q < (4 * b ^ D * a ^ D) * q :=
          Nat.mul_lt_mul_of_pos_right hcoeff hqPos
        _ = preprocessingNoCarryIndexBound D scaleDen * q := by
          simp only [preprocessingNoCarryIndexBound, a, b, mul_assoc]
        _ ≤ h := hlarge
    have hsucc : h + 1 ≤ 2 * h := by omega
    have htwoPow : 2 ^ (e - 1) ≤ 2 ^ e :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le e 1)
    calc
      (2 * scaleDen) ^ e * (e * q * (h + 1) ^ (e - 1)) ≤
          e * q * ((2 * scaleDen) ^ e * (2 * h) ^ (e - 1)) := by
        have hp := Nat.pow_le_pow_left hsucc (e - 1)
        calc
          (2 * scaleDen) ^ e * (e * q * (h + 1) ^ (e - 1)) =
              e * q * ((2 * scaleDen) ^ e *
                (h + 1) ^ (e - 1)) := by ring
          _ ≤ e * q * ((2 * scaleDen) ^ e *
                (2 * h) ^ (e - 1)) := by gcongr
      _ = e * q * ((2 * scaleDen) ^ e *
          (2 ^ (e - 1) * h ^ (e - 1))) := by
        simp only [mul_pow]
      _ ≤ e * q * ((2 * scaleDen) ^ e *
          (2 ^ e * h ^ (e - 1))) := by gcongr
      _ = (e * a ^ e * q) * h ^ (e - 1) := by
        rw [show e * q *
            ((2 * scaleDen) ^ e * (2 ^ e * h ^ (e - 1))) =
              (e * ((2 * scaleDen) ^ e * 2 ^ e) * q) *
                h ^ (e - 1) by ring,
          ← mul_pow]
        dsimp only [a]
        ring
      _ < h * h ^ (e - 1) :=
        Nat.mul_lt_mul_of_pos_right hcoeffQ (by positivity)
      _ = h ^ e := by
        calc
          h * h ^ (e - 1) = h ^ (e - 1 + 1) :=
            (pow_succ' h (e - 1)).symm
          _ = h ^ e := by congr 1; omega

/-- A retained positive-rank approximation is proper at every prescribed
scale paid for by the linear no-carry hierarchy. -/
theorem HApproximation.boundingBox_dilate_proper_of_preprocessingNoCarry
    {A : Finset ℤ} {h e scaleDen D q : ℕ}
    (V : HDimension.HApproximation A h e 1 scaleDen)
    (he : 0 < e) (heD : e ≤ D)
    (hlarge : preprocessingNoCarryIndexBound D scaleDen * q ≤ h) :
    ((BoundingBox.dBoundingBox A e he).progression.dilate q).Proper := by
  have hscaleDen : 0 < scaleDen := V.scaleDen_pos
  have hh : 0 < h := V.scale_pos.trans_le V.scale_le
  have hindexPos : 0 < preprocessingNoCarryIndexBound D scaleDen :=
    preprocessingNoCarryIndexBound_pos (D := D) hscaleDen
  have hqh : q ≤ h := by
    calc
      q = 1 * q := by simp
      _ ≤ preprocessingNoCarryIndexBound D scaleDen * q :=
        Nat.mul_le_mul_right q hindexPos
      _ ≤ h := hlarge
  apply V.boundingBox_dilate_proper_of_numeric he hqh
  simpa only [one_mul] using
    boundingBox_dilate_numeric_of_preprocessing_large
      hscaleDen he heD hh hlarge

end

end Erdos186.CFP.PreprocessingBilu

#print axioms
  Erdos186.CFP.PreprocessingBilu.HApproximation.boundingBox_dilate_proper_of_preprocessingNoCarry
