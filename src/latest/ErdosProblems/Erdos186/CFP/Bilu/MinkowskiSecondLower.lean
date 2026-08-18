/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MinimaAttainment
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecond

/-!
# The lower half of Minkowski's second theorem

This file combines compatible attainment of the successive minima with
the crosspolytope volume calculation from `MinkowskiSecond.lean`.
-/

namespace Erdos186.CFP.Bilu.MinkowskiSecond

open scoped BigOperators
open Erdos186.CFP.Bilu.Mahler

/-- The product of absolute inverse successive minima is the inverse of
their product. -/
theorem prod_abs_inv_successiveMinimum {n : ℕ} [Nonempty (Fin n)]
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    (∏ i, |(successiveMinimum p i)⁻¹|) =
      (∏ i, successiveMinimum p i)⁻¹ := by
  simp_rw [abs_of_pos (inv_pos.mpr (successiveMinimum_pos p hp _))]
  exact Finset.prod_inv_distrib (G := ℝ) (s := Finset.univ)
    (fun i : Fin n ↦ successiveMinimum p i)

/-- **Minkowski's second theorem, lower-volume half**, for the standard
integer lattice and the unit ball of a definite seminorm.

This is the form used in Bilu's proof: the volume of the unit ball is at
least `2^n / n!` divided by the product of the successive minima. -/
theorem minkowskiSecond_lower_volume {n : ℕ} [Nonempty (Fin n)]
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    ENNReal.ofReal ((∏ i, successiveMinimum p i)⁻¹) *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      MeasureTheory.volume {y | p y ≤ 1} := by
  obtain ⟨v, hv, hvp⟩ :=
    exists_independent_integralPoint_le_successiveMinimum p hp
  let a : Fin n → ℝ := fun i ↦ (successiveMinimum p i)⁻¹
  have ha : ∀ i, |a i| * p (integralEmbed (v i)) ≤ 1 := by
    intro i
    have hlam : 0 < successiveMinimum p i := successiveMinimum_pos p hp i
    rw [abs_of_pos (inv_pos.mpr hlam)]
    calc
      (successiveMinimum p i)⁻¹ * p (integralEmbed (v i)) ≤
          (successiveMinimum p i)⁻¹ * successiveMinimum p i :=
        mul_le_mul_of_nonneg_left (hvp i) (inv_nonneg.mpr hlam.le)
      _ = 1 := inv_mul_cancel₀ hlam.ne'
  have hcross := crosspolytope_volume_le_seminorm_unitBall p a v hv ha
  rw [show (∏ i, |a i|) = (∏ i, successiveMinimum p i)⁻¹ by
    simpa [a] using prod_abs_inv_successiveMinimum p hp] at hcross
  exact hcross

/-- Equivalent product form of the lower half:
`2^n / n! ≤ (∏ λ_i) * volume(B)`. -/
theorem minkowskiSecond_lower {n : ℕ} [Nonempty (Fin n)]
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      ENNReal.ofReal (∏ i, successiveMinimum p i) *
        MeasureTheory.volume {y | p y ≤ 1} := by
  let P : ℝ := ∏ i, successiveMinimum p i
  have hP : 0 < P := Finset.prod_pos fun i _ ↦ successiveMinimum_pos p hp i
  have hbase := minkowskiSecond_lower_volume p hp
  change ENNReal.ofReal P⁻¹ *
      ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
        MeasureTheory.volume {y | p y ≤ 1} at hbase
  have hcancel : ENNReal.ofReal P * ENNReal.ofReal P⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hP.le, mul_inv_cancel₀ hP.ne', ENNReal.ofReal_one]
  calc
    ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) =
        1 * ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) := by simp
    _ = (ENNReal.ofReal P * ENNReal.ofReal P⁻¹) *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) := by rw [hcancel]
    _ = ENNReal.ofReal P *
        (ENNReal.ofReal P⁻¹ *
          ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ))) := by
      rw [mul_assoc]
    _ ≤ ENNReal.ofReal P * MeasureTheory.volume {y | p y ≤ 1} := by
      gcongr

end Erdos186.CFP.Bilu.MinkowskiSecond
