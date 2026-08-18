/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MinimaAttainment
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecond
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Measure

/-!
# The upper half of Minkowski's second theorem

This module collects the discrete and measure-theoretic interface used by
the upper half of Minkowski's second theorem for the standard integer
lattice.  In particular it instantiates Mathlib's scaled-grid counting
theorem for the unit ball of a definite seminorm.  Thus a sharp asymptotic
lattice-point estimate immediately becomes the corresponding volume
estimate.
-/

namespace Erdos186.CFP.Bilu.MinkowskiUpper

open scoped BigOperators Pointwise
open Erdos186.CFP.Bilu.Mahler
open Erdos186.CFP.Bilu.MinkowskiSecond
open Filter MeasureTheory Module

/-- The closed unit ball of a seminorm. -/
def unitBall {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | p x ≤ 1}

@[simp]
theorem mem_unitBall {n : ℕ} {p : Seminorm ℝ (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ unitBall p ↔ p x ≤ 1 := Iff.rfl

/-- The seminorm unit ball is closed in the ambient Euclidean topology. -/
theorem isClosed_unitBall {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) :
    IsClosed (unitBall p) := by
  exact isClosed_le (seminorm_continuous_pi p) continuous_const

/-- The seminorm unit ball is measurable. -/
theorem measurableSet_unitBall {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) :
    MeasurableSet (unitBall p) :=
  (isClosed_unitBall p).measurableSet

/-- The seminorm unit ball is convex. -/
theorem convex_unitBall {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) :
    Convex ℝ (unitBall p) := by
  simpa [unitBall] using p.convexOn.convex_le (1 : ℝ)

/-- Definiteness makes the seminorm unit ball bounded in the ambient norm. -/
theorem isBounded_unitBall {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ))
    (hp : IsDefinite p) : Bornology.IsBounded (unitBall p) := by
  obtain ⟨c, hc, hcp⟩ := exists_pos_mul_norm_le_seminorm p hp
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨c⁻¹, fun x hx ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖x‖ = c⁻¹ * (c * ‖x‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ c⁻¹ * p x :=
      mul_le_mul_of_nonneg_left (hcp x) (le_of_lt (inv_pos.mpr hc))
    _ ≤ c⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hc))
    _ = c⁻¹ := mul_one _

/-- The frontier of a seminorm unit ball has zero Euclidean volume. -/
theorem volume_frontier_unitBall {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) :
    volume (frontier (unitBall p)) = 0 :=
  (convex_unitBall p).addHaar_frontier volume

/-- The standard copy of `ℤ^n` in real coordinate space. -/
def standardRealLattice (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

/-- Scaled-grid counts in a definite seminorm ball converge to its volume.

This is the exact asymptotic bridge needed by a lattice-counting proof of
the upper half of Minkowski's second theorem. -/
theorem tendsto_gridCard_div_pow_unitBall {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    Tendsto
      (fun m : ℕ ↦
        (Nat.card ↑(unitBall p ∩ (m : ℝ)⁻¹ • standardRealLattice n) : ℝ) /
          m ^ Fintype.card (Fin n))
      atTop (nhds (volume.real (unitBall p))) := by
  simpa [standardRealLattice] using
    (tendsto_card_div_pow_atTop_volume (unitBall p)
      (isBounded_unitBall p hp) (measurableSet_unitBall p)
      (volume_frontier_unitBall p))

/-- Any eventual upper bound for the normalized grid counts passes to the
Euclidean volume of the seminorm ball. -/
theorem volume_real_unitBall_le_of_eventually_gridCard_div_pow_le {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) {C : ℝ}
    (hC : ∀ᶠ m : ℕ in atTop,
      (Nat.card ↑(unitBall p ∩ (m : ℝ)⁻¹ • standardRealLattice n) : ℝ) /
          m ^ Fintype.card (Fin n) ≤ C) :
    volume.real (unitBall p) ≤ C := by
  exact le_of_tendsto (tendsto_gridCard_div_pow_unitBall p hp) hC

/-- Sharp normalized grid counting implies the real-valued upper half of
Minkowski's second theorem.  This isolates the one genuinely geometric
counting step from all limiting and positivity bookkeeping. -/
theorem upperMinkowskiSecond_real_of_eventually_gridCard_le {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (hcount : ∀ᶠ m : ℕ in atTop,
      (Nat.card ↑(unitBall p ∩ (m : ℝ)⁻¹ • standardRealLattice n) : ℝ) /
          m ^ Fintype.card (Fin n) ≤
        (2 : ℝ) ^ n / ∏ i, successiveMinimum p i) :
    (∏ i, successiveMinimum p i) * volume.real (unitBall p) ≤ (2 : ℝ) ^ n := by
  have hP : 0 < ∏ i, successiveMinimum p i :=
    Finset.prod_pos fun i _ ↦ successiveMinimum_pos p hp i
  have hvol : volume.real (unitBall p) ≤
      (2 : ℝ) ^ n / ∏ i, successiveMinimum p i :=
    volume_real_unitBall_le_of_eventually_gridCard_div_pow_le p hp hcount
  calc
    (∏ i, successiveMinimum p i) * volume.real (unitBall p) ≤
        (∏ i, successiveMinimum p i) *
          ((2 : ℝ) ^ n / ∏ i, successiveMinimum p i) :=
      mul_le_mul_of_nonneg_left hvol hP.le
    _ = (2 : ℝ) ^ n := by field_simp

end Erdos186.CFP.Bilu.MinkowskiUpper
