/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerCoprimeInterpolation
import ErdosProblems.Erdos240.BakerSourceBudgetInequalities

/-!
# The literal outer product in the coprime-node completion

On the circle of radius `4R`, a target integer in `[1,R]` is at distance at
most `R` from every coprime node, whereas every boundary point is at
distance at least `3R`.  Thus every node contributes `1/3`; repetition with
the source multiplicity gives exactly the factor printed on p. 52.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerCoprimeOuterEstimate

open Metric
open InterpolationProducts BakerCoprimeInterpolation

/-- A point on the radius-`4R` circle is at least `3R` from every integer
node in `[1,R]`. -/
theorem three_mul_le_norm_sub_node_of_norm_eq_four_mul
    {R r : ℕ} {z : ℂ} (hr : r ≤ R)
    (hz : ‖z‖ = 4 * (R : ℝ)) :
    3 * (R : ℝ) ≤ ‖z - (r : ℂ)‖ := by
  have hrev : ‖z‖ - ‖(r : ℂ)‖ ≤ ‖z - (r : ℂ)‖ :=
    norm_sub_norm_le z (r : ℂ)
  rw [hz, Complex.norm_natCast] at hrev
  have hr' : (r : ℝ) ≤ R := by exact_mod_cast hr
  linarith

/-- Exact unpowered `3^{-#nodes}` outer ratio for the coprime grid. -/
theorem norm_coprimeNodalProduct_div_le_three_inv_pow
    {q R l : ℕ} (hR : 0 < R) (hl : l ≤ R)
    {z : ℂ} (hz : ‖z‖ = 4 * (R : ℝ)) :
    ‖coprimeNodalProduct q R 1 (l : ℂ)‖ /
        ‖coprimeNodalProduct q R 1 z‖ ≤
      (3 : ℝ)⁻¹ ^ (coprimeNodeIndices q R).card := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hbound := norm_coprimeNodalProduct_div_le
    (q := q) (R := R) (T := 1) (x := (l : ℂ)) (z := z)
    (A := (R : ℝ)) (B := 3 * (R : ℝ)) hRreal.le (by positivity)
    (fun i hi ↦ by
      have hiR : i + 1 ≤ R := by
        rw [mem_coprimeNodeIndices] at hi
        omega
      exact norm_natCast_sub_natCast_le hl hiR)
    (fun i hi ↦ by
      have hiR : i + 1 ≤ R := by
        rw [mem_coprimeNodeIndices] at hi
        omega
      exact three_mul_le_norm_sub_node_of_norm_eq_four_mul hiR hz)
  have hratio : (R : ℝ) / (3 * (R : ℝ)) = (3 : ℝ)⁻¹ := by
    have hRne : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp
  simpa only [Nat.mul_one, hratio] using hbound

/-- Hermite-multiplicity form of the exact coprime outer ratio. -/
theorem norm_coprimeNodalProduct_div_le_three_inv_pow_mul
    {q R T l : ℕ} (hR : 0 < R) (hl : l ≤ R)
    {z : ℂ} (hz : ‖z‖ = 4 * (R : ℝ)) :
    ‖coprimeNodalProduct q R T (l : ℂ)‖ /
        ‖coprimeNodalProduct q R T z‖ ≤
      ((3 : ℝ)⁻¹ ^ (coprimeNodeIndices q R).card) ^ T := by
  exact norm_coprimeNodalProduct_div_le_source_power
    (norm_coprimeNodalProduct_div_le_three_inv_pow hR hl hz)

/-- With prime `q` and a complete residue-block radius, the exponent is
literally `R(q-1)/q`, as in the source. -/
theorem norm_coprimeNodalProduct_div_le_source_three_power
    {q R T l : ℕ} (hq : q.Prime) (hqR : q ∣ R)
    (hR : 0 < R) (hl : l ≤ R)
    {z : ℂ} (hz : ‖z‖ = 4 * (R : ℝ)) :
    ‖coprimeNodalProduct q R T (l : ℂ)‖ /
        ‖coprimeNodalProduct q R T z‖ ≤
      ((3 : ℝ)⁻¹ ^ (R * (q - 1) / q)) ^ T := by
  apply norm_coprimeNodalProduct_div_le_source_power_of_prime_of_dvd hq hqR
  rw [← card_coprimeNodeIndices_of_prime_of_dvd hq hqR]
  exact norm_coprimeNodalProduct_div_le_three_inv_pow hR hl hz

/-- Source-level specialization with the literal predecessor quarter-budget.
The right side is the exact factor consumed by the numerical p. 52 lemma. -/
theorem norm_successor_coprimeNodalProduct_div_le_source_factor
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) (J l : ℕ) (hl : l ≤ P.R (J + 1))
    {z : ℂ} (hz : ‖z‖ = 4 * (P.R (J + 1) : ℝ)) :
    ‖coprimeNodalProduct P.q (P.R (J + 1)) (P.Sstep J / 4) (l : ℂ)‖ /
        ‖coprimeNodalProduct P.q (P.R (J + 1)) (P.Sstep J / 4) z‖ ≤
      ((3 : ℝ)⁻¹ ^
        (P.R (J + 1) * (P.q - 1) / P.q)) ^ (P.Sstep J / 4) := by
  exact norm_coprimeNodalProduct_div_le_source_three_power
    P.q_prime (P.q_dvd_R_succ J) (P.R_pos (J + 1)) hl hz

end Erdos240.BakerCoprimeOuterEstimate

#print axioms Erdos240.BakerCoprimeOuterEstimate.norm_coprimeNodalProduct_div_le_three_inv_pow
#print axioms Erdos240.BakerCoprimeOuterEstimate.norm_successor_coprimeNodalProduct_div_le_source_factor
