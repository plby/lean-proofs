/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.PotentialConvergence
import ErdosProblems.Erdos1165.PlanarLocalCLT
import ErdosProblems.Erdos1165.PotentialFourierIntegral

/-!
# Chronological convergence and radial bounds for the planar potential kernel

`PotentialConvergence.lean` proves absolute summability after grouping the
period-two walk into consecutive pairs.  This file proves that the ordinary
chronological finite sums converge to the same value.  For points in the odd
parity class the ungrouped series is not unconditionally summable, so the
correct statement is a limit of `Finset.range` partial sums.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos1165
namespace PotentialAsymptotic

open EndpointDiagonal PotentialKernel PotentialConvergence PotentialFourierIntegral

/-- Ordinary chronological potential truncation through time `N-1`. -/
noncomputable def potentialPartial (x : Point) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, potentialTerm x n

/-- At every even time the origin is a maximizer of the endpoint mass. -/
theorem potentialTerm_even_bounds (x : Point) (n : ℕ) :
    0 ≤ potentialTerm x (2 * n) ∧
      potentialTerm x (2 * n) ≤ planarReturnProbability n := by
  have hzero := endpointProbability_even_zero n
  have hxnonneg := endpointProbability_nonneg (2 * n) x
  by_cases hx : Even (x.1 + x.2)
  · have hformula := endpointProbability_even_eq_diagonalProductMass_of_even hx n
    have hloss := diagonalProductLoss_nonneg
      (firstDiagonalOffset x) (secondDiagonalOffset x) n
    unfold potentialTerm
    rw [hzero, hformula]
    unfold diagonalProductLoss at hloss
    rw [diagonalProductMass_center] at hloss
    constructor
    · exact hloss
    · linarith [show 0 ≤ diagonalProductMass n (firstDiagonalOffset x)
          (secondDiagonalOffset x) by
        unfold diagonalProductMass BinomialGaussian.evenSymmetricMass
          BinomialGaussian.symBinomialMass
        positivity]
  · unfold potentialTerm
    rw [endpointProbability_even_eq_zero_of_not_even hx]
    rw [hzero, sub_zero]
    exact ⟨(planarReturnProbability_pos n).le, le_rfl⟩

theorem tendsto_potentialTerm_even_zero (x : Point) :
    Tendsto (fun n : ℕ ↦ potentialTerm x (2 * n)) atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun n ↦ (potentialTerm_even_bounds x n).1)
    (Filter.Eventually.of_forall fun n ↦
      (potentialTerm_even_bounds x n).2.trans (planarReturnProbability_upper_bound n))
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The first `2m` chronological summands are exactly the first `m` paired
summands. -/
theorem potentialPartial_even (x : Point) (m : ℕ) :
    potentialPartial x (2 * m) = ∑ n ∈ Finset.range m, potentialPair x n := by
  induction m with
  | zero => simp [potentialPartial]
  | succ m ih =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
      rw [potentialPartial, Finset.sum_range_succ, Finset.sum_range_succ]
      rw [← potentialPartial, ih, Finset.sum_range_succ]
      unfold potentialPair
      ring

/-- The first `2m+1` summands consist of `m` pairs and the next even term. -/
theorem potentialPartial_odd (x : Point) (m : ℕ) :
    potentialPartial x (2 * m + 1) =
      (∑ n ∈ Finset.range m, potentialPair x n) + potentialTerm x (2 * m) := by
  rw [potentialPartial, Finset.sum_range_succ, ← potentialPartial, potentialPartial_even]

/-- Distance from the paired prefix with index `N/2`. -/
noncomputable def chronologicalRemainder (x : Point) (N : ℕ) : ℝ :=
  potentialPartial x N - ∑ n ∈ Finset.range (N / 2), potentialPair x n

theorem chronologicalRemainder_even (x : Point) (m : ℕ) :
    chronologicalRemainder x (2 * m) = 0 := by
  rw [chronologicalRemainder, potentialPartial_even]
  have hdiv : 2 * m / 2 = m := by omega
  rw [hdiv]
  ring

theorem chronologicalRemainder_odd (x : Point) (m : ℕ) :
    chronologicalRemainder x (2 * m + 1) = potentialTerm x (2 * m) := by
  rw [chronologicalRemainder, potentialPartial_odd]
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hdiv]
  ring

theorem abs_chronologicalRemainder_le (x : Point) (N : ℕ) :
    |chronologicalRemainder x N| ≤ 1 / (((N / 2 + 1 : ℕ) : ℝ)) := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' N
  · subst N
    rw [chronologicalRemainder_even]
    simp
    positivity
  · subst N
    rw [chronologicalRemainder_odd]
    have h := potentialTerm_even_bounds x m
    rw [abs_of_nonneg h.1]
    have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]
    simpa only [Nat.cast_add, Nat.cast_one] using
      h.2.trans (planarReturnProbability_upper_bound m)

theorem tendsto_chronologicalRemainder_zero (x : Point) :
    Tendsto (chronologicalRemainder x) atTop (nhds 0) := by
  have hbound : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (((N / 2 + 1 : ℕ) : ℝ)))
      atTop (nhds 0) := by
    have heq : (fun N : ℕ ↦ (1 : ℝ) / (((N / 2 + 1 : ℕ) : ℝ)) ) =
        (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) ∘ (fun N : ℕ ↦ N / 2) := by
      funext N
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    rw [heq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp
      (Nat.tendsto_div_const_atTop (by norm_num : 2 ≠ 0))
  have hnonneg : ∀ N : ℕ, 0 ≤ chronologicalRemainder x N := by
    intro N
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' N
    · subst N
      rw [chronologicalRemainder_even]
    · subst N
      rw [chronologicalRemainder_odd]
      exact (potentialTerm_even_bounds x m).1
  apply squeeze_zero'
    (Filter.Eventually.of_forall (hnonneg))
    (Filter.Eventually.of_forall fun N ↦
      (le_abs_self _).trans (abs_chronologicalRemainder_le x N))
    hbound

/-- The ordinary, chronological potential truncations converge.  This is the
standard infinite planar potential kernel statement, including the parity
class where the two ungrouped subseries diverge separately. -/
theorem tendsto_potentialPartial_planarPotentialKernel (x : Point) :
    Tendsto (potentialPartial x) atTop (nhds (planarPotentialKernel x)) := by
  have hpairs : Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Finset.range (N / 2), potentialPair x n)
      atTop (nhds (planarPotentialKernel x)) := by
    unfold planarPotentialKernel
    exact (summable_potentialPair x).hasSum.tendsto_sum_nat.comp
      (Nat.tendsto_div_const_atTop (by norm_num : 2 ≠ 0))
  have hsum := hpairs.add (tendsto_chronologicalRemainder_zero x)
  convert hsum using 1
  · funext N
    unfold chronologicalRemainder
    ring
  · simp

/-! ## Parity-uniform radial bounds -/

/-- At odd-parity points, the potential kernel is the average of its four
even-parity neighbors.  This is the infinite-sum form of the one-step
cancellation identity. -/
theorem planarPotentialKernel_eq_neighbor_average_of_not_even {x : Point}
    (hx : ¬Even (x.1 + x.2)) :
    planarPotentialKernel x = (1 / 4 : ℝ) * ∑ d : Direction,
      planarPotentialKernel (x - directionVector d) := by
  have hneighbors : Summable (fun n : ℕ ↦ ∑ d : Direction,
      potentialPair (x - directionVector d) n) := by
    apply summable_sum
    intro d hd
    exact summable_potentialPair_of_even (neighbor_even_of_not_even hx d)
  unfold planarPotentialKernel
  calc
    ∑' n, potentialPair x n =
        ∑' n, (1 / 4 : ℝ) * ∑ d : Direction,
          potentialPair (x - directionVector d) n := by
      apply tsum_congr
      exact potentialPair_eq_neighbor_average_of_not_even hx
    _ = (1 / 4 : ℝ) * ∑' n, ∑ d : Direction,
          potentialPair (x - directionVector d) n :=
      hneighbors.tsum_mul_left (1 / 4 : ℝ)
    _ = (1 / 4 : ℝ) * ∑ d : Direction, ∑' n,
          potentialPair (x - directionVector d) n := by
      rw [Summable.tsum_finsetSum]
      intro d hd
      exact summable_potentialPair_of_even (neighbor_even_of_not_even hx d)

/-- Exact odd-parity reduction to the four nonnegative diagonal-coordinate
potentials. -/
theorem planarPotentialKernel_eq_neighbor_diagonalPotential_of_not_even {x : Point}
    (hx : ¬Even (x.1 + x.2)) :
    planarPotentialKernel x = (1 / 4 : ℝ) * ∑ d : Direction,
      diagonalPotential (firstDiagonalOffset (x - directionVector d))
        (secondDiagonalOffset (x - directionVector d)) := by
  rw [planarPotentialKernel_eq_neighbor_average_of_not_even hx]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  exact planarPotentialKernel_eq_diagonalPotential_of_even
    (neighbor_even_of_not_even hx d)

/-- A logarithmic lower comparison which also has the correct value at the
origin, where both diagonal radii vanish. -/
noncomputable def diagonalLogLower (d e : ℕ) : ℝ :=
  if max d e = 0 then 0 else (1 / 4 : ℝ) * Real.log (max d e : ℝ)

/-- The explicit cubic-cutoff logarithmic upper comparison. -/
noncomputable def diagonalLogUpper (d e : ℕ) : ℝ :=
  2 + Real.log (radialCutoff d e : ℝ)

theorem diagonalLogLower_le_potential (d e : ℕ) :
    diagonalLogLower d e ≤ diagonalPotential d e := by
  by_cases hde : max d e = 0
  · simp [diagonalLogLower, hde, diagonalPotential_nonneg]
  · rw [diagonalLogLower, if_neg hde]
    exact diagonalPotential_log_lower hde

theorem diagonalPotential_le_logUpper (d e : ℕ) :
    diagonalPotential d e ≤ diagonalLogUpper d e := by
  exact diagonalPotential_log_upper d e

/-- Lower radial comparison on the whole lattice.  At odd-parity points it is
the average of the comparisons at the four even-parity neighbors. -/
noncomputable def pointLogLower (x : Point) : ℝ :=
  if Even (x.1 + x.2) then
    diagonalLogLower (firstDiagonalOffset x) (secondDiagonalOffset x)
  else
    (1 / 4 : ℝ) * ∑ d : Direction,
      diagonalLogLower (firstDiagonalOffset (x - directionVector d))
        (secondDiagonalOffset (x - directionVector d))

/-- Upper radial comparison on the whole lattice. -/
noncomputable def pointLogUpper (x : Point) : ℝ :=
  if Even (x.1 + x.2) then
    diagonalLogUpper (firstDiagonalOffset x) (secondDiagonalOffset x)
  else
    (1 / 4 : ℝ) * ∑ d : Direction,
      diagonalLogUpper (firstDiagonalOffset (x - directionVector d))
        (secondDiagonalOffset (x - directionVector d))

/-- Uniform explicit logarithmic comparison for the planar potential kernel,
with no parity restriction. -/
theorem pointLogLower_le_planarPotentialKernel_le_pointLogUpper (x : Point) :
    pointLogLower x ≤ planarPotentialKernel x ∧
      planarPotentialKernel x ≤ pointLogUpper x := by
  by_cases hx : Even (x.1 + x.2)
  · simp only [pointLogLower, pointLogUpper, if_pos hx]
    rw [planarPotentialKernel_eq_diagonalPotential_of_even hx]
    exact ⟨diagonalLogLower_le_potential _ _, diagonalPotential_le_logUpper _ _⟩
  · simp only [pointLogLower, pointLogUpper, if_neg hx]
    rw [planarPotentialKernel_eq_neighbor_diagonalPotential_of_not_even hx]
    constructor
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun d hd ↦ diagonalLogLower_le_potential _ _
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun d hd ↦ diagonalPotential_le_logUpper _ _

/-! ## Sharp uniform logarithmic asymptotic -/

/-- The diagonal series constructed by summability is definitionally the
Fourier-coordinate series estimated in `PotentialFourierIntegral`. -/
theorem diagonalPotential_eq_fourierPotential (d e : ℕ) :
    diagonalPotential d e = fourierPotential d e := by
  rfl

/-- The sharp logarithmic main term, extended by zero at diagonal radius
zero. -/
noncomputable def diagonalLogMain (d e : ℕ) : ℝ :=
  if max d e = 0 then 0
  else (2 / Real.pi) * Real.log (max d e : ℝ)

theorem diagonalPotential_zero : diagonalPotential 0 0 = 0 := by
  unfold diagonalPotential diagonalProductLoss diagonalProductMass
  simp

/-- Sharp diagonal estimate with a uniform absolute error, including the
zero-radius endpoint. -/
theorem abs_diagonalPotential_sub_logMain_le (d e : ℕ) :
    |diagonalPotential d e - diagonalLogMain d e| ≤ 100 := by
  by_cases hR : max d e = 0
  · have hd : d = 0 := by omega
    have he : e = 0 := by omega
    subst d
    subst e
    simp [diagonalLogMain, diagonalPotential_zero]
  · rw [diagonalLogMain, if_neg hR, diagonalPotential_eq_fourierPotential]
    exact diagonalPotential_log_asymptotic_bound (Nat.pos_of_ne_zero hR)

/-- The correct logarithmic main term at every lattice point.  Odd-parity
points inherit the average of the four adjacent even-coordinate main terms,
exactly matching the period-two cancellation identity. -/
noncomputable def pointLogMain (x : Point) : ℝ :=
  if Even (x.1 + x.2) then
    diagonalLogMain (firstDiagonalOffset x) (secondDiagonalOffset x)
  else
    (1 / 4 : ℝ) * ∑ d : Direction,
      diagonalLogMain (firstDiagonalOffset (x - directionVector d))
        (secondDiagonalOffset (x - directionVector d))

/-- **Sharp uniform planar potential asymptotic.**  The potential kernel is
within the absolute constant `100` of its parity-correct logarithmic main
term on the whole lattice. -/
theorem abs_planarPotentialKernel_sub_pointLogMain_le (x : Point) :
    |planarPotentialKernel x - pointLogMain x| ≤ 100 := by
  by_cases hx : Even (x.1 + x.2)
  · simp only [pointLogMain, if_pos hx]
    rw [planarPotentialKernel_eq_diagonalPotential_of_even hx]
    exact abs_diagonalPotential_sub_logMain_le _ _
  · simp only [pointLogMain, if_neg hx]
    rw [planarPotentialKernel_eq_neighbor_diagonalPotential_of_not_even hx]
    rw [show (1 / 4 : ℝ) * ∑ d : Direction,
          diagonalPotential (firstDiagonalOffset (x - directionVector d))
              (secondDiagonalOffset (x - directionVector d)) -
        (1 / 4 : ℝ) * ∑ d : Direction,
          diagonalLogMain (firstDiagonalOffset (x - directionVector d))
              (secondDiagonalOffset (x - directionVector d)) =
        (1 / 4 : ℝ) * ∑ d : Direction,
          (diagonalPotential (firstDiagonalOffset (x - directionVector d))
              (secondDiagonalOffset (x - directionVector d)) -
            diagonalLogMain (firstDiagonalOffset (x - directionVector d))
              (secondDiagonalOffset (x - directionVector d))) by
      rw [Finset.sum_sub_distrib]
      ring]
    calc
      |(1 / 4 : ℝ) * ∑ d : Direction,
          (diagonalPotential (firstDiagonalOffset (x - directionVector d))
              (secondDiagonalOffset (x - directionVector d)) -
            diagonalLogMain (firstDiagonalOffset (x - directionVector d))
              (secondDiagonalOffset (x - directionVector d)))| =
          (1 / 4 : ℝ) * |∑ d : Direction,
            (diagonalPotential (firstDiagonalOffset (x - directionVector d))
                (secondDiagonalOffset (x - directionVector d)) -
              diagonalLogMain (firstDiagonalOffset (x - directionVector d))
                (secondDiagonalOffset (x - directionVector d)))| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      _ ≤ (1 / 4 : ℝ) * ∑ _d : Direction, (100 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc
          |∑ d : Direction,
              (diagonalPotential (firstDiagonalOffset (x - directionVector d))
                  (secondDiagonalOffset (x - directionVector d)) -
                diagonalLogMain (firstDiagonalOffset (x - directionVector d))
                  (secondDiagonalOffset (x - directionVector d)))| ≤
              ∑ d : Direction,
                |diagonalPotential (firstDiagonalOffset (x - directionVector d))
                    (secondDiagonalOffset (x - directionVector d)) -
                  diagonalLogMain (firstDiagonalOffset (x - directionVector d))
                    (secondDiagonalOffset (x - directionVector d))| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _d : Direction, (100 : ℝ) := by
            exact Finset.sum_le_sum fun d hd ↦ abs_diagonalPotential_sub_logMain_le _ _
      _ = 100 := by norm_num

end PotentialAsymptotic
end Erdos1165
