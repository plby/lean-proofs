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

import ErdosProblems.Erdos1165.GreenProbability
import ErdosProblems.Erdos1165.PlanarLocalCLT
import ErdosProblems.Erdos1165.PotentialAsymptotic
import ErdosProblems.Erdos1165.PotentialFourierIntegral
import ErdosProblems.Erdos1165.AnnulusHarnack

/-!
# Explicit killed-disc Green bounds

This file connects the sharp, uniform potential-kernel estimate to the
probabilistic killed Green function.  The first part records the exact
identification between the two independently developed diagonal potential
series.  The second part proves the discrete Poisson equation for the
chronological planar potential kernel.  The final part applies finite Dynkin
and the geometric exit tail to obtain quantitative Green and hitting bounds.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos1165
namespace GreenAsymptotic

open Annulus AnnulusHarnack ExitTail GreenFunction GreenProbability
open PlanarPotential PotentialKernel PotentialConvergence PotentialAsymptotic
open PotentialFourierIntegral
open EndpointDiagonal

noncomputable section

/-! ## Identifying the sharp Fourier potential with the chronological one -/

lemma fourierProductMass_eq_diagonalProductMass (n d e : ℕ) :
    fourierProductMass n d e = diagonalProductMass n d e := by
  rfl

lemma fourierProductLoss_eq_diagonalProductLoss (d e n : ℕ) :
    fourierProductLoss d e n = diagonalProductLoss d e n := by
  rfl

lemma fourierPotential_eq_diagonalPotential (d e : ℕ) :
    fourierPotential d e = diagonalPotential d e := by
  unfold fourierPotential diagonalPotential
  apply tsum_congr
  exact fourierProductLoss_eq_diagonalProductLoss d e

/-- Sharp uniform logarithmic estimate for the diagonal potential used by
`planarPotentialKernel`. -/
theorem diagonalPotential_log_bound {d e : ℕ} (hR : 0 < max d e) :
    |diagonalPotential d e -
        (2 / Real.pi) * Real.log (max d e : ℝ)| ≤ 100 := by
  rw [← fourierPotential_eq_diagonalPotential]
  exact diagonalPotential_log_asymptotic_bound hR

/-- Sharp pointwise estimate at every nonzero even-parity lattice point. -/
theorem planarPotentialKernel_log_bound_of_even {x : Point}
    (hxpar : Even (x.1 + x.2)) (hx0 : x ≠ 0) :
    |planarPotentialKernel x -
        (2 / Real.pi) * Real.log
          (max (firstDiagonalOffset x) (secondDiagonalOffset x) : ℝ)| ≤ 100 := by
  rw [planarPotentialKernel_eq_diagonalPotential_of_even hxpar]
  apply diagonalPotential_log_bound
  rw [Nat.pos_iff_ne_zero]
  intro hzero
  have hfirst : firstDiagonalOffset x = 0 := by omega
  have hsecond : secondDiagonalOffset x = 0 := by omega
  obtain ⟨a, ha⟩ := hxpar
  let b : ℤ := x.1 - a
  have hb : x.1 - x.2 = b + b := by
    dsimp [b]
    omega
  have hfirst_eq : firstDiagonalOffset x = a.natAbs := by
    rw [firstDiagonalOffset, ha, natAbs_add_self_div_two]
  have hsecond_eq : secondDiagonalOffset x = b.natAbs := by
    rw [secondDiagonalOffset, hb, natAbs_add_self_div_two]
  rw [hfirst_eq] at hfirst
  rw [hsecond_eq] at hsecond
  have ha0 : a = 0 := Int.natAbs_eq_zero.mp hfirst
  have hb0 : b = 0 := Int.natAbs_eq_zero.mp hsecond
  apply hx0
  ext <;> dsimp [b] at hb0 ⊢ <;> omega

/-! ## The Poisson equation for the potential kernel -/

lemma sum_endpointProbability_neighbor (N : ℕ) (x : Point) :
    ∑ d : Direction, endpointProbability N (neighbor x d) =
      ∑ d : Direction, endpointProbability N (x - directionVector d) := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [neighbor, directionVector]
  have h₀ : x + (1, 0) = x - (-1, 0) := by ext <;> simp
  have h₁ : x + (-1, 0) = x - (1, 0) := by ext <;> simp <;> ring
  have h₂ : x + (0, 1) = x - (0, -1) := by ext <;> simp
  have h₃ : x + (0, -1) = x - (0, 1) := by ext <;> simp <;> ring
  rw [h₀, h₁, h₂, h₃]
  ring

lemma neighborAverage_potentialPartial (x : Point) (N : ℕ) :
    neighborAverage (fun z ↦ potentialPartial z N) x - potentialPartial x N =
      (if x = 0 then 1 else 0) - endpointProbability N x := by
  have havg : neighborAverage (fun z ↦ potentialPartial z N) x =
      (∑ n ∈ Finset.range N, endpointProbability n 0) -
        ∑ n ∈ Finset.range N, endpointProbability (n + 1) x := by
    unfold neighborAverage potentialPartial potentialTerm
    simp_rw [Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show ∑ d : Direction, ∑ n ∈ Finset.range N,
        endpointProbability n (neighbor x d) =
        ∑ n ∈ Finset.range N, ∑ d : Direction,
          endpointProbability n (neighbor x d) by rw [Finset.sum_comm]]
    rw [show ∑ n ∈ Finset.range N, ∑ d : Direction,
        endpointProbability n (neighbor x d) =
        ∑ n ∈ Finset.range N, 4 * endpointProbability (n + 1) x by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sum_endpointProbability_neighbor, endpointProbability_succ]
      ring]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    norm_num
    ring
  have hzero : endpointProbability 0 0 = 1 := by
    simp [endpointProbability, endpointBlocks, blockDisplacement]
  have hx : endpointProbability 0 x = if x = 0 then 1 else 0 := by
    by_cases h : x = 0
    · subst x
      simp [hzero]
    · have hnorm : 0 < manhattanNorm x :=
        Nat.pos_of_ne_zero fun hz ↦ h (manhattanNorm_eq_zero_iff x |>.mp hz)
      rw [endpointProbability_eq_zero_of_lt hnorm, if_neg h]
  rw [havg]
  unfold potentialPartial potentialTerm
  simp_rw [Finset.sum_sub_distrib]
  have hshift : endpointProbability 0 x +
      ∑ n ∈ Finset.range N, endpointProbability (n + 1) x =
      ∑ n ∈ Finset.range (N + 1), endpointProbability n x := by
    simpa [add_comm] using (Finset.sum_range_succ' (endpointProbability · x) N).symm
  have hlast : ∑ n ∈ Finset.range (N + 1), endpointProbability n x =
      (∑ n ∈ Finset.range N, endpointProbability n x) +
        endpointProbability N x := Finset.sum_range_succ _ N
  rw [← hshift] at hlast
  rw [hx] at hlast
  linarith

lemma endpointProbability_even_le (x : Point) (n : ℕ) :
    endpointProbability (2 * n) x ≤ 1 / (n + 1 : ℝ) := by
  have hnonneg := (potentialTerm_even_bounds x n).1
  have hreturn := planarReturnProbability_upper_bound n
  rw [← endpointProbability_even_zero] at hreturn
  unfold potentialTerm at hnonneg
  linarith

lemma endpointProbability_odd_le (x : Point) (n : ℕ) :
    endpointProbability (2 * n + 1) x ≤ 1 / (n + 1 : ℝ) := by
  rw [show 2 * n + 1 = 2 * n + 1 by rfl, endpointProbability_succ]
  calc
    (1 / 4 : ℝ) * ∑ d : Direction,
        endpointProbability (2 * n) (x - directionVector d) ≤
        (1 / 4 : ℝ) * ∑ _d : Direction, (1 / (n + 1 : ℝ)) := by
      gcongr with d
      exact endpointProbability_even_le _ n
    _ = 1 / (n + 1 : ℝ) := by simp

lemma endpointProbability_le_two_div (x : Point) (N : ℕ) :
    endpointProbability N x ≤ 2 / (N + 1 : ℝ) := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' N
  · have h := endpointProbability_even_le x n
    have hn : (0 : ℝ) < n + 1 := by positivity
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h ⊢
    calc
      endpointProbability (2 * n) x ≤ 1 / (n + 1 : ℝ) := h
      _ ≤ 2 / (2 * n + 1 : ℝ) := by
        rw [div_le_div_iff₀ hn (by positivity)]
        nlinarith
  · have h := endpointProbability_odd_le x n
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h ⊢
    convert h using 1
    field_simp
    ring

theorem tendsto_endpointProbability_zero (x : Point) :
    Tendsto (fun N ↦ endpointProbability N x) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (endpointProbability_nonneg · x)
  · exact Filter.Eventually.of_forall (endpointProbability_le_two_div x)
  · convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2 using 1
    · funext N
      ring
    · ring

theorem drift_planarPotentialKernel (x : Point) :
    drift planarPotentialKernel x = if x = 0 then 1 else 0 := by
  have hpartial := neighborAverage_potentialPartial x
  have havg : Tendsto
      (fun N ↦ neighborAverage (fun z ↦ potentialPartial z N) x)
      atTop (nhds (neighborAverage planarPotentialKernel x)) := by
    unfold neighborAverage
    apply Tendsto.div_const
    apply tendsto_finset_sum
    intro d hd
    exact tendsto_potentialPartial_planarPotentialKernel (neighbor x d)
  have hself := tendsto_potentialPartial_planarPotentialKernel x
  have hleft := havg.sub hself
  have hright : Tendsto
      (fun N ↦ (if x = 0 then (1 : ℝ) else 0) - endpointProbability N x)
      atTop (nhds ((if x = 0 then (1 : ℝ) else 0) - 0)) :=
    tendsto_const_nhds.sub (tendsto_endpointProbability_zero x)
  have heq : (fun N ↦ neighborAverage (fun z ↦ potentialPartial z N) x -
      potentialPartial x N) =
      fun N ↦ (if x = 0 then 1 else 0) - endpointProbability N x := by
    funext N
    exact hpartial N
  rw [heq] at hleft
  change neighborAverage planarPotentialKernel x - planarPotentialKernel x = _
  simpa using tendsto_nhds_unique hleft hright

theorem drift_translate_planarPotentialKernel (x y : Point) :
    drift (fun z ↦ planarPotentialKernel (z - y)) x =
      if x = y then 1 else 0 := by
  have havg : neighborAverage (fun z ↦ planarPotentialKernel (z - y)) x =
      neighborAverage planarPotentialKernel (x - y) := by
    have hpoint (d : Direction) : neighbor x d - y = neighbor (x - y) d := by
      unfold neighbor
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub,
        Prod.snd_sub]
      all_goals ring
    unfold neighborAverage
    simp_rw [hpoint]
  unfold drift
  rw [havg]
  have h := drift_planarPotentialKernel (x - y)
  unfold drift at h
  simpa [sub_eq_zero] using h

/-! ## Finite Dynkin identity in Green-function form -/

/-- Real indicator of one lattice point. -/
def pointIndicator (y z : Point) : ℝ := if z = y then 1 else 0

lemma drift_translate_eq_pointIndicator (y : Point) :
    drift (fun z ↦ planarPotentialKernel (z - y)) = pointIndicator y := by
  funext x
  rw [drift_translate_planarPotentialKernel]
  rfl

lemma killedPower_planar_ne_top (D : Finset Point) (N : ℕ) (x y : Point) :
    killedPower planarKernel D N x y ≠ ⊤ := by
  rw [← fairSteps_killedPathEvent]
  exact measure_ne_top fairSteps _

lemma planarFiniteGreen_ne_top (D : Finset Point) (N : ℕ) (x y : Point) :
    planarFiniteGreen D N x y ≠ ⊤ := by
  unfold GreenFunction.planarFiniteGreen GreenFunction.finiteGreen
  exact ENNReal.sum_ne_top.mpr fun n hn ↦ killedPower_planar_ne_top D n x y

lemma planarFiniteGreen_toReal_succ_left (D : Finset Point) (N : ℕ)
    {x : Point} (hx : x ∈ D) (y : Point) :
    (planarFiniteGreen D (N + 1) x y).toReal =
      pointIndicator y x +
        (∑ d : Direction,
          (planarFiniteGreen D N (neighbor x d) y).toReal) / 4 := by
  change (GreenFunction.finiteGreen planarKernel D (N + 1) x y).toReal = _
  rw [GreenFunction.finiteGreen_succ_left, if_pos hx]
  rw [sum_planarKernel_mul_of_zero_outside D x
    (fun z ↦ planarFiniteGreen D N z y)
    (fun z hz ↦ by
      unfold GreenFunction.planarFiniteGreen GreenFunction.finiteGreen
      simp [killedPower_eq_zero_of_notMem_left planarKernel D hz])]
  have hzero : killedPower planarKernel D 0 x y ≠ ⊤ :=
    killedPower_planar_ne_top D 0 x y
  have hterm : ∀ d ∈ (Finset.univ : Finset Direction),
      (1 / 4 : ℝ≥0∞) * planarFiniteGreen D N (x + directionVector d) y ≠ ⊤ := by
    intro d hd
    exact ENNReal.mul_ne_top (by finiteness)
      (planarFiniteGreen_ne_top D N (x + directionVector d) y)
  have hsum : (∑ d : Direction,
      (1 / 4 : ℝ≥0∞) * planarFiniteGreen D N (x + directionVector d) y) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr hterm
  rw [ENNReal.toReal_add hzero hsum, ENNReal.toReal_sum hterm]
  simp only [ENNReal.toReal_mul]
  have hquarter : (1 / 4 : ℝ≥0∞).toReal = (1 / 4 : ℝ) := by norm_num
  rw [hquarter]
  have hsumreal : (∑ d : Direction, (1 / 4 : ℝ) *
      (planarFiniteGreen D N (x + directionVector d) y).toReal) =
      (∑ d : Direction,
        (planarFiniteGreen D N (neighbor x d) y).toReal) / 4 := by
    unfold neighbor
    rw [← Finset.mul_sum]
    ring
  simp only [pointIndicator, killedPower_zero]
  by_cases hxy : x = y
  · subst x
    simp [hx]
    simpa [one_div] using hsumreal
  · simp [hxy]
    simpa [one_div] using hsumreal

lemma planarFiniteGreen_eq_zero_of_notMem_left (D : Finset Point) (N : ℕ)
    {x : Point} (hx : x ∉ D) (y : Point) : planarFiniteGreen D N x y = 0 := by
  unfold GreenFunction.planarFiniteGreen GreenFunction.finiteGreen
  simp [killedPower_eq_zero_of_notMem_left planarKernel D hx]

/-- The stopped occupation of `y` through times `0,...,N` is exactly the
real value of the killed Green sum through time `N`. -/
theorem stoppedOccupation_pointIndicator_eq_planarFiniteGreen
    (D : Finset Point) (N : ℕ) (x y : Point) :
    stoppedOccupation D (N + 1) (pointIndicator y) x =
      (planarFiniteGreen D N x y).toReal := by
  induction N generalizing x with
  | zero =>
      by_cases hx : x ∈ D
      · rw [stoppedOccupation_succ_of_mem D hx]
        by_cases hxy : x = y
        · subst x
          simp [GreenFunction.planarFiniteGreen, GreenFunction.finiteGreen,
            killedPower, pointIndicator, hx]
        · simp [GreenFunction.planarFiniteGreen, GreenFunction.finiteGreen,
            killedPower, pointIndicator, hx, hxy]
      · rw [stoppedOccupation_of_notMem D hx]
        rw [planarFiniteGreen_eq_zero_of_notMem_left D 0 hx]
        simp
  | succ N ih =>
      by_cases hx : x ∈ D
      · rw [show N + 1 + 1 = (N + 1) + 1 by rfl,
          stoppedOccupation_succ_of_mem D hx]
        simp_rw [ih]
        exact (planarFiniteGreen_toReal_succ_left D N hx y).symm
      · rw [stoppedOccupation_of_notMem D hx]
        rw [planarFiniteGreen_eq_zero_of_notMem_left D (N + 1) hx]
        simp

/-- Exact bounded-horizon potential/Green identity. -/
theorem stoppedExpectation_potential_eq_add_finiteGreen
    (D : Finset Point) (N : ℕ) (x y : Point) :
    stoppedExpectation D (N + 1)
        (fun z ↦ planarPotentialKernel (z - y)) x =
      planarPotentialKernel (x - y) +
        (planarFiniteGreen D N x y).toReal := by
  rw [finite_dynkin, drift_translate_eq_pointIndicator,
    stoppedOccupation_pointIndicator_eq_planarFiniteGreen]

/-! ## Passage to the exit-potential limit -/

theorem stoppedExpectation_le_of_mem_or_outerBoundary
    (D : Finset Point) {f : Point → ℝ} {C : ℝ}
    (hf : ∀ z, z ∈ D ∨ z ∈ outerBoundary D → f z ≤ C)
    (n : ℕ) {x : Point} (hx : x ∈ D ∨ x ∈ outerBoundary D) :
    stoppedExpectation D n f x ≤ C := by
  induction n generalizing x with
  | zero => exact hf x hx
  | succ n ih =>
      by_cases hxD : x ∈ D
      · rw [stoppedExpectation_succ]
        calc
          (∑ d : Direction,
              stoppedExpectation D n f (absorbedStep D x d)) / 4 ≤
              (∑ _d : Direction, C) / 4 := by
            gcongr with d
            rw [absorbedStep_of_mem D hxD]
            apply ih
            by_cases hneighbor : neighbor x d ∈ D
            · exact Or.inl hneighbor
            · exact Or.inr (neighbor_mem_outerBoundary D hxD hneighbor)
          _ = C := by simp
      · rw [stoppedExpectation_of_notMem D hxD]
        exact hf x hx

theorem stoppedExpectation_lower_of_mem_or_outerBoundary
    (D : Finset Point) {f : Point → ℝ} {C : ℝ}
    (hf : ∀ z, z ∈ D ∨ z ∈ outerBoundary D → C ≤ f z)
    (n : ℕ) {x : Point} (hx : x ∈ D ∨ x ∈ outerBoundary D) :
    C ≤ stoppedExpectation D n f x := by
  induction n generalizing x with
  | zero => exact hf x hx
  | succ n ih =>
      by_cases hxD : x ∈ D
      · rw [stoppedExpectation_succ]
        calc
          C = (∑ _d : Direction, C) / 4 := by simp
          _ ≤ (∑ d : Direction,
              stoppedExpectation D n f (absorbedStep D x d)) / 4 := by
            gcongr with d
            rw [absorbedStep_of_mem D hxD]
            apply ih
            by_cases hneighbor : neighbor x d ∈ D
            · exact Or.inl hneighbor
            · exact Or.inr (neighbor_mem_outerBoundary D hxD hneighbor)
      · rw [stoppedExpectation_of_notMem D hxD]
        exact hf x hx

theorem tendsto_stoppedExpectation_potential_of_finite
    (D : Finset Point) (x y : Point)
    (hfinite : infiniteGreen D x y ≠ ⊤) :
    Tendsto
      (fun N ↦ stoppedExpectation D (N + 1)
        (fun z ↦ planarPotentialKernel (z - y)) x)
      atTop (nhds (planarPotentialKernel (x - y) +
        (infiniteGreen D x y).toReal)) := by
  have hgreen : Tendsto
      (fun N ↦ (planarFiniteGreen D N x y).toReal) atTop
      (nhds (infiniteGreen D x y).toReal) :=
    (ENNReal.tendsto_toReal hfinite).comp
      (tendsto_planarFiniteGreen D x y)
  have hadd : Tendsto
      (fun N ↦ planarPotentialKernel (x - y) +
        (planarFiniteGreen D N x y).toReal) atTop
      (nhds (planarPotentialKernel (x - y) +
        (infiniteGreen D x y).toReal)) :=
    tendsto_const_nhds.add hgreen
  convert hadd using 1
  funext N
  exact stoppedExpectation_potential_eq_add_finiteGreen D N x y

theorem tendsto_stoppedExpectation_potential_closedDisc
    (R : ℕ) (x y : Point) :
    Tendsto
      (fun N ↦ stoppedExpectation (closedDisc R) (N + 1)
        (fun z ↦ planarPotentialKernel (z - y)) x)
      atTop (nhds (planarPotentialKernel (x - y) +
        (infiniteGreen (closedDisc R) x y).toReal)) := by
  apply tendsto_stoppedExpectation_potential_of_finite
  apply infiniteGreen_ne_top_of_subset_coordinateBox (closedDisc R) R
  intro z hz
  exact (mem_closedDisc R z).mp hz |>.1

/-- Abstract upper Green bound obtained by bounding the potential on the
disc and its one-step outer boundary. -/
theorem infiniteGreen_toReal_le_of_potential_le
    (R : ℕ) {x y : Point} (hx : x ∈ closedDisc R) {U : ℝ}
    (hU : ∀ z, z ∈ closedDisc R ∨ z ∈ outerBoundary (closedDisc R) →
      planarPotentialKernel (z - y) ≤ U) :
    (infiniteGreen (closedDisc R) x y).toReal ≤
      U - planarPotentialKernel (x - y) := by
  have hlim := tendsto_stoppedExpectation_potential_closedDisc R x y
  have hbound : ∀ N, stoppedExpectation (closedDisc R) (N + 1)
      (fun z ↦ planarPotentialKernel (z - y)) x ≤ U := fun N ↦
    stoppedExpectation_le_of_mem_or_outerBoundary (closedDisc R) hU (N + 1)
      (Or.inl hx)
  have hle := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  linarith

/-- Abstract lower Green bound obtained by bounding the potential on the
disc and its one-step outer boundary. -/
theorem potentialLower_sub_le_infiniteGreen_toReal
    (R : ℕ) {x y : Point} (hx : x ∈ closedDisc R) {L : ℝ}
    (hL : ∀ z, z ∈ closedDisc R ∨ z ∈ outerBoundary (closedDisc R) →
      L ≤ planarPotentialKernel (z - y)) :
    L - planarPotentialKernel (x - y) ≤
      (infiniteGreen (closedDisc R) x y).toReal := by
  have hlim := tendsto_stoppedExpectation_potential_closedDisc R x y
  have hbound : ∀ N, L ≤ stoppedExpectation (closedDisc R) (N + 1)
      (fun z ↦ planarPotentialKernel (z - y)) x := fun N ↦
    stoppedExpectation_lower_of_mem_or_outerBoundary (closedDisc R) hL (N + 1)
      (Or.inl hx)
  have hle := ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  linarith

/-! ## Boundary-only lower bounds -/

/-- The planar potential kernel is nonnegative at every lattice point.  On
the even parity class this is diagonal-potential positivity; on the odd class
it is the average of four such values. -/
theorem planarPotentialKernel_nonneg (z : Point) :
    0 ≤ planarPotentialKernel z := by
  by_cases hz : Even (z.1 + z.2)
  · rw [planarPotentialKernel_eq_diagonalPotential_of_even hz]
    exact diagonalPotential_nonneg _ _
  · rw [planarPotentialKernel_eq_neighbor_diagonalPotential_of_not_even hz]
    exact mul_nonneg (by norm_num) <|
      Finset.sum_nonneg fun d _ ↦ diagonalPotential_nonneg _ _

/-- Monotonicity of the exact finite stopped expectation. -/
theorem stoppedExpectation_mono
    (D : Finset Point) {f g : Point → ℝ} (hfg : ∀ z, f z ≤ g z)
    (n : ℕ) (x : Point) :
    stoppedExpectation D n f x ≤ stoppedExpectation D n g x := by
  induction n generalizing x with
  | zero => exact hfg x
  | succ n ih =>
      rw [stoppedExpectation_succ, stoppedExpectation_succ]
      gcongr with d
      exact ih _

/-- Scalar multiplication commutes with the exact finite stopped
expectation. -/
theorem stoppedExpectation_const_mul
    (D : Finset Point) (c : ℝ) (f : Point → ℝ) (n : ℕ) (x : Point) :
    stoppedExpectation D n (fun z ↦ c * f z) x =
      c * stoppedExpectation D n f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [stoppedExpectation_succ, stoppedExpectation_succ]
      simp_rw [ih]
      rw [← Finset.mul_sum]
      ring

/-- Total killed mass remaining in the domain at one fixed time. -/
def planarKilledMass (D : Finset Point) (n : ℕ) (x : Point) : ℝ≥0∞ :=
  ∑ y ∈ D, killedPower planarKernel D n x y

lemma planarKilledMass_ne_top (D : Finset Point) (n : ℕ) (x : Point) :
    planarKilledMass D n x ≠ ⊤ := by
  unfold planarKilledMass
  exact ENNReal.sum_ne_top.mpr fun y hy ↦ killedPower_planar_ne_top D n x y

lemma planarKilledMass_succ_of_mem (D : Finset Point) (n : ℕ)
    {x : Point} (hx : x ∈ D) :
    planarKilledMass D (n + 1) x =
      ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
        planarKilledMass D n (neighbor x d) := by
  unfold planarKilledMass
  simp_rw [killedPower_succ, if_pos hx]
  calc
    (∑ y ∈ D, ∑ z ∈ D,
        planarKernel x z * killedPower planarKernel D n z y) =
        ∑ z ∈ D, planarKernel x z *
          (∑ y ∈ D, killedPower planarKernel D n z y) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
          (∑ y ∈ D,
            killedPower planarKernel D n (x + directionVector d) y) := by
      apply sum_planarKernel_mul_of_zero_outside D x
      intro z hz
      simp [killedPower_eq_zero_of_notMem_left planarKernel D hz]
    _ = ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
          (∑ y ∈ D, killedPower planarKernel D n (neighbor x d) y) := by
      rfl

/-- The stopped expectation of the domain indicator is exactly the real
surviving killed mass. -/
theorem stoppedExpectation_interiorIndicator_eq_planarKilledMass
    (D : Finset Point) (n : ℕ) (x : Point) :
    stoppedExpectation D n (fun z ↦ if z ∈ D then 1 else 0) x =
      (planarKilledMass D n x).toReal := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ D
      · simp [planarKilledMass, killedPower, hx]
      · simp [planarKilledMass, killedPower, hx]
  | succ n ih =>
      by_cases hx : x ∈ D
      · rw [stoppedExpectation_succ, planarKilledMass_succ_of_mem D n hx]
        simp_rw [absorbedStep_of_mem D hx]
        have hterm : ∀ d ∈ (Finset.univ : Finset Direction),
            (1 / 4 : ℝ≥0∞) * planarKilledMass D n (neighbor x d) ≠ ⊤ := by
          intro d hd
          exact ENNReal.mul_ne_top (by finiteness)
            (planarKilledMass_ne_top D n (neighbor x d))
        rw [ENNReal.toReal_sum hterm]
        simp only [ENNReal.toReal_mul]
        have hquarter : (1 / 4 : ℝ≥0∞).toReal = (1 / 4 : ℝ) := by norm_num
        rw [hquarter]
        simp_rw [← ih]
        rw [← Finset.mul_sum]
        ring
      · rw [stoppedExpectation_of_notMem D hx]
        simp [planarKilledMass, hx]

/-- At every finite horizon, boundary exit mass plus surviving interior mass
is one, provided the starting point is in the domain or on its outer
boundary. -/
theorem finiteExitMass_add_planarKilledMass_toReal_eq_one
    (D : Finset Point) (n : ℕ) {x : Point}
    (hx : x ∈ D ∨ x ∈ outerBoundary D) :
    finiteExitMass D (outerBoundary D) n x +
      (planarKilledMass D n x).toReal = 1 := by
  rw [← stoppedExpectation_interiorIndicator_eq_planarKilledMass]
  induction n generalizing x with
  | zero =>
      rcases hx with hxD | hxB
      · have hxB' : x ∉ outerBoundary D := fun h ↦
          (mem_outerBoundary D x).mp h |>.1 hxD
        simp [finiteExitMass, boundaryIndicator, hxD, hxB']
      · have hxD : x ∉ D := (mem_outerBoundary D x).mp hxB |>.1
        simp [finiteExitMass, boundaryIndicator, hxD, hxB]
  | succ n ih =>
      by_cases hxD : x ∈ D
      · rw [finiteExitMass, stoppedExpectation_succ, stoppedExpectation_succ]
        simp_rw [absorbedStep_of_mem D hxD]
        rw [← add_div, ← Finset.sum_add_distrib]
        calc
          (∑ d : Direction,
              (stoppedExpectation D n (boundaryIndicator (outerBoundary D))
                  (neighbor x d) +
                stoppedExpectation D n (fun z ↦ if z ∈ D then 1 else 0)
                  (neighbor x d))) / 4 =
              (∑ _d : Direction, (1 : ℝ)) / 4 := by
            congr 1
            apply Finset.sum_congr rfl
            intro d hd
            apply ih
            by_cases hn : neighbor x d ∈ D
            · exact Or.inl hn
            · exact Or.inr (neighbor_mem_outerBoundary D hxD hn)
          _ = 1 := by simp
      · have hxB : x ∈ outerBoundary D := hx.resolve_left hxD
        rw [finiteExitMass, stoppedExpectation_of_notMem D hxD,
          stoppedExpectation_of_notMem D hxD]
        simp [boundaryIndicator, hxB, hxD]

/-- In a finite closed disc, total killed mass at time `n` tends to zero. -/
theorem tendsto_planarKilledMass_closedDisc_zero
    (R : ℕ) (x : Point) :
    Tendsto (fun n ↦ planarKilledMass (closedDisc R) n x) atTop (nhds 0) := by
  unfold planarKilledMass
  have hterm : ∀ y ∈ closedDisc R,
      Tendsto (fun n ↦ killedPower planarKernel (closedDisc R) n x y)
        atTop (nhds 0) := by
    intro y hy
    apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
    simpa [infiniteGreen] using
      infiniteGreen_ne_top_of_subset_coordinateBox (closedDisc R) R x y
        (fun z hz ↦ (mem_closedDisc R z).mp hz |>.1)
  simpa using tendsto_finset_sum (closedDisc R) hterm

theorem tendsto_planarKilledMass_toReal_closedDisc_zero
    (R : ℕ) (x : Point) :
    Tendsto (fun n ↦ (planarKilledMass (closedDisc R) n x).toReal)
      atTop (nhds 0) := by
  change Tendsto (ENNReal.toReal ∘
      fun n ↦ planarKilledMass (closedDisc R) n x) atTop
    (nhds (ENNReal.toReal 0))
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_planarKilledMass_closedDisc_zero R x)

/-- The real value of `exitMass` is the supremum of the finite real exit
masses. -/
theorem exitMass_toReal_eq_iSup_finiteExitMass
    (D B : Finset Point) (x : Point) :
    (exitMass D B x).toReal = ⨆ n : ℕ, finiteExitMass D B n x := by
  rw [exitMass, ENNReal.toReal_iSup]
  · congr 1
    funext n
    exact ENNReal.toReal_ofReal (finiteExitMass_nonneg D B n x)
  · intro n
    simp

/-- Finite exit masses converge to the real value of their monotone
infinite-horizon envelope. -/
theorem tendsto_finiteExitMass_outerBoundary
    (D : Finset Point) (x : Point) :
    Tendsto (fun n ↦ finiteExitMass D (outerBoundary D) n x) atTop
      (nhds (exitMass D (outerBoundary D) x).toReal) := by
  have hbdd : BddAbove
      (range fun n ↦ finiteExitMass D (outerBoundary D) n x) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact finiteExitMass_le_one D (outerBoundary D) n x
  have hlim := tendsto_atTop_ciSup
    (monotone_finiteExitMass_outerBoundary D x) hbdd
  rwa [← exitMass_toReal_eq_iSup_finiteExitMass] at hlim

/-- A planar walk started in a finite closed disc exits through its one-step
outer boundary with total mass one.  The proof is purely finite-state: the
complement is the killed mass remaining at time `n`, whose terms tend to zero
because every killed Green series in the disc is finite. -/
theorem exitMass_closedDisc_outerBoundary_eq_one
    (R : ℕ) {x : Point} (hx : x ∈ closedDisc R) :
    exitMass (closedDisc R) (outerBoundary (closedDisc R)) x = 1 := by
  apply (ENNReal.toReal_eq_one_iff _).mp
  have hsum :=
    (tendsto_finiteExitMass_outerBoundary (closedDisc R) x).add
      (tendsto_planarKilledMass_toReal_closedDisc_zero R x)
  have heq : (fun n ↦
      finiteExitMass (closedDisc R) (outerBoundary (closedDisc R)) n x +
        (planarKilledMass (closedDisc R) n x).toReal) =
      fun _n : ℕ ↦ (1 : ℝ) := by
    funext n
    exact finiteExitMass_add_planarKilledMass_toReal_eq_one
      (closedDisc R) n (Or.inl hx)
  rw [heq] at hsum
  simpa using tendsto_nhds_unique hsum tendsto_const_nhds

/-- A nonnegative lower bound for the potential on the outer boundary gives
a lower Green estimate weighted by the total exit mass.  Unlike the earlier
support-wide lower bound, no positive lower estimate is required in the
interior of the disc. -/
theorem potentialBoundaryLower_mul_exitMass_sub_le_infiniteGreen_toReal
    (R : ℕ) {x y : Point} {L : ℝ}
    (hL : ∀ z, z ∈ outerBoundary (closedDisc R) →
      L ≤ planarPotentialKernel (z - y)) :
    L * (exitMass (closedDisc R) (outerBoundary (closedDisc R)) x).toReal -
        planarPotentialKernel (x - y) ≤
      (infiniteGreen (closedDisc R) x y).toReal := by
  have hpoint (z : Point) :
      L * boundaryIndicator (outerBoundary (closedDisc R)) z ≤
        planarPotentialKernel (z - y) := by
    by_cases hz : z ∈ outerBoundary (closedDisc R)
    · simpa [boundaryIndicator, hz] using hL z hz
    · simpa [boundaryIndicator, hz] using planarPotentialKernel_nonneg (z - y)
  have hfinite (N : ℕ) :
      L * finiteExitMass (closedDisc R) (outerBoundary (closedDisc R)) (N + 1) x ≤
        stoppedExpectation (closedDisc R) (N + 1)
          (fun z ↦ planarPotentialKernel (z - y)) x := by
    rw [finiteExitMass, ← stoppedExpectation_const_mul]
    exact stoppedExpectation_mono (closedDisc R) hpoint (N + 1) x
  have hexit :=
    ((tendsto_finiteExitMass_outerBoundary (closedDisc R) x).const_mul L).comp
      (tendsto_add_atTop_nat 1)
  have hpotential := tendsto_stoppedExpectation_potential_closedDisc R x y
  have hlim := le_of_tendsto_of_tendsto' hexit hpotential hfinite
  linarith

/-- Boundary-only potential lower bound with the exit-mass factor discharged
for a starting point inside the disc. -/
theorem potentialBoundaryLower_sub_le_infiniteGreen_toReal
    (R : ℕ) {x y : Point} (hx : x ∈ closedDisc R) {L : ℝ}
    (hL : ∀ z, z ∈ outerBoundary (closedDisc R) →
      L ≤ planarPotentialKernel (z - y)) :
    L - planarPotentialKernel (x - y) ≤
      (infiniteGreen (closedDisc R) x y).toReal := by
  have h := potentialBoundaryLower_mul_exitMass_sub_le_infiniteGreen_toReal
    R (x := x) (y := y) hL
  rw [exitMass_closedDisc_outerBoundary_eq_one R hx] at h
  simpa using h

/-- Boundary-only logarithmic Green lower bound, obtained by inserting the
uniform `100`-error potential estimate into the preceding exit-mass bound. -/
theorem pointLogMainBoundaryLower_mul_exitMass_sub_le_infiniteGreen_toReal
    (R : ℕ) {x y : Point} {L : ℝ}
    (hL : ∀ z, z ∈ outerBoundary (closedDisc R) →
      L ≤ pointLogMain (z - y)) :
    (L - 100) *
        (exitMass (closedDisc R) (outerBoundary (closedDisc R)) x).toReal -
        planarPotentialKernel (x - y) ≤
      (infiniteGreen (closedDisc R) x y).toReal := by
  apply potentialBoundaryLower_mul_exitMass_sub_le_infiniteGreen_toReal R
  intro z hz
  have hsharp :=
    (abs_le.mp (abs_planarPotentialKernel_sub_pointLogMain_le (z - y))).1
  linarith [hL z hz]

/-- Explicit all-parity logarithmic lower Green bound requiring the
logarithmic main-term estimate only on the exit boundary. -/
theorem pointLogMainBoundaryLower_sub_le_infiniteGreen_toReal
    (R : ℕ) {x y : Point} (hx : x ∈ closedDisc R) {L : ℝ}
    (hL : ∀ z, z ∈ outerBoundary (closedDisc R) →
      L ≤ pointLogMain (z - y)) :
    L - 100 - planarPotentialKernel (x - y) ≤
      (infiniteGreen (closedDisc R) x y).toReal := by
  apply potentialBoundaryLower_sub_le_infiniteGreen_toReal R hx
  intro z hz
  have hsharp :=
    (abs_le.mp (abs_planarPotentialKernel_sub_pointLogMain_le (z - y))).1
  linarith [hL z hz]

/-! ## Uniform logarithmic envelopes -/

/-- The sharp all-parity potential estimate turns any upper bound for the
explicit logarithmic main term on the stopped-walk support into a killed
Green upper bound.  This formulation keeps the geometric part (bounding the
diagonal radii on a disc and its outer boundary) separate from probability. -/
theorem infiniteGreen_toReal_le_of_pointLogMain_le
    (R : ℕ) {x y : Point} (hx : x ∈ closedDisc R) {U : ℝ}
    (hU : ∀ z, z ∈ closedDisc R ∨ z ∈ outerBoundary (closedDisc R) →
      pointLogMain (z - y) ≤ U) :
    (infiniteGreen (closedDisc R) x y).toReal ≤
      U + 100 - planarPotentialKernel (x - y) := by
  apply infiniteGreen_toReal_le_of_potential_le R hx
  intro z hz
  have hsharp :=
    (abs_le.mp (abs_planarPotentialKernel_sub_pointLogMain_le (z - y))).2
  linarith [hU z hz]

/-- Lower counterpart of `infiniteGreen_toReal_le_of_pointLogMain_le`.
It is useful when a logarithmic lower envelope is available on the entire
finite stopped-walk support. -/
theorem pointLogMainLower_sub_le_infiniteGreen_toReal
    (R : ℕ) {x y : Point} (hx : x ∈ closedDisc R) {L : ℝ}
    (hL : ∀ z, z ∈ closedDisc R ∨ z ∈ outerBoundary (closedDisc R) →
      L ≤ pointLogMain (z - y)) :
    L - 100 - planarPotentialKernel (x - y) ≤
      (infiniteGreen (closedDisc R) x y).toReal := by
  apply potentialLower_sub_le_infiniteGreen_toReal R hx
  intro z hz
  have hsharp :=
    (abs_le.mp (abs_planarPotentialKernel_sub_pointLogMain_le (z - y))).1
  linarith [hL z hz]

/-! ## Real form of the Green quotient -/

/-- The killed-disc hitting probability is the quotient of the corresponding
real Green values.  All `ENNReal.toReal` side conditions are already encoded
by the finite-box argument in `GreenProbability`. -/
theorem simpleRandomWalkFrom_hitBeforeExit_closedDisc_toReal_eq_green_div
    (R : ℕ) (x y : Point) (hy : y ∈ closedDisc R) :
    (simpleRandomWalkFrom x
      (walkHitBeforeExit (closedDisc R) y)).toReal =
      (infiniteGreen (closedDisc R) x y).toReal /
        (infiniteGreen (closedDisc R) y y).toReal := by
  rw [simpleRandomWalkFrom_hitBeforeExit_closedDisc_eq_green_div R x y hy,
    ENNReal.toReal_div]

/-- The diagonal killed Green value is at least the time-zero visit. -/
theorem one_le_infiniteGreen_closedDisc_diagonal_toReal
    (R : ℕ) {y : Point} (hy : y ∈ closedDisc R) :
    1 ≤ (infiniteGreen (closedDisc R) y y).toReal := by
  have hone : (1 : ℝ≥0∞) ≤ infiniteGreen (closedDisc R) y y := by
    have hzero : killedPower planarKernel (closedDisc R) 0 y y ≤
        ∑' n, killedPower planarKernel (closedDisc R) n y y := ENNReal.le_tsum 0
    simpa [infiniteGreen, killedPower, hy] using hzero
  exact ENNReal.toReal_mono
    (infiniteGreen_ne_top_of_subset_coordinateBox (closedDisc R) R y y
      (fun z hz ↦ (mem_closedDisc R z).mp hz |>.1)) hone

/-- Lower hitting-probability estimate obtained by dividing the boundary
logarithmic lower Green bound by the support-wide logarithmic upper bound for
the diagonal Green value. -/
theorem pointLogMain_lower_div_upper_le_hitProbability_toReal
    (R : ℕ) {x y : Point} (hx : x ∈ closedDisc R)
    (hy : y ∈ closedDisc R) {L U : ℝ}
    (hL : ∀ z, z ∈ outerBoundary (closedDisc R) →
      L ≤ pointLogMain (z - y))
    (hU : ∀ z, z ∈ closedDisc R ∨ z ∈ outerBoundary (closedDisc R) →
      pointLogMain (z - y) ≤ U)
    (hnum0 : 0 ≤ L - 100 - planarPotentialKernel (x - y)) :
    (L - 100 - planarPotentialKernel (x - y)) /
        (U + 100 - planarPotentialKernel (y - y)) ≤
      (simpleRandomWalkFrom x
        (walkHitBeforeExit (closedDisc R) y)).toReal := by
  rw [simpleRandomWalkFrom_hitBeforeExit_closedDisc_toReal_eq_green_div R x y hy]
  have hnum := pointLogMainBoundaryLower_sub_le_infiniteGreen_toReal
    R hx hL
  have hden := infiniteGreen_toReal_le_of_pointLogMain_le R hy hU
  have hdiag := one_le_infiniteGreen_closedDisc_diagonal_toReal R hy
  have hdenpos : 0 < (infiniteGreen (closedDisc R) y y).toReal :=
    lt_of_lt_of_le zero_lt_one hdiag
  have hUpos : 0 < U + 100 - planarPotentialKernel (y - y) :=
    hdenpos.trans_le hden
  rw [div_le_div_iff₀ hUpos hdenpos]
  calc
    (L - 100 - planarPotentialKernel (x - y)) *
        (infiniteGreen (closedDisc R) y y).toReal ≤
        (L - 100 - planarPotentialKernel (x - y)) *
          (U + 100 - planarPotentialKernel (y - y)) :=
      mul_le_mul_of_nonneg_left hden hnum0
    _ ≤ (infiniteGreen (closedDisc R) x y).toReal *
          (U + 100 - planarPotentialKernel (y - y)) :=
      mul_le_mul_of_nonneg_right hnum hUpos.le

/-- Upper hitting-probability estimate obtained by dividing the support-wide
logarithmic upper Green bound by the boundary logarithmic lower bound for the
diagonal Green value. -/
theorem hitProbability_toReal_le_pointLogMain_upper_div_lower
    (R : ℕ) {x y : Point} (hx : x ∈ closedDisc R)
    (hy : y ∈ closedDisc R) {L U : ℝ}
    (hL : ∀ z, z ∈ outerBoundary (closedDisc R) →
      L ≤ pointLogMain (z - y))
    (hU : ∀ z, z ∈ closedDisc R ∨ z ∈ outerBoundary (closedDisc R) →
      pointLogMain (z - y) ≤ U)
    (hden0 : 0 < L - 100 - planarPotentialKernel (y - y)) :
    (simpleRandomWalkFrom x
        (walkHitBeforeExit (closedDisc R) y)).toReal ≤
      (U + 100 - planarPotentialKernel (x - y)) /
        (L - 100 - planarPotentialKernel (y - y)) := by
  rw [simpleRandomWalkFrom_hitBeforeExit_closedDisc_toReal_eq_green_div R x y hy]
  have hnum := infiniteGreen_toReal_le_of_pointLogMain_le R hx hU
  have hden := pointLogMainBoundaryLower_sub_le_infiniteGreen_toReal
    R hy hL
  have hdiag := one_le_infiniteGreen_closedDisc_diagonal_toReal R hy
  have hgreenpos : 0 < (infiniteGreen (closedDisc R) y y).toReal :=
    lt_of_lt_of_le zero_lt_one hdiag
  rw [div_le_div_iff₀ hgreenpos hden0]
  calc
    (infiniteGreen (closedDisc R) x y).toReal *
        (L - 100 - planarPotentialKernel (y - y)) ≤
        (infiniteGreen (closedDisc R) x y).toReal *
          (infiniteGreen (closedDisc R) y y).toReal :=
      mul_le_mul_of_nonneg_left hden ENNReal.toReal_nonneg
    _ ≤ (U + 100 - planarPotentialKernel (x - y)) *
          (infiniteGreen (closedDisc R) y y).toReal :=
      mul_le_mul_of_nonneg_right hnum hgreenpos.le

end

end GreenAsymptotic
end Erdos1165
