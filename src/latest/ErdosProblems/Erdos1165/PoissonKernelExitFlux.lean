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

import ErdosProblems.Erdos1165.BoundaryStoppedHarnack

/-!
# The finite-domain Poisson kernel as Green mass times exit flux

For a finite domain `D`, the probability of leaving `D` through a finite set
`B` disjoint from `D` is the sum, over the last interior vertex `a`, of the
killed Green mass at `a` times the one-step transition mass from `a` into
`B`.  This is the exact last-interior-vertex decomposition

`exitMass D B x = ∑ a ∈ D, infiniteGreen D x a * exitFlux B a`.

The final theorem packages the consequence used by Poisson-kernel Harnack
arguments: a pointwise comparison of the killed Green functions, uniform in
the last interior vertex, automatically compares every finite exit event.
-/

open Filter
open scoped BigOperators ENNReal Topology

namespace Erdos1165
namespace PoissonKernelExitFlux

open Annulus AnnulusHarnack GreenFunction GreenProbability GreenAsymptotic
open GreenHarnack
open BoundaryStoppedHarnack PotentialEuclideanGeometry
  PotentialRadialAsymptotic RadialHarnackSpecialization ThickPoint

noncomputable section

/-- One-step transition mass from the interior vertex `a` into the finite
target set `B`. -/
def exitFlux (B : Finset Point) (a : Point) : ℝ≥0∞ :=
  ∑ b ∈ B, planarKernel a b

theorem exitFlux_ne_top (B : Finset Point) (a : Point) :
    exitFlux B a ≠ ⊤ := by
  unfold exitFlux
  apply ENNReal.sum_ne_top.mpr
  intro b hb
  unfold planarKernel
  apply ENNReal.sum_ne_top.mpr
  intro d hd
  split <;> simp

/-- Directional form of the one-step exit flux. -/
theorem exitFlux_eq_sum_directions (B : Finset Point) (a : Point) :
    exitFlux B a = ∑ d : Direction,
      (1 / 4 : ℝ≥0∞) * if neighbor a d ∈ B then 1 else 0 := by
  unfold exitFlux planarKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hmem : a + directionVector d ∈ B
  · rw [Finset.sum_eq_single (a + directionVector d)]
    · simp [neighbor, hmem]
    · intro b hb hne
      simp [hne]
    · exact fun h ↦ (h hmem).elim
  · have hzero : (∑ b ∈ B,
        if b = a + directionVector d then (4 : ℝ≥0∞)⁻¹ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [if_neg]
      intro h
      apply hmem
      simpa [h] using hb
    rw [hzero]
    simp [neighbor, hmem]

/-- The real neighbour average of the boundary indicator is exactly the
`ENNReal` one-step transition flux. -/
theorem ofReal_neighborAverage_boundaryIndicator_eq_exitFlux
    (B : Finset Point) (a : Point) :
    ENNReal.ofReal (neighborAverage (boundaryIndicator B) a) = exitFlux B a := by
  rw [exitFlux_eq_sum_directions]
  unfold neighborAverage
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · simp only [ENNReal.ofReal_ofNat]
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hmem : neighbor a d ∈ B <;>
      simp [boundaryIndicator, hmem]
  · intro d hd
    exact boundaryIndicator_nonneg B (neighbor a d)

/-! ## A finite occupation formula -/

theorem stoppedOccupation_congr_on
    (D : Finset Point) {g h : Point → ℝ}
    (hgh : ∀ z ∈ D, g z = h z) (n : ℕ) (x : Point) :
    stoppedOccupation D n g x = stoppedOccupation D n h x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      by_cases hx : x ∈ D
      · rw [stoppedOccupation_succ_of_mem D hx,
          stoppedOccupation_succ_of_mem D hx, hgh x hx]
        simp_rw [ih]
      · rw [stoppedOccupation_of_notMem D hx,
          stoppedOccupation_of_notMem D hx]

theorem stoppedOccupation_const_mul
    (D : Finset Point) (c : ℝ) (g : Point → ℝ) (n : ℕ) (x : Point) :
    stoppedOccupation D n (fun z ↦ c * g z) x =
      c * stoppedOccupation D n g x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      by_cases hx : x ∈ D
      · rw [stoppedOccupation_succ_of_mem D hx,
          stoppedOccupation_succ_of_mem D hx]
        simp_rw [ih]
        rw [← Finset.mul_sum]
        ring
      · rw [stoppedOccupation_of_notMem D hx,
          stoppedOccupation_of_notMem D hx]
        simp

theorem stoppedOccupation_finset_sum
    {I : Type*} (D : Finset Point) (s : Finset I) (g : I → Point → ℝ)
    (n : ℕ) (x : Point) :
    stoppedOccupation D n (fun z ↦ ∑ i ∈ s, g i z) x =
      ∑ i ∈ s, stoppedOccupation D n (g i) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      by_cases hx : x ∈ D
      · rw [stoppedOccupation_succ_of_mem D hx]
        simp_rw [stoppedOccupation_succ_of_mem D hx, ih,
          Finset.sum_add_distrib]
        simp only [Finset.sum_div]
        rw [Finset.sum_comm]
      · rw [stoppedOccupation_of_notMem D hx]
        simp_rw [stoppedOccupation_of_notMem D hx]
        simp

/-- A stopped occupation with arbitrary weights is the corresponding finite
linear combination of killed Green functions. -/
theorem stoppedOccupation_eq_sum_planarFiniteGreen
    (D : Finset Point) (N : ℕ) (g : Point → ℝ) (x : Point) :
    stoppedOccupation D (N + 1) g x =
      ∑ a ∈ D, g a * (planarFiniteGreen D N x a).toReal := by
  calc
    stoppedOccupation D (N + 1) g x =
        stoppedOccupation D (N + 1)
          (fun z ↦ ∑ a ∈ D, g a * pointIndicator a z) x := by
      apply stoppedOccupation_congr_on
      intro z hz
      rw [Finset.sum_eq_single z]
      · simp [pointIndicator]
      · intro a ha haz
        have hza : z ≠ a := Ne.symm haz
        simp [pointIndicator, hza]
      · exact fun h ↦ (h hz).elim
    _ = ∑ a ∈ D,
        stoppedOccupation D (N + 1) (fun z ↦ g a * pointIndicator a z) x := by
      rw [stoppedOccupation_finset_sum]
    _ = ∑ a ∈ D, g a *
        stoppedOccupation D (N + 1) (pointIndicator a) x := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [stoppedOccupation_const_mul]
    _ = ∑ a ∈ D, g a * (planarFiniteGreen D N x a).toReal := by
      simp_rw [stoppedOccupation_pointIndicator_eq_planarFiniteGreen]

/-! ## Finite- and infinite-horizon last-interior-vertex formulas -/

/-- At a positive finite horizon, the stopped exit mass is the killed Green
mass through the preceding horizon multiplied by the one-step exit flux. -/
theorem ofReal_finiteExitMass_succ_eq_sum_planarFiniteGreen_mul_exitFlux
    (D B : Finset Point) (hDB : Disjoint D B) {x : Point} (hx : x ∈ D)
    (N : ℕ) :
    ENNReal.ofReal (finiteExitMass D B (N + 1) x) =
      ∑ a ∈ D, planarFiniteGreen D N x a * exitFlux B a := by
  have hxB : x ∉ B := fun hxB ↦ Finset.disjoint_left.mp hDB hx hxB
  have hdrift : ∀ a ∈ D,
      drift (boundaryIndicator B) a =
        neighborAverage (boundaryIndicator B) a := by
    intro a ha
    have haB : a ∉ B := fun haB ↦ Finset.disjoint_left.mp hDB ha haB
    simp [drift, boundaryIndicator, haB]
  have hreal : finiteExitMass D B (N + 1) x =
      ∑ a ∈ D, neighborAverage (boundaryIndicator B) a *
        (planarFiniteGreen D N x a).toReal := by
    rw [finiteExitMass, finite_dynkin]
    rw [show boundaryIndicator B x = 0 by simp [boundaryIndicator, hxB], zero_add]
    rw [stoppedOccupation_congr_on D hdrift]
    exact stoppedOccupation_eq_sum_planarFiniteGreen D N
      (neighborAverage (boundaryIndicator B)) x
  rw [hreal, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [ENNReal.ofReal_mul]
    · rw [ofReal_neighborAverage_boundaryIndicator_eq_exitFlux]
      rw [ENNReal.ofReal_toReal (planarFiniteGreen_ne_top D N x a)]
      ac_rfl
    · unfold neighborAverage
      exact div_nonneg (Finset.sum_nonneg fun d hd ↦
        boundaryIndicator_nonneg B (neighbor a d)) (by norm_num)
  · intro a ha
    exact mul_nonneg
      (by
        unfold neighborAverage
        exact div_nonneg (Finset.sum_nonneg fun d hd ↦
          boundaryIndicator_nonneg B (neighbor a d)) (by norm_num))
      ENNReal.toReal_nonneg

/-- Exact finite-domain Poisson-kernel representation by the last interior
vertex. -/
theorem exitMass_eq_sum_infiniteGreen_mul_exitFlux
    (D B : Finset Point) (hDB : Disjoint D B) {x : Point} (hx : x ∈ D) :
    exitMass D B x =
      ∑ a ∈ D, infiniteGreen D x a * exitFlux B a := by
  have hexitTop : exitMass D B x ≠ ⊤ := by
    exact ne_of_lt ((exitMass_le_one D B x).trans_lt ENNReal.one_lt_top)
  have hleft : Tendsto
      (fun N ↦ ENNReal.ofReal (finiteExitMass D B (N + 1) x)) atTop
      (nhds (ENNReal.ofReal (exitMass D B x).toReal)) := by
    exact ENNReal.tendsto_ofReal
      ((tendsto_finiteExitMass_of_disjoint D B hDB x).comp
        (tendsto_add_atTop_nat 1))
  have hright : Tendsto
      (fun N ↦ ∑ a ∈ D, planarFiniteGreen D N x a * exitFlux B a)
      atTop (nhds (∑ a ∈ D, infiniteGreen D x a * exitFlux B a)) := by
    apply tendsto_finsetSum
    intro a ha
    exact ENNReal.Tendsto.mul_const (tendsto_planarFiniteGreen D x a)
      (Or.inr (exitFlux_ne_top B a))
  have heq : (fun N ↦ ENNReal.ofReal (finiteExitMass D B (N + 1) x)) =
      fun N ↦ ∑ a ∈ D, planarFiniteGreen D N x a * exitFlux B a := by
    funext N
    exact ofReal_finiteExitMass_succ_eq_sum_planarFiniteGreen_mul_exitFlux
      D B hDB hx N
  rw [heq] at hleft
  have hlim := tendsto_nhds_unique hleft hright
  rwa [ENNReal.ofReal_toReal hexitTop] at hlim

/-- A uniform pointwise Green comparison compares every finite exit event.
This is the Poisson-kernel consequence needed in annular Harnack arguments. -/
theorem exitMass_le_of_infiniteGreen_le
    (D B : Finset Point) (hDB : Disjoint D B) {x y : Point}
    (hx : x ∈ D) (hy : y ∈ D) (c : ℝ≥0∞)
    (hgreen : ∀ a ∈ D,
      infiniteGreen D y a ≤ c * infiniteGreen D x a) :
    exitMass D B y ≤ c * exitMass D B x := by
  rw [exitMass_eq_sum_infiniteGreen_mul_exitFlux D B hDB hy,
    exitMass_eq_sum_infiniteGreen_mul_exitFlux D B hDB hx]
  calc
    (∑ a ∈ D, infiniteGreen D y a * exitFlux B a) ≤
        ∑ a ∈ D, (c * infiniteGreen D x a) * exitFlux B a := by
      gcongr with a ha
      exact hgreen a ha
    _ = c * ∑ a ∈ D, infiniteGreen D x a * exitFlux B a := by
      simp_rw [mul_assoc]
      rw [Finset.mul_sum]

/-- `toReal` version of `exitMass_le_of_infiniteGreen_le`.  This is the
convenient interface for Green estimates proved by real potential-kernel
calculations. -/
theorem exitMass_le_of_infiniteGreen_toReal_le
    (D B : Finset Point) (hDB : Disjoint D B) {x y : Point}
    (hx : x ∈ D) (hy : y ∈ D) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hfiniteX : ∀ a ∈ D, infiniteGreen D x a ≠ ⊤)
    (hfiniteY : ∀ a ∈ D, infiniteGreen D y a ≠ ⊤)
    (hgreen : ∀ a ∈ D,
      (infiniteGreen D y a).toReal ≤
        c.toReal * (infiniteGreen D x a).toReal) :
    exitMass D B y ≤ c * exitMass D B x := by
  apply exitMass_le_of_infiniteGreen_le D B hDB hx hy c
  intro a ha
  apply (ENNReal.toReal_le_toReal (hfiniteY a ha)
    (ENNReal.mul_ne_top hc (hfiniteX a ha))).mp
  simpa only [ENNReal.toReal_mul] using hgreen a ha

/-- Finite coordinate-box domains automatically supply the finiteness
hypotheses in the preceding `toReal` comparison theorem. -/
theorem exitMass_le_of_infiniteGreen_toReal_le_of_subset_coordinateBox
    (D B : Finset Point) (boxRadius : ℕ) (hD : D ⊆ coordinateBox boxRadius)
    (hDB : Disjoint D B) {x y : Point} (hx : x ∈ D) (hy : y ∈ D)
    (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hgreen : ∀ a ∈ D,
      (infiniteGreen D y a).toReal ≤
        c.toReal * (infiniteGreen D x a).toReal) :
    exitMass D B y ≤ c * exitMass D B x := by
  apply exitMass_le_of_infiniteGreen_toReal_le D B hDB hx hy c hc
  · intro a ha
    exact infiniteGreen_ne_top_of_subset_coordinateBox D boxRadius x a hD
  · intro a ha
    exact infiniteGreen_ne_top_of_subset_coordinateBox D boxRadius y a hD
  · exact hgreen

/-! ## Comparison only on the support of the exit flux -/

/-- Only last interior vertices with nonzero one-step flux into `B` matter
in the Poisson-kernel sum. -/
theorem exitMass_le_of_infiniteGreen_le_on_exitFlux_support
    (D B : Finset Point) (hDB : Disjoint D B) {x y : Point}
    (hx : x ∈ D) (hy : y ∈ D) (c : ℝ≥0∞)
    (hgreen : ∀ a ∈ D, exitFlux B a ≠ 0 →
      infiniteGreen D y a ≤ c * infiniteGreen D x a) :
    exitMass D B y ≤ c * exitMass D B x := by
  rw [exitMass_eq_sum_infiniteGreen_mul_exitFlux D B hDB hy,
    exitMass_eq_sum_infiniteGreen_mul_exitFlux D B hDB hx]
  calc
    (∑ a ∈ D, infiniteGreen D y a * exitFlux B a) ≤
        ∑ a ∈ D, (c * infiniteGreen D x a) * exitFlux B a := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hflux : exitFlux B a = 0
      · simp [hflux]
      · exact mul_le_mul_of_nonneg_right (hgreen a ha hflux) bot_le
    _ = c * ∑ a ∈ D, infiniteGreen D x a * exitFlux B a := by
      simp_rw [mul_assoc]
      rw [Finset.mul_sum]

/-- Support-restricted comparison in the `toReal` form delivered by the
potential-kernel estimates. -/
theorem exitMass_le_of_infiniteGreen_toReal_le_on_exitFlux_support
    (D B : Finset Point) (hDB : Disjoint D B) {x y : Point}
    (hx : x ∈ D) (hy : y ∈ D) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hfiniteX : ∀ a ∈ D, infiniteGreen D x a ≠ ⊤)
    (hfiniteY : ∀ a ∈ D, infiniteGreen D y a ≠ ⊤)
    (hgreen : ∀ a ∈ D, exitFlux B a ≠ 0 →
      (infiniteGreen D y a).toReal ≤
        c.toReal * (infiniteGreen D x a).toReal) :
    exitMass D B y ≤ c * exitMass D B x := by
  apply exitMass_le_of_infiniteGreen_le_on_exitFlux_support
    D B hDB hx hy c
  intro a ha hflux
  apply (ENNReal.toReal_le_toReal (hfiniteY a ha)
    (ENNReal.mul_ne_top hc (hfiniteX a ha))).mp
  simpa only [ENNReal.toReal_mul] using hgreen a ha hflux

/-- Coordinate-box specialization of the support-restricted `toReal`
comparison. -/
theorem
    exitMass_le_of_infiniteGreen_toReal_le_on_exitFlux_support_of_subset_coordinateBox
    (D B : Finset Point) (boxRadius : ℕ) (hD : D ⊆ coordinateBox boxRadius)
    (hDB : Disjoint D B) {x y : Point} (hx : x ∈ D) (hy : y ∈ D)
    (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hgreen : ∀ a ∈ D, exitFlux B a ≠ 0 →
      (infiniteGreen D y a).toReal ≤
        c.toReal * (infiniteGreen D x a).toReal) :
    exitMass D B y ≤ c * exitMass D B x := by
  apply exitMass_le_of_infiniteGreen_toReal_le_on_exitFlux_support
    D B hDB hx hy c hc
  · intro a ha
    exact infiniteGreen_ne_top_of_subset_coordinateBox D boxRadius x a hD
  · intro a ha
    exact infiniteGreen_ne_top_of_subset_coordinateBox D boxRadius y a hD
  · exact hgreen

/-! ## Radial location of the literal-boundary exit-flux support -/

/-- If a one-step transition from `a` can land in a subset of the literal
radius-`R` vertex boundary, then `a` lies no farther than one lattice step
inside that boundary.  The deliberately weak closed bound `R - 2` is stable
under the natural-number radius convention and is the form needed by the
radial-cut argument. -/
theorem natCast_sub_two_le_euclideanRadius_of_exitFlux_ne_zero
    {R : ℕ} (hR : 1 ≤ R) (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 (R : ℝ))
    {a : Point} (hflux : exitFlux B a ≠ 0) :
    (R : ℝ) - 2 ≤ euclideanRadius a := by
  obtain ⟨b, hbB, hbKernel⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (s := B) (f := planarKernel a) hflux
  have hneighbor : ∃ d : Direction, b = a + directionVector d := by
    by_contra h
    have hzero : planarKernel a b = 0 := by
      apply planarKernel_eq_zero_of_not_neighbor
      intro d hd
      exact h ⟨d, hd⟩
    exact hbKernel hzero
  obtain ⟨d, rfl⟩ := hneighbor
  have hboundary := hB (a + directionVector d) hbB
  have hlower :=
    (discBoundary_zero_euclideanRadius_bounds_nat hR hboundary).1
  have hgap :=
    abs_euclideanRadius_sub_neighbor_le (a + directionVector d) d
  rw [add_sub_cancel_right] at hgap
  have hcast : (((R - 1 : ℕ) : ℝ)) = (R : ℝ) - 1 := by
    rw [Nat.cast_sub hR]
    norm_num
  rw [hcast] at hlower
  linarith [(abs_le.mp hgap).2]

/-- In particular, the support statement applies to every last vertex of
the graph interior `boundaryInterior R`. -/
theorem boundaryInterior_exitFlux_support_radius_lower
    {R : ℕ} (hR : 1 ≤ R) (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 (R : ℝ))
    {a : Point} (_ha : a ∈ boundaryInterior R)
    (hflux : exitFlux B a ≠ 0) :
    (R : ℝ) - 2 ≤ euclideanRadius a :=
  natCast_sub_two_le_euclideanRadius_of_exitFlux_ne_zero hR B hB hflux

theorem boundaryInterior_disjoint_finset_of_subset_discBoundary
    (R : ℕ) (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 (R : ℝ)) :
    Disjoint (boundaryInterior R) B := by
  rw [Finset.disjoint_left]
  intro z hzD hzB
  exact (mem_boundaryInterior.mp hzD).2 (hB z hzB)

/-- Under the scale separation used by the radial cut, every nonzero
literal-boundary exit flux is supported on the outer side of that cut. -/
theorem cutRadius_le_euclideanRadius_of_boundaryInterior_exitFlux_ne_zero
    {R S : ℕ} (hSR : S + 4 ≤ R) (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 (R : ℝ))
    {a : Point} (ha : a ∈ boundaryInterior R)
    (hflux : exitFlux B a ≠ 0) :
    (S : ℝ) + 2 ≤ euclideanRadius a := by
  have hR : 1 ≤ R := by omega
  have hradius := boundaryInterior_exitFlux_support_radius_lower
    hR B hB ha hflux
  have hcast : (S : ℝ) + 4 ≤ (R : ℝ) := by exact_mod_cast hSR
  linarith

/-- Ready-to-use literal-boundary specialization: it is enough to prove the
real Green comparison on the outer side of the thick radial cut. -/
theorem boundaryInterior_exitMass_le_of_infiniteGreen_toReal_le_on_outer_side
    {R S : ℕ} (hSR : S + 4 ≤ R) (B : Finset Point)
    (hB : ∀ b ∈ B, b ∈ ThickPoint.discBoundary 0 (R : ℝ))
    {x y : Point} (hx : x ∈ boundaryInterior R)
    (hy : y ∈ boundaryInterior R) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hgreen : ∀ a ∈ boundaryInterior R,
      (S : ℝ) + 2 ≤ euclideanRadius a →
        (infiniteGreen (boundaryInterior R) y a).toReal ≤
          c.toReal * (infiniteGreen (boundaryInterior R) x a).toReal) :
    exitMass (boundaryInterior R) B y ≤
      c * exitMass (boundaryInterior R) B x := by
  apply
    exitMass_le_of_infiniteGreen_toReal_le_on_exitFlux_support_of_subset_coordinateBox
      (boundaryInterior R) B R (boundaryInterior_subset_coordinateBox R)
      (boundaryInterior_disjoint_finset_of_subset_discBoundary R B hB)
      hx hy c hc
  intro a ha hflux
  exact hgreen a ha
    (cutRadius_le_euclideanRadius_of_boundaryInterior_exitFlux_ne_zero
      hSR B hB ha hflux)

end

end PoissonKernelExitFlux
end Erdos1165
