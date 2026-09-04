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

import ErdosProblems.Erdos1165.AnnulusHittingHarnack

/-!
# Boundary-sharp Green and Harnack estimates

The uniform logarithmic estimate in `GreenAsymptotic` gives an absolute
error.  For the inverse-radius Harnack estimates one must instead use the
actual potential kernel on the exit boundary.  This file proves that the
upper Green estimate, like the lower estimate, only needs a boundary bound:
the surviving interior mass tends to zero.  Consequently a boundary
potential oscillation of size `ε` gives the sharp finite-domain formula

`|G_D(x,t) - (a(q-t) - a(x-t))| ≤ ε`.

The last section inserts the explicit all-parity gradient from
`PotentialGradient` through `anchoredPotentialError`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos1165
namespace GreenHarnack

open Annulus AnnulusHarnack AnnulusHittingHarnack
open GreenFunction GreenProbability GreenAsymptotic
open PlanarPotential PotentialKernel PotentialConvergence PotentialAsymptotic
open PotentialGradient EndpointDiagonal

noncomputable section

/-! ## Linearity of the finite stopped expectation -/

theorem stoppedExpectation_add (D : Finset Point) (f g : Point → ℝ)
    (n : ℕ) (x : Point) :
    stoppedExpectation D n (fun z ↦ f z + g z) x =
      stoppedExpectation D n f x + stoppedExpectation D n g x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [stoppedExpectation_succ, stoppedExpectation_succ,
        stoppedExpectation_succ]
      simp_rw [ih, Finset.sum_add_distrib]
      ring

theorem stoppedExpectation_sub (D : Finset Point) (f g : Point → ℝ)
    (n : ℕ) (x : Point) :
    stoppedExpectation D n (fun z ↦ f z - g z) x =
      stoppedExpectation D n f x - stoppedExpectation D n g x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [stoppedExpectation_succ, stoppedExpectation_succ,
        stoppedExpectation_succ]
      simp_rw [ih, Finset.sum_sub_distrib]
      ring

theorem stoppedExpectation_const (D : Finset Point) (c : ℝ)
    (n : ℕ) (x : Point) :
    stoppedExpectation D n (fun _z ↦ c) x = c :=
  finite_optionalStopping D (harmonicOn_const D c) n x

/-- Monotonicity restricted to the only states reachable by the absorbed
walk from the domain or its one-step boundary. -/
theorem stoppedExpectation_mono_of_mem_or_outerBoundary
    (D : Finset Point) {f g : Point → ℝ}
    (hfg : ∀ z, z ∈ D ∨ z ∈ outerBoundary D → f z ≤ g z)
    (n : ℕ) {x : Point} (hx : x ∈ D ∨ x ∈ outerBoundary D) :
    stoppedExpectation D n f x ≤ stoppedExpectation D n g x := by
  induction n generalizing x with
  | zero => exact hfg x hx
  | succ n ih =>
      by_cases hxD : x ∈ D
      · rw [stoppedExpectation_succ, stoppedExpectation_succ]
        gcongr with d
        rw [absorbedStep_of_mem D hxD]
        apply ih
        by_cases hn : neighbor x d ∈ D
        · exact Or.inl hn
        · exact Or.inr (neighbor_mem_outerBoundary D hxD hn)
      · rw [stoppedExpectation_of_notMem D hxD,
          stoppedExpectation_of_notMem D hxD]
        exact hfg x hx

/-! ## The boundary-only upper Green estimate -/

/-- Every value of the potential in the finite disc is dominated by its
finite sum over the disc. -/
lemma planarPotentialKernel_le_sum_closedDisc
    (R : ℕ) {z y : Point} (hz : z ∈ closedDisc R) :
    planarPotentialKernel (z - y) ≤
      ∑ w ∈ closedDisc R, planarPotentialKernel (w - y) := by
  exact Finset.single_le_sum
    (fun w _ ↦ planarPotentialKernel_nonneg (w - y)) hz

/-- Upper Green estimate requiring a potential bound only on the actual exit
boundary.  The correction on unexited paths is bounded by a finite constant
times the killed mass, which vanishes at infinity. -/
theorem infiniteGreen_toReal_le_of_potentialBoundary_le
    (R : ℕ) {x y : Point} (hx : x ∈ closedDisc R) {U : ℝ}
    (hU : ∀ z, z ∈ outerBoundary (closedDisc R) →
      planarPotentialKernel (z - y) ≤ U) :
    (infiniteGreen (closedDisc R) x y).toReal ≤
      U - planarPotentialKernel (x - y) := by
  let C : ℝ := |U| +
    ∑ w ∈ closedDisc R, planarPotentialKernel (w - y)
  have hsupport (z : Point)
      (hz : z ∈ closedDisc R ∨ z ∈ outerBoundary (closedDisc R)) :
      planarPotentialKernel (z - y) -
          C * (if z ∈ closedDisc R then 1 else 0) ≤ U := by
    rcases hz with hzD | hzB
    · rw [if_pos hzD]
      have hsum := planarPotentialKernel_le_sum_closedDisc R (y := y) hzD
      have habs : -|U| ≤ U := neg_abs_le U
      dsimp only [C]
      linarith
    · have hzD : z ∉ closedDisc R := (mem_outerBoundary _ z).mp hzB |>.1
      rw [if_neg hzD, mul_zero, sub_zero]
      exact hU z hzB
  have hfinite (N : ℕ) :
      stoppedExpectation (closedDisc R) (N + 1)
          (fun z ↦ planarPotentialKernel (z - y)) x -
        C * (planarKilledMass (closedDisc R) (N + 1) x).toReal ≤ U := by
    have hbound := stoppedExpectation_le_of_mem_or_outerBoundary
      (closedDisc R) hsupport (N + 1) (Or.inl hx)
    rw [stoppedExpectation_sub,
      stoppedExpectation_const_mul,
      stoppedExpectation_interiorIndicator_eq_planarKilledMass] at hbound
    exact hbound
  have hpotential := tendsto_stoppedExpectation_potential_closedDisc R x y
  have hsurvival :=
    ((tendsto_planarKilledMass_toReal_closedDisc_zero R x).const_mul C).comp
      (tendsto_add_atTop_nat 1)
  have hlim := hpotential.sub hsurvival
  have hle := le_of_tendsto hlim (Filter.Eventually.of_forall hfinite)
  linarith

/-! ## Reference-boundary forms of HLOZ (4.1) and (4.2) -/

/-- A boundary point `q` whose potential is within `ε` of every possible exit
point gives the exact killed-Green approximation used in HLOZ (4.1)--(4.2). -/
theorem abs_infiniteGreen_toReal_sub_boundaryReference_le
    (R : ℕ) {x y q : Point} (hx : x ∈ closedDisc R) {ε : ℝ}
    (hε : ∀ z, z ∈ outerBoundary (closedDisc R) →
      |planarPotentialKernel (z - y) - planarPotentialKernel (q - y)| ≤ ε) :
    |(infiniteGreen (closedDisc R) x y).toReal -
        (planarPotentialKernel (q - y) -
          planarPotentialKernel (x - y))| ≤ ε := by
  have hlower : ∀ z, z ∈ outerBoundary (closedDisc R) →
      planarPotentialKernel (q - y) - ε ≤
        planarPotentialKernel (z - y) := by
    intro z hz
    have h := (abs_le.mp (hε z hz)).1
    linarith
  have hupper : ∀ z, z ∈ outerBoundary (closedDisc R) →
      planarPotentialKernel (z - y) ≤
        planarPotentialKernel (q - y) + ε := by
    intro z hz
    have h := (abs_le.mp (hε z hz)).2
    linarith
  have hlo := potentialBoundaryLower_sub_le_infiniteGreen_toReal R hx hlower
  have hup := infiniteGreen_toReal_le_of_potentialBoundary_le R hx hupper
  rw [abs_le]
  constructor <;> linarith

/-- Diagonal specialization, the finite explicit form of HLOZ (4.1). -/
theorem abs_infiniteGreen_diagonal_toReal_sub_boundaryPotential_le
    (R : ℕ) {y q : Point} (hy : y ∈ closedDisc R) {ε : ℝ}
    (hε : ∀ z, z ∈ outerBoundary (closedDisc R) →
      |planarPotentialKernel (z - y) - planarPotentialKernel (q - y)| ≤ ε) :
    |(infiniteGreen (closedDisc R) y y).toReal -
        planarPotentialKernel (q - y)| ≤ ε := by
  simpa [planarPotentialKernel_zero] using
    abs_infiniteGreen_toReal_sub_boundaryReference_le R hy hε

/-- Off-diagonal specialization, the finite explicit form of HLOZ (4.2). -/
theorem abs_infiniteGreen_offDiagonal_toReal_sub_boundaryPotential_le
    (R : ℕ) {x y q : Point} (hx : x ∈ closedDisc R) {ε : ℝ}
    (hε : ∀ z, z ∈ outerBoundary (closedDisc R) →
      |planarPotentialKernel (z - y) - planarPotentialKernel (q - y)| ≤ ε) :
    |(infiniteGreen (closedDisc R) x y).toReal -
        (planarPotentialKernel (q - y) -
          planarPotentialKernel (x - y))| ≤ ε :=
  abs_infiniteGreen_toReal_sub_boundaryReference_le R hx hε

/-! ## Green quotient bounds, the finite forms of HLOZ (4.6)--(4.7) -/

theorem boundaryReference_lower_div_upper_le_hitProbability_toReal
    (R : ℕ) {x y q : Point} (hx : x ∈ closedDisc R)
    (hy : y ∈ closedDisc R) {ε : ℝ}
    (hε : ∀ z, z ∈ outerBoundary (closedDisc R) →
      |planarPotentialKernel (z - y) - planarPotentialKernel (q - y)| ≤ ε)
    (hnum0 : 0 ≤ planarPotentialKernel (q - y) -
      planarPotentialKernel (x - y) - ε) :
    (planarPotentialKernel (q - y) -
        planarPotentialKernel (x - y) - ε) /
        (planarPotentialKernel (q - y) + ε) ≤
      (simpleRandomWalkFrom x
        (walkHitBeforeExit (closedDisc R) y)).toReal := by
  rw [simpleRandomWalkFrom_hitBeforeExit_closedDisc_toReal_eq_green_div R x y hy]
  have hnum := (abs_le.mp
    (abs_infiniteGreen_toReal_sub_boundaryReference_le R hx hε)).1
  have hden := (abs_le.mp
    (abs_infiniteGreen_diagonal_toReal_sub_boundaryPotential_le R hy hε)).2
  have hdiag := one_le_infiniteGreen_closedDisc_diagonal_toReal R hy
  have hgreenpos : 0 < (infiniteGreen (closedDisc R) y y).toReal :=
    lt_of_lt_of_le zero_lt_one hdiag
  have hrefpos : 0 < planarPotentialKernel (q - y) + ε :=
    hgreenpos.trans_le (by linarith)
  rw [div_le_div_iff₀ hrefpos hgreenpos]
  calc
    (planarPotentialKernel (q - y) - planarPotentialKernel (x - y) - ε) *
        (infiniteGreen (closedDisc R) y y).toReal ≤
      (planarPotentialKernel (q - y) - planarPotentialKernel (x - y) - ε) *
        (planarPotentialKernel (q - y) + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) hnum0
    _ ≤ (infiniteGreen (closedDisc R) x y).toReal *
        (planarPotentialKernel (q - y) + ε) :=
      mul_le_mul_of_nonneg_right (by linarith) hrefpos.le

theorem hitProbability_toReal_le_boundaryReference_upper_div_lower
    (R : ℕ) {x y q : Point} (hx : x ∈ closedDisc R)
    (hy : y ∈ closedDisc R) {ε : ℝ}
    (hε : ∀ z, z ∈ outerBoundary (closedDisc R) →
      |planarPotentialKernel (z - y) - planarPotentialKernel (q - y)| ≤ ε)
    (hden0 : 0 < planarPotentialKernel (q - y) - ε) :
    (simpleRandomWalkFrom x
        (walkHitBeforeExit (closedDisc R) y)).toReal ≤
      (planarPotentialKernel (q - y) -
          planarPotentialKernel (x - y) + ε) /
        (planarPotentialKernel (q - y) - ε) := by
  rw [simpleRandomWalkFrom_hitBeforeExit_closedDisc_toReal_eq_green_div R x y hy]
  have hnum := (abs_le.mp
    (abs_infiniteGreen_toReal_sub_boundaryReference_le R hx hε)).2
  have hden := (abs_le.mp
    (abs_infiniteGreen_diagonal_toReal_sub_boundaryPotential_le R hy hε)).1
  have hdiag := one_le_infiniteGreen_closedDisc_diagonal_toReal R hy
  have hgreenpos : 0 < (infiniteGreen (closedDisc R) y y).toReal :=
    lt_of_lt_of_le zero_lt_one hdiag
  rw [div_le_div_iff₀ hgreenpos hden0]
  calc
    (infiniteGreen (closedDisc R) x y).toReal *
        (planarPotentialKernel (q - y) - ε) ≤
      (infiniteGreen (closedDisc R) x y).toReal *
        (infiniteGreen (closedDisc R) y y).toReal :=
      mul_le_mul_of_nonneg_left (by linarith) ENNReal.toReal_nonneg
    _ ≤ (planarPotentialKernel (q - y) - planarPotentialKernel (x - y) + ε) *
        (infiniteGreen (closedDisc R) y y).toReal :=
      mul_le_mul_of_nonneg_right (by linarith) hgreenpos.le

/-! ## Discharging the boundary oscillation by the explicit gradient -/

/-- A finite, fully explicit uniformization of the all-parity anchored
gradient errors over the exit boundary.  Each summand consists of the two
`300/(radius-2)` parity-anchor costs and the central `150*gap/(radius-gap)`
cost. -/
noncomputable def boundaryAnchoredPotentialError
    (R : ℕ) (target q : Point) : ℝ :=
  ∑ z ∈ outerBoundary (closedDisc R),
    anchoredPotentialError (q - target) (z - target)

theorem anchoredPotentialError_nonneg (u v : Point) :
    0 ≤ anchoredPotentialError u v := by
  unfold anchoredPotentialError
  positivity

theorem anchoredPotentialError_le_boundaryAnchoredPotentialError
    (R : ℕ) (target q : Point) {z : Point}
    (hz : z ∈ outerBoundary (closedDisc R)) :
    anchoredPotentialError (q - target) (z - target) ≤
      boundaryAnchoredPotentialError R target q := by
  unfold boundaryAnchoredPotentialError
  exact Finset.single_le_sum
    (fun w _ ↦ anchoredPotentialError_nonneg (q - target) (w - target)) hz

/-- The gradient theorem discharges the abstract boundary oscillation in the
reference Green formulas.  The hypotheses are only the explicit finite
diagonal-coordinate geometry required by `PotentialGradient`. -/
theorem boundary_potential_oscillation_le_anchoredError
    (R : ℕ) (target q : Point)
    (hqR : 2 < max
      (firstDiagonalOffset (evenAnchor (q - target)))
      (secondDiagonalOffset (evenAnchor (q - target))))
    (hzR : ∀ z, z ∈ outerBoundary (closedDisc R) →
      2 < max
        (firstDiagonalOffset (evenAnchor (z - target)))
        (secondDiagonalOffset (evenAnchor (z - target))))
    (hgap : ∀ z, z ∈ outerBoundary (closedDisc R) →
      natGap
          (firstDiagonalOffset (evenAnchor (q - target)))
          (firstDiagonalOffset (evenAnchor (z - target))) +
        natGap
          (secondDiagonalOffset (evenAnchor (q - target)))
          (secondDiagonalOffset (evenAnchor (z - target))) <
        max (firstDiagonalOffset (evenAnchor (q - target)))
          (secondDiagonalOffset (evenAnchor (q - target)))) :
    ∀ z, z ∈ outerBoundary (closedDisc R) →
      |planarPotentialKernel (z - target) -
          planarPotentialKernel (q - target)| ≤
        boundaryAnchoredPotentialError R target q := by
  intro z hz
  calc
    |planarPotentialKernel (z - target) -
        planarPotentialKernel (q - target)| ≤
      anchoredPotentialError (q - target) (z - target) :=
        abs_planarPotentialKernel_sub_le_via_evenAnchors
          hqR (hzR z hz) (hgap z hz)
    _ ≤ boundaryAnchoredPotentialError R target q :=
      anchoredPotentialError_le_boundaryAnchoredPotentialError R target q hz

/-- Gradient-specialized diagonal Green estimate, with no logarithmic
window assumptions and no absolute `100`-error loss. -/
theorem abs_infiniteGreen_diagonal_sub_boundaryPotential_le_anchoredError
    (R : ℕ) {target q : Point} (htarget : target ∈ closedDisc R)
    (hqR : 2 < max
      (firstDiagonalOffset (evenAnchor (q - target)))
      (secondDiagonalOffset (evenAnchor (q - target))))
    (hzR : ∀ z, z ∈ outerBoundary (closedDisc R) →
      2 < max
        (firstDiagonalOffset (evenAnchor (z - target)))
        (secondDiagonalOffset (evenAnchor (z - target))))
    (hgap : ∀ z, z ∈ outerBoundary (closedDisc R) →
      natGap
          (firstDiagonalOffset (evenAnchor (q - target)))
          (firstDiagonalOffset (evenAnchor (z - target))) +
        natGap
          (secondDiagonalOffset (evenAnchor (q - target)))
          (secondDiagonalOffset (evenAnchor (z - target))) <
        max (firstDiagonalOffset (evenAnchor (q - target)))
          (secondDiagonalOffset (evenAnchor (q - target)))) :
    |(infiniteGreen (closedDisc R) target target).toReal -
        planarPotentialKernel (q - target)| ≤
      boundaryAnchoredPotentialError R target q := by
  apply abs_infiniteGreen_diagonal_toReal_sub_boundaryPotential_le R htarget
  exact boundary_potential_oscillation_le_anchoredError R target q hqR hzR hgap

/-- Gradient-specialized off-diagonal Green estimate. -/
theorem abs_infiniteGreen_offDiagonal_sub_boundaryPotential_le_anchoredError
    (R : ℕ) {x target q : Point} (hx : x ∈ closedDisc R)
    (hqR : 2 < max
      (firstDiagonalOffset (evenAnchor (q - target)))
      (secondDiagonalOffset (evenAnchor (q - target))))
    (hzR : ∀ z, z ∈ outerBoundary (closedDisc R) →
      2 < max
        (firstDiagonalOffset (evenAnchor (z - target)))
        (secondDiagonalOffset (evenAnchor (z - target))))
    (hgap : ∀ z, z ∈ outerBoundary (closedDisc R) →
      natGap
          (firstDiagonalOffset (evenAnchor (q - target)))
          (firstDiagonalOffset (evenAnchor (z - target))) +
        natGap
          (secondDiagonalOffset (evenAnchor (q - target)))
          (secondDiagonalOffset (evenAnchor (z - target))) <
        max (firstDiagonalOffset (evenAnchor (q - target)))
          (secondDiagonalOffset (evenAnchor (q - target)))) :
    |(infiniteGreen (closedDisc R) x target).toReal -
        (planarPotentialKernel (q - target) -
          planarPotentialKernel (x - target))| ≤
      boundaryAnchoredPotentialError R target q := by
  apply abs_infiniteGreen_offDiagonal_toReal_sub_boundaryPotential_le R hx
  exact boundary_potential_oscillation_le_anchoredError R target q hqR hzR hgap

/-! ## Finite-domain exit, used by annulus formulas -/

theorem tendsto_planarKilledMass_of_subset_coordinateBox_zero
    (D : Finset Point) (boxRadius : ℕ) (x : Point)
    (hD : D ⊆ coordinateBox boxRadius) :
    Tendsto (fun n ↦ planarKilledMass D n x) atTop (nhds 0) := by
  unfold planarKilledMass
  have hterm : ∀ y ∈ D,
      Tendsto (fun n ↦ killedPower planarKernel D n x y) atTop (nhds 0) := by
    intro y hy
    apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
    simpa [infiniteGreen] using
      infiniteGreen_ne_top_of_subset_coordinateBox D boxRadius x y hD
  simpa using tendsto_finsetSum D hterm

theorem tendsto_planarKilledMass_toReal_of_subset_coordinateBox_zero
    (D : Finset Point) (boxRadius : ℕ) (x : Point)
    (hD : D ⊆ coordinateBox boxRadius) :
    Tendsto (fun n ↦ (planarKilledMass D n x).toReal) atTop (nhds 0) := by
  change Tendsto (ENNReal.toReal ∘ fun n ↦ planarKilledMass D n x) atTop
    (nhds (ENNReal.toReal 0))
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_planarKilledMass_of_subset_coordinateBox_zero D boxRadius x hD)

theorem tendsto_finiteExitMass_of_disjoint
    (D B : Finset Point) (hDB : Disjoint D B) (x : Point) :
    Tendsto (fun n ↦ finiteExitMass D B n x) atTop
      (nhds (exitMass D B x).toReal) := by
  have hbdd : BddAbove (range fun n ↦ finiteExitMass D B n x) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact finiteExitMass_le_one D B n x
  have hlim := tendsto_atTop_ciSup (monotone_finiteExitMass hDB x) hbdd
  rwa [← exitMass_toReal_eq_iSup_finiteExitMass] at hlim

/-- Every finite domain contained in a coordinate box is exited through its
one-step outer boundary with total mass one. -/
theorem exitMass_outerBoundary_eq_one_of_subset_coordinateBox
    (D : Finset Point) (boxRadius : ℕ) {x : Point} (hx : x ∈ D)
    (hD : D ⊆ coordinateBox boxRadius) :
    exitMass D (outerBoundary D) x = 1 := by
  apply (ENNReal.toReal_eq_one_iff _).mp
  have hexit := tendsto_finiteExitMass_of_disjoint D (outerBoundary D)
    (outerBoundary_disjoint D) x
  have hsurvive :=
    tendsto_planarKilledMass_toReal_of_subset_coordinateBox_zero
      D boxRadius x hD
  have hsum := hexit.add hsurvive
  have heq : (fun n ↦ finiteExitMass D (outerBoundary D) n x +
      (planarKilledMass D n x).toReal) = fun _n : ℕ ↦ (1 : ℝ) := by
    funext n
    exact finiteExitMass_add_planarKilledMass_toReal_eq_one D n (Or.inl hx)
  rw [heq] at hsum
  simpa using tendsto_nhds_unique hsum tendsto_const_nhds

/-! ## Inner and outer exit boundaries of a lattice annulus -/

noncomputable def annulusInnerExitBoundary (r R : ℕ) : Finset Point :=
  (outerBoundary (latticeAnnulus r R)).filter fun z ↦ z ∈ openDisc r

noncomputable def annulusOuterExitBoundary (r R : ℕ) : Finset Point :=
  outerBoundary (latticeAnnulus r R) \ annulusInnerExitBoundary r R

@[simp] theorem mem_annulusInnerExitBoundary (r R : ℕ) (z : Point) :
    z ∈ annulusInnerExitBoundary r R ↔
      z ∈ outerBoundary (latticeAnnulus r R) ∧ z ∈ openDisc r := by
  simp [annulusInnerExitBoundary]

@[simp] theorem mem_annulusOuterExitBoundary (r R : ℕ) (z : Point) :
    z ∈ annulusOuterExitBoundary r R ↔
      z ∈ outerBoundary (latticeAnnulus r R) ∧ z ∉ openDisc r := by
  unfold annulusOuterExitBoundary
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨hzOuter, hzNotInner⟩
    refine ⟨hzOuter, ?_⟩
    intro hzOpen
    apply hzNotInner
    exact (mem_annulusInnerExitBoundary r R z).mpr ⟨hzOuter, hzOpen⟩
  · rintro ⟨hzOuter, hzNotOpen⟩
    refine ⟨hzOuter, ?_⟩
    intro hzInner
    exact hzNotOpen ((mem_annulusInnerExitBoundary r R z).mp hzInner).2

theorem annulus_exitBoundary_union (r R : ℕ) :
    annulusInnerExitBoundary r R ∪ annulusOuterExitBoundary r R =
      outerBoundary (latticeAnnulus r R) := by
  unfold annulusOuterExitBoundary
  apply Finset.union_sdiff_of_subset
  intro z hz
  exact (mem_annulusInnerExitBoundary r R z).mp hz |>.1

theorem annulus_exitBoundary_disjoint (r R : ℕ) :
    Disjoint (annulusInnerExitBoundary r R)
      (annulusOuterExitBoundary r R) := by
  rw [Finset.disjoint_left]
  intro z hzInner hzOuter
  exact (mem_annulusOuterExitBoundary r R z).mp hzOuter |>.2
    ((mem_annulusInnerExitBoundary r R z).mp hzInner |>.2)

theorem latticeAnnulus_subset_coordinateBox (r R : ℕ) :
    latticeAnnulus r R ⊆ coordinateBox R := by
  intro z hz
  exact (mem_closedDisc R z).mp ((mem_latticeAnnulus r R z).mp hz |>.1) |>.1

theorem zero_not_mem_latticeAnnulus {r R : ℕ} (hr : 0 < r) :
    (0 : Point) ∉ latticeAnnulus r R := by
  rw [mem_latticeAnnulus_iff_radiusSqInt]
  simp only [not_and, not_le]
  intro h
  have hzero : radiusSqInt (0 : Point) = 0 := by
    simp [radiusSqInt]
  rw [hzero] at h
  have hrZ : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr
  have hrsq : (0 : ℤ) < (r : ℤ) ^ 2 := by positivity
  exact (not_le_of_gt hrsq h).elim

/-! ## Exact two-boundary potential representation -/

noncomputable def twoBoundaryValue
    (B C : Finset Point) (innerValue outerValue : ℝ) (z : Point) : ℝ :=
  innerValue * boundaryIndicator B z + outerValue * boundaryIndicator C z

theorem stoppedExpectation_twoBoundaryValue
    (D B C : Finset Point) (innerValue outerValue : ℝ)
    (n : ℕ) (x : Point) :
    stoppedExpectation D n (twoBoundaryValue B C innerValue outerValue) x =
      innerValue * finiteExitMass D B n x +
        outerValue * finiteExitMass D C n x := by
  unfold twoBoundaryValue finiteExitMass
  rw [stoppedExpectation_add, stoppedExpectation_const_mul,
    stoppedExpectation_const_mul]

theorem boundaryIndicator_union_eq_add_of_disjoint
    {B C : Finset Point} (hBC : Disjoint B C) (z : Point) :
    boundaryIndicator (B ∪ C) z =
      boundaryIndicator B z + boundaryIndicator C z := by
  by_cases hzB : z ∈ B
  · have hzC : z ∉ C := fun hzC ↦ Finset.disjoint_left.mp hBC hzB hzC
    simp [boundaryIndicator, hzB, hzC]
  · by_cases hzC : z ∈ C <;> simp [boundaryIndicator, hzB, hzC]

theorem finiteExitMass_union_eq_add_of_disjoint
    (D : Finset Point) {B C : Finset Point} (hBC : Disjoint B C)
    (n : ℕ) (x : Point) :
    finiteExitMass D (B ∪ C) n x =
      finiteExitMass D B n x + finiteExitMass D C n x := by
  unfold finiteExitMass
  rw [← stoppedExpectation_add]
  congr 2
  funext z
  exact boundaryIndicator_union_eq_add_of_disjoint hBC z

/-- Real exit masses are additive across a disjoint partition of the entire
outer boundary, and their sum is one in a finite box. -/
theorem exitMass_partition_toReal_add_eq_one
    (D : Finset Point) (boxRadius : ℕ) {x : Point} (hx : x ∈ D)
    (hD : D ⊆ coordinateBox boxRadius)
    (B C : Finset Point) (hB : B ⊆ outerBoundary D)
    (hC : C ⊆ outerBoundary D) (hBC : Disjoint B C)
    (hunion : B ∪ C = outerBoundary D) :
    (exitMass D B x).toReal + (exitMass D C x).toReal = 1 := by
  have hBdisj : Disjoint D B := by
    rw [Finset.disjoint_left]
    intro z hzD hzB
    exact (mem_outerBoundary D z).mp (hB hzB) |>.1 hzD
  have hCdisj : Disjoint D C := by
    rw [Finset.disjoint_left]
    intro z hzD hzC
    exact (mem_outerBoundary D z).mp (hC hzC) |>.1 hzD
  have hsum := (tendsto_finiteExitMass_of_disjoint D B hBdisj x).add
    (tendsto_finiteExitMass_of_disjoint D C hCdisj x)
  have houter := tendsto_finiteExitMass_of_disjoint D (outerBoundary D)
    (outerBoundary_disjoint D) x
  have heq : (fun n ↦ finiteExitMass D B n x + finiteExitMass D C n x) =
      fun n ↦ finiteExitMass D (outerBoundary D) n x := by
    funext n
    rw [← hunion]
    exact (finiteExitMass_union_eq_add_of_disjoint D hBC n x).symm
  rw [heq] at hsum
  have hlimits := tendsto_nhds_unique hsum houter
  rw [exitMass_outerBoundary_eq_one_of_subset_coordinateBox D boxRadius hx hD]
    at hlimits
  simpa using hlimits

/-- If the potential is within `ε` of one reference value on each of two
pieces partitioning the exit boundary, its starting value is within `ε` of
the corresponding exit-mass mixture.  This is the exact finite annular
optional-stopping identity behind HLOZ (4.8)--(4.9). -/
theorem abs_potential_sub_twoBoundaryExitMixture_le
    (D : Finset Point) (boxRadius : ℕ) {x : Point} (hx : x ∈ D)
    (hD : D ⊆ coordinateBox boxRadius) (hzero : (0 : Point) ∉ D)
    (B C : Finset Point)
    (hB : B ⊆ outerBoundary D) (hC : C ⊆ outerBoundary D)
    (hBC : Disjoint B C) (hunion : B ∪ C = outerBoundary D)
    (innerValue outerValue ε : ℝ) (hε0 : 0 ≤ ε)
    (hinner : ∀ z, z ∈ B →
      |planarPotentialKernel z - innerValue| ≤ ε)
    (houter : ∀ z, z ∈ C →
      |planarPotentialKernel z - outerValue| ≤ ε) :
    |planarPotentialKernel x -
        (innerValue * (exitMass D B x).toReal +
          outerValue * (exitMass D C x).toReal)| ≤ ε := by
  let step := twoBoundaryValue B C innerValue outerValue
  let K : ℝ := ∑ z ∈ D, |planarPotentialKernel z|
  have hBdisj : Disjoint D B := by
    rw [Finset.disjoint_left]
    intro z hzD hzB
    exact (mem_outerBoundary D z).mp (hB hzB) |>.1 hzD
  have hCdisj : Disjoint D C := by
    rw [Finset.disjoint_left]
    intro z hzD hzC
    exact (mem_outerBoundary D z).mp (hC hzC) |>.1 hzD
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun z _ ↦ abs_nonneg _
  have hpoint (z : Point) (hz : z ∈ D ∨ z ∈ outerBoundary D) :
      |planarPotentialKernel z - step z| ≤
        ε + K * (if z ∈ D then 1 else 0) := by
    rcases hz with hzD | hzBoundary
    · have hzB : z ∉ B := fun hzB ↦
        (mem_outerBoundary D z).mp (hB hzB) |>.1 hzD
      have hzC : z ∉ C := fun hzC ↦
        (mem_outerBoundary D z).mp (hC hzC) |>.1 hzD
      have hsingle : |planarPotentialKernel z| ≤ K := by
        dsimp only [K]
        exact Finset.single_le_sum
          (fun w _ ↦ abs_nonneg (planarPotentialKernel w)) hzD
      simp only [step, twoBoundaryValue, boundaryIndicator, hzB, hzC,
        if_false, mul_zero, add_zero, sub_zero, hzD, if_true, mul_one]
      linarith
    · have hzUnion : z ∈ B ∪ C := by simpa [hunion] using hzBoundary
      rcases Finset.mem_union.mp hzUnion with hzB | hzC
      · have hzC' : z ∉ C := fun hzC ↦
          Finset.disjoint_left.mp hBC hzB hzC
        have hzD : z ∉ D := (mem_outerBoundary D z).mp hzBoundary |>.1
        simpa [step, twoBoundaryValue, boundaryIndicator, hzB, hzC', hzD]
          using hinner z hzB
      · have hzB' : z ∉ B := fun hzB ↦
          Finset.disjoint_left.mp hBC hzB hzC
        have hzD : z ∉ D := (mem_outerBoundary D z).mp hzBoundary |>.1
        simpa [step, twoBoundaryValue, boundaryIndicator, hzB', hzC, hzD]
          using houter z hzC
  have hupperPoint (z : Point) (hz : z ∈ D ∨ z ∈ outerBoundary D) :
      planarPotentialKernel z - step z ≤
        ε + K * (if z ∈ D then 1 else 0) :=
    (le_abs_self _).trans (hpoint z hz)
  have hlowerPoint (z : Point) (hz : z ∈ D ∨ z ∈ outerBoundary D) :
      -(ε + K * (if z ∈ D then 1 else 0)) ≤
        planarPotentialKernel z - step z := by
    have hp := hpoint z hz
    have ha := neg_abs_le (planarPotentialKernel z - step z)
    linarith
  have hupperFinite (n : ℕ) :
      stoppedExpectation D n (fun z ↦ planarPotentialKernel z) x -
          stoppedExpectation D n step x ≤
        stoppedExpectation D n
          (fun z ↦ ε + K * (if z ∈ D then 1 else 0)) x :=
    by
      rw [← stoppedExpectation_sub]
      exact stoppedExpectation_mono_of_mem_or_outerBoundary D
        hupperPoint n (Or.inl hx)
  have hlowerFinite (n : ℕ) :
      stoppedExpectation D n
          (fun z ↦ -(ε + K * (if z ∈ D then 1 else 0))) x ≤
        stoppedExpectation D n (fun z ↦ planarPotentialKernel z) x -
          stoppedExpectation D n step x := by
    rw [← stoppedExpectation_sub]
    exact stoppedExpectation_mono_of_mem_or_outerBoundary D
      hlowerPoint n (Or.inl hx)
  have hpot : Tendsto
      (fun n ↦ stoppedExpectation D n (fun z ↦ planarPotentialKernel z) x)
      atTop (nhds (planarPotentialKernel x)) := by
    have heq : (fun n ↦ stoppedExpectation D n
        (fun z ↦ planarPotentialKernel z) x) =
        fun _n : ℕ ↦ planarPotentialKernel x := by
      funext n
      have hf : potentialAt 0 = planarPotentialKernel := by
        funext z
        simp [potentialAt]
      rw [← hf]
      exact finite_optionalStopping_potentialAt D hzero n x
    rw [heq]
    exact tendsto_const_nhds
  have hBin := tendsto_finiteExitMass_of_disjoint D B hBdisj x
  have hCout := tendsto_finiteExitMass_of_disjoint D C hCdisj x
  have hstep : Tendsto
      (fun n ↦ stoppedExpectation D n step x) atTop
      (nhds (innerValue * (exitMass D B x).toReal +
        outerValue * (exitMass D C x).toReal)) := by
    have hmix := (hBin.const_mul innerValue).add (hCout.const_mul outerValue)
    convert hmix using 1
    funext n
    simpa only [step] using stoppedExpectation_twoBoundaryValue D B C
      innerValue outerValue n x
  have hdiff := hpot.sub hstep
  have hsurvive :=
    tendsto_planarKilledMass_toReal_of_subset_coordinateBox_zero
      D boxRadius x hD
  have hright : Tendsto
      (fun n ↦ stoppedExpectation D n
        (fun z ↦ ε + K * (if z ∈ D then 1 else 0)) x)
      atTop (nhds ε) := by
    have hraw : Tendsto
        (fun n ↦ ε + K * (planarKilledMass D n x).toReal) atTop
        (nhds (ε + K * 0)) :=
      tendsto_const_nhds.add (hsurvive.const_mul K)
    convert hraw using 1
    · funext n
      rw [stoppedExpectation_add, stoppedExpectation_const,
        stoppedExpectation_const_mul,
        stoppedExpectation_interiorIndicator_eq_planarKilledMass]
    · ring_nf
  have hleft : Tendsto
      (fun n ↦ stoppedExpectation D n
        (fun z ↦ -(ε + K * (if z ∈ D then 1 else 0))) x)
      atTop (nhds (-ε)) := by
    have hraw := hright.neg
    refine hraw.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    rw [show (fun z ↦ -(ε + K * (if z ∈ D then 1 else 0))) =
        fun z ↦ (-1 : ℝ) * (ε + K * (if z ∈ D then 1 else 0)) by
      funext z
      ring]
    change -stoppedExpectation D n
      (fun z ↦ ε + K * (if z ∈ D then 1 else 0)) x =
        stoppedExpectation D n
          (fun z ↦ (-1 : ℝ) * (ε + K * (if z ∈ D then 1 else 0))) x
    rw [stoppedExpectation_const_mul]
    ring
  have hu := le_of_tendsto_of_tendsto' hdiff hright hupperFinite
  have hl := le_of_tendsto_of_tendsto' hleft hdiff hlowerFinite
  rw [abs_le]
  exact ⟨by linarith, hu⟩

/-- Annulus specialization of the two-boundary potential representation.
This is the finite exact form from which the two complementary logarithmic
ratios in HLOZ (4.8)--(4.9) follow once the radial boundary-potential
expansion is supplied. -/
theorem abs_planarPotential_sub_annulusExitMixture_le
    {r R : ℕ} (hr : 0 < r) {x : Point} (hx : x ∈ latticeAnnulus r R)
    (innerValue outerValue ε : ℝ) (hε0 : 0 ≤ ε)
    (hinner : ∀ z, z ∈ annulusInnerExitBoundary r R →
      |planarPotentialKernel z - innerValue| ≤ ε)
    (houter : ∀ z, z ∈ annulusOuterExitBoundary r R →
      |planarPotentialKernel z - outerValue| ≤ ε) :
    |planarPotentialKernel x -
        (innerValue *
            (exitMass (latticeAnnulus r R)
              (annulusInnerExitBoundary r R) x).toReal +
          outerValue *
            (exitMass (latticeAnnulus r R)
              (annulusOuterExitBoundary r R) x).toReal)| ≤ ε := by
  apply abs_potential_sub_twoBoundaryExitMixture_le
    (latticeAnnulus r R) R hx (latticeAnnulus_subset_coordinateBox r R)
    (zero_not_mem_latticeAnnulus hr)
    (annulusInnerExitBoundary r R) (annulusOuterExitBoundary r R)
  · intro z hz
    exact (mem_annulusInnerExitBoundary r R z).mp hz |>.1
  · intro z hz
    exact (mem_annulusOuterExitBoundary r R z).mp hz |>.1
  · exact annulus_exitBoundary_disjoint r R
  · exact annulus_exitBoundary_union r R
  · exact hε0
  · exact hinner
  · exact houter

theorem annulus_exitMass_toReal_add_eq_one
    {r R : ℕ} {x : Point} (hx : x ∈ latticeAnnulus r R) :
    (exitMass (latticeAnnulus r R)
        (annulusInnerExitBoundary r R) x).toReal +
      (exitMass (latticeAnnulus r R)
        (annulusOuterExitBoundary r R) x).toReal = 1 := by
  apply exitMass_partition_toReal_add_eq_one
    (latticeAnnulus r R) R hx (latticeAnnulus_subset_coordinateBox r R)
  · intro z hz
    exact (mem_annulusInnerExitBoundary r R z).mp hz |>.1
  · intro z hz
    exact (mem_annulusOuterExitBoundary r R z).mp hz |>.1
  · exact annulus_exitBoundary_disjoint r R
  · exact annulus_exitBoundary_union r R

/-- Outer-before-inner annulus exit ratio, the finite quantitative form of
HLOZ (4.8). -/
theorem annulusOuterExit_ratio_bounds
    {r R : ℕ} (hr : 0 < r) {x : Point} (hx : x ∈ latticeAnnulus r R)
    (innerValue outerValue ε : ℝ) (hε0 : 0 ≤ ε)
    (hdelta : 0 < outerValue - innerValue)
    (hinner : ∀ z, z ∈ annulusInnerExitBoundary r R →
      |planarPotentialKernel z - innerValue| ≤ ε)
    (houter : ∀ z, z ∈ annulusOuterExitBoundary r R →
      |planarPotentialKernel z - outerValue| ≤ ε) :
    (planarPotentialKernel x - innerValue - ε) /
        (outerValue - innerValue) ≤
      (exitMass (latticeAnnulus r R)
        (annulusOuterExitBoundary r R) x).toReal ∧
    (exitMass (latticeAnnulus r R)
        (annulusOuterExitBoundary r R) x).toReal ≤
      (planarPotentialKernel x - innerValue + ε) /
        (outerValue - innerValue) := by
  let pInner := (exitMass (latticeAnnulus r R)
    (annulusInnerExitBoundary r R) x).toReal
  let pOuter := (exitMass (latticeAnnulus r R)
    (annulusOuterExitBoundary r R) x).toReal
  have htotal : pInner + pOuter = 1 :=
    annulus_exitMass_toReal_add_eq_one hx
  have hmix := abs_planarPotential_sub_annulusExitMixture_le
    hr hx innerValue outerValue ε hε0 hinner houter
  have hrewrite : innerValue * pInner + outerValue * pOuter =
      innerValue + (outerValue - innerValue) * pOuter := by
    linear_combination innerValue * htotal
  change |planarPotentialKernel x -
    (innerValue * pInner + outerValue * pOuter)| ≤ ε at hmix
  rw [hrewrite, abs_le] at hmix
  constructor
  · rw [div_le_iff₀ hdelta]
    linarith
  · rw [le_div_iff₀ hdelta]
    linarith

/-- Inner-before-outer annulus exit ratio, the finite quantitative form of
HLOZ (4.9). -/
theorem annulusInnerExit_ratio_bounds
    {r R : ℕ} (hr : 0 < r) {x : Point} (hx : x ∈ latticeAnnulus r R)
    (innerValue outerValue ε : ℝ) (hε0 : 0 ≤ ε)
    (hdelta : 0 < outerValue - innerValue)
    (hinner : ∀ z, z ∈ annulusInnerExitBoundary r R →
      |planarPotentialKernel z - innerValue| ≤ ε)
    (houter : ∀ z, z ∈ annulusOuterExitBoundary r R →
      |planarPotentialKernel z - outerValue| ≤ ε) :
    (outerValue - planarPotentialKernel x - ε) /
        (outerValue - innerValue) ≤
      (exitMass (latticeAnnulus r R)
        (annulusInnerExitBoundary r R) x).toReal ∧
    (exitMass (latticeAnnulus r R)
        (annulusInnerExitBoundary r R) x).toReal ≤
      (outerValue - planarPotentialKernel x + ε) /
        (outerValue - innerValue) := by
  let pInner := (exitMass (latticeAnnulus r R)
    (annulusInnerExitBoundary r R) x).toReal
  let pOuter := (exitMass (latticeAnnulus r R)
    (annulusOuterExitBoundary r R) x).toReal
  have htotal : pInner + pOuter = 1 :=
    annulus_exitMass_toReal_add_eq_one hx
  have hmix := abs_planarPotential_sub_annulusExitMixture_le
    hr hx innerValue outerValue ε hε0 hinner houter
  have hrewrite : innerValue * pInner + outerValue * pOuter =
      outerValue - (outerValue - innerValue) * pInner := by
    linear_combination outerValue * htotal
  change |planarPotentialKernel x -
    (innerValue * pInner + outerValue * pOuter)| ≤ ε at hmix
  rw [hrewrite, abs_le] at hmix
  constructor
  · rw [div_le_iff₀ hdelta]
    linarith
  · rw [le_div_iff₀ hdelta]
    linarith

/-! ## Canonical path-law realization of exit masses -/

/-- The absorbed increment path lies in the designated boundary set at time
`n`.  When the boundary is disjoint from the domain these events increase in
`n`, because the absorbed path freezes at its first exit point. -/
def absorbedExitAt (D B : Finset Point) (n : ℕ) (x : Point) : Set StepPath :=
  {ω | absorbedPosition D x ω n ∈ B}

lemma absorbedPosition_congr_of_eq_lt (D : Finset Point) (x : Point)
    {ω v : StepPath} {n : ℕ} (h : ∀ j < n, ω j = v j) :
    absorbedPosition D x ω n = absorbedPosition D x v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [absorbedPosition_succ, absorbedPosition_succ,
        ih (fun j hj ↦ h j (by omega)), h n (by omega)]

lemma measurableSet_absorbedExitAt_filtration
    (D B : Finset Point) (n : ℕ) (x : Point) :
    MeasurableSet[incrementFiltration n] (absorbedExitAt D B n x) := by
  let extend : (Fin n → Direction) → StepPath := fun u j ↦
    if hj : j < n then u ⟨j, hj⟩ else 0
  let C : Set (Fin n → Direction) :=
    {u | absorbedPosition D x (extend u) n ∈ B}
  have hpos (ω : StepPath) :
      absorbedPosition D x (extend (stepPrefix n ω)) n =
        absorbedPosition D x ω n := by
    apply absorbedPosition_congr_of_eq_lt
    intro j hj
    simp [extend, stepPrefix, hj]
  have heq : absorbedExitAt D B n x = stepPrefix n ⁻¹' C := by
    ext ω
    change absorbedPosition D x ω n ∈ B ↔
      absorbedPosition D x (extend (stepPrefix n ω)) n ∈ B
    rw [hpos]
  rw [incrementFiltration_apply, heq]
  exact ⟨C, (Set.to_countable C).measurableSet, rfl⟩

lemma measurableSet_absorbedExitAt
    (D B : Finset Point) (n : ℕ) (x : Point) :
    MeasurableSet (absorbedExitAt D B n x) :=
  incrementFiltration.le n _
    (measurableSet_absorbedExitAt_filtration D B n x)

lemma absorbedPosition_succ_shift (D : Finset Point) (x : Point)
    (ω : StepPath) (n : ℕ) :
    absorbedPosition D x ω (n + 1) =
      absorbedPosition D (absorbedStep D x (ω 0)) (shiftSteps 1 ω) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change absorbedStep D (absorbedPosition D x ω (n + 1)) (ω (n + 1)) =
        absorbedStep D
          (absorbedPosition D (absorbedStep D x (ω 0)) (shiftSteps 1 ω) n)
          ((shiftSteps 1 ω) n)
      rw [ih]
      simp [shiftSteps, Nat.add_comm]

private def absorbedExitFirstPiece (D B : Finset Point) (n : ℕ)
    (x : Point) (d : Direction) : Set StepPath :=
  {ω | ω 0 = d} ∩ shiftSteps 1 ⁻¹'
    absorbedExitAt D B n (absorbedStep D x d)

lemma absorbedExitAt_succ_eq_iUnion (D B : Finset Point) (n : ℕ)
    (x : Point) :
    absorbedExitAt D B (n + 1) x =
      ⋃ d : Direction, absorbedExitFirstPiece D B n x d := by
  ext ω
  rw [absorbedExitAt, Set.mem_ofPred_eq, absorbedPosition_succ_shift]
  simp only [Set.mem_iUnion, absorbedExitFirstPiece, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_preimage, absorbedExitAt]
  constructor
  · intro h
    exact ⟨ω 0, rfl, h⟩
  · rintro ⟨d, hd, h⟩
    subst d
    exact h

lemma absorbedExitFirstPiece_pairwise_disjoint (D B : Finset Point)
    (n : ℕ) (x : Point) : Pairwise fun d e : Direction ↦
      Disjoint (absorbedExitFirstPiece D B n x d)
        (absorbedExitFirstPiece D B n x e) := by
  intro d e hde
  rw [Set.disjoint_left]
  intro ω hd he
  exact hde (hd.1.symm.trans he.1)

lemma measurableSet_absorbedExitFirstPiece (D B : Finset Point)
    (n : ℕ) (x : Point) (d : Direction) :
    MeasurableSet (absorbedExitFirstPiece D B n x d) := by
  exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    ((measurable_shiftSteps 1)
      (measurableSet_absorbedExitAt D B n (absorbedStep D x d)))

lemma measure_firstDirection_inter_shift_absorbedExitAt
    (D B : Finset Point) (n : ℕ) (x : Point) (d : Direction) :
    fairSteps ({ω : StepPath | ω 0 = d} ∩
        shiftSteps 1 ⁻¹' absorbedExitAt D B n x) =
      (1 / 4 : ℝ≥0∞) * fairSteps (absorbedExitAt D B n x) := by
  have hfil := measurableSet_absorbedExitAt_filtration D B n x
  rw [incrementFiltration_apply] at hfil
  obtain ⟨C, hC, hCeq⟩ := hfil
  have htail : shiftSteps 1 ⁻¹' absorbedExitAt D B n x =
      stepBlock 1 n ⁻¹' C := by
    rw [← hCeq]
    rfl
  let firstDirectionSet : Set (Fin 1 → Direction) := {u | u 0 = d}
  have hind :=
    (indepFun_stepPrefix_stepBlock 1 n).measure_inter_preimage_eq_mul
      firstDirectionSet C (Set.to_countable _).measurableSet hC
  have hfirstPre : stepPrefix 1 ⁻¹' firstDirectionSet =
      {ω : StepPath | ω 0 = d} := by
    ext ω
    simp [firstDirectionSet, stepPrefix]
  rw [hfirstPre, ← htail] at hind
  rw [hind]
  have hfirst : fairSteps {ω : StepPath | ω 0 = d} = 1 / 4 := by
    change fairSteps ((fun ω : StepPath ↦ ω 0) ⁻¹' {d}) = 1 / 4
    rw [← Measure.map_apply (measurable_pi_apply 0) (MeasurableSet.singleton d),
      fairSteps_eval, fairStep_singleton]
  have hshift : fairSteps (shiftSteps 1 ⁻¹' absorbedExitAt D B n x) =
      fairSteps (absorbedExitAt D B n x) := by
    rw [← Measure.map_apply (measurable_shiftSteps 1)
      (measurableSet_absorbedExitAt D B n x), fairSteps_map_shiftSteps]
  rw [hfirst, hshift]

lemma measure_absorbedExitAt_succ (D B : Finset Point) (n : ℕ)
    (x : Point) :
    fairSteps (absorbedExitAt D B (n + 1) x) =
      ∑ d : Direction, (1 / 4 : ℝ≥0∞) *
        fairSteps (absorbedExitAt D B n (absorbedStep D x d)) := by
  rw [absorbedExitAt_succ_eq_iUnion]
  rw [measure_iUnion (absorbedExitFirstPiece_pairwise_disjoint D B n x)
    (measurableSet_absorbedExitFirstPiece D B n x)]
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro d hd
  exact measure_firstDirection_inter_shift_absorbedExitAt D B n
    (absorbedStep D x d) d

/-- The exact finite stopped-tree exit mass is the probability that the
absorbed IID increment path is in `B` at the same time. -/
theorem fairSteps_absorbedExitAt (D B : Finset Point) (n : ℕ) (x : Point) :
    fairSteps (absorbedExitAt D B n x) =
      ENNReal.ofReal (finiteExitMass D B n x) := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ B <;>
        simp [absorbedExitAt, finiteExitMass, boundaryIndicator, hx]
  | succ n ih =>
      rw [measure_absorbedExitAt_succ]
      simp_rw [ih]
      rw [finiteExitMass, stoppedExpectation_succ]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · change (∑ d ∈ (Finset.univ : Finset Direction), (1 / 4 : ℝ≥0∞) *
            ENNReal.ofReal (finiteExitMass D B n (absorbedStep D x d))) =
          (∑ d ∈ (Finset.univ : Finset Direction),
            ENNReal.ofReal (finiteExitMass D B n (absorbedStep D x d))) /
              ENNReal.ofReal 4
        simp only [ENNReal.ofReal_ofNat]
        rw [← Finset.mul_sum]
        simp [div_eq_mul_inv, mul_comm]
      · intro d hd
        exact finiteExitMass_nonneg D B n (absorbedStep D x d)

/-- The increasing-horizon `exitMass` is the probability of ever entering
`B` for the absorbed IID increment path. -/
theorem fairSteps_iUnion_absorbedExitAt_eq_exitMass
    (D B : Finset Point) (hDB : Disjoint D B) (x : Point) :
    fairSteps (⋃ n, absorbedExitAt D B n x) = exitMass D B x := by
  have hmono : Monotone (absorbedExitAt D B · x) := by
    intro n m hnm ω hω
    have hstable := absorbedPosition_stable_after_exit D x ω
      (fun hD ↦ Finset.disjoint_left.mp hDB hD hω) (m - n)
    rw [Nat.add_sub_of_le hnm] at hstable
    change absorbedPosition D x ω n ∈ B at hω
    change absorbedPosition D x ω m ∈ B
    rw [hstable]
    exact hω
  rw [hmono.measure_iUnion]
  unfold exitMass
  congr 1
  funext n
  exact fairSteps_absorbedExitAt D B n x

/-- Absorb an arbitrary coordinate path on the first step leaving `D`, using
its consecutive increments. -/
def absorbedWalkPosition (D : Finset Point) (s : WalkPath) : ℕ → Point
  | 0 => s 0
  | n + 1 =>
      let z := absorbedWalkPosition D s n
      if z ∈ D then z + (s (n + 1) - s n) else z

@[simp] lemma absorbedWalkPosition_zero (D : Finset Point) (s : WalkPath) :
    absorbedWalkPosition D s 0 = s 0 := rfl

lemma absorbedWalkPosition_succ (D : Finset Point) (s : WalkPath) (n : ℕ) :
    absorbedWalkPosition D s (n + 1) =
      if absorbedWalkPosition D s n ∈ D then
        absorbedWalkPosition D s n + (s (n + 1) - s n)
      else absorbedWalkPosition D s n := rfl

lemma measurable_absorbedWalkPosition (D : Finset Point) (n : ℕ) :
    Measurable fun s : WalkPath ↦ absorbedWalkPosition D s n := by
  induction n with
  | zero => exact measurable_pi_apply 0
  | succ n ih =>
      rw [show (fun s : WalkPath ↦ absorbedWalkPosition D s (n + 1)) =
          fun s ↦ if absorbedWalkPosition D s n ∈ D then
            absorbedWalkPosition D s n + (s (n + 1) - s n)
          else absorbedWalkPosition D s n by rfl]
      apply Measurable.ite
      · exact D.measurableSet.preimage ih
      · exact ih.add
          ((measurable_pi_apply (n + 1)).sub (measurable_pi_apply n))
      · exact ih

/-- The canonical coordinate-path event that the first absorbed exit vertex
lies in `B`. -/
def walkExitThrough (D B : Finset Point) : Set WalkPath :=
  ⋃ n, {s | absorbedWalkPosition D s n ∈ B}

lemma measurableSet_walkExitThrough (D B : Finset Point) :
    MeasurableSet (walkExitThrough D B) := by
  unfold walkExitThrough
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_absorbedWalkPosition D n) B.measurableSet

lemma absorbedWalkPosition_trajectoryFrom
    (D : Finset Point) (x : Point) (ω : StepPath) (n : ℕ) :
    absorbedWalkPosition D (trajectoryFrom x ω) n =
      absorbedPosition D x ω n := by
  induction n with
  | zero => simp [absorbedWalkPosition, trajectoryFrom]
  | succ n ih =>
      rw [absorbedWalkPosition_succ, absorbedPosition_succ, ih,
        trajectoryFrom_succ]
      by_cases h : absorbedPosition D x ω n ∈ D
      · rw [if_pos h, absorbedStep_of_mem D h]
        unfold neighbor
        abel
      · rw [if_neg h, absorbedStep_of_notMem D h]

/-- `exitMass` is exactly the probability of the canonical coordinate-path
exit event for planar simple random walk. -/
theorem simpleRandomWalkFrom_walkExitThrough
    (D B : Finset Point) (hDB : Disjoint D B) (x : Point) :
    simpleRandomWalkFrom x (walkExitThrough D B) = exitMass D B x := by
  rw [simpleRandomWalkFrom, Measure.map_apply (measurable_trajectoryFrom x)
    (measurableSet_walkExitThrough D B)]
  have hpre : trajectoryFrom x ⁻¹' walkExitThrough D B =
      ⋃ n, absorbedExitAt D B n x := by
    ext ω
    simp only [walkExitThrough, Set.mem_preimage, Set.mem_iUnion,
      Set.mem_ofPred_eq, absorbedExitAt]
    constructor <;> rintro ⟨n, hn⟩ <;>
      exact ⟨n, by simpa [absorbedWalkPosition_trajectoryFrom] using hn⟩
  rw [hpre, fairSteps_iUnion_absorbedExitAt_eq_exitMass D B hDB x]

lemma latticeAnnulus_disjoint_innerExitBoundary (r R : ℕ) :
    Disjoint (latticeAnnulus r R) (annulusInnerExitBoundary r R) := by
  rw [Finset.disjoint_left]
  intro z hzD hzB
  exact (mem_outerBoundary _ z).mp
    ((mem_annulusInnerExitBoundary r R z).mp hzB).1 |>.1 hzD

lemma latticeAnnulus_disjoint_outerExitBoundary (r R : ℕ) :
    Disjoint (latticeAnnulus r R) (annulusOuterExitBoundary r R) := by
  rw [Finset.disjoint_left]
  intro z hzD hzB
  exact (mem_outerBoundary _ z).mp
    ((mem_annulusOuterExitBoundary r R z).mp hzB).1 |>.1 hzD

/-- Canonical planar-SRW version of the finite quantitative outer-exit ratio
behind HLOZ (4.8). -/
theorem simpleRandomWalkFrom_annulusOuterExit_ratio_bounds
    {r R : ℕ} (hr : 0 < r) {x : Point} (hx : x ∈ latticeAnnulus r R)
    (innerValue outerValue ε : ℝ) (hε0 : 0 ≤ ε)
    (hdelta : 0 < outerValue - innerValue)
    (hinner : ∀ z, z ∈ annulusInnerExitBoundary r R →
      |planarPotentialKernel z - innerValue| ≤ ε)
    (houter : ∀ z, z ∈ annulusOuterExitBoundary r R →
      |planarPotentialKernel z - outerValue| ≤ ε) :
    (planarPotentialKernel x - innerValue - ε) /
        (outerValue - innerValue) ≤
      (simpleRandomWalkFrom x
        (walkExitThrough (latticeAnnulus r R)
          (annulusOuterExitBoundary r R))).toReal ∧
    (simpleRandomWalkFrom x
        (walkExitThrough (latticeAnnulus r R)
          (annulusOuterExitBoundary r R))).toReal ≤
      (planarPotentialKernel x - innerValue + ε) /
        (outerValue - innerValue) := by
  rw [simpleRandomWalkFrom_walkExitThrough _ _
    (latticeAnnulus_disjoint_outerExitBoundary r R)]
  exact annulusOuterExit_ratio_bounds hr hx innerValue outerValue ε hε0
    hdelta hinner houter

/-- Canonical planar-SRW version of the finite quantitative inner-exit ratio
behind HLOZ (4.9). -/
theorem simpleRandomWalkFrom_annulusInnerExit_ratio_bounds
    {r R : ℕ} (hr : 0 < r) {x : Point} (hx : x ∈ latticeAnnulus r R)
    (innerValue outerValue ε : ℝ) (hε0 : 0 ≤ ε)
    (hdelta : 0 < outerValue - innerValue)
    (hinner : ∀ z, z ∈ annulusInnerExitBoundary r R →
      |planarPotentialKernel z - innerValue| ≤ ε)
    (houter : ∀ z, z ∈ annulusOuterExitBoundary r R →
      |planarPotentialKernel z - outerValue| ≤ ε) :
    (outerValue - planarPotentialKernel x - ε) /
        (outerValue - innerValue) ≤
      (simpleRandomWalkFrom x
        (walkExitThrough (latticeAnnulus r R)
          (annulusInnerExitBoundary r R))).toReal ∧
    (simpleRandomWalkFrom x
        (walkExitThrough (latticeAnnulus r R)
          (annulusInnerExitBoundary r R))).toReal ≤
      (outerValue - planarPotentialKernel x + ε) /
        (outerValue - innerValue) := by
  rw [simpleRandomWalkFrom_walkExitThrough _ _
    (latticeAnnulus_disjoint_innerExitBoundary r R)]
  exact annulusInnerExit_ratio_bounds hr hx innerValue outerValue ε hε0
    hdelta hinner houter

end

end GreenHarnack
end Erdos1165
