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

import ErdosProblems.Erdos991.CapArea
import ErdosProblems.Erdos991.CapSupEnergy
import ErdosProblems.Erdos991.EnergyFromLog
import ErdosProblems.Erdos991.Fekete
import ErdosProblems.Erdos991.LogPotential
import ErdosProblems.Erdos991.LogSeriesBound

/-!
# Erdős Problem 991

For a finite subset of the unit two-sphere, consider the product of its
Euclidean chordal distances over unordered pairs.  We prove that every
sequence of configurations maximizing that product is asymptotically
uniform in spherical caps.

The normalized area of the cap
`{x | t ≤ ⟪x,u⟫}` is `(1 - t) / 2`.  Thus the conclusion below is exactly

`sup_C |#(A n ∩ C) - area(C) * n| = o(n)`.

The proof uses the finite positive-kernel and Stolarsky identities established
in `ErdosProblems.Erdos988`.  Its mathematical details and source audit are
in `tex/991.tex`.

Progress log:
* mathematical reconstruction and source verification: complete;
* Lean implementation: exact cap area, logarithmic potential, Fekete
  comparison, logarithmic series, asymptotic energy, and cap supremum complete;
* final validation: the integrated theorem and dependency audit appear below.
-/

open Filter Finset MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Pointwise Topology

namespace Erdos991

noncomputable section

open Erdos988

/-- Chordal distance, regarded as a function of an unordered pair. -/
def unorderedPairDistance : Sym2 S2 → ℝ :=
  Check991Fekete.pairDist

/-- The product of chordal distances over the unordered, distinct pairs in
`P`.  This is literally the product occurring in Erdős Problem 991. -/
def distanceProduct (P : Finset S2) : ℝ :=
  Check991Fekete.unorderedDistanceProduct P

/-- A finite subset of the sphere maximizes the unordered distance product
among all subsets having the same cardinality. -/
def IsDistanceProductMaximizer (P : Finset S2) : Prop :=
  ∀ Q : Finset S2, Q.card = P.card → distanceProduct Q ≤ distanceProduct P

/-- The absolute error of a cap, written with its literal probability-normalized
surface area rather than the closed formula `(1-t)/2`. -/
noncomputable def actualCapError (P : Finset S2) (u : S2) (t : ℝ) : ℝ := by
  classical
  exact |((P.filter fun x ↦ x ∈ sphericalCap u t).card : ℝ) -
    normalizedArea (sphericalCap u t) * P.card|

/-- All literal-area cap errors of `P`. -/
noncomputable def actualCapErrorSet (P : Finset S2) : Set ℝ :=
  {r | ∃ u : S2, ∃ t : ℝ,
    t ∈ Icc (-1 : ℝ) 1 ∧ r = actualCapError P u t}

/-- The exact discrepancy appearing in Erdős Problem 991: the supremum is
over all spherical caps and their actual normalized surface areas. -/
noncomputable def actualSphericalCapDiscrepancy (P : Finset S2) : ℝ :=
  sSup (actualCapErrorSet P)

lemma actualCapError_eq_capError (P : Finset S2) (u : S2) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    actualCapError P u t = capError P u t := by
  classical
  rw [actualCapError, capError, signedCapError, normalizedArea_sphericalCap u ht]

theorem actualSphericalCapDiscrepancy_eq (P : Finset S2) :
    actualSphericalCapDiscrepancy P = sphericalCapDiscrepancy P := by
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨u, t, ht, rfl⟩
    exact ⟨u, t, ht, actualCapError_eq_capError P u ht⟩
  · rintro ⟨u, t, ht, rfl⟩
    exact ⟨u, t, ht, (actualCapError_eq_capError P u ht).symm⟩

/-- The analytic core of the proof.  It is stated with the literal cap-area
fact isolated, so the exact geometric calculation can be
used transparently in `erdos_991` below. -/
theorem erdos_991_of_exact_area
    (A : ℕ → Finset S2)
    (hcard : ∀ n : ℕ, (A n).card = n)
    (hmax : ∀ n : ℕ, IsDistanceProductMaximizer (A n))
    (hcap : ∀ (u : S2) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      (surfaceProbability : Measure S2) (sphericalCap u t) =
        ENNReal.ofReal (capArea t)) :
    (fun n : ℕ ↦ sphericalCapDiscrepancy (A n)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  have hFekete (n : ℕ) : Check991Fekete.IsLogFekete n (A n) := by
    refine ⟨hcard n, ?_⟩
    intro B hB
    exact hmax n B (hB.trans (hcard n).symm)
  have hlogIntegrable (y : S2) :
      Integrable (fun x : S2 ↦ Real.log (dist x y))
        (surfaceProbability : Measure S2) :=
    Check991LogPotential.integrable_log_dist_of_cap_area y (hcap y)
  have hlogIntegral (y : S2) :
      (∫ x : S2, Real.log (dist x y) ∂(surfaceProbability : Measure S2)) =
        Real.log 2 - 1 / 2 :=
    Check991LogPotential.integral_log_dist_of_cap_area y (hcap y)
  have hcapReal : Erdos991CapSupEnergy.ExactSphericalCapArea := by
    intro u t ht
    simp only [Measure.real, hcap u t ht,
      ENNReal.toReal_ofReal (capArea_nonneg ht)]
  have hnull (S : Finset S2) :
      (surfaceProbability : Measure S2) (S : Set S2) = 0 :=
    surfaceProbability_finset_null S
  have henergyBound (n : ℕ) :
      Check991Fekete.orderedLogEnergy (A n) ≤
        (n : ℝ) * ((n : ℝ) - 1) * (1 / 2 - Real.log 2) :=
    Check991Fekete.IsLogFekete.orderedLogEnergy_le_sphere_constant_of_integral
      (hFekete n) (surfaceProbability : Measure S2)
      hlogIntegrable hlogIntegral hnull
  have hoff (n : ℕ) :
      Erdos991EnergyFromLog.truncatedOffDiagonalLogMoment (A n) n ≤
        (n : ℝ) * (n - 1) := by
    have hseries := Erdos991LogSeriesBound.truncatedOffDiagonalLogMoment_le (A n) n
    rw [hcard n] at hseries
    calc
      Erdos991EnergyFromLog.truncatedOffDiagonalLogMoment (A n) n ≤
          2 * (Check991Fekete.orderedLogEnergy (A n) +
            (n : ℝ) * ((n : ℝ) - 1) * Real.log 2) := hseries
      _ ≤ 2 * (((n : ℝ) * ((n : ℝ) - 1) * (1 / 2 - Real.log 2)) +
            (n : ℝ) * ((n : ℝ) - 1) * Real.log 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa only [add_comm] using
            (add_le_add_right (henergyBound n)
              ((n : ℝ) * ((n : ℝ) - 1) * Real.log 2))
      _ = (n : ℝ) * (n - 1) := by ring
  have henergy : Tendsto
      (fun n : ℕ ↦ energyDeficit (A n) / (n : ℝ) ^ 2)
        atTop (nhds 0) :=
    Erdos991EnergyFromLog.energyDeficit_div_sq_tendsto_zero_of_offDiagonal_log_bound
      A hcard hoff
  exact
    Erdos991CapSupEnergy.discrepancy_isLittleO_of_energyDeficit_of_exactSphericalCapArea
      hcapReal A hcard henergy

/-- **Erdős Problem 991.**  Every sequence of `n`-point subsets of the unit
two-sphere maximizing the product of all unordered pairwise chordal distances
has spherical-cap counting discrepancy `o(n)`, where cap area is the literal
probability-normalized surface area. -/
theorem erdos_991
    (A : ℕ → Finset S2)
    (hcard : ∀ n : ℕ, (A n).card = n)
    (hmax : ∀ n : ℕ, IsDistanceProductMaximizer (A n)) :
    (fun n : ℕ ↦ actualSphericalCapDiscrepancy (A n)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
  simpa only [actualSphericalCapDiscrepancy_eq] using
    erdos_991_of_exact_area A hcard hmax
      (fun u t ht ↦ surfaceProbability_sphericalCap u ht)

end

end Erdos991

#print axioms Erdos991.erdos_991
