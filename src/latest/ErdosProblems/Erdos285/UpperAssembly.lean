/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős 285: Martin's upper-bound assembly

This file contains only the high-level bookkeeping in Proposition 4 of
Greg Martin's *Denser Egyptian fractions*.  The two difficult arithmetic
inputs are represented by explicit finite sets:

* `large` is the set supplied by the approximate-representation result
  (Proposition 6 in Martin's paper), and
* `correction` is the small-denominator set supplied by the exact-correction
  result (Proposition 7).

The theorem `propositionFour_upperAssembly` proves, rather than assumes, that
their union is disjoint, has the requested cardinality, has the exact
reciprocal sum, avoids zero, and has all denominators at most the chosen
cutoff.  `propositionFour_upperAssembly_eventually` is the filter-level form
used by an asymptotic proof.  The final two lemmas turn the quantitative
choice of the cutoff into convergence of its ratio to the number of terms.
-/

namespace Erdos285

open Filter Finset
open scoped BigOperators Topology

/-- The real reciprocal sum of a finite set of natural denominators. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (1 : ℝ) / n

/-- Martin's `π⁺(y)`: the number of prime powers not exceeding `y`. -/
def primePowerCount (y : ℕ) : ℕ :=
  ((Finset.Icc 1 y).filter IsPrimePow).card

/-- Proposition 7 contributes exactly twice `π⁺(y)` denominators. -/
def correctionCount (y : ℕ) : ℕ :=
  2 * primePowerCount y

/-- The number `R = t - 2π⁺(y)` requested from Proposition 6. -/
def mainCount (t y : ℕ) : ℕ :=
  t - correctionCount y

/-- The upper bound `2 y⁴` for the denominators in Proposition 7. -/
def correctionCutoff (y : ℕ) : ℕ :=
  2 * y ^ 4

theorem mainCount_add_correctionCount {t y : ℕ} (hcount : correctionCount y ≤ t) :
    mainCount t y + correctionCount y = t := by
  exact Nat.sub_add_cancel hcount

/-- The properties of the final finite set needed by the upper-bound argument. -/
structure UpperWitness (r : ℝ) (t x : ℕ) (A : Finset ℕ) : Prop where
  card_eq : A.card = t
  zero_not_mem : 0 ∉ A
  sum_eq : reciprocalSum A = r
  le_cutoff : ∀ n ∈ A, n ≤ x

namespace UpperWitness

/-- A nonempty upper witness has maximum denominator at most its cutoff. -/
theorem max'_le {r : ℝ} {t x : ℕ} {A : Finset ℕ}
    (hA : UpperWitness r t x A) (ht : 0 < t) :
    A.max' (by
      apply Finset.card_ne_zero.mp
      rw [hA.card_eq]
      exact ht.ne') ≤ x := by
  exact hA.le_cutoff _ (Finset.max'_mem A _)

end UpperWitness

/--
All Proposition 6/7 hypotheses at one value of `t`.  This bundled form is
useful under `Filter.Eventually`; the main assembly theorem below also exposes
every field as an ordinary theorem argument.
-/
structure PropositionFourInput
    (r : ℝ) (t y R lower x : ℕ) (residual : ℝ)
    (large correction : Finset ℕ) : Prop where
  R_eq : R = mainCount t y
  correctionCount_le : correctionCount y ≤ t
  large_card : large.card = R
  correction_card : correction.card = correctionCount y
  large_zero_not_mem : 0 ∉ large
  correction_zero_not_mem : 0 ∉ correction
  large_sum : reciprocalSum large = r - residual
  correction_sum : reciprocalSum correction = residual
  large_lower : ∀ n ∈ large, lower ≤ n
  large_upper : ∀ n ∈ large, n ≤ x
  correction_upper : ∀ n ∈ correction, n ≤ correctionCutoff y
  cutoffs_separated : correctionCutoff y < lower
  correctionCutoff_le : correctionCutoff y ≤ x

/--
The bookkeeping step in Martin's Proposition 4.

The interval separation proves disjointness.  Consequently cardinalities and
reciprocal sums add without overlap.  The identities `R = t - 2π⁺(y)` and
`|correction| = 2π⁺(y)` then give exactly `t` terms.
-/
theorem propositionFour_upperAssembly
    {r : ℝ} {t y R lower x : ℕ} {residual : ℝ}
    {large correction : Finset ℕ}
    (hR : R = mainCount t y)
    (hcount : correctionCount y ≤ t)
    (hlargeCard : large.card = R)
    (hcorrectionCard : correction.card = correctionCount y)
    (hlargeZero : 0 ∉ large)
    (hcorrectionZero : 0 ∉ correction)
    (hlargeSum : reciprocalSum large = r - residual)
    (hcorrectionSum : reciprocalSum correction = residual)
    (hlargeLower : ∀ n ∈ large, lower ≤ n)
    (hlargeUpper : ∀ n ∈ large, n ≤ x)
    (hcorrectionUpper : ∀ n ∈ correction, n ≤ correctionCutoff y)
    (hseparated : correctionCutoff y < lower)
    (hcorrectionCutoff : correctionCutoff y ≤ x) :
    Disjoint large correction ∧ UpperWitness r t x (large ∪ correction) := by
  have hdisjoint : Disjoint large correction := by
    rw [Finset.disjoint_left]
    intro n hnlarge hncorrection
    have hnlow : lower ≤ n := hlargeLower n hnlarge
    have hnupper : n ≤ correctionCutoff y := hcorrectionUpper n hncorrection
    omega
  refine ⟨hdisjoint, ?_⟩
  refine
    { card_eq := ?_
      zero_not_mem := ?_
      sum_eq := ?_
      le_cutoff := ?_ }
  · rw [Finset.card_union_of_disjoint hdisjoint, hlargeCard, hR, hcorrectionCard]
    exact mainCount_add_correctionCount hcount
  · simpa only [Finset.mem_union, not_or] using ⟨hlargeZero, hcorrectionZero⟩
  · rw [reciprocalSum, Finset.sum_union hdisjoint, ← reciprocalSum,
      ← reciprocalSum, hlargeSum, hcorrectionSum]
    ring
  · intro n hn
    rw [Finset.mem_union] at hn
    rcases hn with hnlarge | hncorrection
    · exact hlargeUpper n hnlarge
    · exact (hcorrectionUpper n hncorrection).trans hcorrectionCutoff

/-- The bundled-input version of `propositionFour_upperAssembly`. -/
theorem PropositionFourInput.assemble
    {r : ℝ} {t y R lower x : ℕ} {residual : ℝ}
    {large correction : Finset ℕ}
    (h : PropositionFourInput r t y R lower x residual large correction) :
    Disjoint large correction ∧ UpperWitness r t x (large ∪ correction) := by
  exact propositionFour_upperAssembly h.R_eq h.correctionCount_le h.large_card
    h.correction_card h.large_zero_not_mem h.correction_zero_not_mem h.large_sum
    h.correction_sum h.large_lower h.large_upper h.correction_upper
    h.cutoffs_separated h.correctionCutoff_le

/--
Apply the two arithmetic constructions eventually and assemble their union at
every sufficiently large number of terms.
-/
theorem propositionFour_upperAssembly_eventually
    (r : ℝ) (y R lower x : ℕ → ℕ) (residual : ℕ → ℝ)
    (large correction : ℕ → Finset ℕ)
    (hinput : ∀ᶠ t in atTop,
      PropositionFourInput r t (y t) (R t) (lower t) (x t) (residual t)
        (large t) (correction t)) :
    ∀ᶠ t in atTop, UpperWitness r t (x t) (large t ∪ correction t) := by
  filter_upwards [hinput] with t ht
  exact ht.assemble.2

/--
An additive `o(t)` error in the cutoff implies convergence of the cutoff per
term.  The division by `t` is harmless eventually because positive naturals
form a tail of `atTop`.
-/
theorem tendsto_cutoff_ratio_of_additive_error
    (C : ℝ) (x : ℕ → ℕ) (error : ℕ → ℝ)
    (hx : ∀ᶠ t in atTop, (x t : ℝ) = C * t + error t)
    (herror : Tendsto (fun t : ℕ ↦ error t / (t : ℝ)) atTop (nhds 0)) :
    Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C) := by
  have hformula : ∀ᶠ t in atTop,
      C + error t / (t : ℝ) = (x t : ℝ) / (t : ℝ) := by
    filter_upwards [hx, eventually_gt_atTop (0 : ℕ)] with t hxt ht
    rw [hxt]
    field_simp
  have hbase : Tendsto (fun t : ℕ ↦ C + error t / (t : ℝ)) atTop (nhds C) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  exact hbase.congr' hformula

/-- A relative `o(1)` error gives the same ratio convergence in one step. -/
theorem tendsto_cutoff_ratio_of_relative_error
    (C : ℝ) (x : ℕ → ℕ) (error : ℕ → ℝ)
    (hx : ∀ᶠ t in atTop, (x t : ℝ) = (C + error t) * t)
    (herror : Tendsto error atTop (nhds 0)) :
    Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C) := by
  have hformula : ∀ᶠ t in atTop,
      C + error t = (x t : ℝ) / (t : ℝ) := by
    filter_upwards [hx, eventually_gt_atTop (0 : ℕ)] with t hxt ht
    rw [hxt]
    field_simp
  have hbase : Tendsto (fun t : ℕ ↦ C + error t) atTop (nhds C) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  exact hbase.congr' hformula

/--
Filter-level Proposition 4 with the ratio estimate packaged alongside the
constructed Egyptian-fraction sets.
-/
theorem propositionFour_upperAssembly_with_ratio
    (r C : ℝ) (y R lower x : ℕ → ℕ) (residual error : ℕ → ℝ)
    (large correction : ℕ → Finset ℕ)
    (hinput : ∀ᶠ t in atTop,
      PropositionFourInput r t (y t) (R t) (lower t) (x t) (residual t)
        (large t) (correction t))
    (hx : ∀ᶠ t in atTop, (x t : ℝ) = C * t + error t)
    (herror : Tendsto (fun t : ℕ ↦ error t / (t : ℝ)) atTop (nhds 0)) :
    (∀ᶠ t in atTop, UpperWitness r t (x t) (large t ∪ correction t)) ∧
      Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C) := by
  exact ⟨propositionFour_upperAssembly_eventually r y R lower x residual large correction hinput,
    tendsto_cutoff_ratio_of_additive_error C x error hx herror⟩

end Erdos285
