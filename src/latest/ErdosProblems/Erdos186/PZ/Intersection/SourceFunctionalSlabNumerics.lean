/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceHalfCoreThicknessAssembly
import ErdosProblems.Erdos186.PZ.Intersection.SourceParameterNumerics

/-!
# Fixed-parameter numerics for the source functional slab

For fixed positive `delta` and `gamma`, and with the selected rank bounded,
this file chooses one slab width and one positive real thickness which satisfy
all four scalar hypotheses of the source functional-slab theorem.  The same
choices work for the forward and reverse constants.
-/

namespace Erdos186.PZ.Intersection

open Filter
open scoped BigOperators Topology

noncomputable section

set_option autoImplicit false

/-- The smallest integral slab budget above `delta * N`. -/
def sourceFunctionalSlabBudget (delta : ℝ) (N : ℕ) : ℕ :=
  Nat.ceil (delta * (N : ℝ))

theorem sourceFunctionalSlabBudget_density (delta : ℝ) (N : ℕ) :
    delta * (N : ℝ) ≤ (sourceFunctionalSlabBudget delta N : ℝ) := by
  exact Nat.le_ceil _

theorem sourceFunctionalSlabBudget_cast_le {delta : ℝ} (hdelta : 0 ≤ delta)
    (N : ℕ) :
    (sourceFunctionalSlabBudget delta N : ℝ) ≤ delta * (N : ℝ) + 1 := by
  unfold sourceFunctionalSlabBudget
  exact (Nat.ceil_lt_add_one (mul_nonneg hdelta (by positivity))).le

/-- The dimension-dependent fixed coefficient in the low-rank slab
inequality. -/
def sourceFunctionalSlabFixedTerm {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (constant : ℝ) (r : ℕ) : ℝ :=
  (2 : ℝ) ^ r * (2 * (context.scaleDen r : ℝ)) ^ r *
    (3 : ℝ) ^ r * constant *
    ((((2 * context.scaleDen r + 1) ^ r * 2 ^ r : ℕ) : ℝ))

/-- The coefficient of `t` in the full-rank slab inequality. -/
def sourceFunctionalSlabFullTerm {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (constant : ℝ) (r : ℕ) : ℝ :=
  sourceFunctionalSlabFixedTerm context constant r * (2 * (r : ℝ))

/-- A finite common bound for both source slab constants in every rank up to
`rankCeiling`. -/
def sourceFunctionalSlabTermBound {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (forwardConstant reverseConstant : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (rankCeiling + 1),
    (sourceFunctionalSlabFixedTerm context forwardConstant r +
      sourceFunctionalSlabFixedTerm context reverseConstant r +
      sourceFunctionalSlabFullTerm context forwardConstant r +
      sourceFunctionalSlabFullTerm context reverseConstant r)

theorem sourceFunctionalSlabFixedTerm_nonneg {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {constant : ℝ} (hconstant : 0 ≤ constant) (r : ℕ) :
    0 ≤ sourceFunctionalSlabFixedTerm context constant r := by
  unfold sourceFunctionalSlabFixedTerm
  positivity

theorem sourceFunctionalSlabFullTerm_nonneg {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {constant : ℝ} (hconstant : 0 ≤ constant) (r : ℕ) :
    0 ≤ sourceFunctionalSlabFullTerm context constant r := by
  unfold sourceFunctionalSlabFullTerm
  exact mul_nonneg
    (sourceFunctionalSlabFixedTerm_nonneg hconstant r) (by positivity)

theorem sourceFunctionalSlabTermBound_nonneg {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {rankCeiling : ℕ} {forwardConstant reverseConstant : ℝ}
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    0 ≤ sourceFunctionalSlabTermBound context rankCeiling
      forwardConstant reverseConstant := by
  unfold sourceFunctionalSlabTermBound
  exact Finset.sum_nonneg fun r _ ↦ by
    have hf := sourceFunctionalSlabFixedTerm_nonneg
      (context := context) hforward r
    have hr := sourceFunctionalSlabFixedTerm_nonneg
      (context := context) hreverse r
    have hff := sourceFunctionalSlabFullTerm_nonneg
      (context := context) hforward r
    have hfr := sourceFunctionalSlabFullTerm_nonneg
      (context := context) hreverse r
    positivity

theorem sourceFunctionalSlabFixedTerm_le_bound {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {rankCeiling r : ℕ} {forwardConstant reverseConstant : ℝ}
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant)
    (hr : r ≤ rankCeiling) :
    sourceFunctionalSlabFixedTerm context forwardConstant r ≤
      sourceFunctionalSlabTermBound context rankCeiling
        forwardConstant reverseConstant := by
  unfold sourceFunctionalSlabTermBound
  let F : ℕ → ℝ := fun i ↦
    sourceFunctionalSlabFixedTerm context forwardConstant i +
      sourceFunctionalSlabFixedTerm context reverseConstant i +
      sourceFunctionalSlabFullTerm context forwardConstant i +
      sourceFunctionalSlabFullTerm context reverseConstant i
  have hsum : F r ≤ ∑ i ∈ Finset.range (rankCeiling + 1), F i := by
    apply Finset.single_le_sum
    · intro i hi
      have hf := sourceFunctionalSlabFixedTerm_nonneg
        (context := context) hforward i
      have hr' := sourceFunctionalSlabFixedTerm_nonneg
        (context := context) hreverse i
      have hff := sourceFunctionalSlabFullTerm_nonneg
        (context := context) hforward i
      have hfr := sourceFunctionalSlabFullTerm_nonneg
        (context := context) hreverse i
      dsimp only [F]
      positivity
    · simp only [Finset.mem_range]
      omega
  have hcomponent : sourceFunctionalSlabFixedTerm context forwardConstant r ≤
      F r := by
    have hf := sourceFunctionalSlabFixedTerm_nonneg
      (context := context) hforward r
    have hr' := sourceFunctionalSlabFixedTerm_nonneg
      (context := context) hreverse r
    have hff := sourceFunctionalSlabFullTerm_nonneg
      (context := context) hforward r
    have hfr := sourceFunctionalSlabFullTerm_nonneg
      (context := context) hreverse r
    dsimp only [F]
    linarith
  exact hcomponent.trans hsum

theorem sourceFunctionalSlabReverseFixedTerm_le_bound {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {rankCeiling r : ℕ} {forwardConstant reverseConstant : ℝ}
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant)
    (hr : r ≤ rankCeiling) :
    sourceFunctionalSlabFixedTerm context reverseConstant r ≤
      sourceFunctionalSlabTermBound context rankCeiling
        forwardConstant reverseConstant := by
  unfold sourceFunctionalSlabTermBound
  let F : ℕ → ℝ := fun i ↦
    sourceFunctionalSlabFixedTerm context forwardConstant i +
      sourceFunctionalSlabFixedTerm context reverseConstant i +
      sourceFunctionalSlabFullTerm context forwardConstant i +
      sourceFunctionalSlabFullTerm context reverseConstant i
  have hsum : F r ≤ ∑ i ∈ Finset.range (rankCeiling + 1), F i := by
    apply Finset.single_le_sum
    · intro i hi
      have hf := sourceFunctionalSlabFixedTerm_nonneg
        (context := context) hforward i
      have hr' := sourceFunctionalSlabFixedTerm_nonneg
        (context := context) hreverse i
      have hff := sourceFunctionalSlabFullTerm_nonneg
        (context := context) hforward i
      have hfr := sourceFunctionalSlabFullTerm_nonneg
        (context := context) hreverse i
      dsimp only [F]
      positivity
    · simp only [Finset.mem_range]
      omega
  have hcomponent : sourceFunctionalSlabFixedTerm context reverseConstant r ≤
      F r := by
    have hf := sourceFunctionalSlabFixedTerm_nonneg
      (context := context) hforward r
    have hff := sourceFunctionalSlabFullTerm_nonneg
      (context := context) hforward r
    have hfr := sourceFunctionalSlabFullTerm_nonneg
      (context := context) hreverse r
    dsimp only [F]
    linarith
  exact hcomponent.trans hsum

theorem sourceFunctionalSlabFullTerm_le_bound {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {rankCeiling r : ℕ} {forwardConstant reverseConstant : ℝ}
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant)
    (hr : r ≤ rankCeiling) :
    sourceFunctionalSlabFullTerm context forwardConstant r ≤
      sourceFunctionalSlabTermBound context rankCeiling
        forwardConstant reverseConstant := by
  unfold sourceFunctionalSlabTermBound
  let F : ℕ → ℝ := fun i ↦
    sourceFunctionalSlabFixedTerm context forwardConstant i +
      sourceFunctionalSlabFixedTerm context reverseConstant i +
      sourceFunctionalSlabFullTerm context forwardConstant i +
      sourceFunctionalSlabFullTerm context reverseConstant i
  have hsum : F r ≤ ∑ i ∈ Finset.range (rankCeiling + 1), F i := by
    apply Finset.single_le_sum
    · intro i hi
      have hf := sourceFunctionalSlabFixedTerm_nonneg
        (context := context) hforward i
      have hr' := sourceFunctionalSlabFixedTerm_nonneg
        (context := context) hreverse i
      have hff := sourceFunctionalSlabFullTerm_nonneg
        (context := context) hforward i
      have hfr := sourceFunctionalSlabFullTerm_nonneg
        (context := context) hreverse i
      dsimp only [F]
      positivity
    · simp only [Finset.mem_range]
      omega
  have hcomponent : sourceFunctionalSlabFullTerm context forwardConstant r ≤
      F r := by
    have hf := sourceFunctionalSlabFixedTerm_nonneg
      (context := context) hforward r
    have hr' := sourceFunctionalSlabFixedTerm_nonneg
      (context := context) hreverse r
    have hfr := sourceFunctionalSlabFullTerm_nonneg
      (context := context) hreverse r
    dsimp only [F]
    linarith
  exact hcomponent.trans hsum

theorem sourceFunctionalSlabReverseFullTerm_le_bound {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {rankCeiling r : ℕ} {forwardConstant reverseConstant : ℝ}
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant)
    (hr : r ≤ rankCeiling) :
    sourceFunctionalSlabFullTerm context reverseConstant r ≤
      sourceFunctionalSlabTermBound context rankCeiling
        forwardConstant reverseConstant := by
  unfold sourceFunctionalSlabTermBound
  let F : ℕ → ℝ := fun i ↦
    sourceFunctionalSlabFixedTerm context forwardConstant i +
      sourceFunctionalSlabFixedTerm context reverseConstant i +
      sourceFunctionalSlabFullTerm context forwardConstant i +
      sourceFunctionalSlabFullTerm context reverseConstant i
  have hsum : F r ≤ ∑ i ∈ Finset.range (rankCeiling + 1), F i := by
    apply Finset.single_le_sum
    · intro i hi
      have hf := sourceFunctionalSlabFixedTerm_nonneg
        (context := context) hforward i
      have hr' := sourceFunctionalSlabFixedTerm_nonneg
        (context := context) hreverse i
      have hff := sourceFunctionalSlabFullTerm_nonneg
        (context := context) hforward i
      have hfr := sourceFunctionalSlabFullTerm_nonneg
        (context := context) hreverse i
      dsimp only [F]
      positivity
    · simp only [Finset.mem_range]
      omega
  have hcomponent : sourceFunctionalSlabFullTerm context reverseConstant r ≤
      F r := by
    have hf := sourceFunctionalSlabFixedTerm_nonneg
      (context := context) hforward r
    have hr' := sourceFunctionalSlabFixedTerm_nonneg
      (context := context) hreverse r
    have hff := sourceFunctionalSlabFullTerm_nonneg
      (context := context) hforward r
    dsimp only [F]
    linarith
  exact hcomponent.trans hsum

end

end Erdos186.PZ.Intersection
