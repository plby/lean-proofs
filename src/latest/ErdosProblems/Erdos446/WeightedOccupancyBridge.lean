/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperBlockMassError
import ErdosProblems.Erdos446.UpperFiniteLayers

/-!
# Erdős Problem 446: the sharp weighted occupancy bridge

The prime blocks in the upper bound do not have exactly equal reciprocal
mass.  This file keeps their actual masses `λᵢ`, proves the weighted
multinomial normalization

`sum_{|ν|=k} prod λᵢ^(νᵢ) / νᵢ! = (sum λᵢ)^k / k!`,

and records the fact that the cumulative prime-block masses differ from
`h * log 2` by one geometrically small error, independent of `h`.  Once the
error is at most half a cell, normalization moves every cumulative boundary
by at most one uniform cell.  The last theorem inserts the already proved
product-error estimate directly into a sharp-envelope dyadic layer; thus it
is ready for the numerical layer summation without replacing every block
mass by a common majorant.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Reciprocal-factorial mass of a count vector with cell masses `λ`. -/
noncomputable def weightedCompositionMass {v : ℕ}
    (lam : Fin v → ℝ) (b : Fin v → ℕ) : ℝ :=
  (∏ i : Fin v, lam i ^ b i) / compositionFactorial b

/-- Exact weighted multinomial identity.  This is the normalization used
when the individual prime-block masses are retained. -/
theorem sum_weightedCompositionMass_compositionsOf
    {v : ℕ} (lam : Fin v → ℝ) (k : ℕ) :
    (∑ b ∈ compositionsOf v k, weightedCompositionMass lam b) =
      (∑ i : Fin v, lam i) ^ k / (k.factorial : ℝ) := by
  have hmulti := Finset.sum_pow_eq_sum_piAntidiag
    (s := (Finset.univ : Finset (Fin v))) lam k
  have hfin :
      Finset.piAntidiag (Finset.univ : Finset (Fin v)) k =
        compositionsOf v k := by
    ext b
    simp [compositionsOf]
  rw [hfin] at hmulti
  calc
    (∑ b ∈ compositionsOf v k, weightedCompositionMass lam b) =
        ∑ b ∈ compositionsOf v k,
          ((Nat.multinomial Finset.univ b : ℝ) *
            ∏ i : Fin v, lam i ^ b i) / (k.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [weightedCompositionMass, div_eq_mul_inv]
      calc
        (∏ i : Fin v, lam i ^ b i) * (compositionFactorial b)⁻¹ =
            (∏ i : Fin v, lam i ^ b i) *
              (1 / compositionFactorial b) := by rw [one_div]
        _ = (∏ i : Fin v, lam i ^ b i) *
              ((Nat.multinomial Finset.univ b : ℝ) /
                (k.factorial : ℝ)) := by
          rw [inv_compositionFactorial_eq_multinomial_div_of_mem hb]
        _ = _ := by ring
    _ = ((∑ b ∈ compositionsOf v k,
          (Nat.multinomial Finset.univ b : ℝ) *
            ∏ i : Fin v, lam i ^ b i)) / (k.factorial : ℝ) := by
      rw [Finset.sum_div]
    _ = (∑ i : Fin v, lam i) ^ k / (k.factorial : ℝ) := by
      rw [hmulti]

/-- The actual reciprocal mass of the first `h` consecutive prime blocks. -/
noncomputable def primeBlockPrefixMass (M h : ℕ) : ℝ :=
  ∑ i ∈ Finset.range h, primeBlockMass (M + i)

/-- The total mass of `v` consecutive prime blocks. -/
noncomputable def primeBlockWindowMass (M v : ℕ) : ℝ :=
  primeBlockPrefixMass M v

private theorem geometricHalf_sum_le_two (h : ℕ) :
    (∑ i ∈ Finset.range h, (1 / 2 : ℝ) ^ i) ≤ 2 := by
  rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
  have hp : 0 ≤ (1 / 2 : ℝ) ^ h := by positivity
  norm_num
  linarith

/-- A geometric error in the individual block masses accumulates to a
single `O(2⁻ᴹ)` error, uniformly in the number of retained blocks. -/
theorem primeBlockPrefixMass_error_le
    {C : ℝ} (hC : 0 ≤ C) {M : ℕ}
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (h : ℕ) :
    |primeBlockPrefixMass M h - (h : ℝ) * Real.log 2| ≤
      2 * C / (2 : ℝ) ^ M := by
  have hpowM : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  have hterm : ∀ i ∈ Finset.range h,
      |primeBlockMass (M + i) - Real.log 2| ≤
        (C / (2 : ℝ) ^ M) * (1 / 2 : ℝ) ^ i := by
    intro i hi
    calc
      |primeBlockMass (M + i) - Real.log 2| ≤
          C / (2 : ℝ) ^ (M + i) := hmass i
      _ = (C / (2 : ℝ) ^ M) * (1 / 2 : ℝ) ^ i := by
        rw [pow_add]
        rw [one_div, inv_pow]
        field_simp
  calc
    |primeBlockPrefixMass M h - (h : ℝ) * Real.log 2| =
        |∑ i ∈ Finset.range h,
          (primeBlockMass (M + i) - Real.log 2)| := by
      rw [primeBlockPrefixMass, Finset.sum_sub_distrib]
      simp
    _ ≤ ∑ i ∈ Finset.range h,
          |primeBlockMass (M + i) - Real.log 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range h,
          (C / (2 : ℝ) ^ M) * (1 / 2 : ℝ) ^ i := by
      exact Finset.sum_le_sum hterm
    _ = (C / (2 : ℝ) ^ M) *
          ∑ i ∈ Finset.range h, (1 / 2 : ℝ) ^ i := by
      rw [Finset.mul_sum]
    _ ≤ (C / (2 : ℝ) ^ M) * 2 := by
      apply mul_le_mul_of_nonneg_left (geometricHalf_sum_le_two h)
      positivity
    _ = 2 * C / (2 : ℝ) ^ M := by ring

/-- Both the prefix and the whole window have the same absolute error
budget. -/
theorem primeBlockPrefixWindow_error_le
    {C : ℝ} (hC : 0 ≤ C) {M v : ℕ}
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (h : ℕ) :
    |primeBlockPrefixMass M h - (h : ℝ) * Real.log 2| ≤
        2 * C / (2 : ℝ) ^ M ∧
      |primeBlockWindowMass M v - (v : ℝ) * Real.log 2| ≤
        2 * C / (2 : ℝ) ^ M := by
  exact ⟨primeBlockPrefixMass_error_le hC hmass h,
    primeBlockPrefixMass_error_le hC hmass v⟩

/-- Unconditional eventual form of the cumulative block-mass estimate. -/
theorem exists_primeBlockPrefixMass_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, ∀ M : ℕ, J ≤ M →
      ∀ h : ℕ,
      |primeBlockPrefixMass M h - (h : ℝ) * Real.log 2| ≤
        2 * C / (2 : ℝ) ^ M := by
  obtain ⟨C, hC, J, htail⟩ :=
    exists_primeBlockMass_geometric_error_threshold
  refine ⟨C, hC, J, ?_⟩
  intro M hMJ h
  apply primeBlockPrefixMass_error_le hC.le (h := h)
  intro i
  exact htail (M + i) (by omega)

/-- If the accumulated Mertens error is at most half a uniform cell, then
normalizing by the *actual* total mass moves a prefix boundary by at most one
cell.  The cross-multiplied form avoids any positivity assumption on the
total and is the form needed for quantile/order-statistic comparisons. -/
theorem primeBlockPrefix_oneCellOffset
    {C : ℝ} (hC : 0 ≤ C) {M v h : ℕ} (hhv : h ≤ v)
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (hsmall : 4 * C ≤ Real.log 2 * (2 : ℝ) ^ M) :
    ((h - 1 : ℕ) : ℝ) * primeBlockWindowMass M v ≤
      (v : ℝ) * primeBlockPrefixMass M h := by
  by_cases hh0 : h = 0
  · subst h
    simp [primeBlockPrefixMass]
  let E : ℝ := 2 * C / (2 : ℝ) ^ M
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpow : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  have htwoE : 2 * E ≤ Real.log 2 := by
    calc
      2 * E = 4 * C / (2 : ℝ) ^ M := by dsimp [E]; ring
      _ ≤ Real.log 2 := (div_le_iff₀ hpow).2 hsmall
  have hprefAbs := primeBlockPrefixMass_error_le hC hmass h
  have htotalAbs := primeBlockPrefixMass_error_le hC hmass v
  change |primeBlockPrefixMass M h - (h : ℝ) * Real.log 2| ≤ E at hprefAbs
  change |primeBlockWindowMass M v - (v : ℝ) * Real.log 2| ≤ E at htotalAbs
  have hprefLower : (h : ℝ) * Real.log 2 - E ≤
      primeBlockPrefixMass M h := by
    linarith [neg_le_of_abs_le hprefAbs]
  have htotalUpper : primeBlockWindowMass M v ≤
      (v : ℝ) * Real.log 2 + E := by
    linarith [le_of_abs_le htotalAbs]
  have hhm : ((h - 1 : ℕ) : ℝ) ≤ (v : ℝ) := by
    exact_mod_cast (show h - 1 ≤ v by omega)
  have hleft : ((h - 1 : ℕ) : ℝ) * primeBlockWindowMass M v ≤
      ((h - 1 : ℕ) : ℝ) * ((v : ℝ) * Real.log 2 + E) :=
    mul_le_mul_of_nonneg_left htotalUpper (by positivity)
  have hright : (v : ℝ) * ((h : ℝ) * Real.log 2 - E) ≤
      (v : ℝ) * primeBlockPrefixMass M h :=
    mul_le_mul_of_nonneg_left hprefLower (by positivity)
  calc
    ((h - 1 : ℕ) : ℝ) * primeBlockWindowMass M v ≤
        ((h - 1 : ℕ) : ℝ) * ((v : ℝ) * Real.log 2 + E) := hleft
    _ ≤ (v : ℝ) * ((h : ℝ) * Real.log 2 - E) := by
      have hone : 1 ≤ h := by omega
      have hsub : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
        rw [Nat.cast_sub hone]
        norm_num
      have herrorMul : ((h - 1 : ℕ) : ℝ) * E ≤ (v : ℝ) * E :=
        mul_le_mul_of_nonneg_right hhm hE
      have htwoEMul : (v : ℝ) * (2 * E) ≤
          (v : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left htwoE (by positivity)
      rw [hsub]
      nlinarith
    _ ≤ (v : ℝ) * primeBlockPrefixMass M h := hright

/-- The reverse one-cell comparison.  Together with
`primeBlockPrefix_oneCellOffset`, this says that every cumulative boundary
for the normalized nonuniform cells lies between the adjacent uniform-cell
boundaries. -/
theorem primeBlockPrefix_oneCellOffset_upper
    {C : ℝ} (hC : 0 ≤ C) {M v h : ℕ} (hhv : h ≤ v)
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (hsmall : 4 * C ≤ Real.log 2 * (2 : ℝ) ^ M) :
    (v : ℝ) * primeBlockPrefixMass M h ≤
      ((h + 1 : ℕ) : ℝ) * primeBlockWindowMass M v := by
  by_cases hh : h = v
  · subst h
    rw [primeBlockWindowMass]
    have hnonneg : 0 ≤ primeBlockPrefixMass M v := by
      dsimp [primeBlockPrefixMass]
      exact Finset.sum_nonneg fun i hi ↦ primeBlockMass_nonneg _
    exact mul_le_mul_of_nonneg_right (by
      exact_mod_cast (show v ≤ v + 1 by omega)) hnonneg
  have hh1v : h + 1 ≤ v := by omega
  let E : ℝ := 2 * C / (2 : ℝ) ^ M
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpow : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  have htwoE : 2 * E ≤ Real.log 2 := by
    calc
      2 * E = 4 * C / (2 : ℝ) ^ M := by dsimp [E]; ring
      _ ≤ Real.log 2 := (div_le_iff₀ hpow).2 hsmall
  have hprefAbs := primeBlockPrefixMass_error_le hC hmass h
  have htotalAbs := primeBlockPrefixMass_error_le hC hmass v
  change |primeBlockPrefixMass M h - (h : ℝ) * Real.log 2| ≤ E at hprefAbs
  change |primeBlockWindowMass M v - (v : ℝ) * Real.log 2| ≤ E at htotalAbs
  have hprefUpper : primeBlockPrefixMass M h ≤
      (h : ℝ) * Real.log 2 + E := by
    linarith [le_of_abs_le hprefAbs]
  have htotalLower : (v : ℝ) * Real.log 2 - E ≤
      primeBlockWindowMass M v := by
    linarith [neg_le_of_abs_le htotalAbs]
  have hhvR : (h : ℝ) + 1 ≤ (v : ℝ) := by
    exact_mod_cast hh1v
  calc
    (v : ℝ) * primeBlockPrefixMass M h ≤
        (v : ℝ) * ((h : ℝ) * Real.log 2 + E) :=
      mul_le_mul_of_nonneg_left hprefUpper (by positivity)
    _ ≤ ((h + 1 : ℕ) : ℝ) *
        ((v : ℝ) * Real.log 2 - E) := by
      push_cast
      have hvh : (v : ℝ) + ((h : ℝ) + 1) ≤ 2 * (v : ℝ) := by
        linarith
      have herr : ((v : ℝ) + ((h : ℝ) + 1)) * E ≤
          (v : ℝ) * Real.log 2 := by
        calc
          ((v : ℝ) + ((h : ℝ) + 1)) * E ≤
              (2 * (v : ℝ)) * E :=
            mul_le_mul_of_nonneg_right hvh hE
          _ ≤ (v : ℝ) * Real.log 2 := by
            nlinarith
      nlinarith
    _ ≤ ((h + 1 : ℕ) : ℝ) * primeBlockWindowMass M v :=
      mul_le_mul_of_nonneg_left htotalLower (by positivity)

/-- Ratio form of the one-cell comparison. -/
theorem normalizedPrimeBlockPrefix_oneCellOffset
    {C : ℝ} (hC : 0 ≤ C) {M v h : ℕ}
    (hv : 0 < v) (hhv : h ≤ v)
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (hsmall : 4 * C ≤ Real.log 2 * (2 : ℝ) ^ M)
    (hwindow : 0 < primeBlockWindowMass M v) :
    ((h - 1 : ℕ) : ℝ) / (v : ℝ) ≤
      primeBlockPrefixMass M h / primeBlockWindowMass M v := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  rw [div_le_div_iff₀ hvR hwindow]
  simpa only [mul_comm] using
    primeBlockPrefix_oneCellOffset hC hhv hmass hsmall

/-- Ratio form of the upper one-cell comparison. -/
theorem normalizedPrimeBlockPrefix_oneCellOffset_upper
    {C : ℝ} (hC : 0 ≤ C) {M v h : ℕ}
    (hv : 0 < v) (hhv : h ≤ v)
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (hsmall : 4 * C ≤ Real.log 2 * (2 : ℝ) ^ M)
    (hwindow : 0 < primeBlockWindowMass M v) :
    primeBlockPrefixMass M h / primeBlockWindowMass M v ≤
      ((h + 1 : ℕ) : ℝ) / (v : ℝ) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  rw [div_le_div_iff₀ hwindow hvR]
  simpa only [mul_comm] using
    primeBlockPrefix_oneCellOffset_upper hC hhv hmass hsmall

/-- The one-cell comparison with the proved prime-block Mertens estimate
already substituted.  Its hypotheses are only explicit inequalities on the
finite parameters. -/
theorem exists_normalizedPrimeBlockPrefix_oneCellOffset :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, ∀ M : ℕ, J ≤ M →
      4 * C ≤ Real.log 2 * (2 : ℝ) ^ M →
      ∀ v : ℕ, 0 < v → ∀ h : ℕ, h ≤ v →
      ((h - 1 : ℕ) : ℝ) / (v : ℝ) ≤
        primeBlockPrefixMass M h / primeBlockWindowMass M v := by
  obtain ⟨C, hC, J, htail⟩ :=
    exists_primeBlockMass_geometric_error_threshold
  refine ⟨C, hC, J, ?_⟩
  intro M hMJ hsmall v hv h hhv
  have hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i) := by
    intro i
    exact htail (M + i) (by omega)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  let E : ℝ := 2 * C / (2 : ℝ) ^ M
  have hEhalf : E ≤ Real.log 2 / 2 := by
    dsimp [E]
    apply (div_le_iff₀ hpow).2
    nlinarith
  have htotalAbs := primeBlockPrefixMass_error_le hC.le hmass v
  change |primeBlockWindowMass M v - (v : ℝ) * Real.log 2| ≤ E at htotalAbs
  have htotalLower : (v : ℝ) * Real.log 2 - E ≤
      primeBlockWindowMass M v := by
    linarith [neg_le_of_abs_le htotalAbs]
  have hvOne : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hwindow : 0 < primeBlockWindowMass M v := by
    have hlog := Real.log_pos one_lt_two
    nlinarith
  exact normalizedPrimeBlockPrefix_oneCellOffset
    hC.le hv hhv hmass hsmall hwindow

/-- Unconditional eventual two-sided cell comparison.  This is the precise
finite quantile statement behind the `O(1)` displacement from the weighted
prime-block order statistics to the uniform Smirnov model. -/
theorem exists_normalizedPrimeBlockPrefix_twoSidedOffset :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, ∀ M : ℕ, J ≤ M →
      4 * C ≤ Real.log 2 * (2 : ℝ) ^ M →
      ∀ v : ℕ, 0 < v → ∀ h : ℕ, h ≤ v →
      ((h - 1 : ℕ) : ℝ) / (v : ℝ) ≤
          primeBlockPrefixMass M h / primeBlockWindowMass M v ∧
        primeBlockPrefixMass M h / primeBlockWindowMass M v ≤
          ((h + 1 : ℕ) : ℝ) / (v : ℝ) := by
  obtain ⟨C, hC, J, htail⟩ :=
    exists_primeBlockMass_geometric_error_threshold
  refine ⟨C, hC, J, ?_⟩
  intro M hMJ hsmall v hv h hhv
  have hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i) := by
    intro i
    exact htail (M + i) (by omega)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  let E : ℝ := 2 * C / (2 : ℝ) ^ M
  have hEhalf : E ≤ Real.log 2 / 2 := by
    dsimp [E]
    apply (div_le_iff₀ hpow).2
    nlinarith
  have htotalAbs := primeBlockPrefixMass_error_le hC.le hmass v
  change |primeBlockWindowMass M v - (v : ℝ) * Real.log 2| ≤ E at htotalAbs
  have htotalLower : (v : ℝ) * Real.log 2 - E ≤
      primeBlockWindowMass M v := by
    linarith [neg_le_of_abs_le htotalAbs]
  have hvOne : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hwindow : 0 < primeBlockWindowMass M v := by
    have hlog := Real.log_pos one_lt_two
    nlinarith
  exact ⟨normalizedPrimeBlockPrefix_oneCellOffset
      hC.le hv hhv hmass hsmall hwindow,
    normalizedPrimeBlockPrefix_oneCellOffset_upper
      hC.le hv hhv hmass hsmall hwindow⟩

/-- The vector of the actual prime-block masses in a finite window. -/
noncomputable def primeBlockCellMass (M v : ℕ) : Fin v → ℝ :=
  fun i ↦ primeBlockMass (M + i.val)

/-- Weighted mass of a finite family of block-count vectors. -/
noncomputable def weightedOccupancyMassOver {v : ℕ}
    (lam : Fin v → ℝ) (I : Finset (Fin v → ℕ)) : ℝ :=
  ∑ b ∈ I, weightedCompositionMass lam b

theorem weightedCompositionMass_primeBlockCellMass
    {M v : ℕ} (b : Fin v → ℕ) :
    weightedCompositionMass (primeBlockCellMass M v) b =
      ∏ i : Fin v,
        primeBlockMass (M + i) ^ b i / ((b i).factorial : ℝ) := by
  rw [weightedCompositionMass, Finset.prod_div_distrib]
  rfl

/-- The arithmetic cluster mass of any family is bounded by its exact
weighted occupancy mass once a common cluster envelope is known. -/
theorem blockClusterMassOver_le_weightedOccupancyMass
    {M v : ℕ} {I : Finset (Fin v → ℕ)} {A : ℝ}
    (hA : 0 ≤ A)
    (henvelope : ∀ b ∈ I, ∀ a ∈ compositionBlockFamily M b,
      clusterLength a ≤ A) :
    blockClusterMassOver M I ≤
      A * weightedOccupancyMassOver (primeBlockCellMass M v) I := by
  rw [blockClusterMassOver, weightedOccupancyMassOver, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  rw [weightedCompositionMass_primeBlockCellMass]
  exact compositionBlockClusterMass_le_product hA (henvelope b hb)

/-- Summing all count vectors recovers the `Λ^k/k!` normalization, where
`Λ` is the actual total prime-block mass. -/
theorem weightedOccupancyMassOver_compositionsOf_primeBlock
    (M v k : ℕ) :
    weightedOccupancyMassOver (primeBlockCellMass M v)
        (compositionsOf v k) =
      primeBlockWindowMass M v ^ k / (k.factorial : ℝ) := by
  rw [weightedOccupancyMassOver,
    sum_weightedCompositionMass_compositionsOf]
  congr 2
  rw [primeBlockWindowMass, primeBlockPrefixMass,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- Coarse but completely assumption-free weighted normalization of one
sharp layer.  The sharper theorem below replaces the total weighted mass by
the Smirnov probability of the layer. -/
theorem sharpBlockDyadicLayer_clusterMass_le_windowPower
    (M k v m : ℕ) :
    blockClusterMassOver M (sharpBlockDyadicLayer M k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m) *
        (primeBlockWindowMass M v ^ k / (k.factorial : ℝ)) := by
  let A := sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity))
      (by positivity)
  have hweighted := blockClusterMassOver_le_weightedOccupancyMass hA
    (I := sharpBlockDyadicLayer M k v m) (fun b hb a ha ↦
      sharpBlockDyadicLayer_clusterLength_le hb ha)
  have hsubset : sharpBlockDyadicLayer M k v m ⊆ compositionsOf v k :=
    Finset.filter_subset _ _
  have hmassNonneg : ∀ b : Fin v → ℕ,
      0 ≤ weightedCompositionMass (primeBlockCellMass M v) b := by
    intro b
    dsimp [weightedCompositionMass, primeBlockCellMass]
    exact div_nonneg
      (Finset.prod_nonneg fun i hi ↦
        pow_nonneg (primeBlockMass_nonneg _) _)
      (by dsimp [compositionFactorial]; positivity)
  calc
    blockClusterMassOver M (sharpBlockDyadicLayer M k v m) ≤
        A * weightedOccupancyMassOver (primeBlockCellMass M v)
          (sharpBlockDyadicLayer M k v m) := hweighted
    _ ≤ A * weightedOccupancyMassOver (primeBlockCellMass M v)
          (compositionsOf v k) := by
      apply mul_le_mul_of_nonneg_left _ hA
      rw [weightedOccupancyMassOver, weightedOccupancyMassOver]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun b hb hnot ↦ hmassNonneg b)
    _ = A * (primeBlockWindowMass M v ^ k /
          (k.factorial : ℝ)) := by
      rw [weightedOccupancyMassOver_compositionsOf_primeBlock]

/-- A sharp-envelope layer is controlled with the exact `(log 2)^k` base
and a single absolute nonuniformity factor.  This is the direct input to the
finite dyadic layer sum. -/
theorem sharpBlockDyadicLayer_clusterMass_le_weightedSmirnov
    {M k v m : ℕ} {C Q : ℝ}
    (hv : 0 < v) (hC : 0 ≤ C)
    (hoffset : m + blockLayerSlack k + 1 ≤ 2 ^ M)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hprob : smirnovProbability k (m + blockLayerSlack k) v ≤ Q) :
    blockClusterMassOver M (sharpBlockDyadicLayer M k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
          (Q * (v : ℝ) ^ k / (k.factorial : ℝ)) := by
  let A := sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity))
      (by positivity)
  have hI : sharpBlockDyadicLayer M k v m ⊆
      smirnovOccupancies k (m + blockLayerSlack k) v :=
    sharpBlockDyadicLayer_subset_smirnov M k v m
  have henvelope : ∀ b ∈ sharpBlockDyadicLayer M k v m,
      ∀ a ∈ compositionBlockFamily M b, clusterLength a ≤ A := by
    intro b hb a ha
    exact sharpBlockDyadicLayer_clusterLength_le hb ha
  have hraw := blockClusterMassOver_le_smirnovOccupancyMass_of_offset
    hC hA hoffset hI hmass henvelope
  have hmassProb : smirnovOccupancyMass k (m + blockLayerSlack k) v =
      smirnovProbability k (m + blockLayerSlack k) v * (v : ℝ) ^ k /
        (k.factorial : ℝ) :=
    smirnovOccupancyMass_eq_probability_mul hv
  rw [hmassProb] at hraw
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hprob (by positivity)) (by positivity)
  · dsimp [A]
    positivity

/-- The preceding layer estimate with the geometric Mertens theorem already
instantiated.  Only the explicit scale condition remains; the constants are
absolute and independent of the layer parameters. -/
theorem exists_sharpBlockDyadicLayer_clusterMass_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, ∀ M : ℕ, J ≤ M →
      ∀ k v m : ℕ, 0 < v →
      m + blockLayerSlack k + 1 ≤ 2 ^ M →
      ∀ Q : ℝ,
      smirnovProbability k (m + blockLayerSlack k) v ≤ Q →
      blockClusterMassOver M (sharpBlockDyadicLayer M k v m) ≤
        (sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m) *
          Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
            (Q * (v : ℝ) ^ k / (k.factorial : ℝ)) := by
  obtain ⟨C, hC, J, htail⟩ :=
    exists_primeBlockMass_geometric_error_threshold
  refine ⟨C, hC, J, ?_⟩
  intro M hMJ k v m hv hoffset Q hprob
  apply sharpBlockDyadicLayer_clusterMass_le_weightedSmirnov
    hv hC.le hoffset (Q := Q) (hprob := hprob)
  intro i
  exact htail (M + i.val) (by omega)

end Erdos446
