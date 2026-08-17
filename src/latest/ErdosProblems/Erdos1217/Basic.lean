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

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Filter.ENNReal

/-!
# Erdős Problem 1217: elementary definitions

This file records the quantities occurring literally in Problem 1217.  The
public cutoff is real and half open: `positiveBelow x` is the finite set of
positive natural numbers whose real casts are strictly smaller than `x`.

The ratios are formed in `ℝ`; only the complete normalized term is embedded
in `ℝ≥0∞`.  Consequently values at the finitely many small cutoffs, where one
of the logarithmic denominators vanishes or is negative, are harmless and are
sent to zero by `ENNReal.ofReal`.
-/

open Filter
open scoped BigOperators ENNReal

namespace Erdos1217

/-- Positive natural numbers in the real half-open interval `[1,x)`. -/
noncomputable def positiveBelow (x : ℝ) : Finset ℕ :=
  Finset.Ico 1 ⌈x⌉₊

/-- Positive natural numbers in the natural half-open interval `[1,x)`. -/
def positiveBelowNat (x : ℕ) : Finset ℕ :=
  Finset.Ico 1 x

@[simp]
lemma mem_positiveBelow_iff {x : ℝ} {n : ℕ} :
    n ∈ positiveBelow x ↔ 1 ≤ n ∧ (n : ℝ) < x := by
  simp [positiveBelow, Nat.lt_ceil]

@[simp]
lemma mem_positiveBelowNat_iff {x n : ℕ} :
    n ∈ positiveBelowNat x ↔ 1 ≤ n ∧ n < x := by
  simp [positiveBelowNat]

@[simp]
lemma positiveBelow_natCast (x : ℕ) :
    positiveBelow (x : ℝ) = positiveBelowNat x := by
  simp [positiveBelow, positiveBelowNat]

lemma positiveBelow_mono : Monotone positiveBelow := by
  intro x y hxy
  exact Finset.Ico_subset_Ico le_rfl (Nat.ceil_mono hxy)

lemma positiveBelowNat_mono : Monotone positiveBelowNat := by
  intro x y hxy
  exact Finset.Ico_subset_Ico le_rfl hxy

/-- The weight `1 / (n log n)`, with its irrelevant singular values set to zero. -/
noncomputable def doublyHarmonicWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then ((n : ℝ) * Real.log n)⁻¹ else 0

@[simp] lemma doublyHarmonicWeight_zero : doublyHarmonicWeight 0 = 0 := by
  simp [doublyHarmonicWeight]

@[simp] lemma doublyHarmonicWeight_one : doublyHarmonicWeight 1 = 0 := by
  simp [doublyHarmonicWeight]

lemma doublyHarmonicWeight_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    doublyHarmonicWeight n = ((n : ℝ) * Real.log n)⁻¹ := by
  simp [doublyHarmonicWeight, hn]

lemma doublyHarmonicWeight_of_lt_two {n : ℕ} (hn : n < 2) :
    doublyHarmonicWeight n = 0 := by
  simp [doublyHarmonicWeight, Nat.not_le.mpr hn]

lemma doublyHarmonicWeight_nonneg (n : ℕ) : 0 ≤ doublyHarmonicWeight n := by
  by_cases hn : 2 ≤ n
  · rw [doublyHarmonicWeight_of_two_le hn]
    exact inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))))
  · simp [doublyHarmonicWeight, hn]

lemma doublyHarmonicWeight_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < doublyHarmonicWeight n := by
  rw [doublyHarmonicWeight_of_two_le hn]
  apply inv_pos.mpr
  exact mul_pos (Nat.cast_pos.mpr (by omega))
    (Real.log_pos (by exact_mod_cast hn))

lemma doublyHarmonicWeight_eq_inv_mul_log {n : ℕ} (hn : 2 ≤ n) :
    doublyHarmonicWeight n = (n : ℝ)⁻¹ * (Real.log n)⁻¹ := by
  rw [doublyHarmonicWeight_of_two_le hn, mul_inv_rev]
  exact mul_comm _ _

/-- The logarithmic (harmonic) mass of `A ∩ [1,x)`. -/
noncomputable def harmonicMass (A : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ (positiveBelow x).filter (fun n ↦ n ∈ A), (n : ℝ)⁻¹

/-- Natural-cutoff version of `harmonicMass`. -/
noncomputable def harmonicMassNat (A : Set ℕ) (x : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (positiveBelowNat x).filter (fun n ↦ n ∈ A), (n : ℝ)⁻¹

/-- The doubly harmonic mass `∑_{n∈A, 1≤n<x} 1/(n log n)`. -/
noncomputable def weightedMass (A : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ (positiveBelow x).filter (fun n ↦ n ∈ A), doublyHarmonicWeight n

/-- Natural-cutoff version of `weightedMass`. -/
noncomputable def weightedMassNat (A : Set ℕ) (x : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (positiveBelowNat x).filter (fun n ↦ n ∈ A), doublyHarmonicWeight n

/-- The number of distinct values of `c` in the real half-open interval `[1,x)`. -/
noncomputable def chainCount (c : ℕ → ℕ) (x : ℝ) : ℕ := by
  classical
  exact ((positiveBelow x).filter (fun n ↦ n ∈ Set.range c)).card

/-- Natural-cutoff version of `chainCount`. -/
noncomputable def chainCountNat (c : ℕ → ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((positiveBelowNat x).filter (fun n ↦ n ∈ Set.range c)).card

/-- The normalized logarithmic-density term at real cutoff `x`. -/
noncomputable def lowerLogDensityTerm (A : Set ℕ) (x : ℝ) : ENNReal :=
  ENNReal.ofReal (harmonicMass A x / Real.log x)

/-- Natural-cutoff version of `lowerLogDensityTerm`. -/
noncomputable def lowerLogDensityTermNat (A : Set ℕ) (x : ℕ) : ENNReal :=
  ENNReal.ofReal (harmonicMassNat A x / Real.log x)

/-- The normalized doubly harmonic term at real cutoff `x`. -/
noncomputable def weightedTerm (A : Set ℕ) (x : ℝ) : ENNReal :=
  ENNReal.ofReal (weightedMass A x / Real.log (Real.log x))

/-- Natural-cutoff version of `weightedTerm`. -/
noncomputable def weightedTermNat (A : Set ℕ) (x : ℕ) : ENNReal :=
  ENNReal.ofReal (weightedMassNat A x / Real.log (Real.log x))

/-- The normalized number of values of `c` below real cutoff `x`. -/
noncomputable def chainTerm (c : ℕ → ℕ) (x : ℝ) : ENNReal :=
  ENNReal.ofReal ((chainCount c x : ℝ) / Real.log (Real.log x))

/-- Natural-cutoff version of `chainTerm`. -/
noncomputable def chainTermNat (c : ℕ → ℕ) (x : ℕ) : ENNReal :=
  ENNReal.ofReal ((chainCountNat c x : ℝ) / Real.log (Real.log x))

/-- Lower logarithmic density, with the exact real cutoff used in the problem. -/
noncomputable def lowerLogDensity (A : Set ℕ) : ENNReal :=
  Filter.liminf (lowerLogDensityTerm A) Filter.atTop

/-- Natural-cutoff lower logarithmic density. -/
noncomputable def lowerLogDensityNat (A : Set ℕ) : ENNReal :=
  Filter.liminf (lowerLogDensityTermNat A) Filter.atTop

/-- The right-hand limsup in Problem 1217. -/
noncomputable def weightedRate (A : Set ℕ) : ENNReal :=
  Filter.limsup (weightedTerm A) Filter.atTop

/-- Natural-cutoff version of `weightedRate`. -/
noncomputable def weightedRateNat (A : Set ℕ) : ENNReal :=
  Filter.limsup (weightedTermNat A) Filter.atTop

/-- The left-hand limsup in Problem 1217 for the values of `c`. -/
noncomputable def chainRate (c : ℕ → ℕ) : ENNReal :=
  Filter.limsup (chainTerm c) Filter.atTop

/-- Natural-cutoff version of `chainRate`. -/
noncomputable def chainRateNat (c : ℕ → ℕ) : ENNReal :=
  Filter.limsup (chainTermNat c) Filter.atTop

/-! ## Elementary identities and order properties -/

@[simp]
lemma harmonicMass_natCast (A : Set ℕ) (x : ℕ) :
    harmonicMass A (x : ℝ) = harmonicMassNat A x := by
  classical
  simp [harmonicMass, harmonicMassNat]

@[simp]
lemma weightedMass_natCast (A : Set ℕ) (x : ℕ) :
    weightedMass A (x : ℝ) = weightedMassNat A x := by
  classical
  simp [weightedMass, weightedMassNat]

@[simp]
lemma chainCount_natCast (c : ℕ → ℕ) (x : ℕ) :
    chainCount c (x : ℝ) = chainCountNat c x := by
  classical
  simp [chainCount, chainCountNat]

lemma harmonicMass_nonneg (A : Set ℕ) (x : ℝ) : 0 ≤ harmonicMass A x := by
  classical
  apply Finset.sum_nonneg
  intro n hn
  exact inv_nonneg.mpr (Nat.cast_nonneg n)

lemma harmonicMassNat_nonneg (A : Set ℕ) (x : ℕ) : 0 ≤ harmonicMassNat A x := by
  simpa using harmonicMass_nonneg A (x : ℝ)

lemma weightedMass_nonneg (A : Set ℕ) (x : ℝ) : 0 ≤ weightedMass A x := by
  classical
  apply Finset.sum_nonneg
  intro n hn
  exact doublyHarmonicWeight_nonneg n

lemma weightedMassNat_nonneg (A : Set ℕ) (x : ℕ) : 0 ≤ weightedMassNat A x := by
  simpa using weightedMass_nonneg A (x : ℝ)

@[simp]
lemma harmonicMass_empty (x : ℝ) : harmonicMass (∅ : Set ℕ) x = 0 := by
  classical
  simp [harmonicMass]

@[simp]
lemma harmonicMassNat_empty (x : ℕ) : harmonicMassNat (∅ : Set ℕ) x = 0 := by
  simpa using harmonicMass_empty (x : ℝ)

@[simp]
lemma weightedMass_empty (x : ℝ) : weightedMass (∅ : Set ℕ) x = 0 := by
  classical
  simp [weightedMass]

@[simp]
lemma weightedMassNat_empty (x : ℕ) : weightedMassNat (∅ : Set ℕ) x = 0 := by
  simpa using weightedMass_empty (x : ℝ)

lemma harmonicMass_mono (A : Set ℕ) : Monotone (harmonicMass A) := by
  classical
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨positiveBelow_mono hxy hn.1, hn.2⟩
  · intro n hn hnot
    exact inv_nonneg.mpr (Nat.cast_nonneg n)

lemma harmonicMassNat_mono (A : Set ℕ) : Monotone (harmonicMassNat A) := by
  intro x y hxy
  simpa using harmonicMass_mono A (show (x : ℝ) ≤ y by exact_mod_cast hxy)

lemma weightedMass_mono (A : Set ℕ) : Monotone (weightedMass A) := by
  classical
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨positiveBelow_mono hxy hn.1, hn.2⟩
  · intro n hn hnot
    exact doublyHarmonicWeight_nonneg n

lemma weightedMassNat_mono (A : Set ℕ) : Monotone (weightedMassNat A) := by
  intro x y hxy
  simpa using weightedMass_mono A (show (x : ℝ) ≤ y by exact_mod_cast hxy)

lemma chainCount_mono (c : ℕ → ℕ) : Monotone (chainCount c) := by
  classical
  intro x y hxy
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨positiveBelow_mono hxy hn.1, hn.2⟩

lemma chainCountNat_mono (c : ℕ → ℕ) : Monotone (chainCountNat c) := by
  intro x y hxy
  simpa using chainCount_mono c (show (x : ℝ) ≤ y by exact_mod_cast hxy)

lemma chainCount_le_card_positiveBelow (c : ℕ → ℕ) (x : ℝ) :
    chainCount c x ≤ (positiveBelow x).card := by
  classical
  exact Finset.card_filter_le _ _

lemma chainCountNat_le_card_positiveBelowNat (c : ℕ → ℕ) (x : ℕ) :
    chainCountNat c x ≤ (positiveBelowNat x).card := by
  simpa using chainCount_le_card_positiveBelow c (x : ℝ)

lemma harmonicMass_mono_set {A B : Set ℕ} (hAB : A ⊆ B) (x : ℝ) :
    harmonicMass A x ≤ harmonicMass B x := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hAB hn.2⟩
  · intro n hn hnot
    exact inv_nonneg.mpr (Nat.cast_nonneg n)

lemma harmonicMassNat_mono_set {A B : Set ℕ} (hAB : A ⊆ B) (x : ℕ) :
    harmonicMassNat A x ≤ harmonicMassNat B x := by
  simpa using harmonicMass_mono_set hAB (x : ℝ)

lemma weightedMass_mono_set {A B : Set ℕ} (hAB : A ⊆ B) (x : ℝ) :
    weightedMass A x ≤ weightedMass B x := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hAB hn.2⟩
  · intro n hn hnot
    exact doublyHarmonicWeight_nonneg n

lemma weightedMassNat_mono_set {A B : Set ℕ} (hAB : A ⊆ B) (x : ℕ) :
    weightedMassNat A x ≤ weightedMassNat B x := by
  simpa using weightedMass_mono_set hAB (x : ℝ)

lemma harmonicMass_congr_set {A B : Set ℕ} (hAB : A = B) (x : ℝ) :
    harmonicMass A x = harmonicMass B x := by
  subst B
  rfl

lemma weightedMass_congr_set {A B : Set ℕ} (hAB : A = B) (x : ℝ) :
    weightedMass A x = weightedMass B x := by
  subst B
  rfl

lemma chainCount_congr_range {c d : ℕ → ℕ} (hcd : Set.range c = Set.range d) (x : ℝ) :
    chainCount c x = chainCount d x := by
  classical
  simp [chainCount, hcd]

lemma chainCountNat_congr_range {c d : ℕ → ℕ} (hcd : Set.range c = Set.range d) (x : ℕ) :
    chainCountNat c x = chainCountNat d x := by
  classical
  simp [chainCountNat, hcd]

lemma chainCount_mono_range {c d : ℕ → ℕ} (hcd : Set.range c ⊆ Set.range d) (x : ℝ) :
    chainCount c x ≤ chainCount d x := by
  classical
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hcd hn.2⟩

lemma chainCountNat_mono_range {c d : ℕ → ℕ} (hcd : Set.range c ⊆ Set.range d) (x : ℕ) :
    chainCountNat c x ≤ chainCountNat d x := by
  simpa using chainCount_mono_range hcd (x : ℝ)

@[simp]
lemma lowerLogDensityTerm_natCast (A : Set ℕ) (x : ℕ) :
    lowerLogDensityTerm A (x : ℝ) = lowerLogDensityTermNat A x := by
  simp [lowerLogDensityTerm, lowerLogDensityTermNat]

@[simp]
lemma weightedTerm_natCast (A : Set ℕ) (x : ℕ) :
    weightedTerm A (x : ℝ) = weightedTermNat A x := by
  simp [weightedTerm, weightedTermNat]

@[simp]
lemma chainTerm_natCast (c : ℕ → ℕ) (x : ℕ) :
    chainTerm c (x : ℝ) = chainTermNat c x := by
  simp [chainTerm, chainTermNat]

lemma lowerLogDensityTerm_mono_set {A B : Set ℕ} (hAB : A ⊆ B)
    {x : ℝ} (hx : 1 < x) :
    lowerLogDensityTerm A x ≤ lowerLogDensityTerm B x := by
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right (harmonicMass_mono_set hAB x) (Real.log_nonneg hx.le)

lemma weightedTerm_mono_set {A B : Set ℕ} (hAB : A ⊆ B)
    {x : ℝ} (hx : Real.exp 1 < x) :
    weightedTerm A x ≤ weightedTerm B x := by
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right (weightedMass_mono_set hAB x)
  have hxpos : 0 < x := (Real.exp_pos 1).trans hx
  exact Real.log_nonneg ((Real.le_log_iff_exp_le hxpos).2 hx.le)

lemma chainTerm_congr_range {c d : ℕ → ℕ} (hcd : Set.range c = Set.range d) (x : ℝ) :
    chainTerm c x = chainTerm d x := by
  simp [chainTerm, chainCount_congr_range hcd]

lemma chainTermNat_congr_range {c d : ℕ → ℕ} (hcd : Set.range c = Set.range d) (x : ℕ) :
    chainTermNat c x = chainTermNat d x := by
  simp [chainTermNat, chainCountNat_congr_range hcd]

lemma chainTerm_mono_range {c d : ℕ → ℕ} (hcd : Set.range c ⊆ Set.range d)
    {x : ℝ} (hx : Real.exp 1 < x) :
    chainTerm c x ≤ chainTerm d x := by
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right
  · exact_mod_cast chainCount_mono_range hcd x
  · have hxpos : 0 < x := (Real.exp_pos 1).trans hx
    exact Real.log_nonneg ((Real.le_log_iff_exp_le hxpos).2 hx.le)

lemma lowerLogDensity_congr_set {A B : Set ℕ} (hAB : A = B) :
    lowerLogDensity A = lowerLogDensity B := by
  subst B
  rfl

lemma weightedRate_congr_set {A B : Set ℕ} (hAB : A = B) :
    weightedRate A = weightedRate B := by
  subst B
  rfl

lemma lowerLogDensityNat_congr_set {A B : Set ℕ} (hAB : A = B) :
    lowerLogDensityNat A = lowerLogDensityNat B := by
  subst B
  rfl

lemma weightedRateNat_congr_set {A B : Set ℕ} (hAB : A = B) :
    weightedRateNat A = weightedRateNat B := by
  subst B
  rfl

lemma lowerLogDensity_mono_set {A B : Set ℕ} (hAB : A ⊆ B) :
    lowerLogDensity A ≤ lowerLogDensity B := by
  apply Filter.liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx using
    lowerLogDensityTerm_mono_set hAB hx

lemma lowerLogDensityNat_mono_set {A B : Set ℕ} (hAB : A ⊆ B) :
    lowerLogDensityNat A ≤ lowerLogDensityNat B := by
  apply Filter.liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_gt_atTop 1] with x hx
  simpa only [← lowerLogDensityTerm_natCast] using
    lowerLogDensityTerm_mono_set hAB (show (1 : ℝ) < x by exact_mod_cast hx)

lemma weightedRate_mono_set {A B : Set ℕ} (hAB : A ⊆ B) :
    weightedRate A ≤ weightedRate B := by
  apply Filter.limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx using
    weightedTerm_mono_set hAB hx

lemma weightedRateNat_mono_set {A B : Set ℕ} (hAB : A ⊆ B) :
    weightedRateNat A ≤ weightedRateNat B := by
  apply Filter.limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_gt_atTop ⌈Real.exp 1⌉₊] with x hx
  have hceil : Real.exp 1 ≤ (⌈Real.exp 1⌉₊ : ℝ) := Nat.le_ceil _
  simpa only [← weightedTerm_natCast] using
    weightedTerm_mono_set hAB (hceil.trans_lt (by exact_mod_cast hx))

lemma chainRate_congr_range {c d : ℕ → ℕ} (hcd : Set.range c = Set.range d) :
    chainRate c = chainRate d := by
  apply congrArg (fun f : ℝ → ENNReal ↦ Filter.limsup f Filter.atTop)
  funext x
  exact chainTerm_congr_range hcd x

lemma chainRateNat_congr_range {c d : ℕ → ℕ} (hcd : Set.range c = Set.range d) :
    chainRateNat c = chainRateNat d := by
  apply congrArg (fun f : ℕ → ENNReal ↦ Filter.limsup f Filter.atTop)
  funext x
  exact chainTermNat_congr_range hcd x

lemma chainRate_mono_range {c d : ℕ → ℕ} (hcd : Set.range c ⊆ Set.range d) :
    chainRate c ≤ chainRate d := by
  apply Filter.limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx using
    chainTerm_mono_range hcd hx

lemma chainRateNat_mono_range {c d : ℕ → ℕ} (hcd : Set.range c ⊆ Set.range d) :
    chainRateNat c ≤ chainRateNat d := by
  apply Filter.limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_gt_atTop ⌈Real.exp 1⌉₊] with x hx
  have hceil : Real.exp 1 ≤ (⌈Real.exp 1⌉₊ : ℝ) := Nat.le_ceil _
  simpa only [← chainTerm_natCast] using
    chainTerm_mono_range hcd (hceil.trans_lt (by exact_mod_cast hx))

/-! ## Logarithmic denominators at infinity -/

lemma tendsto_log_log_atTop :
    Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

lemma tendsto_log_natCast_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_log_log_natCast_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_natCast_atTop

lemma eventually_log_pos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x :=
  (Real.tendsto_log_atTop.eventually_gt_atTop 0)

lemma eventually_log_log_pos : ∀ᶠ x : ℝ in atTop, 0 < Real.log (Real.log x) :=
  (tendsto_log_log_atTop.eventually_gt_atTop 0)

lemma eventually_log_natCast_pos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) :=
  (tendsto_log_natCast_atTop.eventually_gt_atTop 0)

lemma eventually_log_log_natCast_pos :
    ∀ᶠ n : ℕ in atTop, 0 < Real.log (Real.log (n : ℝ)) :=
  (tendsto_log_log_natCast_atTop.eventually_gt_atTop 0)

/-! The normalized quantities are nonnegative by construction. -/

lemma lowerLogDensityTerm_nonneg (A : Set ℕ) (x : ℝ) :
    0 ≤ lowerLogDensityTerm A x := bot_le

lemma lowerLogDensityTermNat_nonneg (A : Set ℕ) (x : ℕ) :
    0 ≤ lowerLogDensityTermNat A x := bot_le

lemma weightedTerm_nonneg (A : Set ℕ) (x : ℝ) :
    0 ≤ weightedTerm A x := bot_le

lemma weightedTermNat_nonneg (A : Set ℕ) (x : ℕ) :
    0 ≤ weightedTermNat A x := bot_le

lemma chainTerm_nonneg (c : ℕ → ℕ) (x : ℝ) :
    0 ≤ chainTerm c x := bot_le

lemma chainTermNat_nonneg (c : ℕ → ℕ) (x : ℕ) :
    0 ≤ chainTermNat c x := bot_le

lemma lowerLogDensity_nonneg (A : Set ℕ) : 0 ≤ lowerLogDensity A := bot_le

lemma lowerLogDensityNat_nonneg (A : Set ℕ) : 0 ≤ lowerLogDensityNat A := bot_le

lemma weightedRate_nonneg (A : Set ℕ) : 0 ≤ weightedRate A := bot_le

lemma weightedRateNat_nonneg (A : Set ℕ) : 0 ≤ weightedRateNat A := bot_le

lemma chainRate_nonneg (c : ℕ → ℕ) : 0 ≤ chainRate c := bot_le

lemma chainRateNat_nonneg (c : ℕ → ℕ) : 0 ≤ chainRateNat c := bot_le

end Erdos1217
