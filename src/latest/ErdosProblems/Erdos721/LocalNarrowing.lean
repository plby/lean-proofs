/- leanprover/lean4:v4.33.0 -/
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

import ErdosProblems.Erdos721.LocalDensityStep

/-!
# Bourgain's local narrowing dichotomy

This file proves the elementary regular-Bohr-set averaging lemma which lets
the Kelley--Meka iteration pass to two nested local scales simultaneously.
If no translate has nearly the old density on both scales, one of the two
scales already carries the required density increment.
-/

namespace Erdos721

open Finset Fintype Real
open scoped BigOperators Pointwise

namespace CyclicLocalNarrowing

variable {N : ℕ} [NeZero N]

/-- The mean of a finite-set indicator is its cyclic density. -/
lemma expect_realIndicator (A : Finset (ZMod N)) :
    (𝔼 x : ZMod N, CyclicBohr.realIndicator A x) = (A.card : ℝ) / N := by
  rw [Fintype.expect_eq_sum_div_card]
  have hsum : ∑ x : ZMod N, CyclicBohr.realIndicator A x = A.card := by
    unfold CyclicBohr.realIndicator
    rw [← Finset.sum_filter]
    simp
  rw [hsum, ZMod.card]

/-- Summing all translated relative densities counts every point of `A`
exactly once after normalization. -/
lemma sum_slice_density_eq_card
    (A S : Finset (ZMod N)) (hS : S.Nonempty) :
    ∑ x : ZMod N,
        (CyclicBohr.translatedSlice A S x).card / (S.card : ℝ) = A.card := by
  have havg := CyclicBohr.expect_realConvolution
    (CyclicBohr.realIndicator A) (CyclicBohr.uniformWeight S)
  rw [CyclicBohr.average_uniformWeight hS, mul_one,
    expect_realIndicator A] at havg
  simp_rw [CyclicBohr.realConvolution_indicator_uniformWeight A S hS] at havg
  rw [Fintype.expect_eq_sum_div_card, ZMod.card] at havg
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  apply (div_left_inj' hN).mp
  simpa using havg

/-- If `A ⊆ B_t` and `S ⊆ B_delta`, every nonzero translated slice is
indexed by the outer carrier `B_(t+delta)`. -/
lemma sum_slice_density_over_outer_eq_card
    (B : CyclicBohr.Set N) (A S : Finset (ZMod N)) {t delta : ℝ}
    (ht : 0 ≤ t) (hdelta : 0 ≤ delta)
    (hA : A ⊆ (B.dilate t).carrier)
    (hS : S.Nonempty) (hSsub : S ⊆ (B.dilate delta).carrier) :
    ∑ x ∈ (B.dilate (t + delta)).carrier,
        (CyclicBohr.translatedSlice A S x).card / (S.card : ℝ) = A.card := by
  rw [← sum_slice_density_eq_card A S hS]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _hx hxouter
  have hempty : CyclicBohr.translatedSlice A S x = ∅ := by
    by_contra hne
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [CyclicBohr.translatedSlice, Finset.mem_filter] at ha
    have hadd :=
      CyclicBohr.Set.add_mem_dilate ht hdelta (hA ha.1) (hSsub ha.2)
    have hxeq : a + (x - a) = x := by abel
    exact hxouter (hxeq ▸ hadd)
  simp [hempty]

/-- Bourgain's narrowing dichotomy in exact finite form.  The numerical
condition `4 ≤ M * epsilon` leaves enough room to combine the two bad sets;
the regularity inequality is the sole use of Bohr regularity. -/
theorem narrowing_dichotomy
    (B : CyclicBohr.Set N) (A S T : Finset (ZMod N)) (M : ℕ)
    {t delta alpha epsilon : ℝ}
    (hM : 0 < M) (ht : 0 ≤ t) (hdelta : 0 ≤ delta)
    (halpha : 0 < alpha) (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < 1)
    (hscale : 4 ≤ (M : ℝ) * epsilon)
    (hregular :
      M * (B.dilate (t + delta)).carrier.card ≤
        (M + 1) * (B.dilate t).carrier.card)
    (hA : A ⊆ (B.dilate t).carrier)
    (hdensity : alpha * (B.dilate t).carrier.card = A.card)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSsub : S ⊆ (B.dilate delta).carrier)
    (hTsub : T ⊆ (B.dilate delta).carrier) :
    (∃ x ∈ (B.dilate (t + delta)).carrier,
      (1 - epsilon) * alpha ≤
        (CyclicBohr.translatedSlice A S x).card / (S.card : ℝ) ∧
      (1 - epsilon) * alpha ≤
        (CyclicBohr.translatedSlice A T x).card / (T.card : ℝ)) ∨
    (∃ x,
      (1 + epsilon / 2) * alpha ≤
        (CyclicBohr.translatedSlice A S x).card / (S.card : ℝ)) ∨
    ∃ x,
      (1 + epsilon / 2) * alpha ≤
        (CyclicBohr.translatedSlice A T x).card / (T.card : ℝ) := by
  let D := (B.dilate (t + delta)).carrier
  by_contra h
  push Not at h
  rcases h with ⟨hboth, hSinc, hTinc⟩
  have hpoint (x : ZMod N) (hx : x ∈ D) :
      (CyclicBohr.translatedSlice A S x).card / (S.card : ℝ) +
          (CyclicBohr.translatedSlice A T x).card / (T.card : ℝ) <
        (2 - epsilon / 2) * alpha := by
    have hSupper := hSinc x
    have hTupper := hTinc x
    have hnot := hboth x hx
    by_cases hSlow :
        (1 - epsilon) * alpha ≤
          (CyclicBohr.translatedSlice A S x).card / (S.card : ℝ)
    · have hTlow :
          (CyclicBohr.translatedSlice A T x).card / (T.card : ℝ) <
            (1 - epsilon) * alpha := hnot hSlow
      nlinarith
    · have hSlow' :
          (CyclicBohr.translatedSlice A S x).card / (S.card : ℝ) <
            (1 - epsilon) * alpha := lt_of_not_ge hSlow
      nlinarith
  have hD : D.Nonempty := CyclicBohr.Set.carrier_nonempty _
  have hsumlt :
      ∑ x ∈ D,
          ((CyclicBohr.translatedSlice A S x).card / (S.card : ℝ) +
            (CyclicBohr.translatedSlice A T x).card / (T.card : ℝ)) <
        ∑ _x ∈ D, (2 - epsilon / 2) * alpha := by
    apply Finset.sum_lt_sum_of_nonempty hD
    intro x hx
    exact hpoint x hx
  have hsumS :=
    sum_slice_density_over_outer_eq_card B A S ht hdelta hA hS hSsub
  have hsumT :=
    sum_slice_density_over_outer_eq_card B A T ht hdelta hA hT hTsub
  have hcardlt :
      2 * (A.card : ℝ) <
        (D.card : ℝ) * ((2 - epsilon / 2) * alpha) := by
    rw [Finset.sum_add_distrib, hsumS, hsumT] at hsumlt
    simp only [Finset.sum_const, nsmul_eq_mul] at hsumlt
    convert hsumlt using 1 <;> ring
  have hcancel :
      2 * ((B.dilate t).carrier.card : ℝ) <
        (D.card : ℝ) * (2 - epsilon / 2) := by
    apply lt_of_mul_lt_mul_left (a := alpha) (by
      calc
        alpha * (2 * ((B.dilate t).carrier.card : ℝ)) =
            2 * (A.card : ℝ) := by rw [← hdensity]; ring
        _ < (D.card : ℝ) * ((2 - epsilon / 2) * alpha) := hcardlt
        _ = alpha * ((D.card : ℝ) * (2 - epsilon / 2)) := by ring)
    exact halpha.le
  have hregularR :
      (M : ℝ) * D.card ≤
        ((M : ℝ) + 1) * (B.dilate t).carrier.card := by
    exact_mod_cast hregular
  have hcoeff0 : 0 ≤ 2 - epsilon / 2 := by linarith
  have hcoeff :
      ((M : ℝ) + 1) * (2 - epsilon / 2) ≤ 2 * M := by
    nlinarith
  have hscaled :
      (M : ℝ) * ((D.card : ℝ) * (2 - epsilon / 2)) ≤
        (M : ℝ) * (2 * (B.dilate t).carrier.card) := by
    calc
      (M : ℝ) * ((D.card : ℝ) * (2 - epsilon / 2)) =
          ((M : ℝ) * D.card) * (2 - epsilon / 2) := by ring
      _ ≤ (((M : ℝ) + 1) * (B.dilate t).carrier.card) *
          (2 - epsilon / 2) := mul_le_mul_of_nonneg_right hregularR hcoeff0
      _ = ((B.dilate t).carrier.card : ℝ) *
          (((M : ℝ) + 1) * (2 - epsilon / 2)) := by ring
      _ ≤ ((B.dilate t).carrier.card : ℝ) * (2 * M) := by gcongr
      _ = (M : ℝ) * (2 * (B.dilate t).carrier.card) := by ring
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hbound :
      (D.card : ℝ) * (2 - epsilon / 2) ≤
        2 * (B.dilate t).carrier.card :=
    le_of_mul_le_mul_left hscaled hMreal
  exact (not_lt_of_ge hbound) hcancel

end CyclicLocalNarrowing
end Erdos721
