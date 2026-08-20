/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.NibbleProfileAlgebra
import Mathlib

/-!
# Scalar reductions for the clique-removal drift

The finite nibble theorem exposes two inequalities containing natural-number
products and truncated subtraction.  This file reduces them to transparent
real profile inequalities.  It is important here that an incident-clique
degree is at most the total number of available cliques; retaining this fact
avoids any estimate of a truncated subtraction by zero.
-/

namespace Erdos722.NibbleScalar

noncomputable section

/-- A sufficient real inequality for the upper edge-degree drift. -/
lemma upper_edge_scalar_of_profile
    {K C L x M : ℕ} {degree degreeNext cliqueUpper window : ℝ}
    (hK : 0 < K) (hKC : K * C ≤ L) (hxM : x ≤ M)
    (hwindow : 0 ≤ degree - window)
    (hcritical : -window ≤ (x : ℝ) - degree)
    (hMUpper : (M : ℝ) ≤ cliqueUpper)
    (hprofile :
      cliqueUpper * (degree - degreeNext) ≤
        (degree - window) * (K - 1) * (L - K * C)) :
    (0 : ℝ) ≤
      ((x * (K - 1) * (L - C) : ℕ) : ℝ) -
      ((x * (K - 1) ^ 2 * C : ℕ) : ℝ) +
      ((M - x : ℕ) : ℝ) * (degreeNext - degree) := by
  have hCK : C ≤ L := by
    calc
      C ≤ K * C := by
        exact Nat.le_mul_of_pos_left C hK
      _ ≤ L := hKC
  have hK1 : 1 ≤ K := hK
  have hcoef : (0 : ℝ) ≤ (K - 1) * (L - K * C) := by
    apply mul_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast hK1)
    · exact sub_nonneg.mpr (by exact_mod_cast hKC)
  have hxLower : degree - window ≤ (x : ℝ) := by linarith
  have hpositive :
      (degree - window) * (K - 1) * (L - K * C) ≤
        (x : ℝ) * (K - 1) * (L - K * C) := by
    nlinarith
  have hmxUpper : ((M - x : ℕ) : ℝ) ≤ cliqueUpper := by
    rw [Nat.cast_sub hxM]
    exact (sub_le_self _ (Nat.cast_nonneg x)).trans hMUpper
  have hmain :
      cliqueUpper * (degree - degreeNext) ≤
        (x : ℝ) * (K - 1) * (L - K * C) :=
    hprofile.trans hpositive
  have hsum : (0 : ℝ) ≤
      (x : ℝ) * (K - 1) * (L - K * C) +
        ((M - x : ℕ) : ℝ) * (degreeNext - degree) := by
    by_cases hdelta : degreeNext - degree ≤ 0
    · have hnegative :
          cliqueUpper * (degreeNext - degree) ≤
            ((M - x : ℕ) : ℝ) * (degreeNext - degree) := by
        exact mul_le_mul_of_nonpos_right hmxUpper hdelta
      nlinarith
    · have hdelta0 : 0 ≤ degreeNext - degree := le_of_not_ge hdelta
      have hfirst0 : 0 ≤
          (x : ℝ) * (K - 1) * (L - K * C) := by
        nlinarith [mul_nonneg (Nat.cast_nonneg x) hcoef]
      have hsecond0 : 0 ≤
          ((M - x : ℕ) : ℝ) * (degreeNext - degree) := by positivity
      linarith
  convert hsum using 1 <;>
    push_cast [Nat.cast_sub hCK, Nat.cast_sub hK1, Nat.cast_sub hKC,
      Nat.cast_sub hxM] <;> ring

/-- A sufficient real inequality for the lower edge-degree drift. -/
lemma lower_edge_scalar_of_profile
    {K U x M : ℕ} {degree degreeNext cliqueLower : ℝ}
    (hK : 0 < K) (hxU : x ≤ U) (hxM : x ≤ M)
    (hMLower : cliqueLower ≤ (M : ℝ))
    (hdelta : degreeNext - degree ≤ 0)
    (hprofile :
      (U : ℝ) * (K - 1) * U +
          (cliqueLower - U) * (degreeNext - degree) ≤ 0) :
    (((x * (K - 1) * U : ℕ) : ℝ) +
      ((M - x : ℕ) : ℝ) * (degreeNext - degree)) ≤ 0 := by
  have hK1 : 1 ≤ K := hK
  have hpos : (0 : ℝ) ≤ (K - 1) * U := by
    exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hK1))
      (Nat.cast_nonneg U)
  have hfirst :
      (x : ℝ) * (K - 1) * U ≤ (U : ℝ) * (K - 1) * U := by
    nlinarith [show (x : ℝ) ≤ U by exact_mod_cast hxU]
  have hmxLower : cliqueLower - U ≤ ((M - x : ℕ) : ℝ) := by
    rw [Nat.cast_sub hxM]
    have hxUReal : (x : ℝ) ≤ U := by exact_mod_cast hxU
    linarith
  have hsecond :
      ((M - x : ℕ) : ℝ) * (degreeNext - degree) ≤
        (cliqueLower - U) * (degreeNext - degree) := by
    exact mul_le_mul_of_nonpos_right hmxLower hdelta
  have hsum :
      (x : ℝ) * (K - 1) * U +
          ((M - x : ℕ) : ℝ) * (degreeNext - degree) ≤ 0 := by
    linarith
  convert hsum using 1 <;>
    push_cast [Nat.cast_sub hK1, Nat.cast_sub hxM] <;> ring

lemma floor_profile_sub_one_lt
    {a : ℝ} (ha : 0 ≤ a) : a - 1 < (Nat.floor a : ℝ) := by
  have h := Nat.lt_floor_add_one a
  change a < (Nat.floor a : ℝ) + 1 at h
  linarith

lemma ceil_profile_lt_add_one
    {a : ℝ} (ha : 0 ≤ a) : (Nat.ceil a : ℝ) < a + 1 := by
  exact Nat.ceil_lt_add_one ha

/-- Rounding a lower degree profile down costs less than one in the upper
total-clique drift inequality. -/
lemma clique_upper_scalar_of_profile
    {K C L : ℕ} {lower clique cliqueNext : ℝ}
    (hlower : 0 ≤ lower)
    (hprofile : clique - cliqueNext ≤
      (K : ℝ) * (lower - 1 - K * C))
    (hL : L = Nat.floor lower) :
    (0 : ℝ) ≤ ((K * L : ℕ) : ℝ) -
        ((K ^ 2 * C : ℕ) : ℝ) + (cliqueNext - clique) := by
  have hfloor := floor_profile_sub_one_lt hlower
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hmain : clique - cliqueNext ≤
      (K : ℝ) * ((L : ℝ) - K * C) := by
    apply hprofile.trans
    apply mul_le_mul_of_nonneg_left _ hK0
    rw [hL]
    linarith
  push_cast
  nlinarith

/-- Rounding an upper degree profile up costs less than one in the lower
total-clique drift inequality. -/
lemma clique_lower_scalar_of_profile
    {K U : ℕ} {upper clique cliqueNext : ℝ}
    (hupper : 0 ≤ upper)
    (hprofile : (K : ℝ) * (upper + 1) ≤ clique - cliqueNext)
    (hU : U = Nat.ceil upper) :
    ((K * U : ℕ) : ℝ) + (cliqueNext - clique) ≤ 0 := by
  have hceil := ceil_profile_lt_add_one hupper
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hmain : (K : ℝ) * U ≤ clique - cliqueNext := by
    calc
      (K : ℝ) * U ≤ (K : ℝ) * (upper + 1) := by
        rw [hU]
        exact mul_le_mul_of_nonneg_left hceil.le hK0
      _ ≤ clique - cliqueNext := hprofile
  push_cast
  linarith

end

end Erdos722.NibbleScalar
