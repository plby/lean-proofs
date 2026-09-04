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
import ErdosProblems.Erdos722.NibbleInstantiation
import Mathlib

/-!
# Uniform jump and variance bounds for the concrete nibble

This file turns the exact one-step reciprocal-profile formulae into the
three polynomial scales used by the final indexed Freedman union bound.
-/

namespace Erdos722.NibbleBounds

open Finset
open Erdos722.NibbleProfiles
open Erdos722.NibbleConcrete
open Erdos722.NibbleAsymptotic
open Erdos722.NibbleMoments
open Erdos722.NibbleBarrier
open Erdos722.NibbleInstantiation
open Erdos722.NibbleFinite
open Erdos722.FiniteFreedman

noncomputable section

variable {n q r g i : ℕ}

lemma one_div_density_le_scale
    (hT : 0 < scale n q r)
    (hx : 0 < density g (K q r) i)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i) :
    1 / density g (K q r) i ≤ scale n q r := by
  have hTR : (0 : ℝ) < scale n q r := by exact_mod_cast hT
  have hmul : (1 : ℝ) ≤ (scale n q r : ℝ) * density g (K q r) i := by
    have := mul_le_mul_of_nonneg_left hlower hTR.le
    simpa [hTR.ne'] using this
  apply (div_le_iff₀ hx).2
  simpa [mul_comm] using hmul

lemma degreeCenter_le_base
    (hD : 0 ≤ centerDegree n q r)
    (hx : 0 ≤ density g (K q r) i)
    (hxone : density g (K q r) i ≤ 1) :
    degreeCenter (centerDegree n q r) g (K q r) i ≤ centerDegree n q r := by
  unfold degreeCenter
  have hp : density g (K q r) i ^ (K q r - 1) ≤ 1 := by
    simpa using pow_le_one₀ hx hxone
  nlinarith [mul_nonneg hD
    (sub_nonneg.mpr (by simpa using hp))]

lemma degreeErrorUpperGrowth_le
    (hg : 0 < g) (hK : 2 < K q r) (hT : 0 < scale n q r)
    (hstep : K q r * (i + 1) < g)
    (hlower₀ : 1 / (scale n q r : ℝ) ≤ density g (K q r) i)
    (hlower₁ : 1 / (scale n q r : ℝ) ≤ density g (K q r) (i + 1)) :
    degreeErrorUpperGrowth g n q r i ≤
      ((4 * K q r - 1 : ℕ) : ℝ) * (K q r : ℝ) *
        centerDegree n q r / g := by
  have hx : 0 < density g (K q r) i := density_pos hg
    (Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1) |>.trans_lt hstep)
  have hy : 0 < density g (K q r) (i + 1) := density_pos hg hstep
  have hyone : density g (K q r) (i + 1) ≤ 1 :=
    density_le_one_of_mul_le hg hstep.le
  have hD : 0 ≤ centerDegree n q r := by
    unfold centerDegree
    positivity
  have hcenter :
      degreeCenter (centerDegree n q r) g (K q r) (i + 1) ≤
        centerDegree n q r :=
    degreeCenter_le_base hD hy.le hyone
  have herr := degreeError_le_center_div_scale hK.le hT hy hlower₁
  have herrBase :
      degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) (i + 1) ≤
        centerDegree n q r / scale n q r := by
    exact herr.trans (div_le_div_of_nonneg_right hcenter
      (by exact_mod_cast (Nat.zero_le (scale n q r))))
  have hinv := one_div_density_le_scale hT hx hlower₀
  rw [degreeErrorUpperGrowth_eq hg hK.le hstep]
  have hs : (0 : ℝ) ≤ (4 * K q r - 1 : ℕ) := by positivity
  have hKg : (0 : ℝ) ≤ (K q r : ℝ) / g := by positivity
  calc
    ((4 * K q r - 1 : ℕ) : ℝ) *
          degreeError (profileA n q r) (centerDegree n q r)
            g (K q r) (i + 1) *
          ((K q r : ℝ) / g) * (1 / density g (K q r) i) ≤
        ((4 * K q r - 1 : ℕ) : ℝ) *
          (centerDegree n q r / scale n q r) *
          ((K q r : ℝ) / g) * scale n q r := by
      gcongr
    _ = ((4 * K q r - 1 : ℕ) : ℝ) * (K q r : ℝ) *
          centerDegree n q r / g := by
      have hTR : (scale n q r : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
      field_simp [hTR]

lemma degreeProfileStep_le
    (hg : 0 < g) (hK : 2 < K q r) (hT : 0 < scale n q r)
    (hstep : K q r * (i + 1) < g)
    (hlower₀ : 1 / (scale n q r : ℝ) ≤ density g (K q r) i)
    (hlower₁ : 1 / (scale n q r : ℝ) ≤ density g (K q r) (i + 1)) :
    |upperProfile g n q r (i + 1) - upperProfile g n q r i| ≤
        (5 * (K q r : ℝ) ^ 2) * centerDegree n q r / g ∧
    |lowerProfile g n q r (i + 1) - lowerProfile g n q r i| ≤
        (5 * (K q r : ℝ) ^ 2) * centerDegree n q r / g := by
  have hraw := degreeProfiles_step_abs_le (n := n) hg hstep
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hx : 0 < density g (K q r) i := density_pos hg
    (Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1) |>.trans_lt hstep)
  have hxone : density g (K q r) i ≤ 1 :=
    density_le_one_of_mul_le hg
      (Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1) |>.trans hstep.le)
  have hpow : density g (K q r) i ^ (K q r - 2) ≤ 1 := by
    simpa using pow_le_one₀ hx.le hxone
  have hcenterTerm :
      centerDegree n q r *
          (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
            density g (K q r) i ^ (K q r - 2)) ≤
        (K q r : ℝ) ^ 2 * centerDegree n q r / g := by
    have hD : 0 ≤ centerDegree n q r := by unfold centerDegree; positivity
    have hcast : ((K q r - 1 : ℕ) : ℝ) ≤ K q r := by
      exact_mod_cast Nat.sub_le (K q r) 1
    calc
      _ ≤ centerDegree n q r *
          ((K q r : ℝ) * ((K q r : ℝ) / g) * 1) := by gcongr
      _ = _ := by field_simp
  have hgrowth := degreeErrorUpperGrowth_le hg hK hT hstep hlower₀ hlower₁
  have hcoef : ((4 * K q r - 1 : ℕ) : ℝ) ≤ 4 * (K q r : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * K q r)]
    norm_num
  have hgrowth' : degreeErrorUpperGrowth g n q r i ≤
      4 * (K q r : ℝ) ^ 2 * centerDegree n q r / g := by
    have hbase : 0 ≤ (K q r : ℝ) * centerDegree n q r / g := by
      apply div_nonneg
      · exact mul_nonneg (by positivity) (by unfold centerDegree; positivity)
      · positivity
    calc
      _ ≤ ((4 * K q r - 1 : ℕ) : ℝ) * (K q r : ℝ) *
          centerDegree n q r / g := hgrowth
      _ = ((4 * K q r - 1 : ℕ) : ℝ) *
          ((K q r : ℝ) * centerDegree n q r / g) := by ring
      _ ≤ (4 * (K q r : ℝ)) *
          ((K q r : ℝ) * centerDegree n q r / g) :=
        mul_le_mul_of_nonneg_right hcoef hbase
      _ = _ := by ring
  have hsum := add_le_add hcenterTerm hgrowth'
  constructor
  · exact hraw.1.trans (by convert hsum using 1 <;> ring)
  · exact hraw.2.trans (by convert hsum using 1 <;> ring)

lemma cliqueErrorUpperGrowth_le
    (hg : 0 < g) (hK : 2 < K q r) (hT : 0 < scale n q r)
    (hstep : K q r * (i + 1) < g)
    (hlower₀ : 1 / (scale n q r : ℝ) ≤ density g (K q r) i)
    (hlower₁ : 1 / (scale n q r : ℝ) ≤ density g (K q r) (i + 1)) :
    cliqueErrorUpperGrowth g n q r i ≤
      ((4 * K q r - 2 : ℕ) : ℝ) * centerDegree n q r := by
  have hx : 0 < density g (K q r) i := density_pos hg
    (Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1) |>.trans_lt hstep)
  have hy : 0 < density g (K q r) (i + 1) := density_pos hg hstep
  have hyone : density g (K q r) (i + 1) ≤ 1 :=
    density_le_one_of_mul_le hg hstep.le
  have hD : 0 ≤ centerDegree n q r := by unfold centerDegree; positivity
  have hcenter : degreeCenter (centerDegree n q r) g (K q r) (i + 1) ≤
      centerDegree n q r := degreeCenter_le_base hD hy.le hyone
  have herr := degreeError_le_center_div_scale hK.le hT hy hlower₁
  have herrBase :
      degreeError (profileA n q r) (centerDegree n q r)
          g (K q r) (i + 1) ≤ centerDegree n q r / scale n q r :=
    herr.trans (div_le_div_of_nonneg_right hcenter
      (by exact_mod_cast (Nat.zero_le (scale n q r))))
  have hremNonneg : 0 ≤ remaining g (K q r) (i + 1) := by
    exact (remaining_pos hstep).le
  have hremUpper : remaining g (K q r) (i + 1) ≤ g := by
    unfold remaining
    exact sub_le_self _ (by positivity)
  have hErrNonneg : 0 ≤ degreeError (profileA n q r) (centerDegree n q r)
      g (K q r) (i + 1) := by
    unfold degreeError profileA centerDegree
    positivity
  have hcliqueErr :
      cliqueError (profileA n q r) (centerDegree n q r)
          g (K q r) (i + 1) ≤
        (g : ℝ) / K q r * (centerDegree n q r / scale n q r) := by
    rw [cliqueError_eq_remaining_mul hg hK.le hstep]
    have hremCast : (remaining g (K q r) (i + 1) : ℝ) ≤ g := by
      exact hremUpper
    have hKreal : (0 : ℝ) < K q r := by exact_mod_cast (by omega : 0 < K q r)
    have hfactor : remaining g (K q r) (i + 1) / (K q r : ℝ) ≤
        (g : ℝ) / K q r := div_le_div_of_nonneg_right hremCast hKreal.le
    exact mul_le_mul hfactor herrBase hErrNonneg
      (div_nonneg (Nat.cast_nonneg g) hKreal.le)
  have hinv := one_div_density_le_scale hT hx hlower₀
  rw [cliqueErrorUpperGrowth_eq hg hK.le hstep]
  have hs : (0 : ℝ) ≤ (4 * K q r - 2 : ℕ) := by positivity
  have hKg : (0 : ℝ) ≤ (K q r : ℝ) / g := by positivity
  calc
    ((4 * K q r - 2 : ℕ) : ℝ) *
          cliqueError (profileA n q r) (centerDegree n q r)
            g (K q r) (i + 1) *
          ((K q r : ℝ) / g) * (1 / density g (K q r) i) ≤
        ((4 * K q r - 2 : ℕ) : ℝ) *
          (((g : ℝ) / K q r) *
            (centerDegree n q r / scale n q r)) *
          ((K q r : ℝ) / g) * scale n q r := by
      gcongr
    _ = ((4 * K q r - 2 : ℕ) : ℝ) * centerDegree n q r := by
      have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
      have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
      have hT0 : (scale n q r : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
      field_simp [hg0, hK0, hT0]

lemma cliqueProfileStep_le
    (hg : 0 < g) (hK : 2 < K q r) (hT : 0 < scale n q r)
    (hstep : K q r * (i + 1) < g)
    (hlower₀ : 1 / (scale n q r : ℝ) ≤ density g (K q r) i)
    (hlower₁ : 1 / (scale n q r : ℝ) ≤ density g (K q r) (i + 1)) :
    |cliqueUpperProfile g n q r (i + 1) - cliqueUpperProfile g n q r i| ≤
        5 * (K q r : ℝ) * centerDegree n q r ∧
    |cliqueLowerProfile g n q r (i + 1) - cliqueLowerProfile g n q r i| ≤
        5 * (K q r : ℝ) * centerDegree n q r := by
  have hraw := cliqueProfiles_step_abs_le (n := n) hg (by omega) hstep
  have hx : 0 < density g (K q r) i := density_pos hg
    (Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1) |>.trans_lt hstep)
  have hxone : density g (K q r) i ≤ 1 :=
    density_le_one_of_mul_le hg
      (Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1) |>.trans hstep.le)
  have hpow : density g (K q r) i ^ (K q r - 1) ≤ 1 := by
    simpa using pow_le_one₀ hx.le hxone
  have hcenterTerm :
      ((g : ℝ) * centerDegree n q r / K q r) *
          ((K q r : ℝ) * ((K q r : ℝ) / g) *
            density g (K q r) i ^ (K q r - 1)) ≤
        (K q r : ℝ) * centerDegree n q r := by
    have hD : 0 ≤ centerDegree n q r := by unfold centerDegree; positivity
    have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    have hK0 : (K q r : ℝ) ≠ 0 := by exact_mod_cast (by omega : K q r ≠ 0)
    calc
      _ ≤ ((g : ℝ) * centerDegree n q r / K q r) *
          ((K q r : ℝ) * ((K q r : ℝ) / g) * 1) := by gcongr
      _ = _ := by field_simp [hg0, hK0]
  have hgrowth := cliqueErrorUpperGrowth_le hg hK hT hstep hlower₀ hlower₁
  have hcoef : ((4 * K q r - 2 : ℕ) : ℝ) ≤ 4 * (K q r : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ 4 * K q r)]
    norm_num
  have hgrowth' : cliqueErrorUpperGrowth g n q r i ≤
      4 * (K q r : ℝ) * centerDegree n q r := by
    exact hgrowth.trans (mul_le_mul_of_nonneg_right hcoef
      (by unfold centerDegree; positivity))
  have hsum := add_le_add hcenterTerm hgrowth'
  constructor
  · exact hraw.1.trans (by convert hsum using 1 <;> ring)
  · exact hraw.2.trans (by convert hsum using 1 <;> ring)

lemma faceWeight_eq_one_div_density
    (hg : 0 < g) (hi : K q r * i < g) :
    faceWeight g (K q r) i = 1 / density g (K q r) i := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hrem : remaining g (K q r) i ≠ 0 :=
    (remaining_pos hi).ne'
  unfold faceWeight density
  field_simp [hg0, hrem]

lemma faceWeight_le_scale
    (hg : 0 < g) (hT : 0 < scale n q r)
    (hi : K q r * i < g)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i) :
    faceWeight g (K q r) i ≤ scale n q r := by
  rw [faceWeight_eq_one_div_density hg hi]
  exact one_div_density_le_scale hT (density_pos hg hi) hlower

lemma faceWeight_step_nonneg
    (hg : 0 < g) (hstep : K q r * (i + 1) < g) :
    0 ≤ faceWeight g (K q r) (i + 1) - faceWeight g (K q r) i := by
  have hi : K q r * i < g :=
    (Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1)).trans_lt hstep
  rw [faceWeight_eq_one_div_density hg hstep,
    faceWeight_eq_one_div_density hg hi]
  have hx := density_pos hg hi
  have hy := density_pos hg hstep
  have hyx : density g (K q r) (i + 1) ≤ density g (K q r) i := by
    rw [density_succ]
    have : (0 : ℝ) ≤ (K q r : ℝ) / g := by positivity
    linarith
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hy hyx)

lemma faceWeight_step_le
    (hg : 0 < g) (hT : 0 < scale n q r)
    (hstep : K q r * (i + 1) < g)
    (hlower₀ : 1 / (scale n q r : ℝ) ≤ density g (K q r) i)
    (hlower₁ : 1 / (scale n q r : ℝ) ≤ density g (K q r) (i + 1)) :
    faceWeight g (K q r) (i + 1) - faceWeight g (K q r) i ≤
      (K q r : ℝ) * (scale n q r : ℝ) ^ 2 / g := by
  have hi : K q r * i < g :=
    (Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1)).trans_lt hstep
  have hx := density_pos hg hi
  have hy := density_pos hg hstep
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hidentity :
      faceWeight g (K q r) (i + 1) - faceWeight g (K q r) i =
        ((K q r : ℝ) / g) * (1 / density g (K q r) i) *
          (1 / density g (K q r) (i + 1)) := by
    rw [faceWeight_eq_one_div_density hg hstep,
      faceWeight_eq_one_div_density hg hi]
    have hs := density_succ g (K q r) i
    have hdiff : density g (K q r) i - (K q r : ℝ) / g ≠ 0 := by
      rw [← hs]
      exact hy.ne'
    have hscaled : density g (K q r) i * (g : ℝ) - K q r ≠ 0 := by
      apply ne_of_gt
      have hdiffPos : 0 < density g (K q r) i - (K q r : ℝ) / g := by
        rw [← hs]
        exact hy
      have hgR : (0 : ℝ) < g := by exact_mod_cast hg
      calc
        0 < (density g (K q r) i - (K q r : ℝ) / g) * g :=
          mul_pos hdiffPos hgR
        _ = density g (K q r) i * g - K q r := by
          field_simp [hg0]
    rw [hs]
    field_simp [hg0, hx.ne', hdiff, hscaled]
    ring
  rw [hidentity]
  have hinv₀ := one_div_density_le_scale hT hx hlower₀
  have hinv₁ := one_div_density_le_scale hT hy hlower₁
  have hKg : (0 : ℝ) ≤ (K q r : ℝ) / g := by positivity
  calc
    _ ≤ ((K q r : ℝ) / g) * scale n q r * scale n q r := by gcongr
    _ = _ := by ring

lemma upperNat_cast_le_three_base
    (hg : 0 < g) (hK : 2 < K q r) (hT : 1 ≤ scale n q r)
    (hi : K q r * i < g)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i)
    (hDone : 1 ≤ centerDegree n q r) :
    (upperNat g n q r i : ℝ) ≤ 3 * centerDegree n q r := by
  have hx := density_pos hg hi
  have hxone := density_le_one_of_mul_le hg hi.le
  have hD : 0 ≤ centerDegree n q r :=
    (by norm_num : (0 : ℝ) ≤ 1).trans hDone
  have hcenter := degreeCenter_le_base hD hx.le hxone
  have herr := degreeError_le_center_div_scale hK.le (by omega) hx hlower
  have hTreal : (1 : ℝ) ≤ scale n q r := by exact_mod_cast hT
  have herrCenter : degreeError (profileA n q r) (centerDegree n q r)
      g (K q r) i ≤ centerDegree n q r := by
    calc
      _ ≤ degreeCenter (centerDegree n q r) g (K q r) i / scale n q r := herr
      _ ≤ centerDegree n q r / scale n q r :=
        div_le_div_of_nonneg_right hcenter (Nat.cast_nonneg _)
      _ ≤ centerDegree n q r := by
        exact (div_le_iff₀ (show (0 : ℝ) < scale n q r by positivity)).2
          (by nlinarith)
  have hu : upperProfile g n q r i ≤ 2 * centerDegree n q r := by
    unfold upperProfile degreeUpper
    linarith
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ upperProfile g n q r i by
    unfold upperProfile degreeUpper
    exact add_nonneg
      (by unfold degreeCenter; positivity)
      (by unfold degreeError profileA centerDegree; positivity))
  change (Nat.ceil (upperProfile g n q r i) : ℝ) ≤ _
  have hDone' : (1 : ℝ) ≤ centerDegree n q r := hDone
  linarith

/-- At every step covered by the terminal density bound, the rounded upper
profile is at most three times its *current* centre.  Retaining this current
centre is what makes the clique-count denominator cancel in the moment
estimates below. -/
lemma upperNat_cast_le_three_center
    (hK : 2 < K q r) (hT : 8 ≤ scale n q r)
    (hx : 0 < density g (K q r) i)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i)
    (hpower : (scale n q r : ℝ) ^ K q r ≤ centerDegree n q r) :
    (upperNat g n q r i : ℝ) ≤
      3 * degreeCenter (centerDegree n q r) g (K q r) i := by
  let Z := degreeCenter (centerDegree n q r) g (K q r) i
  let E := degreeError (profileA n q r) (centerDegree n q r) g (K q r) i
  have hTpos : 0 < scale n q r := by omega
  have hZscale : (scale n q r : ℝ) ≤ Z := by
    simpa [Z] using scale_le_degreeCenter (by omega) hTpos hlower hpower
  have hEZ : E ≤ Z / scale n q r := by
    simpa [E, Z] using degreeError_le_center_div_scale hK.le hTpos hx hlower
  have hZ0 : 0 ≤ Z := by
    dsimp [Z]
    unfold degreeCenter centerDegree
    positivity
  have hE0 : 0 ≤ E := by
    dsimp [E]
    unfold degreeError profileA centerDegree
    positivity
  have hTreal : (8 : ℝ) ≤ scale n q r := by exact_mod_cast hT
  have hEsmall : E ≤ Z / 8 := by
    calc
      E ≤ Z / scale n q r := hEZ
      _ ≤ Z / 8 := by gcongr
  have hupperNonneg : 0 ≤ upperProfile g n q r i := by
    dsimp [upperProfile, degreeUpper, Z, E]
    positivity
  have hceil := Nat.ceil_lt_add_one hupperNonneg
  change (Nat.ceil (upperProfile g n q r i) : ℝ) ≤ 3 * Z
  have hZone : (1 : ℝ) ≤ Z :=
    (show (1 : ℝ) ≤ 8 by norm_num).trans (hTreal.trans hZscale)
  change (Nat.ceil (Z + E) : ℝ) < Z + E + 1 at hceil
  change (Nat.ceil (Z + E) : ℝ) ≤ 3 * Z
  linarith

/-- The lower degree profile retains at least half of its current centre. -/
lemma half_center_le_lowerProfile
    (hK : 2 < K q r) (hT : 8 ≤ scale n q r)
    (hx : 0 < density g (K q r) i)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i) :
    degreeCenter (centerDegree n q r) g (K q r) i / 2 ≤
      lowerProfile g n q r i := by
  let Z := degreeCenter (centerDegree n q r) g (K q r) i
  let E := degreeError (profileA n q r) (centerDegree n q r) g (K q r) i
  have hTpos : 0 < scale n q r := by omega
  have hEZ : E ≤ Z / scale n q r := by
    simpa [E, Z] using degreeError_le_center_div_scale hK.le hTpos hx hlower
  have hZ0 : 0 ≤ Z := by
    dsimp [Z]
    unfold degreeCenter centerDegree
    positivity
  have hTreal : (8 : ℝ) ≤ scale n q r := by exact_mod_cast hT
  have hEhalf : E ≤ Z / 2 := hEZ.trans (by
    gcongr
    exact_mod_cast (show 2 ≤ scale n q r by omega))
  dsimp [lowerProfile, degreeLower, Z, E]
  linarith

lemma cliqueLowerProfile_ge_center
    (hg : 0 < g) (hK : 2 < K q r) (hT : 8 ≤ scale n q r)
    (hi : K q r * i < g)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i) :
    remaining g (K q r) i *
          degreeCenter (centerDegree n q r) g (K q r) i /
          (2 * (K q r : ℝ)) ≤
      cliqueLowerProfile g n q r i := by
  have hx := density_pos hg hi
  have hrem : 0 ≤ remaining g (K q r) i := (remaining_pos hi).le
  have hhalf := half_center_le_lowerProfile hK hT hx hlower
  rw [cliqueLowerProfile_eq_remaining_mul hg (by omega) hi]
  have hKR : (0 : ℝ) < K q r := by positivity
  calc
    remaining g (K q r) i *
          degreeCenter (centerDegree n q r) g (K q r) i /
          (2 * (K q r : ℝ)) =
        remaining g (K q r) i / (K q r : ℝ) *
          (degreeCenter (centerDegree n q r) g (K q r) i / 2) := by ring
    _ ≤ remaining g (K q r) i / (K q r : ℝ) *
          lowerProfile g n q r i := by gcongr

/-- The rounded degree divided by the tracked clique lower profile has the
scale forced by the surviving host size. -/
lemma upperNat_div_cliqueLowerProfile_le
    (hg : 0 < g) (hK : 2 < K q r) (hT : 8 ≤ scale n q r)
    (hi : K q r * i < g)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i)
    (hpower : (scale n q r : ℝ) ^ K q r ≤ centerDegree n q r) :
    (upperNat g n q r i : ℝ) / cliqueLowerProfile g n q r i ≤
      6 * (K q r : ℝ) * scale n q r / g := by
  let Z := degreeCenter (centerDegree n q r) g (K q r) i
  let R := remaining g (K q r) i
  let C := cliqueLowerProfile g n q r i
  have hx := density_pos hg hi
  have hU := upperNat_cast_le_three_center hK hT hx hlower hpower
  have hCge : R * Z / (2 * (K q r : ℝ)) ≤ C := by
    simpa [R, Z, C] using cliqueLowerProfile_ge_center hg hK hT hi hlower
  have hZscale : (scale n q r : ℝ) ≤ Z :=
    scale_le_degreeCenter (by omega) (by omega) hlower hpower
  have hZpos : 0 < Z := (by positivity : (0 : ℝ) < scale n q r).trans_le hZscale
  have hRpos : 0 < R := by simpa [R] using remaining_pos hi
  have hCpos : 0 < C := lt_of_lt_of_le
    (div_pos (mul_pos hRpos hZpos) (by positivity)) hCge
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hTR : (0 : ℝ) < scale n q r := by positivity
  have hremain : (g : ℝ) ≤ (scale n q r : ℝ) * R := by
    have hdiv : (1 : ℝ) / scale n q r ≤ R / g := by
      simpa [density, R] using hlower
    have := (div_le_div_iff₀ hTR hgR).mp hdiv
    simpa [mul_comm] using this
  have hone : (1 : ℝ) ≤ (scale n q r : ℝ) * R / g :=
    (le_div_iff₀ hgR).2 (by simpa [mul_comm] using hremain)
  apply (div_le_iff₀ hCpos).2
  calc
    (upperNat g n q r i : ℝ) ≤ 3 * Z := hU
    _ ≤ (6 * (K q r : ℝ) * scale n q r / g) *
          (R * Z / (2 * (K q r : ℝ))) := by
      have hKpos : (0 : ℝ) < K q r := by positivity
      rw [show (6 * (K q r : ℝ) * scale n q r / g) *
          (R * Z / (2 * (K q r : ℝ))) =
            3 * Z * ((scale n q r : ℝ) * R / g) by
        field_simp
        ring]
      simpa using mul_le_mul_of_nonneg_left hone
        (show 0 ≤ 3 * Z by positivity)
    _ ≤ (6 * (K q r : ℝ) * scale n q r / g) * C := by
      gcongr

/-- The edge absolute-moment denominator cancels one current degree centre;
the remaining loss is only one power of the stopping scale. -/
lemma edgeMomentTerm_le
    (hg : 0 < g) (hK : 2 < K q r) (hT : 8 ≤ scale n q r)
    (hi : K q r * i < g)
    (hlower : 1 / (scale n q r : ℝ) ≤ density g (K q r) i)
    (hpower : (scale n q r : ℝ) ^ K q r ≤ centerDegree n q r) :
    (((upperNat g n q r i * (K q r - 1) *
          upperNat g n q r i : ℕ) : ℝ) /
        cliqueLowerProfile g n q r i) ≤
      18 * (K q r : ℝ) ^ 2 * scale n q r * centerDegree n q r / g := by
  let Z := degreeCenter (centerDegree n q r) g (K q r) i
  let R := remaining g (K q r) i
  let C := cliqueLowerProfile g n q r i
  let U : ℝ := upperNat g n q r i
  have hx := density_pos hg hi
  have hxone := density_le_one_of_mul_le hg hi.le
  have hU := upperNat_cast_le_three_center hK hT hx hlower hpower
  have hCge : R * Z / (2 * (K q r : ℝ)) ≤ C := by
    simpa [R, Z, C] using cliqueLowerProfile_ge_center hg hK hT hi hlower
  have hZscale : (scale n q r : ℝ) ≤ Z :=
    scale_le_degreeCenter (by omega) (by omega) hlower hpower
  have hZpos : 0 < Z := (by positivity : (0 : ℝ) < scale n q r).trans_le hZscale
  have hRpos : 0 < R := by simpa [R] using remaining_pos hi
  have hCpos : 0 < C := lt_of_lt_of_le
    (div_pos (mul_pos hRpos hZpos) (by positivity)) hCge
  have hD0 : 0 ≤ centerDegree n q r := by
    unfold centerDegree
    positivity
  have hZD : Z ≤ centerDegree n q r := by
    simpa [Z] using degreeCenter_le_base hD0 hx.le hxone
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hremain : (g : ℝ) ≤ (scale n q r : ℝ) * R := by
    have hTR : (0 : ℝ) < scale n q r := by positivity
    have hdiv : (1 : ℝ) / scale n q r ≤ R / g := by
      simpa [density, R] using hlower
    have := (div_le_div_iff₀ hTR hgR).mp hdiv
    simpa [mul_comm] using this
  have hone : (1 : ℝ) ≤ (scale n q r : ℝ) * R / g :=
    (le_div_iff₀ hgR).2 (by simpa [mul_comm] using hremain)
  have hnum : (((upperNat g n q r i * (K q r - 1) *
          upperNat g n q r i : ℕ) : ℝ)) ≤
      9 * (K q r : ℝ) * Z ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ K q r)]
    simp only [Nat.cast_one]
    change (upperNat g n q r i : ℝ) * ((K q r : ℝ) - (1 : ℝ)) *
      (upperNat g n q r i : ℝ) ≤ _
    have hU0 : 0 ≤ (upperNat g n q r i : ℝ) := by positivity
    have hKm : (0 : ℝ) ≤ (K q r : ℝ) - 1 :=
      sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ K q r by omega))
    have hKmK : (K q r : ℝ) - 1 ≤ K q r := by linarith
    calc
      (upperNat g n q r i : ℝ) * ((K q r : ℝ) - 1) *
          (upperNat g n q r i : ℝ) ≤
          (3 * Z) * ((K q r : ℝ) - 1) * (3 * Z) := by
        gcongr
      _ ≤ (3 * Z) * (K q r : ℝ) * (3 * Z) := by gcongr
      _ = 9 * (K q r : ℝ) * Z ^ 2 := by ring
  apply (div_le_iff₀ hCpos).2
  calc
    (((upperNat g n q r i * (K q r - 1) *
          upperNat g n q r i : ℕ) : ℝ)) ≤
        9 * (K q r : ℝ) * Z ^ 2 := hnum
    _ ≤ (18 * (K q r : ℝ) ^ 2 * scale n q r *
          centerDegree n q r / g) *
          (R * Z / (2 * (K q r : ℝ))) := by
      have hKpos : (0 : ℝ) < K q r := by positivity
      rw [show (18 * (K q r : ℝ) ^ 2 * scale n q r *
          centerDegree n q r / g) *
          (R * Z / (2 * (K q r : ℝ))) =
          9 * (K q r : ℝ) * Z * centerDegree n q r *
            ((scale n q r : ℝ) * R / g) by
        field_simp
        ring]
      calc
        9 * (K q r : ℝ) * Z ^ 2 ≤
            9 * (K q r : ℝ) * Z * centerDegree n q r := by
          rw [show 9 * (K q r : ℝ) * Z ^ 2 =
            (9 * (K q r : ℝ) * Z) * Z by ring]
          exact mul_le_mul_of_nonneg_left hZD (by positivity)
        _ ≤ 9 * (K q r : ℝ) * Z * centerDegree n q r *
              ((scale n q r : ℝ) * R / g) := by
          simpa using mul_le_mul_of_nonneg_left hone
            (show 0 ≤ 9 * (K q r : ℝ) * Z * centerDegree n q r by positivity)
    _ ≤ (18 * (K q r : ℝ) ^ 2 * scale n q r *
          centerDegree n q r / g) * C := by gcongr

def concreteJumpCap
    (host : Finset (Finset (Fin n))) (q r : ℕ) :
    BarrierIndex host r → ℝ
  | Sum.inl (Sum.inl _) =>
      (K q r : ℝ) * (n : ℝ) ^ (q - r - 1) +
        5 * (K q r : ℝ) ^ 2 * centerDegree n q r / host.card
  | Sum.inl (Sum.inr _) =>
      8 * (K q r : ℝ) * centerDegree n q r
  | Sum.inr _ => 3 * (K q r : ℝ) * scale n q r

def concreteAbsCap
    (host : Finset (Finset (Fin n))) (q r : ℕ) :
    BarrierIndex host r → ℝ
  | Sum.inl (Sum.inl _) =>
      24 * (K q r : ℝ) ^ 2 * scale n q r *
        centerDegree n q r / host.card
  | Sum.inl (Sum.inr _) =>
      8 * (K q r : ℝ) * centerDegree n q r
  | Sum.inr _ =>
      8 * (K q r : ℝ) * n * (scale n q r : ℝ) ^ 2 / host.card

lemma barrierAbsBudget_le_concreteAbsCap
    {host : Finset (Finset (Fin n))}
    (hg : 0 < host.card) (hK : 2 < K q r)
    (hT : 8 ≤ scale n q r)
    (hpower : (scale n q r : ℝ) ^ K q r ≤ centerDegree n q r)
    (hstep : K q r * (i + 1) < host.card)
    (hlower₀ : 1 / (scale n q r : ℝ) ≤
      density host.card (K q r) i)
    (hlower₁ : 1 / (scale n q r : ℝ) ≤
      density host.card (K q r) (i + 1))
    (z : BarrierIndex host r) :
    barrierAbsBudget host q r
        (upperProfile host.card n q r) (lowerProfile host.card n q r)
        (cliqueUpperProfile host.card n q r)
        (cliqueLowerProfile host.card n q r)
        (faceWeight host.card (K q r))
        (faceCap n (faceSlack n q r) (faceEps n q r)
          host.card (K q r))
        (upperNat host.card n q r)
        (cliqueLowerProfile host.card n q r) z i ≤
      concreteAbsCap host q r z := by
  have hi : K q r * i < host.card :=
    (Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1)).trans_lt hstep
  have hx := density_pos hg hi
  have hxone := density_le_one_of_mul_le hg hi.le
  have hdegree := degreeProfileStep_le hg hK (by omega)
    hstep hlower₀ hlower₁
  have hclique := cliqueProfileStep_le hg hK (by omega)
    hstep hlower₀ hlower₁
  have hD0 : 0 ≤ centerDegree n q r := by
    unfold centerDegree
    positivity
  have hZle : degreeCenter (centerDegree n q r) host.card (K q r) i ≤
      centerDegree n q r := degreeCenter_le_base hD0 hx.le hxone
  have hUcenter := upperNat_cast_le_three_center hK hT hx hlower₀ hpower
  have hUbase : (upperNat host.card n q r i : ℝ) ≤
      3 * centerDegree n q r := hUcenter.trans (by gcongr)
  rcases z with (eb | b) | f
  · rcases eb with ⟨e, b⟩
    have hmoment := edgeMomentTerm_le hg hK hT hi hlower₀ hpower
    cases b
    · simp only [barrierAbsBudget, concreteAbsCap]
      rw [show Nat.choose q r = K q r by rfl]
      calc
        (((upperNat host.card n q r i * (K q r - 1) *
              upperNat host.card n q r i : ℕ) : ℝ) /
              cliqueLowerProfile host.card n q r i) +
            |upperProfile host.card n q r (i + 1) -
              upperProfile host.card n q r i| ≤
          18 * (K q r : ℝ) ^ 2 * scale n q r * centerDegree n q r /
              host.card +
            5 * (K q r : ℝ) ^ 2 * centerDegree n q r / host.card :=
          add_le_add hmoment hdegree.1
        _ ≤ 24 * (K q r : ℝ) ^ 2 * scale n q r *
              centerDegree n q r / host.card := by
          have hTR : (8 : ℝ) ≤ scale n q r := by exact_mod_cast hT
          have hgR : (0 : ℝ) < host.card := by exact_mod_cast hg
          field_simp
          have hX : 0 ≤ (K q r : ℝ) ^ 2 * centerDegree n q r := by
            positivity
          nlinarith [mul_nonneg (sub_nonneg.mpr hTR) hX]
    · simp only [barrierAbsBudget, concreteAbsCap]
      rw [show Nat.choose q r = K q r by rfl]
      calc
        (((upperNat host.card n q r i * (K q r - 1) *
              upperNat host.card n q r i : ℕ) : ℝ) /
              cliqueLowerProfile host.card n q r i) +
            |lowerProfile host.card n q r (i + 1) -
              lowerProfile host.card n q r i| ≤
          18 * (K q r : ℝ) ^ 2 * scale n q r * centerDegree n q r /
              host.card +
            5 * (K q r : ℝ) ^ 2 * centerDegree n q r / host.card :=
          add_le_add hmoment hdegree.2
        _ ≤ 24 * (K q r : ℝ) ^ 2 * scale n q r *
              centerDegree n q r / host.card := by
          have hTR : (8 : ℝ) ≤ scale n q r := by exact_mod_cast hT
          have hgR : (0 : ℝ) < host.card := by exact_mod_cast hg
          field_simp
          have hX : 0 ≤ (K q r : ℝ) ^ 2 * centerDegree n q r := by
            positivity
          nlinarith [mul_nonneg (sub_nonneg.mpr hTR) hX]
  · have hKU : (K q r : ℝ) * (upperNat host.card n q r i : ℝ) ≤
        3 * (K q r : ℝ) * centerDegree n q r := by
      calc
        (K q r : ℝ) * (upperNat host.card n q r i : ℝ) ≤
            (K q r : ℝ) * (3 * centerDegree n q r) :=
          mul_le_mul_of_nonneg_left hUbase (by positivity)
        _ = _ := by ring
    cases b
    · simp only [barrierAbsBudget, concreteAbsCap]
      rw [show Nat.choose q r = K q r by rfl]
      calc
        (K q r : ℝ) * (upperNat host.card n q r i : ℝ) +
            |cliqueUpperProfile host.card n q r (i + 1) -
              cliqueUpperProfile host.card n q r i| ≤
          3 * (K q r : ℝ) * centerDegree n q r +
            5 * (K q r : ℝ) * centerDegree n q r :=
          add_le_add hKU hclique.1
        _ = 8 * (K q r : ℝ) * centerDegree n q r := by ring
    · simp only [barrierAbsBudget, concreteAbsCap]
      rw [show Nat.choose q r = K q r by rfl]
      calc
        (K q r : ℝ) * (upperNat host.card n q r i : ℝ) +
            |cliqueLowerProfile host.card n q r (i + 1) -
              cliqueLowerProfile host.card n q r i| ≤
          3 * (K q r : ℝ) * centerDegree n q r +
            5 * (K q r : ℝ) * centerDegree n q r :=
          add_le_add hKU hclique.2
        _ = 8 * (K q r : ℝ) * centerDegree n q r := by ring
  · let dw := faceWeight host.card (K q r) (i + 1) -
        faceWeight host.card (K q r) i
    have hdw0 : 0 ≤ dw := by
      simpa [dw] using faceWeight_step_nonneg hg hstep
    have hdw : dw ≤ (K q r : ℝ) * (scale n q r : ℝ) ^ 2 /
        host.card := by
      simpa [dw] using faceWeight_step_le hg (by omega) hstep hlower₀ hlower₁
    have hw := faceWeight_le_scale (n := n) hg (by omega) hstep hlower₁
    have hw0 : 0 ≤ faceWeight host.card (K q r) (i + 1) :=
      (faceWeight_pos hg hstep).le
    have hratio0 := upperNat_div_cliqueLowerProfile_le
      hg hK hT hi hlower₀ hpower
    have hratio : (((n * upperNat host.card n q r i : ℕ) : ℝ) /
          cliqueLowerProfile host.card n q r i) ≤
        (n : ℝ) * (6 * (K q r : ℝ) * scale n q r / host.card) := by
      push_cast
      calc
        (n : ℝ) * (upperNat host.card n q r i : ℝ) /
            cliqueLowerProfile host.card n q r i =
          (n : ℝ) * ((upperNat host.card n q r i : ℝ) /
            cliqueLowerProfile host.card n q r i) := by ring
        _ ≤ _ := by gcongr
    have hmiddle : faceWeight host.card (K q r) (i + 1) *
          (((n * upperNat host.card n q r i : ℕ) : ℝ) /
            cliqueLowerProfile host.card n q r i) ≤
        6 * (K q r : ℝ) * n * (scale n q r : ℝ) ^ 2 / host.card := by
      calc
        _ ≤ faceWeight host.card (K q r) (i + 1) *
            ((n : ℝ) * (6 * (K q r : ℝ) * scale n q r / host.card)) := by
          exact mul_le_mul_of_nonneg_left hratio hw0
        _ ≤ (scale n q r : ℝ) *
            ((n : ℝ) * (6 * (K q r : ℝ) * scale n q r / host.card)) := by
          apply mul_le_mul_of_nonneg_right hw
          have hgR : (0 : ℝ) < host.card := by exact_mod_cast hg
          positivity
        _ = _ := by ring
    have heps : 0 ≤ faceEps n q r := by unfold faceEps; positivity
    have hepsOne : faceEps n q r ≤ 1 := by
      unfold faceEps
      have hTR : (0 : ℝ) < scale n q r := by positivity
      apply (div_le_iff₀ hTR).2
      simpa using (show (8 : ℝ) ≤ scale n q r by exact_mod_cast hT)
    have hcapDiff :
        faceCap n (faceSlack n q r) (faceEps n q r)
              host.card (K q r) (i + 1) -
            faceCap n (faceSlack n q r) (faceEps n q r)
              host.card (K q r) i =
          (n : ℝ) * faceEps n q r * dw := by
      unfold faceCap
      dsimp [dw]
      ring
    simp only [barrierAbsBudget, concreteAbsCap]
    rw [abs_of_nonneg hdw0, abs_of_nonneg hw0, hcapDiff,
      abs_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) heps) hdw0)]
    have hfirst : dw * n ≤
        (K q r : ℝ) * n * (scale n q r : ℝ) ^ 2 / host.card := by
      calc
        dw * n ≤ ((K q r : ℝ) * (scale n q r : ℝ) ^ 2 /
            host.card) * n := by gcongr
        _ = _ := by ring
    have hlast : (n : ℝ) * faceEps n q r * dw ≤
        (K q r : ℝ) * n * (scale n q r : ℝ) ^ 2 / host.card := by
      calc
        (n : ℝ) * faceEps n q r * dw = faceEps n q r * (dw * n) := by ring
        _ ≤ 1 * (dw * n) := by gcongr
        _ ≤ _ := by simpa using hfirst
    calc
      dw * n +
            faceWeight host.card (K q r) (i + 1) *
              (((n * upperNat host.card n q r i : ℕ) : ℝ) /
                cliqueLowerProfile host.card n q r i) +
            (n : ℝ) * faceEps n q r * dw ≤
          ((K q r : ℝ) * n * (scale n q r : ℝ) ^ 2 / host.card) +
            (6 * (K q r : ℝ) * n * (scale n q r : ℝ) ^ 2 / host.card) +
            ((K q r : ℝ) * n * (scale n q r : ℝ) ^ 2 / host.card) :=
        add_le_add (add_le_add hfirst hmiddle) hlast
      _ = 8 * (K q r : ℝ) * n * (scale n q r : ℝ) ^ 2 /
          host.card := by ring

lemma barrierJump_le_concreteJumpCap
    {host : Finset (Finset (Fin n))}
    (hg : 0 < host.card) (hK : 2 < K q r)
    (hT : 8 ≤ scale n q r) (hDone : 1 ≤ centerDegree n q r)
    (hhostFace : (2 : ℝ) * n * scale n q r ≤ host.card)
    (hstep : K q r * (i + 1) < host.card)
    (hlower₀ : 1 / (scale n q r : ℝ) ≤
      density host.card (K q r) i)
    (hlower₁ : 1 / (scale n q r : ℝ) ≤
      density host.card (K q r) (i + 1))
    (z : BarrierIndex host r) :
    barrierJump host q r
        (upperProfile host.card n q r) (lowerProfile host.card n q r)
        (cliqueUpperProfile host.card n q r)
        (cliqueLowerProfile host.card n q r)
        (faceWeight host.card (K q r))
        (faceCap n (faceSlack n q r) (faceEps n q r)
          host.card (K q r))
        (upperNat host.card n q r) z i ≤ concreteJumpCap host q r z := by
  have hdegree := degreeProfileStep_le hg hK (by omega) hstep hlower₀ hlower₁
  have hclique := cliqueProfileStep_le hg hK (by omega) hstep hlower₀ hlower₁
  rcases z with (eb | b) | f
  · rcases eb with ⟨e, b⟩
    cases b
    · simpa [barrierJump, concreteJumpCap, edgeDeletionJump, K,
        Nat.cast_mul, Nat.cast_pow] using
        add_le_add_left hdegree.1
          ((K q r : ℝ) * (n : ℝ) ^ (q - r - 1))
    · simpa [barrierJump, concreteJumpCap, edgeDeletionJump, K,
        Nat.cast_mul, Nat.cast_pow] using
        add_le_add_left hdegree.2
          ((K q r : ℝ) * (n : ℝ) ^ (q - r - 1))
  · have hU := upperNat_cast_le_three_base hg hK (by omega)
      ((Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1)).trans_lt hstep)
      hlower₀ hDone
    have hKU : (K q r : ℝ) * (upperNat host.card n q r i : ℝ) ≤
        3 * (K q r : ℝ) * centerDegree n q r := by
      calc
        (K q r : ℝ) * upperNat host.card n q r i ≤
            (K q r : ℝ) * (3 * centerDegree n q r) :=
          mul_le_mul_of_nonneg_left hU (by positivity)
        _ = _ := by ring
    cases b
    · simp only [barrierJump, concreteJumpCap]
      rw [show Nat.choose q r = K q r by rfl]
      calc
        (K q r : ℝ) * (upperNat host.card n q r i : ℝ) +
            |cliqueUpperProfile host.card n q r (i + 1) -
              cliqueUpperProfile host.card n q r i| ≤
          3 * (K q r : ℝ) * centerDegree n q r +
            5 * (K q r : ℝ) * centerDegree n q r :=
          add_le_add hKU hclique.1
        _ = 8 * (K q r : ℝ) * centerDegree n q r := by ring
    · simp only [barrierJump, concreteJumpCap]
      rw [show Nat.choose q r = K q r by rfl]
      calc
        (K q r : ℝ) * (upperNat host.card n q r i : ℝ) +
            |cliqueLowerProfile host.card n q r (i + 1) -
              cliqueLowerProfile host.card n q r i| ≤
          3 * (K q r : ℝ) * centerDegree n q r +
            5 * (K q r : ℝ) * centerDegree n q r :=
          add_le_add hKU hclique.2
        _ = 8 * (K q r : ℝ) * centerDegree n q r := by ring
  · let dw := faceWeight host.card (K q r) (i + 1) -
        faceWeight host.card (K q r) i
    have hdw0 : 0 ≤ dw := by
      simpa [dw] using faceWeight_step_nonneg hg hstep
    have hdw := faceWeight_step_le hg (by omega) hstep hlower₀ hlower₁
    have hw := faceWeight_le_scale (n := n) hg (by omega) hstep hlower₁
    have hw0 : 0 ≤ faceWeight host.card (K q r) (i + 1) :=
      (faceWeight_pos hg hstep).le
    have heps : 0 ≤ faceEps n q r := by unfold faceEps; positivity
    have hepsOne : faceEps n q r ≤ 1 := by
      unfold faceEps
      have hTR : (0 : ℝ) < scale n q r := by positivity
      apply (div_le_iff₀ hTR).2
      simpa using (show (8 : ℝ) ≤ scale n q r by exact_mod_cast hT)
    have hcapDiff :
        faceCap n (faceSlack n q r) (faceEps n q r)
              host.card (K q r) (i + 1) -
            faceCap n (faceSlack n q r) (faceEps n q r)
              host.card (K q r) i =
          (n : ℝ) * faceEps n q r * dw := by
      unfold faceCap
      dsimp [dw]
      ring
    have hsmallTerm : dw * n ≤
        (K q r : ℝ) * scale n q r / 2 := by
      have hdw' : dw ≤ (K q r : ℝ) * (scale n q r : ℝ) ^ 2 /
          host.card := by simpa [dw] using hdw
      calc
        dw * n ≤ ((K q r : ℝ) * (scale n q r : ℝ) ^ 2 /
            host.card) * n :=
          mul_le_mul_of_nonneg_right hdw' (Nat.cast_nonneg n)
        _ ≤ (K q r : ℝ) * scale n q r / 2 := by
          have hgR : (0 : ℝ) < host.card := by exact_mod_cast hg
          rw [show (K q r : ℝ) * (scale n q r : ℝ) ^ 2 /
              host.card * n =
            ((K q r : ℝ) * (scale n q r : ℝ) ^ 2 * n) /
              host.card by ring]
          apply (div_le_iff₀ hgR).2
          have hrel : (2 : ℝ) * n * scale n q r ≤ host.card := hhostFace
          have hKT : 0 ≤ (K q r : ℝ) * scale n q r := by positivity
          nlinarith [mul_nonneg hKT (sub_nonneg.mpr hrel)]
    have hcapSmall : (n : ℝ) * faceEps n q r * dw ≤
        (K q r : ℝ) * scale n q r / 2 := by
      calc
        (n : ℝ) * faceEps n q r * dw = faceEps n q r * (dw * n) := by ring
        _ ≤ 1 * (dw * n) := by gcongr
        _ ≤ _ := by simpa using hsmallTerm
    simp only [barrierJump, concreteJumpCap]
    rw [abs_of_nonneg hdw0, abs_of_nonneg hw0, hcapDiff,
      abs_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) heps) hdw0)]
    have hweightTerm : faceWeight host.card (K q r) (i + 1) *
        (Nat.choose q r : ℝ) ≤
          (K q r : ℝ) * scale n q r := by
      rw [show Nat.choose q r = K q r by rfl]
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ K q r)
        (sub_nonneg.mpr hw)]
    nlinarith

/-- A constant pointwise bound sums to `depth` times that constant over the
recursive variance budget. -/
lemma varianceBudget_le_depth_mul
    (v : ℕ → ℝ) (C : ℝ) (start depth : ℕ)
    (h : ∀ i, start ≤ i → i < start + depth → v i ≤ C) :
    varianceBudget v start depth ≤ (depth : ℝ) * C := by
  induction depth generalizing start with
  | zero => simp [varianceBudget]
  | succ depth ih =>
      rw [varianceBudget]
      have hstart : v start ≤ C := h start (by omega) (by omega)
      have htail : varianceBudget v (start + 1) depth ≤ (depth : ℝ) * C := by
        apply ih
        intro i hi₀ hi₁
        apply h i (by omega)
        omega
      push_cast
      linarith

lemma varianceBudget_nonneg_of
    (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) (start depth : ℕ) :
    0 ≤ varianceBudget v start depth := by
  induction depth generalizing start with
  | zero => simp [varianceBudget]
  | succ depth ih =>
      rw [varianceBudget]
      exact add_nonneg (hv start) (ih (start + 1))

def concreteVarianceTotalCap
    (host : Finset (Finset (Fin n))) (q r : ℕ) :
    BarrierIndex host r → ℝ := fun z ↦
  (host.card : ℝ) * concreteJumpCap host q r z * concreteAbsCap host q r z

def scoreConstant (q r : ℕ) : ℝ :=
  40000 * (2 : ℝ) ^ (q - r + 1) * (q - r).factorial * (K q r : ℝ) ^ 4

def concentrationScore (n q r : ℕ) : ℝ :=
  (n : ℝ) /
    (scoreConstant q r * (scale n q r : ℝ) ^ (10 * K q r - 1))

private lemma edge_score_cross
    {P : ℕ} {x C K₀ T D N J : ℝ}
    (hx : 0 ≤ x) (hC : 1 ≤ C) (hK : 1 ≤ K₀) (hT : 1 ≤ T)
    (hD : 0 < D) (hN : 0 ≤ N) (hJ : 0 ≤ J)
    (hJbound : J ≤ 6 * K₀ ^ 2 * N)
    (hlower : x * N ≤ C * D) :
    (x / (40000 * C * K₀ ^ 4 * T ^ (2 * P + 1))) *
        (4 * (24 * K₀ ^ 2 * T * D * J +
          (D / (4 * T ^ P)) * J)) ≤
      ((D / (4 * T ^ P)) / 2) ^ 2 := by
  have hK0 : 0 < K₀ := lt_of_lt_of_le (by norm_num) hK
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hTP : 1 ≤ T ^ P := one_le_pow₀ hT
  have hWle : D / (4 * T ^ P) ≤ D := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * T ^ P)).2
    nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hTP)]
  have hDle : D ≤ K₀ ^ 2 * T * D := by
    have hfac : 1 ≤ K₀ ^ 2 * T := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr (one_le_pow₀ hK : 1 ≤ K₀ ^ 2))
        (sub_nonneg.mpr hT)]
    nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hfac)]
  have hbracket : 24 * K₀ ^ 2 * T * D + D / (4 * T ^ P) ≤
      25 * K₀ ^ 2 * T * D := by linarith
  have hsum : 24 * K₀ ^ 2 * T * D * J +
        (D / (4 * T ^ P)) * J ≤
      150 * K₀ ^ 4 * N * T * D := by
    calc
      _ = J * (24 * K₀ ^ 2 * T * D + D / (4 * T ^ P)) := by ring
      _ ≤ (6 * K₀ ^ 2 * N) * (25 * K₀ ^ 2 * T * D) := by
        exact mul_le_mul hJbound hbracket (by positivity) (by positivity)
      _ = _ := by ring
  calc
    (x / (40000 * C * K₀ ^ 4 * T ^ (2 * P + 1))) *
        (4 * (24 * K₀ ^ 2 * T * D * J +
          (D / (4 * T ^ P)) * J)) ≤
      (x / (40000 * C * K₀ ^ 4 * T ^ (2 * P + 1))) *
        (4 * (150 * K₀ ^ 4 * N * T * D)) := by gcongr
    _ ≤ ((D / (4 * T ^ P)) / 2) ^ 2 := by
      have hpow : T ^ (2 * P + 1) = (T ^ P) ^ 2 * T := by
        rw [pow_add, pow_one, show 2 * P = P + P by omega, pow_add, pow_two]
      rw [hpow]
      field_simp
      nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hlower)]

private lemma clique_score_cross
    {P : ℕ} {x C K₀ T D g : ℝ}
    (hx : 0 ≤ x) (hC : 1 ≤ C) (hK : 1 ≤ K₀) (hT : 1 ≤ T)
    (hD : 0 < D) (hg : 0 < g) (hxg : x ≤ g) :
    (x / (40000 * C * K₀ ^ 4 * T ^ (2 * P + 1))) *
        (4 * (64 * K₀ ^ 2 * g * D ^ 2 +
          (g * D / (4 * K₀ * T ^ P)) * (8 * K₀ * D))) ≤
      ((g * D / (4 * K₀ * T ^ P)) / 2) ^ 2 := by
  have hK0 : 0 < K₀ := lt_of_lt_of_le (by norm_num) hK
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hTP : 1 ≤ T ^ P := one_le_pow₀ hT
  have hsmall : (g * D / (4 * K₀ * T ^ P)) * (8 * K₀ * D) ≤
      2 * K₀ ^ 2 * g * D ^ 2 := by
    have hdiv : (g * D / (4 * K₀ * T ^ P)) * (8 * K₀ * D) =
        2 * g * D ^ 2 / T ^ P := by field_simp; ring
    rw [hdiv]
    have hle : 2 * g * D ^ 2 / T ^ P ≤ 2 * g * D ^ 2 := by
      apply (div_le_iff₀ (by positivity : 0 < T ^ P)).2
      nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * g * D ^ 2)
        (sub_nonneg.mpr hTP)]
    exact hle.trans (by
      have hKsq : 1 ≤ K₀ ^ 2 := one_le_pow₀ hK
      nlinarith [mul_nonneg
        (by positivity : 0 ≤ 2 * g * D ^ 2)
        (sub_nonneg.mpr hKsq)])
  have hsum : 64 * K₀ ^ 2 * g * D ^ 2 +
        (g * D / (4 * K₀ * T ^ P)) * (8 * K₀ * D) ≤
      66 * K₀ ^ 2 * g * D ^ 2 := by linarith
  calc
    (x / (40000 * C * K₀ ^ 4 * T ^ (2 * P + 1))) *
        (4 * (64 * K₀ ^ 2 * g * D ^ 2 +
          (g * D / (4 * K₀ * T ^ P)) * (8 * K₀ * D))) ≤
      (x / (40000 * C * K₀ ^ 4 * T ^ (2 * P + 1))) *
        (4 * (66 * K₀ ^ 2 * g * D ^ 2)) := by gcongr
    _ ≤ ((g * D / (4 * K₀ * T ^ P)) / 2) ^ 2 := by
      have hpow : T ^ (2 * P + 1) = (T ^ P) ^ 2 * T := by
        rw [pow_add, pow_one, show 2 * P = P + P by omega, pow_add, pow_two]
      rw [hpow]
      field_simp
      have hCg : x ≤ C * T * g := by
        calc
          x ≤ g := hxg
          _ ≤ C * T * g := by
            have hCT : 1 ≤ C * T := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hT)]
            nlinarith [mul_nonneg hg.le (sub_nonneg.mpr hCT)]
      nlinarith [mul_nonneg (by positivity : 0 ≤ K₀ ^ 2 * g * D ^ 2)
        (sub_nonneg.mpr hCg)]

private lemma face_score_cross
    {Q : ℕ} {x C K₀ T : ℝ}
    (hQ : 7 ≤ Q) (hx : 0 < x) (hC : 1 ≤ C)
    (hK : 1 ≤ K₀) (hT : 1 ≤ T) :
    (x / (40000 * C * K₀ ^ 4 * T ^ Q)) *
        (4 * (24 * K₀ ^ 2 * x * T ^ 3 +
          (x / (2 * T ^ 2)) * (3 * K₀ * T))) ≤
      ((x / (2 * T ^ 2)) / 2) ^ 2 := by
  have hK0 : 0 < K₀ := lt_of_lt_of_le (by norm_num) hK
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hsmall : (x / (2 * T ^ 2)) * (3 * K₀ * T) ≤
      3 * K₀ ^ 2 * x * T ^ 3 := by
    have heq : (x / (2 * T ^ 2)) * (3 * K₀ * T) =
        (3 * K₀ * x) / (2 * T) := by field_simp
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 2 * T)).2
    have hfac : 1 ≤ 2 * K₀ * T ^ 4 := by
      have hT4 : 1 ≤ T ^ 4 := one_le_pow₀ hT
      nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hT4)]
    nlinarith [mul_nonneg
      (by positivity : 0 ≤ 3 * K₀ * x)
      (sub_nonneg.mpr hfac)]
  have hsum : 24 * K₀ ^ 2 * x * T ^ 3 +
        (x / (2 * T ^ 2)) * (3 * K₀ * T) ≤
      27 * K₀ ^ 2 * x * T ^ 3 := by linarith
  calc
    (x / (40000 * C * K₀ ^ 4 * T ^ Q)) *
        (4 * (24 * K₀ ^ 2 * x * T ^ 3 +
          (x / (2 * T ^ 2)) * (3 * K₀ * T))) ≤
      (x / (40000 * C * K₀ ^ 4 * T ^ Q)) *
        (4 * (27 * K₀ ^ 2 * x * T ^ 3)) := by gcongr
    _ ≤ ((x / (2 * T ^ 2)) / 2) ^ 2 := by
      have hpow : T ^ 7 ≤ T ^ Q := pow_le_pow_right₀ hT hQ
      have hconst : 1728 * T ^ 7 ≤ 40000 * C * K₀ ^ 2 * T ^ Q := by
        have hCK : 1 ≤ C * K₀ ^ 2 := by
          have hKsq : 1 ≤ K₀ ^ 2 := one_le_pow₀ hK
          nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hKsq)]
        calc
          1728 * T ^ 7 ≤ 40000 * T ^ 7 := by gcongr <;> norm_num
          _ ≤ 40000 * T ^ Q := by gcongr
          _ ≤ 40000 * C * K₀ ^ 2 * T ^ Q := by
            nlinarith [mul_nonneg
              (by positivity : 0 ≤ 40000 * T ^ Q)
              (sub_nonneg.mpr hCK)]
      field_simp
      nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hconst)]

/-- The canonical optimized positive Freedman rate associated with a window,
jump bound, and deterministic total variance bound. -/
def freedmanRate (window jump variance : ℝ) : ℝ :=
  (window - jump) /
    (2 * (variance + (window - jump) * jump))

def concreteRate
    (host : Finset (Finset (Fin n))) (q r : ℕ) :
    BarrierIndex host r → ℝ := fun z ↦
  freedmanRate (profileWindow host q r z)
    (concreteJumpCap host q r z) (concreteVarianceTotalCap host q r z)

lemma freedmanRate_pos {window jump variance : ℝ}
    (hjump : 0 < jump) (hgap : jump < window) (hvariance : 0 ≤ variance) :
    0 < freedmanRate window jump variance := by
  unfold freedmanRate
  exact div_pos (sub_pos.mpr hgap)
    (mul_pos (by norm_num)
      (add_pos_of_nonneg_of_pos hvariance
        (mul_pos (sub_pos.mpr hgap) hjump)))

lemma freedmanRate_mul_jump_le_one {window jump variance : ℝ}
    (hjump : 0 < jump) (hgap : jump < window) (hvariance : 0 ≤ variance) :
    freedmanRate window jump variance * jump ≤ 1 := by
  let G := window - jump
  let S := variance + G * jump
  have hG : 0 < G := by simpa [G] using sub_pos.mpr hgap
  have hS : 0 < S := add_pos_of_nonneg_of_pos hvariance (mul_pos hG hjump)
  change (G / (2 * S)) * jump ≤ 1
  rw [show (G / (2 * S)) * jump = (G * jump) / (2 * S) by ring]
  apply (div_le_iff₀ (mul_pos (by norm_num) hS)).2
  dsimp [S]
  nlinarith [mul_nonneg hG.le hjump.le]

lemma freedman_exponent_le {window jump variance varianceCap : ℝ}
    (hjump : 0 < jump) (hgap : jump < window)
    (hvariance : 0 ≤ variance) (hvarianceCap : variance ≤ varianceCap) :
    -freedmanRate window jump varianceCap * (window - jump) +
        (freedmanRate window jump varianceCap) ^ 2 * variance ≤
      -(window - jump) ^ 2 /
        (4 * (varianceCap + (window - jump) * jump)) := by
  let G := window - jump
  let S := varianceCap + G * jump
  have hG : 0 < G := by simpa [G] using sub_pos.mpr hgap
  have hVcap : 0 ≤ varianceCap := hvariance.trans hvarianceCap
  have hS : 0 < S := add_pos_of_nonneg_of_pos hVcap (mul_pos hG hjump)
  have hVS : variance ≤ S := hvarianceCap.trans (le_add_of_nonneg_right
    (mul_nonneg hG.le hjump.le))
  change -(G / (2 * S)) * G + (G / (2 * S)) ^ 2 * variance ≤
    -(G ^ 2) / (4 * S)
  have hsq : 0 ≤ (G / (2 * S)) ^ 2 := sq_nonneg _
  calc
    -(G / (2 * S)) * G + (G / (2 * S)) ^ 2 * variance ≤
        -(G / (2 * S)) * G + (G / (2 * S)) ^ 2 * S := by
      simpa [add_comm] using add_le_add_left
        (mul_le_mul_of_nonneg_left hVS hsq) (-(G / (2 * S)) * G)
    _ = -(G ^ 2) / (4 * S) := by
      field_simp
      ring

lemma score_le_freedman_of_half_window
    {score window jump variance : ℝ}
    (hscore : 0 ≤ score) (hjump : 0 < jump) (hvariance : 0 ≤ variance)
    (hhalf : 2 * jump ≤ window)
    (hcross : score * (4 * (variance + window * jump)) ≤
      (window / 2) ^ 2) :
    score ≤ (window - jump) ^ 2 /
      (4 * (variance + (window - jump) * jump)) := by
  have hwindow : 0 < window := lt_of_lt_of_le (by linarith : 0 < 2 * jump) hhalf
  have hgap : window / 2 ≤ window - jump := by linarith
  have hgap0 : 0 < window - jump := by linarith
  have hden : 0 < 4 * (variance + (window - jump) * jump) := by positivity
  apply (le_div_iff₀ hden).2
  calc
    score * (4 * (variance + (window - jump) * jump)) ≤
        score * (4 * (variance + window * jump)) := by
      have hprod : (window - jump) * jump ≤ window * jump := by
        nlinarith [sq_nonneg jump]
      have hadd := add_le_add_left hprod variance
      have hfour := mul_le_mul_of_nonneg_left hadd (by norm_num : (0 : ℝ) ≤ 4)
      exact mul_le_mul_of_nonneg_left (by simpa [add_comm] using hfour) hscore
    _ ≤ (window / 2) ^ 2 := hcross
    _ ≤ (window - jump) ^ 2 := by
      have hdiff : 0 ≤ (window - jump) - window / 2 := sub_nonneg.mpr hgap
      have hsum : 0 ≤ (window - jump) + window / 2 := by linarith
      nlinarith [mul_nonneg hdiff hsum]

lemma concreteJumpCap_nonneg
    {host : Finset (Finset (Fin n))} (hg : 0 < host.card)
    (z : BarrierIndex host r) : 0 ≤ concreteJumpCap host q r z := by
  have hgR : (0 : ℝ) < host.card := by exact_mod_cast hg
  have hD : 0 ≤ centerDegree n q r := by
    unfold centerDegree
    positivity
  rcases z with (eb | b) | f
  · rcases eb with ⟨e, b⟩
    cases b <;> simp only [ge_iff_le] <;> positivity
  · cases b <;> simp only [ge_iff_le] <;> positivity
  · simp only [ge_iff_le]
    positivity

lemma concreteAbsCap_nonneg
    {host : Finset (Finset (Fin n))} (hg : 0 < host.card)
    (z : BarrierIndex host r) : 0 ≤ concreteAbsCap host q r z := by
  have hgR : (0 : ℝ) < host.card := by exact_mod_cast hg
  have hD : 0 ≤ centerDegree n q r := by
    unfold centerDegree
    positivity
  rcases z with (eb | b) | f
  · rcases eb with ⟨e, b⟩
    cases b <;> simp only [ge_iff_le] <;> positivity
  · cases b <;> simp only [ge_iff_le] <;> positivity
  · simp only [ge_iff_le]
    positivity

lemma concrete_jump_pos_and_half_window
    {host : Finset (Finset (Fin n))}
    (hg : 0 < host.card) (hn : 0 < n) (hK : 2 < K q r)
    (hT : 8 ≤ scale n q r) (hD : 0 < centerDegree n q r)
    (hDg : centerDegree n q r / host.card ≤
      (n : ℝ) ^ (q - r - 1))
    (hedge : 48 * (K q r : ℝ) ^ 2 *
        (n : ℝ) ^ (q - r - 1) ≤ initialError n q r)
    (hclique : 64 * (K q r : ℝ) ^ 2 *
        (scale n q r : ℝ) ^ (5 * K q r - 1) ≤ host.card)
    (hface : 12 * (K q r : ℝ) * (scale n q r : ℝ) ^ 3 ≤ n) :
    (∀ z : BarrierIndex host r, 0 < concreteJumpCap host q r z) ∧
      (∀ z : BarrierIndex host r,
        2 * concreteJumpCap host q r z ≤ profileWindow host q r z) := by
  have hKR : (1 : ℝ) ≤ K q r := by exact_mod_cast (show 1 ≤ K q r by omega)
  have hTR : (0 : ℝ) < scale n q r := by positivity
  have hgR : (0 : ℝ) < host.card := by exact_mod_cast hg
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro z
    rcases z with (eb | b) | f
    · rcases eb with ⟨e, b⟩
      cases b <;> simp [concreteJumpCap] <;> positivity
    · cases b <;> simp [concreteJumpCap] <;> positivity
    · simp [concreteJumpCap]
      positivity
  · intro z
    rcases z with (eb | b) | f
    · rcases eb with ⟨e, b⟩
      have hJ : (K q r : ℝ) * (n : ℝ) ^ (q - r - 1) +
            5 * (K q r : ℝ) ^ 2 * centerDegree n q r / host.card ≤
          6 * (K q r : ℝ) ^ 2 * (n : ℝ) ^ (q - r - 1) := by
        calc
          _ ≤ (K q r : ℝ) * (n : ℝ) ^ (q - r - 1) +
              5 * (K q r : ℝ) ^ 2 *
                (n : ℝ) ^ (q - r - 1) := by
            have hterm : 5 * (K q r : ℝ) ^ 2 * centerDegree n q r /
                  host.card ≤
                5 * (K q r : ℝ) ^ 2 * (n : ℝ) ^ (q - r - 1) := by
              rw [show 5 * (K q r : ℝ) ^ 2 * centerDegree n q r /
                    host.card = 5 * (K q r : ℝ) ^ 2 *
                      (centerDegree n q r / host.card) by ring]
              exact mul_le_mul_of_nonneg_left hDg (by positivity)
            simpa [add_comm] using add_le_add_left hterm
              ((K q r : ℝ) * (n : ℝ) ^ (q - r - 1))
          _ ≤ _ := by
            have hN : 0 ≤ (n : ℝ) ^ (q - r - 1) := by positivity
            nlinarith [mul_nonneg (sub_nonneg.mpr hKR)
              (mul_nonneg (by positivity : (0 : ℝ) ≤ K q r) hN)]
      cases b <;> simp only [concreteJumpCap, profileWindow] <;>
        exact (mul_le_mul_of_nonneg_left hJ (by norm_num)).trans (by
          have := hedge
          linarith)
    · cases b <;> simp only [concreteJumpCap, profileWindow] <;>
        unfold initialError <;>
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * K q r)).2 <;>
        rw [show (host.card : ℝ) *
            (centerDegree n q r / (scale n q r : ℝ) ^ (5 * K q r - 1)) =
          ((host.card : ℝ) * centerDegree n q r) /
            (scale n q r : ℝ) ^ (5 * K q r - 1) by ring] <;>
        apply (le_div_iff₀ (pow_pos hTR (5 * K q r - 1))).2 <;>
        convert mul_le_mul_of_nonneg_right hclique hD.le using 1 <;> ring
    · simp only [concreteJumpCap, profileWindow]
      unfold faceSlack
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      apply (le_div_iff₀ (pow_pos hTR 2)).2
      have hpow : (scale n q r : ℝ) ^ 3 =
          (scale n q r : ℝ) * (scale n q r : ℝ) ^ 2 := by ring
      rw [hpow] at hface
      nlinarith [hface]

lemma concentrationScore_le_freedman_score
    {host : Finset (Finset (Fin n))}
    (hg : 0 < host.card) (hn : 0 < n) (hK : 2 < K q r)
    (hT : 8 ≤ scale n q r) (hD : 0 < centerDegree n q r)
    (hDg : centerDegree n q r / host.card ≤
      (n : ℝ) ^ (q - r - 1))
    (hCD : (n : ℝ) * (n : ℝ) ^ (q - r - 1) ≤
      ((2 : ℝ) ^ (q - r + 1) * (q - r).factorial) * centerDegree n q r)
    (hng : (n : ℝ) ≤ host.card)
    (hedge : 48 * (K q r : ℝ) ^ 2 *
        (n : ℝ) ^ (q - r - 1) ≤ initialError n q r)
    (hclique : 64 * (K q r : ℝ) ^ 2 *
        (scale n q r : ℝ) ^ (5 * K q r - 1) ≤ host.card)
    (hface : 12 * (K q r : ℝ) * (scale n q r : ℝ) ^ 3 ≤ n) :
    ∀ z : BarrierIndex host r,
      concentrationScore n q r ≤
        (profileWindow host q r z - concreteJumpCap host q r z) ^ 2 /
          (4 * (concreteVarianceTotalCap host q r z +
            (profileWindow host q r z - concreteJumpCap host q r z) *
              concreteJumpCap host q r z)) := by
  let C : ℝ := (2 : ℝ) ^ (q - r + 1) * (q - r).factorial
  let P := 5 * K q r - 1
  have hC : (1 : ℝ) ≤ C := by
    have hpow : (1 : ℝ) ≤ 2 ^ (q - r + 1) := one_le_pow₀ (by norm_num)
    have hfac : (1 : ℝ) ≤ (q - r).factorial := by
      exact_mod_cast (Nat.factorial_pos (q - r))
    dsimp [C]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow) (sub_nonneg.mpr hfac)]
  have hKR : (1 : ℝ) ≤ K q r := by exact_mod_cast (show 1 ≤ K q r by omega)
  have hTR : (1 : ℝ) ≤ scale n q r := by exact_mod_cast (show 1 ≤ scale n q r by omega)
  have hgR : (0 : ℝ) < host.card := by exact_mod_cast hg
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalfData := concrete_jump_pos_and_half_window hg hn hK hT hD
    hDg hedge hclique hface
  intro z
  apply score_le_freedman_of_half_window
  · unfold concentrationScore scoreConstant
    positivity
  · exact hhalfData.1 z
  · exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (concreteJumpCap_nonneg hg z))
      (concreteAbsCap_nonneg hg z)
  · exact hhalfData.2 z
  · rcases z with (eb | b) | f
    · rcases eb with ⟨e, b⟩
      let J := (K q r : ℝ) * (n : ℝ) ^ (q - r - 1) +
        5 * (K q r : ℝ) ^ 2 * centerDegree n q r / host.card
      have hJ0 : 0 ≤ J := by dsimp [J]; positivity
      have hJbound : J ≤ 6 * (K q r : ℝ) ^ 2 *
          (n : ℝ) ^ (q - r - 1) := by
        dsimp [J]
        have hterm : 5 * (K q r : ℝ) ^ 2 * centerDegree n q r /
              host.card ≤
            5 * (K q r : ℝ) ^ 2 * (n : ℝ) ^ (q - r - 1) := by
          rw [show 5 * (K q r : ℝ) ^ 2 * centerDegree n q r /
                host.card = 5 * (K q r : ℝ) ^ 2 *
                  (centerDegree n q r / host.card) by ring]
          exact mul_le_mul_of_nonneg_left hDg (by positivity)
        calc
          _ ≤ (K q r : ℝ) * (n : ℝ) ^ (q - r - 1) +
              5 * (K q r : ℝ) ^ 2 * (n : ℝ) ^ (q - r - 1) := by
            linarith
          _ ≤ _ := by
            have hN : 0 ≤ (n : ℝ) ^ (q - r - 1) := by positivity
            nlinarith [mul_nonneg (sub_nonneg.mpr hKR)
              (mul_nonneg (by positivity : (0 : ℝ) ≤ K q r) hN)]
      have hcross := edge_score_cross (P := P) hnR.le hC hKR hTR hD
        (by positivity : 0 ≤ (n : ℝ) ^ (q - r - 1)) hJ0 hJbound
        (by simpa [C] using hCD)
      cases b <;>
        convert hcross using 1 <;>
        simp [concentrationScore, scoreConstant, concreteVarianceTotalCap,
          concreteJumpCap, concreteAbsCap, profileWindow, initialError,
          P, C, J, show 10 * K q r - 1 = 2 * (5 * K q r - 1) + 1 by omega] <;>
        field_simp [hgR.ne'] <;> ring
    · have hcross := clique_score_cross (P := P) hnR.le hC hKR hTR hD
        hgR hng
      cases b <;>
        convert hcross using 1 <;>
        simp [concentrationScore, scoreConstant, concreteVarianceTotalCap,
          concreteJumpCap, concreteAbsCap, profileWindow, initialError,
          P, C, show 10 * K q r - 1 = 2 * (5 * K q r - 1) + 1 by omega] <;>
        field_simp [hgR.ne'] <;> ring
    · have hQ : 7 ≤ 10 * K q r - 1 := by omega
      have hcross := face_score_cross (Q := 10 * K q r - 1)
        hQ hnR hC hKR hTR
      convert hcross using 1 <;>
        simp [concentrationScore, scoreConstant, concreteVarianceTotalCap,
          concreteJumpCap, concreteAbsCap, profileWindow, faceSlack, C] <;>
        field_simp [hgR.ne'] <;> ring

/-- Uniform total predictable-variance bound for every concrete barrier. -/
lemma concrete_varianceBudget_le_totalCap
    {host : Finset (Finset (Fin n))}
    (hg : 0 < host.card) (hK : 2 < K q r)
    (hT : 8 ≤ scale n q r) (hDone : 1 ≤ centerDegree n q r)
    (hpower : (scale n q r : ℝ) ^ K q r ≤ centerDegree n q r)
    (htarget : stopTarget host.card n q r ≤ host.card)
    (hhostFace : (2 : ℝ) * n * scale n q r ≤ host.card)
    (z : BarrierIndex host r) :
    varianceBudget (concreteVariance host q r z) 0
        (depth host.card n q r) ≤ concreteVarianceTotalCap host q r z := by
  let d := depth host.card n q r
  let J := concreteJumpCap host q r z
  let A := concreteAbsCap host q r z
  have hKpos : 0 < K q r := by omega
  have hTpos : 0 < scale n q r := by omega
  have htargetPos : 0 < stopTarget host.card n q r := by
    dsimp [stopTarget]
    omega
  have hstep : ∀ i < d, K q r * (i + 1) < host.card := by
    intro i hi
    exact mul_succ_lt_of_lt_depth hKpos htargetPos
      (by simpa only [d, depth] using hi)
  have hlower : ∀ i, i ≤ d →
      1 / (scale n q r : ℝ) ≤ density host.card (K q r) i := by
    intro i hi
    exact one_div_scale_le_density hg hKpos hTpos htarget
      (by simpa only [d] using hi)
  have hpoint : ∀ i, 0 ≤ i → i < 0 + d →
      concreteVariance host q r z i ≤ J * A := by
    intro i _hi0 hi
    have hs := hstep i (by simpa using hi)
    have hl0 := hlower i (by omega)
    have hl1 := hlower (i + 1) (by omega)
    have hJ := barrierJump_le_concreteJumpCap hg hK hT hDone hhostFace
      hs hl0 hl1 z
    have hA := barrierAbsBudget_le_concreteAbsCap hg hK hT hpower
      hs hl0 hl1 z
    have hiDepth : i < depth host.card n q r := by
      simpa only [Nat.zero_add, d] using hi
    simp only [concreteVariance, finiteVariance, if_pos hiDepth]
    apply mul_le_mul hJ hA
    · exact barrierAbsBudget_nonneg host q r
        (upperProfile host.card n q r) (lowerProfile host.card n q r)
        (cliqueUpperProfile host.card n q r)
        (cliqueLowerProfile host.card n q r)
        (faceWeight host.card (K q r))
        (faceCap n (faceSlack n q r) (faceEps n q r)
          host.card (K q r))
        (upperNat host.card n q r)
        (cliqueLowerProfile host.card n q r) z i (by
          have hiStep : K q r * i < host.card :=
            (Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1)).trans_lt hs
          have hx := density_pos hg hiStep
          have hCge := cliqueLowerProfile_ge_center hg hK hT hiStep hl0
          have hZscale := scale_le_degreeCenter hKpos hTpos hl0 hpower
          exact lt_of_lt_of_le
            (div_pos (mul_pos (remaining_pos hiStep)
              ((by exact_mod_cast hTpos : (0 : ℝ) < scale n q r).trans_le hZscale))
              (by positivity)) hCge)
    · exact concreteJumpCap_nonneg hg z
  have hsum := varianceBudget_le_depth_mul
    (concreteVariance host q r z) (J * A) 0 d hpoint
  have hd : d ≤ host.card := by
    dsimp [d, depth]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hJA : 0 ≤ J * A := mul_nonneg
    (by simpa [J] using concreteJumpCap_nonneg (q := q) (r := r) hg z)
    (by simpa [A] using concreteAbsCap_nonneg (q := q) (r := r) hg z)
  calc
    varianceBudget (concreteVariance host q r z) 0
        (depth host.card n q r) ≤ (d : ℝ) * (J * A) := by simpa [d] using hsum
    _ ≤ (host.card : ℝ) * (J * A) := by gcongr
    _ = concreteVarianceTotalCap host q r z := by
      simp [concreteVarianceTotalCap, J, A]
      ring

lemma concrete_varianceBudget_nonneg
    {host : Finset (Finset (Fin n))}
    (hg : 0 < host.card) (hK : 2 < K q r)
    (hT : 8 ≤ scale n q r)
    (hpower : (scale n q r : ℝ) ^ K q r ≤ centerDegree n q r)
    (htarget : stopTarget host.card n q r ≤ host.card)
    (z : BarrierIndex host r) :
    0 ≤ varianceBudget (concreteVariance host q r z) 0
      (depth host.card n q r) := by
  apply varianceBudget_nonneg_of
  intro i
  unfold concreteVariance finiteVariance
  split_ifs with hi
  · have hKpos : 0 < K q r := by omega
    have hTpos : 0 < scale n q r := by omega
    have htargetPos : 0 < stopTarget host.card n q r := by
      dsimp [stopTarget]
      omega
    have hs := mul_succ_lt_of_lt_depth hKpos htargetPos hi
    have hiStep : K q r * i < host.card :=
      (Nat.mul_le_mul_left (K q r) (by omega : i ≤ i + 1)).trans_lt hs
    have hl0 := one_div_scale_le_density hg hKpos hTpos htarget hi.le
    have hx := density_pos hg hiStep
    have hCge := cliqueLowerProfile_ge_center hg hK hT hiStep hl0
    have hZscale := scale_le_degreeCenter hKpos hTpos hl0 hpower
    have hCpos : 0 < cliqueLowerProfile host.card n q r i :=
      lt_of_lt_of_le
        (div_pos (mul_pos (remaining_pos hiStep)
          ((by exact_mod_cast hTpos : (0 : ℝ) < scale n q r).trans_le hZscale))
          (by positivity)) hCge
    exact mul_nonneg
      (barrierJump_nonneg host q r
        (upperProfile host.card n q r) (lowerProfile host.card n q r)
        (cliqueUpperProfile host.card n q r)
        (cliqueLowerProfile host.card n q r)
        (faceWeight host.card (K q r))
        (faceCap n (faceSlack n q r) (faceEps n q r)
          host.card (K q r))
        (upperNat host.card n q r) z i)
      (barrierAbsBudget_nonneg host q r
        (upperProfile host.card n q r) (lowerProfile host.card n q r)
        (cliqueUpperProfile host.card n q r)
        (cliqueLowerProfile host.card n q r)
        (faceWeight host.card (K q r))
        (faceCap n (faceSlack n q r) (faceEps n q r)
          host.card (K q r))
        (upperNat host.card n q r)
        (cliqueLowerProfile host.card n q r) z i hCpos)
  · positivity

lemma concreteVarianceTotalCap_nonneg
    {host : Finset (Finset (Fin n))} (z : BarrierIndex host r) :
    0 ≤ concreteVarianceTotalCap host q r z := by
  rcases z with (eb | b) | f
  · rcases eb with ⟨e, b⟩
    cases b <;>
      simp [concreteVarianceTotalCap, concreteJumpCap, concreteAbsCap] <;>
      unfold centerDegree <;> positivity
  · cases b <;>
      simp [concreteVarianceTotalCap, concreteJumpCap, concreteAbsCap] <;>
      unfold centerDegree <;> positivity
  · simp [concreteVarianceTotalCap, concreteJumpCap, concreteAbsCap]
    positivity

lemma concrete_rate_pos
    {host : Finset (Finset (Fin n))}
    (hjumpPos : ∀ z, 0 < concreteJumpCap host q r z)
    (hjumpLt : ∀ z, concreteJumpCap host q r z < profileWindow host q r z)
    (z : BarrierIndex host r) : 0 < concreteRate host q r z := by
  apply freedmanRate_pos (hjumpPos z) (hjumpLt z)
  exact concreteVarianceTotalCap_nonneg z

lemma concrete_rate_mul_jump_le_one
    {host : Finset (Finset (Fin n))}
    (hjumpPos : ∀ z, 0 < concreteJumpCap host q r z)
    (hjumpLt : ∀ z, concreteJumpCap host q r z < profileWindow host q r z)
    (z : BarrierIndex host r) :
    concreteRate host q r z * concreteJumpCap host q r z ≤ 1 := by
  apply freedmanRate_mul_jump_le_one (hjumpPos z) (hjumpLt z)
  exact concreteVarianceTotalCap_nonneg z

/-- A common lower bound on the three Freedman scores and a polynomial
cardinality estimate imply the single finite union bound consumed by the
nibble instantiation. -/
lemma concrete_exponential_sum_lt_one_of_score
    {host : Finset (Finset (Fin n))}
    (hvarianceNonneg : ∀ z,
      0 ≤ varianceBudget (concreteVariance host q r z) 0
        (depth host.card n q r))
    (hvariance : ∀ z,
      varianceBudget (concreteVariance host q r z) 0
          (depth host.card n q r) ≤ concreteVarianceTotalCap host q r z)
    (hjumpPos : ∀ z, 0 < concreteJumpCap host q r z)
    (hjumpLt : ∀ z, concreteJumpCap host q r z < profileWindow host q r z)
    (score : ℝ)
    (hscore : ∀ z,
      score ≤
        (profileWindow host q r z - concreteJumpCap host q r z) ^ 2 /
          (4 * (concreteVarianceTotalCap host q r z +
            (profileWindow host q r z - concreteJumpCap host q r z) *
              concreteJumpCap host q r z)))
    (hcard : (Fintype.card
        (BarrierIndex host r × Fin (depth host.card n q r + 1)) : ℝ) *
          Real.exp (-score) < 1) :
    (∑ z : BarrierIndex host r × Fin (depth host.card n q r + 1),
      Real.exp (-concreteRate host q r z.1 *
          (profileWindow host q r z.1 - concreteJumpCap host q r z.1)) *
        Real.exp ((concreteRate host q r z.1) ^ 2 *
          varianceBudget (concreteVariance host q r z.1) 0
            (depth host.card n q r))) < 1 := by
  have hterm : ∀ z : BarrierIndex host r,
      Real.exp (-concreteRate host q r z *
          (profileWindow host q r z - concreteJumpCap host q r z)) *
        Real.exp ((concreteRate host q r z) ^ 2 *
          varianceBudget (concreteVariance host q r z) 0
            (depth host.card n q r)) ≤ Real.exp (-score) := by
    intro z
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hexp := freedman_exponent_le
      (hjumpPos z) (hjumpLt z)
      (hvarianceNonneg z)
      (hvariance z)
    exact hexp.trans (by simpa [neg_div] using neg_le_neg (hscore z))
  calc
    (∑ z : BarrierIndex host r × Fin (depth host.card n q r + 1),
      Real.exp (-concreteRate host q r z.1 *
          (profileWindow host q r z.1 - concreteJumpCap host q r z.1)) *
        Real.exp ((concreteRate host q r z.1) ^ 2 *
          varianceBudget (concreteVariance host q r z.1) 0
            (depth host.card n q r))) ≤
        ∑ _z : BarrierIndex host r × Fin (depth host.card n q r + 1),
          Real.exp (-score) := by
      apply Finset.sum_le_sum
      intro z hz
      exact hterm z.1
    _ = (Fintype.card
        (BarrierIndex host r × Fin (depth host.card n q r + 1)) : ℝ) *
          Real.exp (-score) := by simp
    _ < 1 := hcard

end

end Erdos722.NibbleBounds
