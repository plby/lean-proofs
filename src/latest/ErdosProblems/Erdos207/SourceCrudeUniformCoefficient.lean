/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCrudeTailExpressions

/-! # One explicit coefficient bounds all four source-order sums -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceCrudeBaseCoefficient (ell q : ℕ) (w Z : ℝ≥0) : ℝ≥0 :=
  (((q + 1) ^ ell : ℕ) : ℝ≥0) * (2 : ℝ≥0) ^ q * Z * w ^ q

def sourceCrudeDoubleCoefficient (ell q : ℕ) (w Z : ℝ≥0) : ℝ≥0 :=
  2 * sourceCommonGoodCoefficient ell q w Z Z + sourceGainReverseGoodCoefficient ell q w Z Z +
    sourceCrudeBaseCoefficient ell q w Z

def sourceCrudeUniformCoefficient (ell q h : ℕ) (w Z : ℝ≥0) : ℝ≥0 :=
  1 + h * sourceCrudeBaseCoefficient ell q w Z +
    (h : ℝ≥0) ^ 2 * sourceCrudeDoubleCoefficient ell q w Z

theorem sourceCrude_monomial_le (ell q a b d : ℕ) (w z Z : ℝ≥0)
    (ha : a ≤ q + 1) (hb : b ≤ q) (hd : d ≤ q) (hw : 1 ≤ w) (hz : z ≤ Z) :
    (((a ^ ell : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ b * z)) * w ^ d ≤
      sourceCrudeBaseCoefficient ell q w Z := by
  have ha' : (((a ^ ell : ℕ) : ℝ≥0)) ≤ ((q + 1) ^ ell : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_left ha ell
  have hb' : (2 : ℝ≥0) ^ b ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hb
  have hd' : w ^ d ≤ w ^ q := pow_le_pow_right₀ hw hd
  calc
    _ ≤ (((q + 1) ^ ell : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ q * Z) * w ^ q :=
      mul_le_mul' (mul_le_mul' ha' (mul_le_mul' hb' hz)) hd'
    _ = _ := by unfold sourceCrudeBaseCoefficient; ring

theorem sourceNibble_coefficient_le_crude_base (ell q r : ℕ) (w z Z : ℝ≥0)
    (hr : r ≤ q) (hw : 1 ≤ w) (hz : z ≤ Z) :
    sourceNibbleMomentCoefficient ell r w * z ≤ sourceCrudeBaseCoefficient ell q w Z := by
  have h := sourceCrude_monomial_le ell q (r + 1) (r - 2) r w z Z (by omega) (by omega) hr hw hz
  convert h using 1
  unfold sourceNibbleMomentCoefficient
  ring

theorem sourceCommon_coefficient_le_crude_double (ell q r : ℕ) (w z z' Z : ℝ≥0)
    (hr : r ≤ q) (hw : 1 ≤ w) (hz : z ≤ Z) (hz' : z' ≤ Z) :
    sourceCommonMomentCoefficient ell q r w z z' ≤ sourceCrudeDoubleCoefficient ell q w Z := by
  have hgood : sourceCommonGoodCoefficient ell q w z z' ≤ sourceCommonGoodCoefficient ell q w Z Z := by
    unfold sourceCommonGoodCoefficient sourceCommonClassCoefficient
    gcongr
  have hswap : sourceCommonGoodCoefficient ell q w z' z ≤ sourceCommonGoodCoefficient ell q w Z Z := by
    unfold sourceCommonGoodCoefficient sourceCommonClassCoefficient
    gcongr
  have hex := sourceCrude_monomial_le ell q (r - 3) (r - 3) (r - 4) w z Z
    (by omega) (by omega) (by omega) hw hz
  have hsum := add_le_add (add_le_add hgood hswap) hex
  change sourceCommonMomentCoefficient ell q r w z z' ≤ _ at hsum
  exact hsum.trans (by
    unfold sourceCrudeDoubleCoefficient
    rw [two_mul]
    exact add_le_add (le_add_of_nonneg_right zero_le) le_rfl)

theorem sourceGain_coefficient_le_crude_double (ell q r : ℕ) (w z z' Z : ℝ≥0)
    (hr : r ≤ q) (hw : 1 ≤ w) (hz : z ≤ Z) (hz' : z' ≤ Z) :
    sourceGainMomentCoefficient ell q r w z z' ≤ sourceCrudeDoubleCoefficient ell q w Z := by
  have hgood : sourceCommonGoodCoefficient ell q w z z' ≤ sourceCommonGoodCoefficient ell q w Z Z := by
    unfold sourceCommonGoodCoefficient sourceCommonClassCoefficient
    gcongr
  have hreverse : sourceGainReverseGoodCoefficient ell q w z z' ≤ sourceGainReverseGoodCoefficient ell q w Z Z := by
    unfold sourceGainReverseGoodCoefficient sourceCommonClassCoefficient
    gcongr
  have hex : (((r + 1) ^ ell : ℕ) : ℝ≥0) * (2 : ℝ≥0) ^ r * z * w ^ r ≤
      sourceCrudeBaseCoefficient ell q w Z := by
    convert sourceCrude_monomial_le ell q (r + 1) r r w z Z (by omega) hr hr hw hz using 1 <;> ring
  have hsum := add_le_add (add_le_add hgood hreverse) hex
  change sourceGainMomentCoefficient ell q r w z z' ≤ _ at hsum
  exact hsum.trans (by
    unfold sourceCrudeDoubleCoefficient
    rw [two_mul]
    exact add_le_add (add_le_add (le_add_of_nonneg_right zero_le) le_rfl) le_rfl)

theorem sourceCrudeUniformCoefficient_one_le (ell q h : ℕ) (w Z : ℝ≥0) :
    1 ≤ sourceCrudeUniformCoefficient ell q h w Z := by
  unfold sourceCrudeUniformCoefficient
  exact (le_add_of_nonneg_right (show 0 ≤ h * sourceCrudeBaseCoefficient ell q w Z from zero_le)).trans
    (le_add_of_nonneg_right zero_le)

theorem sourceCrudeUniformCoefficient_linear (ell q h : ℕ) (w Z : ℝ≥0) :
    h * sourceCrudeBaseCoefficient ell q w Z ≤ sourceCrudeUniformCoefficient ell q h w Z := by
  unfold sourceCrudeUniformCoefficient
  exact (le_add_of_nonneg_left (show (0 : ℝ≥0) ≤ 1 from zero_le)).trans
    (le_add_of_nonneg_right zero_le)

theorem sourceCrudeUniformCoefficient_quadratic (ell q h : ℕ) (w Z : ℝ≥0) :
    (h : ℝ≥0) ^ 2 * sourceCrudeDoubleCoefficient ell q w Z ≤
      sourceCrudeUniformCoefficient ell q h w Z := by
  unfold sourceCrudeUniformCoefficient
  exact le_add_of_nonneg_left zero_le

theorem sourceCrude_root_sum_le_uniform
    {I : Type*} [Fintype I] (order : I → ℕ) (z : I → ℝ≥0)
    (ell q n j c : ℕ) (w Z : ℝ≥0) (horder : ∀ i, order i ≤ q)
    (hz : ∀ i, z i ≤ Z) (hc : c ≤ j) (hw : 1 ≤ w) :
    sourceCrudeRootCoefficient order z ell n j c w ≤
      sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z * (n : ℝ≥0) ^ (j - c - 5) := by
  classical
  have hterm : ∀ i : {i : I // j ≤ order i},
      ((((order i.1 - j + c + 1) ^ ell : ℕ) : ℝ≥0) *
        ((2 : ℝ≥0) ^ (order i.1 - 2) * z i.1) * w ^ (order i.1 - j + c)) ≤
          sourceCrudeBaseCoefficient ell q w Z := by
    intro i
    have hi := horder i.1
    exact sourceCrude_monomial_le ell q _ _ _ w (z i.1) Z (by omega) (by omega) (by omega) hw (hz i.1)
  have hsum := sum_le_sum (s := (univ : Finset {i : I // j ≤ order i}))
    (fun i _ ↦ mul_le_mul_of_nonneg_right (hterm i) (show 0 ≤ (n : ℝ≥0) ^ (j - c - 5) from zero_le))
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
  change sourceCrudeRootCoefficient order z ell n j c w ≤ _ at hsum
  have hcard : (Fintype.card {i : I // j ≤ order i} : ℝ≥0) ≤ Fintype.card I := by
    exact_mod_cast Fintype.card_subtype_le (fun i : I ↦ j ≤ order i)
  calc
    _ ≤ (Fintype.card I : ℝ≥0) * (sourceCrudeBaseCoefficient ell q w Z * (n : ℝ≥0) ^ (j - c - 5)) :=
      hsum.trans (mul_le_mul_of_nonneg_right hcard zero_le)
    _ = ((Fintype.card I : ℝ≥0) * sourceCrudeBaseCoefficient ell q w Z) * (n : ℝ≥0) ^ (j - c - 5) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (sourceCrudeUniformCoefficient_linear ell q (Fintype.card I) w Z) zero_le

theorem sourceCrude_pair_sum_le_uniform
    {I : Type*} [Fintype I] (order : I → ℕ) (z : I → ℝ≥0)
    (ell q : ℕ) (w Z : ℝ≥0) (horder : ∀ i, order i ≤ q) (hz : ∀ i, z i ≤ Z) (hw : 1 ≤ w) :
    (∑ i, sourceNibbleMomentCoefficient ell (order i) w * z i) ≤
      sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z := by
  have hsum := sum_le_sum (s := (univ : Finset I)) (fun i _ ↦
    sourceNibble_coefficient_le_crude_base ell q (order i) w (z i) Z (horder i) hw (hz i))
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
  exact hsum.trans (sourceCrudeUniformCoefficient_linear ell q (Fintype.card I) w Z)

theorem sourceCrude_common_sum_le_uniform
    {I : Type*} [Fintype I] (order : I → ℕ) (z : I → ℝ≥0)
    (ell q : ℕ) (w Z : ℝ≥0) (horder : ∀ i, order i ≤ q) (hz : ∀ i, z i ≤ Z) (hw : 1 ≤ w) :
    (∑ i, ∑ i', sourceCommonMomentCoefficient ell q (order i) w (z i) (z i')) ≤
      sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z := by
  have hsum := sum_le_sum (s := (univ : Finset I)) (fun i _ ↦
    sum_le_sum (s := (univ : Finset I)) (fun i' _ ↦
      sourceCommon_coefficient_le_crude_double ell q (order i) w (z i) (z i') Z (horder i) hw (hz i) (hz i')))
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc, ← pow_two] at hsum
  exact hsum.trans (sourceCrudeUniformCoefficient_quadratic ell q (Fintype.card I) w Z)

theorem sourceCrude_gain_sum_le_uniform
    {I : Type*} [Fintype I] (order : I → ℕ) (z : I → ℝ≥0)
    (ell q n j c : ℕ) (w Z : ℝ≥0) (horder : ∀ i, order i ≤ q) (hz : ∀ i, z i ≤ Z) (hw : 1 ≤ w) :
    (∑ i, ∑ i', sourceGainMomentCoefficient ell q (order i) w (z i) (z i') *
      (n : ℝ≥0) ^ (j - c - 4)) ≤
        sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z * (n : ℝ≥0) ^ (j - c - 4) := by
  have hsum := sum_le_sum (s := (univ : Finset I)) (fun i _ ↦
    sum_le_sum (s := (univ : Finset I)) (fun i' _ ↦
      mul_le_mul_of_nonneg_right
        (sourceGain_coefficient_le_crude_double ell q (order i) w (z i) (z i') Z (horder i) hw (hz i) (hz i'))
        (show 0 ≤ (n : ℝ≥0) ^ (j - c - 4) from zero_le)))
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc, ← pow_two] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_right
    (sourceCrudeUniformCoefficient_quadratic ell q (Fintype.card I) w Z) zero_le)

end

end Erdos207
