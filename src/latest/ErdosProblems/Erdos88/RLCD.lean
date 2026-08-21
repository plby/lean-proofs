/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Regularized least common denominators

This file formalizes the Euclidean distance to the integer lattice, the
least common denominator `D_L`, and the maximum-based regularized LCD used
in Kwan--Sah--Sauermann--Sawhney's solution of Erdős Problem 88.
-/

open scoped BigOperators

namespace Erdos88
namespace RLCD

/-- The positive part of the natural logarithm. -/
noncomputable def logPlus (x : ℝ) : ℝ := max 0 (Real.log x)

lemma logPlus_nonneg (x : ℝ) : 0 ≤ logPlus x := by
  exact le_max_left _ _

lemma logPlus_eq_zero_of_pos_of_le_one {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) :
    logPlus x = 0 := by
  rw [logPlus, max_eq_left]
  exact Real.log_nonpos hx0.le hx

lemma logPlus_eq_log {x : ℝ} (hx : 1 ≤ x) : logPlus x = Real.log x := by
  rw [logPlus, max_eq_right]
  exact Real.log_nonneg hx

/-- Distance of a real number to the nearest integer. -/
noncomputable def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma distToInt_nonneg (x : ℝ) : 0 ≤ distToInt x := abs_nonneg _

lemma distToInt_le_half (x : ℝ) : distToInt x ≤ 1 / 2 := by
  exact abs_sub_round x

/-- The chosen nearest integer is at least as close as every integer. -/
lemma distToInt_le (x : ℝ) (z : ℤ) : distToInt x ≤ |x - (z : ℝ)| := by
  exact round_le x z

@[simp] lemma distToInt_zero : distToInt 0 = 0 := by
  simp [distToInt]

/-- Euclidean norm, written explicitly to make coordinate restrictions easy. -/
noncomputable def euclidNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

lemma euclidNorm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ euclidNorm x := Real.sqrt_nonneg _

/-- Euclidean distance from a finite real vector to the integer lattice. -/
noncomputable def latticeDist {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, distToInt (x i) ^ 2)

lemma latticeDist_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ latticeDist x := Real.sqrt_nonneg _

@[simp] lemma latticeDist_zero {ι : Type*} [Fintype ι] :
    latticeDist (fun _ : ι ↦ 0) = 0 := by
  simp [latticeDist]

lemma round_eq_zero_of_abs_lt_half {x : ℝ} (hx : |x| < 1 / 2) : round x = 0 := by
  rw [round_eq_zero_iff]
  constructor <;> linarith [abs_lt.mp hx |>.1, abs_lt.mp hx |>.2]

lemma distToInt_eq_abs_of_abs_lt_half {x : ℝ} (hx : |x| < 1 / 2) :
    distToInt x = |x| := by
  simp [distToInt, round_eq_zero_of_abs_lt_half hx]

/-- In the central half-open unit cube the nearest lattice point is zero. -/
lemma latticeDist_eq_euclidNorm_of_abs_lt_half {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i, |x i| < 1 / 2) :
    latticeDist x = euclidNorm x := by
  simp only [latticeDist, euclidNorm, distToInt_eq_abs_of_abs_lt_half (hx _), sq_abs]

/-- A dimension-only bound for distance to the integer lattice. -/
lemma latticeDist_le_sqrt_card {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    latticeDist x ≤ Real.sqrt (Fintype.card ι) := by
  apply Real.sqrt_le_sqrt
  simpa only [latticeDist, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_ofNat, one_pow, mul_one] using
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
      (sq_le_sq₀ (distToInt_nonneg (x i)) (by norm_num : (0 : ℝ) ≤ 1)).2
        ((distToInt_le_half (x i)).trans (by norm_num)))

/-- A vector in the integer lattice, viewed in real Euclidean space. -/
def integerVectorCast {ι : Type*} (z : ι → ℤ) : ι → ℝ := fun i ↦ z i

/-- `latticeDist` is no larger than the Euclidean distance to any integer
vector. -/
lemma latticeDist_le_integerVector {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (z : ι → ℤ) :
    latticeDist x ≤ euclidNorm (fun i ↦ x i - integerVectorCast z i) := by
  apply Real.sqrt_le_sqrt
  simpa only [latticeDist, euclidNorm, integerVectorCast, sq_abs] using
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
      (sq_le_sq₀ (distToInt_nonneg (x i)) (abs_nonneg (x i - (z i : ℝ)))).2
        (distToInt_le (x i) (z i)))

/-- Coordinatewise rounding realizes the distance to the integer lattice. -/
lemma exists_integerVector_eq_latticeDist {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ∃ z : ι → ℤ,
      latticeDist x = euclidNorm (fun i ↦ x i - integerVectorCast z i) := by
  refine ⟨fun i ↦ round (x i), ?_⟩
  simp [latticeDist, euclidNorm, integerVectorCast, distToInt, sq_abs]

/-- If all coordinates are nonnegative, coordinatewise rounding realizes
the lattice distance using a vector of natural numbers. -/
lemma exists_natVector_eq_latticeDist {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ z : ι → ℕ,
      latticeDist x = euclidNorm (fun i ↦ x i - (z i : ℝ)) := by
  let z : ι → ℕ := fun i ↦ (round (x i)).toNat
  have hround : ∀ i, (z i : ℤ) = round (x i) := by
    intro i
    apply Int.toNat_of_nonneg
    rw [round_eq]
    exact Int.floor_nonneg.mpr (by linarith [hx i])
  refine ⟨z, ?_⟩
  simp only [latticeDist, euclidNorm, distToInt]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show (z i : ℝ) = (round (x i) : ℝ) by exact_mod_cast hround i]
  exact sq_abs (x i - (round (x i) : ℝ))

lemma sum_sq_eq_one_of_euclidNorm_eq_one {ι : Type*} [Fintype ι]
    {v : ι → ℝ} (hv : euclidNorm v = 1) :
    ∑ i, (v i) ^ 2 = 1 := by
  have hs : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  rw [euclidNorm] at hv
  nlinarith [Real.sq_sqrt hs]

lemma euclidNorm_ne_zero_of_eq_one {ι : Type*} [Fintype ι]
    {v : ι → ℝ} (hv : euclidNorm v = 1) : euclidNorm v ≠ 0 := by
  simp [hv]

lemma exists_abs_pos_of_euclidNorm_eq_one {ι : Type*} [Fintype ι]
    {v : ι → ℝ} (hv : euclidNorm v = 1) : ∃ i, 0 < |v i| := by
  by_contra h
  push Not at h
  have hz : v = 0 := by
    funext i
    simpa [abs_nonpos_iff] using h i
  simp [hz, euclidNorm] at hv

/-- The elementary analytic inequality used in the LCD lower bound. -/
lemma sqrt_logPlus_le_half (x : ℝ) (hx : 0 < x) :
    Real.sqrt (logPlus x) ≤ x / 2 := by
  by_cases hx1 : x ≤ 1
  · rw [logPlus_eq_zero_of_pos_of_le_one hx hx1]
    simpa using div_nonneg hx.le (by norm_num : (0 : ℝ) ≤ 2)
  · have h1x : 1 < x := lt_of_not_ge hx1
    rw [logPlus_eq_log h1x.le, Real.sqrt_le_left (by positivity)]
    have hlog := Real.log_le_sub_one_of_pos hx
    nlinarith [sq_nonneg (x - 2)]

/-- The admissible scales in the definition of `D_L`. -/
def lcdScales {ι : Type*} [Fintype ι] (L : ℝ) (v : ι → ℝ) : Set ℝ :=
  {θ | 0 < θ ∧ latticeDist (fun i ↦ θ * v i) < L * Real.sqrt (logPlus (θ / L))}

/-- The least common denominator `D_L(v)`. -/
noncomputable def LCD {ι : Type*} [Fintype ι] (L : ℝ) (v : ι → ℝ) : ℝ :=
  sInf (lcdScales L v)

lemma lcdScales_bddBelow {ι : Type*} [Fintype ι] (L : ℝ) (v : ι → ℝ) :
    BddBelow (lcdScales L v) := by
  refine ⟨0, ?_⟩
  intro θ hθ
  exact hθ.1.le

lemma lcdScales_nonempty {ι : Type*} [Fintype ι] {L : ℝ} (hL : 1 ≤ L)
    (v : ι → ℝ) : (lcdScales L v).Nonempty := by
  let q : ℝ := Fintype.card ι + 1
  let θ : ℝ := L * Real.exp q
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hq0 : 0 ≤ q := by positivity
  have hθ0 : 0 < θ := mul_pos hL0 (Real.exp_pos q)
  refine ⟨θ, hθ0, ?_⟩
  have hratio : θ / L = Real.exp q := by
    simp [θ, hL0.ne']
  have hlog : logPlus (θ / L) = q := by
    rw [hratio, logPlus_eq_log (Real.one_le_exp hq0), Real.log_exp]
  rw [hlog]
  refine (latticeDist_le_sqrt_card (fun i ↦ θ * v i)).trans_lt ?_
  have hsqrt_lt : Real.sqrt (Fintype.card ι) < Real.sqrt q := by
    apply Real.sqrt_lt_sqrt
    · positivity
    · simp [q]
  have hsqrt_nonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  calc
    Real.sqrt (Fintype.card ι) < Real.sqrt q := hsqrt_lt
    _ ≤ L * Real.sqrt q := by nlinarith

lemma LCD_le_of_mem {ι : Type*} [Fintype ι] {L : ℝ} {v : ι → ℝ} {θ : ℝ}
    (hθ : θ ∈ lcdScales L v) : LCD L v ≤ θ := by
  exact csInf_le (lcdScales_bddBelow L v) hθ

lemma LCD_nonneg {ι : Type*} [Fintype ι] {L : ℝ} (hL : 1 ≤ L) (v : ι → ℝ) :
    0 ≤ LCD L v := by
  apply le_csInf (lcdScales_nonempty hL v)
  intro θ hθ
  exact hθ.1.le

lemma latticeDist_scale_eq {ι : Type*} [Fintype ι] {v : ι → ℝ} {θ : ℝ}
    (hθ : 0 < θ) (hv : euclidNorm v = 1)
    (hsmall : ∀ i, |θ * v i| < 1 / 2) :
    latticeDist (fun i ↦ θ * v i) = θ := by
  rw [latticeDist_eq_euclidNorm_of_abs_lt_half _ hsmall, euclidNorm]
  have hsum := sum_sq_eq_one_of_euclidNorm_eq_one hv
  simp only [mul_pow, ← Finset.mul_sum, hsum, mul_one, Real.sqrt_sq hθ.le]

lemma lcdScale_ge_inv_two_norm {ι : Type*} [Fintype ι] {L : ℝ} (hL : 1 ≤ L)
    {v : ι → ℝ} (hv : euclidNorm v = 1) {θ : ℝ} (hθ : θ ∈ lcdScales L v) :
    (2 * ‖v‖)⁻¹ ≤ θ := by
  have hv0 : v ≠ 0 := by
    intro hvz
    subst v
    simp [euclidNorm] at hv
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  by_contra hbad
  have hlt : θ < (2 * ‖v‖)⁻¹ := lt_of_not_ge hbad
  have hinv : (2 * ‖v‖)⁻¹ * ‖v‖ = 1 / 2 := by
    field_simp
  have hθnorm : θ * ‖v‖ < 1 / 2 := by
    calc
      θ * ‖v‖ < (2 * ‖v‖)⁻¹ * ‖v‖ := mul_lt_mul_of_pos_right hlt hnorm
      _ = 1 / 2 := hinv
  have hsmall : ∀ i, |θ * v i| < 1 / 2 := by
    intro i
    rw [abs_mul, abs_of_pos hθ.1]
    have hvi : |v i| ≤ ‖v‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
    exact (mul_le_mul_of_nonneg_left hvi hθ.1.le).trans_lt hθnorm
  have hdist : latticeDist (fun i ↦ θ * v i) = θ :=
    latticeDist_scale_eq hθ.1 hv hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hsqrt := sqrt_logPlus_le_half (θ / L) (div_pos hθ.1 hL0)
  have hrhs : L * Real.sqrt (logPlus (θ / L)) ≤ θ / 2 := by
    calc
      L * Real.sqrt (logPlus (θ / L)) ≤ L * ((θ / L) / 2) :=
        mul_le_mul_of_nonneg_left hsqrt hL0.le
      _ = θ / 2 := by field_simp
  have hdistlt := hθ.2
  rw [hdist] at hdistlt
  nlinarith [hθ.1, hdistlt, hrhs]

/-- KSSS Lemma 4.10: a unit vector has no admissible LCD scale below
`(2 * ‖v‖∞)⁻¹`. -/
theorem LCD_ge_inv_two_norm {ι : Type*} [Fintype ι] {L : ℝ} (hL : 1 ≤ L)
    {v : ι → ℝ} (hv : euclidNorm v = 1) :
    (2 * ‖v‖)⁻¹ ≤ LCD L v := by
  apply le_csInf (lcdScales_nonempty hL v)
  intro θ hθ
  exact lcdScale_ge_inv_two_norm hL hv hθ

/-- An LCD upper bound produces an actual nearby integer vector at a scale
less than twice that bound. This is the infimum-to-witness step used in
KSSS Lemma 4.12. -/
theorem exists_integer_approximant_of_LCD_le {ι : Type*} [Fintype ι]
    {L B : ℝ} (hL : 1 ≤ L) (hB : 0 < B) {v : ι → ℝ}
    (hLCD : LCD L v ≤ B) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2 * B ∧
      ∃ w : ι → ℤ,
        euclidNorm (fun i ↦ θ * v i - integerVectorCast w i) <
          L * Real.sqrt (logPlus (θ / L)) := by
  have hInf : LCD L v < 2 * B := lt_of_le_of_lt hLCD (by linarith)
  obtain ⟨θ, hθscale, hθlt⟩ :=
    exists_lt_of_csInf_lt (lcdScales_nonempty hL v) hInf
  obtain ⟨w, hw⟩ := exists_integerVector_eq_latticeDist (fun i ↦ θ * v i)
  refine ⟨θ, hθscale.1, hθlt, w, ?_⟩
  rw [← hw]
  exact hθscale.2

/-- Nonnegative version of `exists_integer_approximant_of_LCD_le`.  This is
the form used in Lemma 4.12, where the coefficient vector is nonnegative. -/
theorem exists_nat_approximant_of_LCD_le {ι : Type*} [Fintype ι]
    {L B : ℝ} (hL : 1 ≤ L) (hB : 0 < B) {v : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hLCD : LCD L v ≤ B) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2 * B ∧
      ∃ w : ι → ℕ,
        euclidNorm (fun i ↦ θ * v i - (w i : ℝ)) <
          L * Real.sqrt (logPlus (θ / L)) := by
  have hInf : LCD L v < 2 * B := lt_of_le_of_lt hLCD (by linarith)
  obtain ⟨θ, hθscale, hθlt⟩ :=
    exists_lt_of_csInf_lt (lcdScales_nonempty hL v) hInf
  obtain ⟨w, hw⟩ := exists_natVector_eq_latticeDist (fun i ↦ θ * v i)
    (fun i ↦ mul_nonneg hθscale.1.le (hv i))
  refine ⟨θ, hθscale.1, hθlt, w, ?_⟩
  rw [← hw]
  exact hθscale.2

/-- The preceding witness together with the fact that its scale really is
an admissible LCD scale.  Retaining this membership makes Lemma 4.10
available in the radius estimate of Lemma 4.12. -/
theorem exists_nat_lcdScale_of_LCD_le {ι : Type*} [Fintype ι]
    {L B : ℝ} (hL : 1 ≤ L) (hB : 0 < B) {v : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hLCD : LCD L v ≤ B) :
    ∃ θ : ℝ, θ ∈ lcdScales L v ∧ θ < 2 * B ∧
      ∃ w : ι → ℕ,
        euclidNorm (fun i ↦ θ * v i - (w i : ℝ)) <
          L * Real.sqrt (logPlus (θ / L)) := by
  have hInf : LCD L v < 2 * B := lt_of_le_of_lt hLCD (by linarith)
  obtain ⟨θ, hθscale, hθlt⟩ :=
    exists_lt_of_csInf_lt (lcdScales_nonempty hL v) hInf
  obtain ⟨w, hw⟩ := exists_natVector_eq_latticeDist (fun i ↦ θ * v i)
    (fun i ↦ mul_nonneg hθscale.1.le (hv i))
  refine ⟨θ, hθscale, hθlt, w, ?_⟩
  rw [← hw]
  exact hθscale.2

lemma sum_sq_le_sq_of_euclidNorm_le {ι : Type*} [Fintype ι]
    (x : ι → ℝ) {E : ℝ} (hE : euclidNorm x ≤ E) (hE0 : 0 ≤ E) :
    ∑ i, (x i) ^ 2 ≤ E ^ 2 := by
  have hs : 0 ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  rw [← Real.sq_sqrt hs]
  exact (sq_le_sq₀ (euclidNorm_nonneg x) hE0).2 (by simpa [euclidNorm] using hE)

/-- Finite counting form of the elementary second-moment bound: the
coordinates larger than `T` consume at least `T^2` each. -/
lemma card_large_coordinates_mul_sq_le_sum_sq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ((s.filter fun i ↦ T < |x i|).card : ℝ) * T ^ 2 ≤
      ∑ i ∈ s, (x i) ^ 2 := by
  let bad := s.filter fun i ↦ T < |x i|
  calc
    (bad.card : ℝ) * T ^ 2 = ∑ _i ∈ bad, T ^ 2 := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ bad, (x i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : T < |x i| := (Finset.mem_filter.mp hi).2
      simpa [sq_abs] using
        (sq_le_sq₀ hT (abs_nonneg (x i))).2 hi'.le
    _ ≤ ∑ i ∈ s, (x i) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i _ _
      exact sq_nonneg (x i)

/-- A convenient integral consequence of the second-moment estimate. -/
lemma card_large_coordinates_le {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (T E : ℝ) (C : ℕ)
    (hT : 0 < T) (hE : euclidNorm x ≤ E) (hE0 : 0 ≤ E)
    (hbudget : E ^ 2 < (C + 1 : ℕ) * T ^ 2) :
    (Finset.univ.filter fun i ↦ T < |x i|).card ≤ C := by
  classical
  by_contra hC
  have hsucc : C + 1 ≤ (Finset.univ.filter fun i ↦ T < |x i|).card := by omega
  have hcast : ((C + 1 : ℕ) : ℝ) ≤
      ((Finset.univ.filter fun i ↦ T < |x i|).card : ℝ) := by exact_mod_cast hsucc
  have hmarkov :
      ((Finset.univ.filter fun i ↦ T < |x i|).card : ℝ) * T ^ 2 ≤
        ∑ i, (x i) ^ 2 := by
    simpa using card_large_coordinates_mul_sq_le_sum_sq
      (s := Finset.univ) (x := x) T hT.le
  have hsum := sum_sq_le_sq_of_euclidNorm_le
    x hE hE0
  have hmul := mul_le_mul_of_nonneg_right hcast (sq_nonneg T)
  linarith

lemma card_large_coordinates_le_of_sum_sq_lt {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (T : ℝ) (C : ℕ) (hT : 0 < T)
    (hsum : (∑ i, (x i) ^ 2) < (C + 1 : ℕ) * T ^ 2) :
    (Finset.univ.filter fun i ↦ T < |x i|).card ≤ C := by
  classical
  by_contra hC
  have hsucc : C + 1 ≤ (Finset.univ.filter fun i ↦ T < |x i|).card := by omega
  have hcast : ((C + 1 : ℕ) : ℝ) ≤
      ((Finset.univ.filter fun i ↦ T < |x i|).card : ℝ) := by exact_mod_cast hsucc
  have hmarkov :
      ((Finset.univ.filter fun i ↦ T < |x i|).card : ℝ) * T ^ 2 ≤
        ∑ i, (x i) ^ 2 := by
    simpa using card_large_coordinates_mul_sq_le_sum_sq
      (s := Finset.univ) (x := x) T hT.le
  have hmul := mul_le_mul_of_nonneg_right hcast (sq_nonneg T)
  linarith

/-- Squaring the triangle inequality coordinatewise gives a deliberately
coarse but useful bound on the integer approximant. -/
lemma sum_sq_nat_approximant_le {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (w : ι → ℕ) (θ E : ℝ)
    (hv : euclidNorm v = 1)
    (happrox : euclidNorm (fun i ↦ θ * v i - (w i : ℝ)) ≤ E)
    (hE0 : 0 ≤ E) :
    ∑ i, ((w i : ℝ) ^ 2) ≤ 2 * θ ^ 2 + 2 * E ^ 2 := by
  let e : ι → ℝ := fun i ↦ θ * v i - (w i : ℝ)
  have hpoint : ∀ i, ((w i : ℝ) ^ 2) ≤
      2 * (θ * v i) ^ 2 + 2 * (e i) ^ 2 := by
    intro i
    have hid : (w i : ℝ) = θ * v i - e i := by simp [e]
    rw [hid]
    nlinarith [sq_nonneg (θ * v i + e i)]
  have hvsum : ∑ i, (θ * v i) ^ 2 = θ ^ 2 := by
    have hsum := sum_sq_eq_one_of_euclidNorm_eq_one hv
    simp only [mul_pow, ← Finset.mul_sum, hsum, mul_one]
  have hesum : ∑ i, (e i) ^ 2 ≤ E ^ 2 :=
    sum_sq_le_sq_of_euclidNorm_le e (by simpa [e] using happrox) hE0
  calc
    ∑ i, ((w i : ℝ) ^ 2) ≤ ∑ i, (2 * (θ * v i) ^ 2 + 2 * (e i) ^ 2) :=
      Finset.sum_le_sum fun i _ ↦ hpoint i
    _ = 2 * (∑ i, (θ * v i) ^ 2) + 2 * (∑ i, (e i) ^ 2) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * θ ^ 2 + 2 * E ^ 2 := by rw [hvsum]; linarith

/-- Restriction of a vector to a finite coordinate set. -/
def restrict {ι : Type*} (d : ι → ℝ) (I : Finset ι) : I → ℝ := fun i ↦ d i

/-- Normalized restriction of a vector to a finite coordinate set. -/
noncomputable def normalizedRestrict {ι : Type*} (d : ι → ℝ) (I : Finset ι) : I → ℝ :=
  fun i ↦ d i / euclidNorm (restrict d I)

lemma euclidNorm_eq_zero_iff {ι : Type*} [Fintype ι] {x : ι → ℝ} :
    euclidNorm x = 0 ↔ x = 0 := by
  have hs : 0 ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  rw [euclidNorm, Real.sqrt_eq_zero hs]
  constructor
  · intro hsum
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) ↦ sq_nonneg (x j))).mp hsum i (Finset.mem_univ i)
    simpa using (sq_eq_zero_iff.mp hi)
  · rintro rfl
    simp

lemma euclidNorm_normalizedRestrict {ι : Type*} (d : ι → ℝ) (I : Finset ι)
    (hI : euclidNorm (restrict d I) ≠ 0) :
    euclidNorm (normalizedRestrict d I) = 1 := by
  let a := euclidNorm (restrict d I)
  have ha : a ≠ 0 := hI
  have hs : 0 ≤ ∑ i : I, (restrict d I i) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have ha2 : a ^ 2 = ∑ i : I, (restrict d I i) ^ 2 := by
    simpa [a, euclidNorm] using Real.sq_sqrt hs
  have hsum : ∑ i : I, (normalizedRestrict d I i) ^ 2 = 1 := by
    calc
      ∑ i : I, (normalizedRestrict d I i) ^ 2 =
          (∑ i : I, (restrict d I i) ^ 2) / a ^ 2 := by
            simp only [normalizedRestrict, restrict, div_pow, Finset.sum_div, a]
      _ = a ^ 2 / a ^ 2 := by rw [ha2]
      _ = 1 := div_self (pow_ne_zero 2 ha)
  rw [euclidNorm, Real.sqrt_eq_one]
  change (∑ i : I, (normalizedRestrict d I i) ^ 2) = 1
  exact hsum

/-- Coordinate sets of a prescribed cardinality. -/
def coordinateSets (n k : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powersetCard k

/-- Coordinates on which a vector vanishes. -/
noncomputable def zeroCoordinates {n : ℕ} (d : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ d i = 0

@[simp] lemma mem_zeroCoordinates {n : ℕ} {d : Fin n → ℝ} {i : Fin n} :
    i ∈ zeroCoordinates d ↔ d i = 0 := by
  simp [zeroCoordinates]

@[simp] lemma mem_coordinateSets {n k : ℕ} {I : Finset (Fin n)} :
    I ∈ coordinateSets n k ↔ I.card = k := by
  simp [coordinateSets]

@[simp] lemma coordinateSets_nonempty_iff {n k : ℕ} :
    (coordinateSets n k).Nonempty ↔ k ≤ n := by
  simp [coordinateSets]

lemma exists_nonzero_mem_of_zeroCoordinates_card_lt {n k : ℕ} {d : Fin n → ℝ}
    {I : Finset (Fin n)} (hI : I ∈ coordinateSets n k)
    (hz : (zeroCoordinates d).card < k) :
    ∃ i ∈ I, d i ≠ 0 := by
  by_contra h
  push Not at h
  have hsub : I ⊆ zeroCoordinates d := by
    intro i hi
    exact mem_zeroCoordinates.mpr (h i hi)
  have hcard := Finset.card_le_card hsub
  have hIk : I.card = k := mem_coordinateSets.mp hI
  omega

lemma euclidNorm_restrict_ne_zero_of_zeroCoordinates_card_lt {n k : ℕ}
    {d : Fin n → ℝ} {I : Finset (Fin n)} (hI : I ∈ coordinateSets n k)
    (hz : (zeroCoordinates d).card < k) :
    euclidNorm (restrict d I) ≠ 0 := by
  obtain ⟨i, hi, hdi⟩ := exists_nonzero_mem_of_zeroCoordinates_card_lt hI hz
  intro hnorm
  have hzero : restrict d I = 0 := euclidNorm_eq_zero_iff.mp hnorm
  have hzcoord := congrFun hzero (⟨i, hi⟩ : I)
  exact hdi (by simpa [restrict] using hzcoord)

lemma euclidNorm_normalizedRestrict_eq_one_of_zeroCoordinates_card_lt {n k : ℕ}
    {d : Fin n → ℝ} {I : Finset (Fin n)} (hI : I ∈ coordinateSets n k)
    (hz : (zeroCoordinates d).card < k) :
    euclidNorm (normalizedRestrict d I) = 1 :=
  euclidNorm_normalizedRestrict d I
    (euclidNorm_restrict_ne_zero_of_zeroCoordinates_card_lt hI hz)

/-- Maximum of `D_L` over all coordinate restrictions of size `k`.
It is zero when `k > n`, when there is no such coordinate set. -/
noncomputable def regularizedLCDCard {n : ℕ} (L : ℝ) (k : ℕ)
    (d : Fin n → ℝ) : ℝ :=
  if h : (coordinateSets n k).Nonempty then
    (coordinateSets n k).sup' h fun I ↦ LCD L (normalizedRestrict d I)
  else 0

/-- The paper's regularization cardinality `ceil (n^(1-gamma))`. -/
noncomputable def regularizationCard (n : ℕ) (γ : ℝ) : ℕ :=
  Nat.ceil ((n : ℝ) ^ (1 - γ))

/-- The common cardinality of the buckets in KSSS Lemma 4.12. -/
noncomputable def smallRLCDBucketCard (n : ℕ) (γ : ℝ) : ℕ :=
  Nat.ceil ((n : ℝ) ^ (1 - 2 * γ))

noncomputable def smallRLCDValueRange (n : ℕ) (γ : ℝ) : ℕ :=
  Nat.floor ((n : ℝ) ^ (2 * γ / 3))

noncomputable def smallRLCDErrorCount (n : ℕ) (γ : ℝ) : ℕ :=
  Nat.floor ((n : ℝ) ^ (1 - 3 * γ))

noncomputable def smallRLCDLargeCount (n : ℕ) (γ : ℝ) : ℕ :=
  Nat.floor (10 * (n : ℝ) ^ (1 - 4 * γ / 3))

/-- The maximum-based regularized least common denominator. -/
noncomputable def regularizedLCD {n : ℕ} (L γ : ℝ) (d : Fin n → ℝ) : ℝ :=
  regularizedLCDCard L (regularizationCard n γ) d

lemma regularizedLCDCard_eq_zero_of_lt {n k : ℕ} (L : ℝ) (d : Fin n → ℝ)
    (hnk : n < k) : regularizedLCDCard L k d = 0 := by
  rw [regularizedLCDCard, dif_neg]
  simpa using not_le_of_gt hnk

lemma LCD_normalizedRestrict_le_regularizedLCDCard {n k : ℕ} (L : ℝ)
    (d : Fin n → ℝ) {I : Finset (Fin n)} (hI : I ∈ coordinateSets n k) :
    LCD L (normalizedRestrict d I) ≤ regularizedLCDCard L k d := by
  rw [regularizedLCDCard, dif_pos ⟨I, hI⟩]
  exact Finset.le_sup'
    (s := coordinateSets n k)
    (f := fun J ↦ LCD L (normalizedRestrict d J)) hI

/-- The regularized LCD is attained on one of the fixed-cardinality
coordinate sets. -/
lemma exists_coordinateSet_eq_regularizedLCDCard {n k : ℕ} (L : ℝ)
    (d : Fin n → ℝ) (hk : k ≤ n) :
    ∃ I ∈ coordinateSets n k,
      regularizedLCDCard L k d = LCD L (normalizedRestrict d I) := by
  have hne : (coordinateSets n k).Nonempty := coordinateSets_nonempty_iff.mpr hk
  rw [regularizedLCDCard, dif_pos hne]
  exact Finset.exists_mem_eq_sup'
    (s := coordinateSets n k) (H := hne)
    (f := fun I ↦ LCD L (normalizedRestrict d I))

/-- Characterization of the maximum by coordinatewise upper bounds. -/
lemma regularizedLCDCard_le_iff {n k : ℕ} (L : ℝ) (d : Fin n → ℝ)
    (hk : k ≤ n) (A : ℝ) :
    regularizedLCDCard L k d ≤ A ↔
      ∀ I ∈ coordinateSets n k, LCD L (normalizedRestrict d I) ≤ A := by
  have hne : (coordinateSets n k).Nonempty := coordinateSets_nonempty_iff.mpr hk
  rw [regularizedLCDCard, dif_pos hne, Finset.sup'_le_iff]

lemma regularizedLCDCard_nonneg {n k : ℕ} {L : ℝ} (hL : 1 ≤ L)
    {d : Fin n → ℝ} (hk : k ≤ n) (hz : (zeroCoordinates d).card < k) :
    0 ≤ regularizedLCDCard L k d := by
  obtain ⟨I, _hI, hmax⟩ := exists_coordinateSet_eq_regularizedLCDCard L d hk
  rw [hmax]
  exact LCD_nonneg hL (normalizedRestrict d I)

/-- Every fixed-cardinality restriction is bounded by the regularized LCD,
and Lemma 4.10 supplies its explicit lower bound. -/
lemma inv_two_norm_normalizedRestrict_le_regularizedLCDCard {n k : ℕ}
    {L : ℝ} (hL : 1 ≤ L) {d : Fin n → ℝ} {I : Finset (Fin n)}
    (hI : I ∈ coordinateSets n k) (hz : (zeroCoordinates d).card < k) :
    (2 * ‖normalizedRestrict d I‖)⁻¹ ≤ regularizedLCDCard L k d := by
  calc
    (2 * ‖normalizedRestrict d I‖)⁻¹ ≤ LCD L (normalizedRestrict d I) :=
      LCD_ge_inv_two_norm hL
        (euclidNorm_normalizedRestrict_eq_one_of_zeroCoordinates_card_lt hI hz)
    _ ≤ regularizedLCDCard L k d :=
      LCD_normalizedRestrict_le_regularizedLCDCard L d hI

/-! ## The deterministic maximal-bucket argument in Lemma 4.12 -/

/-- A fixed-size set of coordinates whose entries all lie near one
nonnegative real center. -/
def IsBucket {α : Type*} (d : α → ℝ) (k : ℕ) (ρ : ℝ) (I : Finset α) : Prop :=
  I.card = k ∧ ∃ κ : ℝ, 0 ≤ κ ∧ ∀ i ∈ I, |d i - κ| ≤ ρ

lemma IsBucket.mono_radius {α : Type*} {d : α → ℝ} {k : ℕ}
    {ρ ρ' : ℝ} {I : Finset α} (hI : IsBucket d k ρ I) (hρ : ρ ≤ ρ') :
    IsBucket d k ρ' I := by
  obtain ⟨hcard, κ, hκ, hclose⟩ := hI
  exact ⟨hcard, κ, hκ, fun i hi ↦ (hclose i hi).trans hρ⟩

lemma IsBucket.map_subtype {α : Type*} [DecidableEq α] {S : Finset α}
    {d : α → ℝ} {k : ℕ} {ρ : ℝ} {I : Finset S}
    (hI : IsBucket (fun i : S ↦ d i) k ρ I) :
    IsBucket d k ρ (I.map ⟨Subtype.val, Subtype.val_injective⟩) := by
  obtain ⟨hcard, κ, hκ, hclose⟩ := hI
  refine ⟨by simpa using hcard, κ, hκ, ?_⟩
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
  exact hclose j hj

/-- Pigeonhole step in KSSS Lemma 4.12. If many coordinates are well
approximated, after a positive rescaling, by nonnegative integers in a
fixed finite range, then a prescribed-size subfamily lies in one bucket. -/
theorem exists_bucket_of_many_good_integer_approximations
    {α : Type*} [Fintype α] (d : α → ℝ) (w : α → ℕ)
    (G : Finset α) (a τ : ℝ) (M k : ℕ) (ha : 0 < a)
    (hgood : ∀ i ∈ G, |a * d i - (w i : ℝ)| ≤ τ ∧ w i ≤ M)
    (hcard : (M + 1) * k ≤ G.card) :
    ∃ I : Finset α, I ⊆ G ∧ IsBucket d k (τ / a) I := by
  classical
  have hmaps : ∀ i ∈ G, w i ∈ Finset.range (M + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hgood i hi).2)
  have hrange : (Finset.range (M + 1)).Nonempty := by simp
  have hpig : (Finset.range (M + 1)).card * k ≤ G.card := by
    simpa using hcard
  obtain ⟨r, hr, hrfiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := G) (t := Finset.range (M + 1)) (f := w) hmaps hrange hpig
  obtain ⟨I, hIfiber, hIcard⟩ := Finset.exists_subset_card_eq hrfiber
  have hIG : I ⊆ G := fun i hi ↦ (Finset.mem_filter.mp (hIfiber hi)).1
  refine ⟨I, hIG, hIcard, (r : ℝ) / a, div_nonneg (Nat.cast_nonneg r) ha.le, ?_⟩
  intro i hi
  have hiFiber := Finset.mem_filter.mp (hIfiber hi)
  have hwi : w i = r := hiFiber.2
  have happ := (hgood i hiFiber.1).1
  rw [hwi] at happ
  calc
    |d i - (r : ℝ) / a| = |(a * d i - (r : ℝ)) / a| := by
      congr 1
      field_simp
    _ = |a * d i - (r : ℝ)| / a := by rw [abs_div, abs_of_pos ha]
    _ ≤ τ / a := div_le_div_of_nonneg_right happ ha.le

/-- Quantitative extraction of one bucket from a small Euclidean lattice
error.  The two displayed budget inequalities are precisely the two
second-moment deletions in the proof of KSSS Lemma 4.12. -/
theorem exists_bucket_of_controlled_nat_approximation
    {α : Type*} [Fintype α] (d : α → ℝ) (w : α → ℕ)
    (a τ E T : ℝ) (M k Cerror Clarge : ℕ)
    (ha : 0 < a) (hτ : 0 < τ) (hT : 0 < T) (hE0 : 0 ≤ E)
    (happrox : euclidNorm (fun i ↦ a * d i - (w i : ℝ)) ≤ E)
    (herrorBudget : E ^ 2 < (Cerror + 1 : ℕ) * τ ^ 2)
    (hlargeBudget : (∑ i, ((w i : ℝ) ^ 2)) < (Clarge + 1 : ℕ) * T ^ 2)
    (hrange : T < (M + 1 : ℕ))
    (hcapacity : (M + 1) * k + Cerror + Clarge ≤ Fintype.card α) :
    ∃ I : Finset α, IsBucket d k (τ / a) I := by
  classical
  let e : α → ℝ := fun i ↦ a * d i - (w i : ℝ)
  let badError : Finset α := Finset.univ.filter fun i ↦ τ < |e i|
  let badLarge : Finset α := Finset.univ.filter fun i ↦ T < (w i : ℝ)
  let good : Finset α := Finset.univ.filter fun i ↦ |e i| ≤ τ ∧ w i ≤ M
  have hbadError : badError.card ≤ Cerror := by
    simpa [badError, e] using card_large_coordinates_le
      e τ E Cerror hτ (by simpa [e] using happrox) hE0 herrorBudget
  have hbadLarge : badLarge.card ≤ Clarge := by
    have h := card_large_coordinates_le_of_sum_sq_lt
      (fun i ↦ (w i : ℝ)) T Clarge hT hlargeBudget
    simpa [badLarge, abs_of_nonneg] using h
  have hcover : Finset.univ ⊆ (good ∪ badError) ∪ badLarge := by
    intro i _hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      good, badError, badLarge]
    by_cases he : |e i| ≤ τ
    · by_cases hw : w i ≤ M
      · exact Or.inl (Or.inl ⟨he, hw⟩)
      · apply Or.inr
        have hwNat : M + 1 ≤ w i := by omega
        have hwReal : ((M + 1 : ℕ) : ℝ) ≤ (w i : ℝ) := by exact_mod_cast hwNat
        exact hrange.trans_le hwReal
    · exact Or.inl (Or.inr (lt_of_not_ge he))
  have hcardCover := Finset.card_le_card hcover
  have hcardUnion₁ := Finset.card_union_le good badError
  have hcardUnion₂ := Finset.card_union_le (good ∪ badError) badLarge
  rw [Finset.card_univ] at hcardCover
  have hgoodCard : (M + 1) * k ≤ good.card := by omega
  have hgood : ∀ i ∈ good,
      |a * d i - (w i : ℝ)| ≤ τ ∧ w i ≤ M := by
    intro i hi
    simpa [good, e] using (Finset.mem_filter.mp hi).2
  obtain ⟨I, _hIgood, hI⟩ := exists_bucket_of_many_good_integer_approximations
    d w good a τ M k ha hgood hgoodCard
  exact ⟨I, hI⟩

/-- The analytic-to-combinatorial core of Lemma 4.12, with all of the
eventual power estimates exposed as explicit numerical hypotheses. -/
theorem exists_bucket_of_small_LCD
    {α : Type*} [Fintype α] (d : α → ℝ)
    (L B τ E T ρ : ℝ) (M k Cerror Clarge : ℕ)
    (hd : ∀ i, 0 ≤ d i) (hnorm : 0 < euclidNorm d)
    (hL : 1 ≤ L) (hB : 0 < B) (hE0 : 0 ≤ E) (hτ : 0 < τ) (hT : 0 < T)
    (hLCD : LCD L (fun i ↦ d i / euclidNorm d) ≤ B)
    (hEbound : ∀ θ, 0 < θ → θ < 2 * B →
      L * Real.sqrt (logPlus (θ / L)) ≤ E)
    (herrorBudget : E ^ 2 < (Cerror + 1 : ℕ) * τ ^ 2)
    (hlargeBudget : ∀ θ, 0 < θ → θ < 2 * B →
      2 * θ ^ 2 + 2 * E ^ 2 < (Clarge + 1 : ℕ) * T ^ 2)
    (hrange : T < (M + 1 : ℕ))
    (hcapacity : (M + 1) * k + Cerror + Clarge ≤ Fintype.card α)
    (hradius : ∀ θ, 0 < θ → θ < 2 * B →
      τ / (θ / euclidNorm d) ≤ ρ) :
    ∃ I : Finset α, IsBucket d k ρ I := by
  let v : α → ℝ := fun i ↦ d i / euclidNorm d
  have hunit : euclidNorm v = 1 := by
    have ha : euclidNorm d ≠ 0 := hnorm.ne'
    have hs : 0 ≤ ∑ i, (d i) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have ha2 : (euclidNorm d) ^ 2 = ∑ i, (d i) ^ 2 := by
      simpa [euclidNorm] using Real.sq_sqrt hs
    rw [euclidNorm, Real.sqrt_eq_one]
    change (∑ i, (v i) ^ 2) = 1
    calc
      ∑ i, (v i) ^ 2 = (∑ i, (d i) ^ 2) / (euclidNorm d) ^ 2 := by
        simp only [v, div_pow, Finset.sum_div]
      _ = (euclidNorm d) ^ 2 / (euclidNorm d) ^ 2 := by rw [ha2]
      _ = 1 := div_self (pow_ne_zero 2 ha)
  obtain ⟨θ, hθ, hθB, w, hw⟩ := exists_nat_approximant_of_LCD_le
    hL hB (v := v) (fun i ↦ div_nonneg (hd i) hnorm.le) (by simpa [v] using hLCD)
  have hwE : euclidNorm (fun i ↦ θ * v i - (w i : ℝ)) ≤ E :=
    hw.le.trans (hEbound θ hθ hθB)
  have hscale : 0 < θ / euclidNorm d := div_pos hθ hnorm
  have hscaledApprox :
      euclidNorm (fun i ↦ (θ / euclidNorm d) * d i - (w i : ℝ)) ≤ E := by
    have heq : (fun i ↦ (θ / euclidNorm d) * d i - (w i : ℝ)) =
        (fun i ↦ θ * v i - (w i : ℝ)) := by
      funext i
      simp only [v]
      ring
    rw [heq]
    exact hwE
  have hsumw : (∑ i, ((w i : ℝ) ^ 2)) <
      (Clarge + 1 : ℕ) * T ^ 2 :=
    (sum_sq_nat_approximant_le v w θ E hunit hwE hE0).trans_lt
      (hlargeBudget θ hθ hθB)
  obtain ⟨I, hI⟩ := exists_bucket_of_controlled_nat_approximation
    d w (θ / euclidNorm d) τ E T M k Cerror Clarge hscale hτ hT hE0
      hscaledApprox herrorBudget hsumw hrange hcapacity
  exact ⟨I, hI.mono_radius (hradius θ hθ hθB)⟩

/-- Source-level version of the preceding extraction lemma.  Lemma 4.10
turns the ambient sup-norm bound into the required bucket radius. -/
theorem exists_bucket_of_small_LCD_of_norm_le
    {α : Type*} [Fintype α] (d : α → ℝ)
    (L B τ E T ρ D : ℝ) (M k Cerror Clarge : ℕ)
    (hd : ∀ i, 0 ≤ d i) (hnorm : 0 < euclidNorm d) (hsup : ‖d‖ ≤ D)
    (hL : 1 ≤ L) (hB : 0 < B) (hE0 : 0 ≤ E) (hτ : 0 < τ) (hT : 0 < T)
    (hLCD : LCD L (fun i ↦ d i / euclidNorm d) ≤ B)
    (hEbound : ∀ θ, 0 < θ → θ < 2 * B →
      L * Real.sqrt (logPlus (θ / L)) ≤ E)
    (herrorBudget : E ^ 2 < (Cerror + 1 : ℕ) * τ ^ 2)
    (hlargeBudget : ∀ θ, 0 < θ → θ < 2 * B →
      2 * θ ^ 2 + 2 * E ^ 2 < (Clarge + 1 : ℕ) * T ^ 2)
    (hrange : T < (M + 1 : ℕ))
    (hcapacity : (M + 1) * k + Cerror + Clarge ≤ Fintype.card α)
    (hradiusBudget : 2 * D * τ ≤ ρ) :
    ∃ I : Finset α, IsBucket d k ρ I := by
  let v : α → ℝ := fun i ↦ d i / euclidNorm d
  have ha : euclidNorm d ≠ 0 := hnorm.ne'
  have hunit : euclidNorm v = 1 := by
    have hs : 0 ≤ ∑ i, (d i) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have ha2 : (euclidNorm d) ^ 2 = ∑ i, (d i) ^ 2 := by
      simpa [euclidNorm] using Real.sq_sqrt hs
    rw [euclidNorm, Real.sqrt_eq_one]
    change (∑ i, (v i) ^ 2) = 1
    calc
      ∑ i, (v i) ^ 2 = (∑ i, (d i) ^ 2) / (euclidNorm d) ^ 2 := by
        simp only [v, div_pow, Finset.sum_div]
      _ = (euclidNorm d) ^ 2 / (euclidNorm d) ^ 2 := by rw [ha2]
      _ = 1 := div_self (pow_ne_zero 2 ha)
  obtain ⟨θ, hθscale, hθB, w, hw⟩ := exists_nat_lcdScale_of_LCD_le
    hL hB (v := v) (fun i ↦ div_nonneg (hd i) hnorm.le) (by simpa [v] using hLCD)
  have hθ : 0 < θ := hθscale.1
  have hwE : euclidNorm (fun i ↦ θ * v i - (w i : ℝ)) ≤ E :=
    hw.le.trans (hEbound θ hθ hθB)
  have hD0 : 0 ≤ D := (norm_nonneg d).trans hsup
  have hvnorm : ‖v‖ ≤ D / euclidNorm d := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hD0 hnorm.le)).2
    intro i
    simp only [v, Real.norm_eq_abs, abs_div, abs_of_pos hnorm]
    have hdi : |d i| ≤ ‖d‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm d i
    exact div_le_div_of_nonneg_right
      (hdi.trans hsup) hnorm.le
  have hvne : v ≠ 0 := by
    intro hv
    rw [hv] at hunit
    simp [euclidNorm] at hunit
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hθlower : (2 * ‖v‖)⁻¹ ≤ θ := lcdScale_ge_inv_two_norm hL hunit hθscale
  have hone : 1 ≤ 2 * ‖v‖ * θ := by
    have hmul := mul_le_mul_of_nonneg_left hθlower (mul_pos two_pos hvpos).le
    simpa [mul_assoc, hvpos.ne'] using hmul
  have havD : euclidNorm d * ‖v‖ ≤ D := by
    have := (le_div_iff₀ hnorm).mp hvnorm
    simpa [mul_comm] using this
  have havDθ := mul_le_mul_of_nonneg_right havD hθ.le
  have haratio : euclidNorm d / θ ≤ 2 * D := by
    rw [div_le_iff₀ hθ]
    nlinarith
  have hscale : 0 < θ / euclidNorm d := div_pos hθ hnorm
  have hscaledApprox :
      euclidNorm (fun i ↦ (θ / euclidNorm d) * d i - (w i : ℝ)) ≤ E := by
    have heq : (fun i ↦ (θ / euclidNorm d) * d i - (w i : ℝ)) =
        (fun i ↦ θ * v i - (w i : ℝ)) := by
      funext i
      simp only [v]
      ring
    rw [heq]
    exact hwE
  have hsumw : (∑ i, ((w i : ℝ) ^ 2)) <
      (Clarge + 1 : ℕ) * T ^ 2 :=
    (sum_sq_nat_approximant_le v w θ E hunit hwE hE0).trans_lt
      (hlargeBudget θ hθ hθB)
  have hradius : τ / (θ / euclidNorm d) ≤ ρ := by
    calc
      τ / (θ / euclidNorm d) = τ * (euclidNorm d / θ) := by field_simp
      _ ≤ τ * (2 * D) := mul_le_mul_of_nonneg_left haratio hτ.le
      _ = 2 * D * τ := by ring
      _ ≤ ρ := hradiusBudget
  obtain ⟨I, hI⟩ := exists_bucket_of_controlled_nat_approximation
    d w (θ / euclidNorm d) τ E T M k Cerror Clarge hscale hτ hT hE0
      hscaledApprox herrorBudget hsumw hrange hcapacity
  exact ⟨I, hI.mono_radius hradius⟩

/-- All buckets with prescribed size and radius. -/
noncomputable def goodBuckets {α : Type*} [Fintype α]
    (d : α → ℝ) (k : ℕ) (ρ : ℝ) : Finset (Finset α) := by
  classical
  exact Finset.univ.filter (IsBucket d k ρ)

@[simp] lemma mem_goodBuckets {α : Type*} [Fintype α] {d : α → ℝ}
    {k : ℕ} {ρ : ℝ} {I : Finset α} :
    I ∈ goodBuckets d k ρ ↔ IsBucket d k ρ I := by
  classical
  simp [goodBuckets]

/-- Pairwise-disjoint families of good buckets. -/
noncomputable def bucketFamilies {α : Type*} [Fintype α]
    (d : α → ℝ) (k : ℕ) (ρ : ℝ) : Finset (Finset (Finset α)) := by
  classical
  exact (goodBuckets d k ρ).powerset.filter fun F ↦
    (F : Set (Finset α)).PairwiseDisjoint id

@[simp] lemma mem_bucketFamilies {α : Type*} [Fintype α] {d : α → ℝ}
    {k : ℕ} {ρ : ℝ} {F : Finset (Finset α)} :
    F ∈ bucketFamilies d k ρ ↔
      F ⊆ goodBuckets d k ρ ∧ (F : Set (Finset α)).PairwiseDisjoint id := by
  classical
  simp [bucketFamilies]

/-- The concrete output of the bucket decomposition: `blocks` are
pairwise disjoint good buckets and `remainder` is exactly their complement. -/
structure BucketDecomposition {α : Type*} [Fintype α] [DecidableEq α]
    (d : α → ℝ) (k : ℕ) (ρ : ℝ) where
  blocks : Finset (Finset α)
  blocks_good : ∀ I ∈ blocks, IsBucket d k ρ I
  blocks_disjoint : (blocks : Set (Finset α)).PairwiseDisjoint id
  remainder : Finset α
  remainder_eq : remainder = Finset.univ \ blocks.biUnion id

namespace BucketDecomposition

variable {α : Type*} [Fintype α] [DecidableEq α] {d : α → ℝ} {k : ℕ} {ρ : ℝ}

lemma remainder_disjoint (D : BucketDecomposition d k ρ) :
    Disjoint D.remainder (D.blocks.biUnion id) := by
  rw [D.remainder_eq, Finset.disjoint_left]
  intro x hxR hxU
  exact (Finset.mem_sdiff.mp hxR).2 hxU

lemma remainder_union_covered (D : BucketDecomposition d k ρ) :
    D.remainder ∪ D.blocks.biUnion id = Finset.univ := by
  rw [D.remainder_eq]
  exact Finset.sdiff_union_of_subset (Finset.subset_univ _)

end BucketDecomposition

/-- Finite maximality principle used in KSSS Lemma 4.12. If every remainder
larger than `q` contains a good `k`-bucket, then a maximal disjoint family of
good buckets leaves at most `q` coordinates. -/
theorem exists_bucketDecomposition_of_extract {α : Type*} [Fintype α] [DecidableEq α]
    (d : α → ℝ) (k q : ℕ) (ρ : ℝ) (hk : 0 < k)
    (hextract : ∀ R : Finset α, q < R.card →
      ∃ I : Finset α, I ⊆ R ∧ IsBucket d k ρ I) :
    ∃ D : BucketDecomposition d k ρ, D.remainder.card ≤ q := by
  classical
  have hfamilies : (bucketFamilies d k ρ).Nonempty := by
    refine ⟨∅, ?_⟩
    simp
  obtain ⟨F, hFmem, hFmax⟩ := Finset.exists_mem_eq_sup'
    (s := bucketFamilies d k ρ) (H := hfamilies)
    (f := fun A ↦ A.card)
  have hF := mem_bucketFamilies.mp hFmem
  let U : Finset α := F.biUnion id
  let R : Finset α := Finset.univ \ U
  have hRcard : R.card ≤ q := by
    by_contra hq
    have hqR : q < R.card := Nat.lt_of_not_ge hq
    obtain ⟨I, hIR, hIgood⟩ := hextract R hqR
    have hImemgood : I ∈ goodBuckets d k ρ := mem_goodBuckets.mpr hIgood
    have hIne : I.Nonempty := Finset.card_pos.mp (hIgood.1.symm ▸ hk)
    have hInotF : I ∉ F := by
      intro hIF
      obtain ⟨x, hxI⟩ := hIne
      have hxR : x ∈ R := hIR hxI
      have hxU : x ∈ U := by
        exact Finset.mem_biUnion.mpr ⟨I, hIF, hxI⟩
      exact (Finset.mem_sdiff.mp hxR).2 hxU
    have hIdisj : ∀ J ∈ F, Disjoint I J := by
      intro J hJF
      rw [Finset.disjoint_left]
      intro x hxI hxJ
      have hxR : x ∈ R := hIR hxI
      have hxU : x ∈ U := Finset.mem_biUnion.mpr ⟨J, hJF, hxJ⟩
      exact (Finset.mem_sdiff.mp hxR).2 hxU
    have hinsert_pairwise :
        ((insert I F : Finset (Finset α)) : Set (Finset α)).PairwiseDisjoint id := by
      intro A hA B hB hAB
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hA hB
      rcases hA with rfl | hAF
      · rcases hB with rfl | hBF
        · exact (hAB rfl).elim
        · exact hIdisj B hBF
      · rcases hB with rfl | hBF
        · exact (hIdisj A hAF).symm
        · exact hF.2 hAF hBF hAB
    have hinsert_mem : insert I F ∈ bucketFamilies d k ρ := by
      apply mem_bucketFamilies.mpr
      refine ⟨?_, hinsert_pairwise⟩
      exact Finset.insert_subset hImemgood hF.1
    have hlemax : (insert I F).card ≤
        (bucketFamilies d k ρ).sup' hfamilies (fun A ↦ A.card) :=
      Finset.le_sup' (f := fun A : Finset (Finset α) ↦ A.card) hinsert_mem
    rw [hFmax, Finset.card_insert_of_notMem hInotF] at hlemax
    omega
  refine ⟨{
    blocks := F
    blocks_good := fun I hI ↦ mem_goodBuckets.mp (hF.1 hI)
    blocks_disjoint := hF.2
    remainder := R
    remainder_eq := rfl
  }, hRcard⟩

/-- Exact finite form of the small-RLCD bucket decomposition.  Compared
with the asymptotic statement of KSSS Lemma 4.12, the phrase "for all
sufficiently large `n`" has been replaced by the five explicit numerical
inequalities used in its proof. -/
theorem exists_bucketDecomposition_of_small_LCD
    {α : Type*} [Fintype α] [DecidableEq α] (d : α → ℝ)
    (sampleCard blockCard q : ℕ) (L B τ E T ρ : ℝ)
    (M Cerror Clarge : ℕ)
    (hd : ∀ i, 0 ≤ d i) (hblock : 0 < blockCard)
    (hsample : sampleCard ≤ q + 1)
    (hL : 1 ≤ L) (hB : 0 < B) (hE0 : 0 ≤ E) (hτ : 0 < τ) (hT : 0 < T)
    (hnorm : ∀ S : Finset α, S.card = sampleCard →
      0 < euclidNorm (restrict d S))
    (hLCD : ∀ S : Finset α, S.card = sampleCard →
      LCD L (normalizedRestrict d S) ≤ B)
    (hEbound : ∀ θ, 0 < θ → θ < 2 * B →
      L * Real.sqrt (logPlus (θ / L)) ≤ E)
    (herrorBudget : E ^ 2 < (Cerror + 1 : ℕ) * τ ^ 2)
    (hlargeBudget : ∀ θ, 0 < θ → θ < 2 * B →
      2 * θ ^ 2 + 2 * E ^ 2 < (Clarge + 1 : ℕ) * T ^ 2)
    (hrange : T < (M + 1 : ℕ))
    (hcapacity : (M + 1) * blockCard + Cerror + Clarge ≤ sampleCard)
    (hradius : ∀ (S : Finset α) (θ : ℝ), S.card = sampleCard →
      0 < θ → θ < 2 * B → τ / (θ / euclidNorm (restrict d S)) ≤ ρ) :
    ∃ D : BucketDecomposition d blockCard ρ, D.remainder.card ≤ q := by
  apply exists_bucketDecomposition_of_extract d blockCard q ρ hblock
  intro R hqR
  have hsampleR : sampleCard ≤ R.card := by omega
  obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq hsampleR
  have hnormS : 0 < euclidNorm (restrict d S) := hnorm S hScard
  have hLCDS :
      LCD L (fun i : S ↦ restrict d S i / euclidNorm (restrict d S)) ≤ B := by
    have heq : (fun i : S ↦ restrict d S i / euclidNorm (restrict d S)) =
        normalizedRestrict d S := by
      funext i
      rfl
    rw [heq]
    exact hLCD S hScard
  have hcapacityS : (M + 1) * blockCard + Cerror + Clarge ≤ Fintype.card S := by
    simpa [Fintype.card_coe, hScard] using hcapacity
  obtain ⟨I, hI⟩ := exists_bucket_of_small_LCD
    (restrict d S) L B τ E T ρ M blockCard Cerror Clarge
      (fun i ↦ hd i) hnormS hL hB hE0 hτ hT hLCDS hEbound herrorBudget
      hlargeBudget hrange hcapacityS (fun θ hθ hθB ↦ hradius S θ hScard hθ hθB)
  let e : S ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨I.map e, ?_, hI.map_subtype⟩
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
  exact hSR j.property

/-- Exact finite decomposition with the bucket radius discharged by the
sup-norm estimate from Lemma 4.10. -/
theorem exists_bucketDecomposition_of_small_LCD_of_norm_le
    {α : Type*} [Fintype α] [DecidableEq α] (d : α → ℝ)
    (sampleCard blockCard q : ℕ) (L B τ E T ρ D : ℝ)
    (M Cerror Clarge : ℕ)
    (hd : ∀ i, 0 ≤ d i) (hblock : 0 < blockCard)
    (hsample : sampleCard ≤ q + 1)
    (hL : 1 ≤ L) (hB : 0 < B) (hE0 : 0 ≤ E) (hτ : 0 < τ) (hT : 0 < T)
    (hnorm : ∀ S : Finset α, S.card = sampleCard →
      0 < euclidNorm (restrict d S))
    (hsup : ∀ S : Finset α, S.card = sampleCard → ‖restrict d S‖ ≤ D)
    (hLCD : ∀ S : Finset α, S.card = sampleCard →
      LCD L (normalizedRestrict d S) ≤ B)
    (hEbound : ∀ θ, 0 < θ → θ < 2 * B →
      L * Real.sqrt (logPlus (θ / L)) ≤ E)
    (herrorBudget : E ^ 2 < (Cerror + 1 : ℕ) * τ ^ 2)
    (hlargeBudget : ∀ θ, 0 < θ → θ < 2 * B →
      2 * θ ^ 2 + 2 * E ^ 2 < (Clarge + 1 : ℕ) * T ^ 2)
    (hrange : T < (M + 1 : ℕ))
    (hcapacity : (M + 1) * blockCard + Cerror + Clarge ≤ sampleCard)
    (hradiusBudget : 2 * D * τ ≤ ρ) :
    ∃ D' : BucketDecomposition d blockCard ρ, D'.remainder.card ≤ q := by
  apply exists_bucketDecomposition_of_extract d blockCard q ρ hblock
  intro R hqR
  have hsampleR : sampleCard ≤ R.card := by omega
  obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq hsampleR
  have hnormS : 0 < euclidNorm (restrict d S) := hnorm S hScard
  have hLCDS :
      LCD L (fun i : S ↦ restrict d S i / euclidNorm (restrict d S)) ≤ B := by
    have heq : (fun i : S ↦ restrict d S i / euclidNorm (restrict d S)) =
        normalizedRestrict d S := by
      funext i
      rfl
    rw [heq]
    exact hLCD S hScard
  have hcapacityS : (M + 1) * blockCard + Cerror + Clarge ≤ Fintype.card S := by
    simpa [Fintype.card_coe, hScard] using hcapacity
  obtain ⟨I, hI⟩ := exists_bucket_of_small_LCD_of_norm_le
    (restrict d S) L B τ E T ρ D M blockCard Cerror Clarge
      (fun i ↦ hd i) hnormS (hsup S hScard) hL hB hE0 hτ hT hLCDS hEbound
      herrorBudget hlargeBudget hrange hcapacityS hradiusBudget
  let e : S ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨I.map e, ?_, hI.map_subtype⟩
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
  exact hSR j.property

lemma smallRLCD_capacity_of_growth (γ : ℝ) (hγ : 0 < γ) (hγ4 : γ < 1 / 4)
    (n : ℕ) (hn : 1 ≤ n) (hgrowth : 15 < (n : ℝ) ^ (γ / 3)) :
    (smallRLCDValueRange n γ + 1) * smallRLCDBucketCard n γ +
          smallRLCDErrorCount n γ + smallRLCDLargeCount n γ ≤
        regularizationCard n γ := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hγ23 : 0 ≤ 2 * γ / 3 := by positivity
  have hbexp : 0 ≤ 1 - 2 * γ := by linarith
  have hMone : 1 ≤ (n : ℝ) ^ (2 * γ / 3) := Real.one_le_rpow hn1 hγ23
  have hBone : 1 ≤ (n : ℝ) ^ (1 - 2 * γ) := Real.one_le_rpow hn1 hbexp
  have hM : ((smallRLCDValueRange n γ + 1 : ℕ) : ℝ) ≤
      2 * (n : ℝ) ^ (2 * γ / 3) := by
    have hf := Nat.floor_le
      (Real.rpow_nonneg (show (0 : ℝ) ≤ (n : ℝ) from hn0.le) (2 * γ / 3))
    change ((Nat.floor ((n : ℝ) ^ (2 * γ / 3)) + 1 : ℕ) : ℝ) ≤ _
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hB : ((smallRLCDBucketCard n γ : ℕ) : ℝ) ≤
      2 * (n : ℝ) ^ (1 - 2 * γ) := by
    have hc := (Nat.ceil_lt_add_one
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) (1 - 2 * γ))).le
    change ((Nat.ceil ((n : ℝ) ^ (1 - 2 * γ)) : ℕ) : ℝ) ≤ _
    nlinarith
  have hprod : (((smallRLCDValueRange n γ + 1) *
      smallRLCDBucketCard n γ : ℕ) : ℝ) ≤
      4 * (n : ℝ) ^ (1 - 4 * γ / 3) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (2 * (n : ℝ) ^ (2 * γ / 3)) *
          (2 * (n : ℝ) ^ (1 - 2 * γ)) :=
        mul_le_mul hM hB (by positivity) (by positivity)
      _ = 4 * ((n : ℝ) ^ (2 * γ / 3) * (n : ℝ) ^ (1 - 2 * γ)) := by ring
      _ = 4 * (n : ℝ) ^ (2 * γ / 3 + (1 - 2 * γ)) := by
        rw [Real.rpow_add hn0]
      _ = 4 * (n : ℝ) ^ (1 - 4 * γ / 3) := by congr 2 <;> ring
  have herr : ((smallRLCDErrorCount n γ : ℕ) : ℝ) ≤
      (n : ℝ) ^ (1 - 4 * γ / 3) := by
    calc
      ((smallRLCDErrorCount n γ : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 - 3 * γ) := by
        exact Nat.floor_le (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) _)
      _ ≤ (n : ℝ) ^ (1 - 4 * γ / 3) := by
        apply Real.rpow_le_rpow_of_exponent_le hn1
        linarith
  have hlarge : ((smallRLCDLargeCount n γ : ℕ) : ℝ) ≤
      10 * (n : ℝ) ^ (1 - 4 * γ / 3) := by
    exact Nat.floor_le (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) _))
  have hsum : (((smallRLCDValueRange n γ + 1) * smallRLCDBucketCard n γ +
      smallRLCDErrorCount n γ + smallRLCDLargeCount n γ : ℕ) : ℝ) ≤
      15 * (n : ℝ) ^ (1 - 4 * γ / 3) := by
    simp only [Nat.cast_add]
    nlinarith
  have hpow : (n : ℝ) ^ (1 - 4 * γ / 3) * (n : ℝ) ^ (γ / 3) =
      (n : ℝ) ^ (1 - γ) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have htarget : 15 * (n : ℝ) ^ (1 - 4 * γ / 3) <
      (n : ℝ) ^ (1 - γ) := by
    calc
      15 * (n : ℝ) ^ (1 - 4 * γ / 3) =
          (n : ℝ) ^ (1 - 4 * γ / 3) * 15 := by ring
      _ < (n : ℝ) ^ (1 - 4 * γ / 3) * (n : ℝ) ^ (γ / 3) :=
        mul_lt_mul_of_pos_left hgrowth (Real.rpow_pos_of_pos hn0 _)
      _ = (n : ℝ) ^ (1 - γ) := hpow
  have hceil : (n : ℝ) ^ (1 - γ) ≤ (regularizationCard n γ : ℕ) := by
    exact Nat.le_ceil _
  exact_mod_cast hsum.trans (htarget.le.trans hceil)

/-- KSSS Lemma 4.12 with its three eventual numerical estimates stated
explicitly.  The theorem below discharges these estimates uniformly for
all sufficiently large `n`. -/
theorem small_RLCD_bucket_decomposition_of_numeric
    (H γ L : ℝ) (hH : 0 < H) (hγ : 0 < γ) (hγ4 : γ < 1 / 4) (hL : 1 ≤ L)
    (n : ℕ) (hn : 4 ≤ n)
    (hlog : (L * Real.sqrt (Real.log n)) ^ 2 < (n : ℝ) ^ γ)
    (hcapacity :
      (smallRLCDValueRange n γ + 1) * smallRLCDBucketCard n γ +
          smallRLCDErrorCount n γ + smallRLCDLargeCount n γ ≤
        regularizationCard n γ)
    (hradius : 2 * (H * n) * (n : ℝ) ^ (-(1 : ℝ) / 2 + 2 * γ) ≤
      (n : ℝ) ^ ((1 : ℝ) / 2 + 4 * γ))
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (hsup : ‖d‖ ≤ H * n)
    (hnorm : ∀ S : Finset (Fin n), S.card = regularizationCard n γ →
      (n : ℝ) ^ ((3 : ℝ) / 2 - 2 * γ) ≤ euclidNorm (restrict d S))
    (hsmall : regularizedLCD L γ d ≤ Real.sqrt n) :
    ∃ D : BucketDecomposition d (smallRLCDBucketCard n γ)
        ((n : ℝ) ^ ((1 : ℝ) / 2 + 4 * γ)),
      D.remainder.card ≤ Nat.floor ((n : ℝ) ^ (1 - γ)) := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hτ : 0 < (n : ℝ) ^ (-(1 : ℝ) / 2 + 2 * γ) := Real.rpow_pos_of_pos hn0 _
  have hT : 0 < (n : ℝ) ^ (2 * γ / 3) := Real.rpow_pos_of_pos hn0 _
  have hE0 : 0 ≤ L * Real.sqrt (Real.log n) :=
    mul_nonneg (zero_le_one.trans hL) (Real.sqrt_nonneg _)
  have hblock : 0 < smallRLCDBucketCard n γ := by
    rw [smallRLCDBucketCard, Nat.ceil_pos]
    exact Real.rpow_pos_of_pos hn0 _
  have hsample : regularizationCard n γ ≤ Nat.floor ((n : ℝ) ^ (1 - γ)) + 1 := by
    exact Nat.ceil_le_floor_add_one _
  have hB : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hnormPos : ∀ S : Finset (Fin n), S.card = regularizationCard n γ →
      0 < euclidNorm (restrict d S) := by
    intro S hS
    exact (Real.rpow_pos_of_pos hn0 _).trans_le (hnorm S hS)
  have hsupRestrict : ∀ S : Finset (Fin n), S.card = regularizationCard n γ →
      ‖restrict d S‖ ≤ H * n := by
    intro S _hS
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    have hi : ‖d i‖ ≤ ‖d‖ := norm_le_pi_norm d i
    simpa [restrict] using hi.trans hsup
  have hLCD : ∀ S : Finset (Fin n), S.card = regularizationCard n γ →
      LCD L (normalizedRestrict d S) ≤ Real.sqrt n := by
    intro S hS
    exact (LCD_normalizedRestrict_le_regularizedLCDCard L d
      (mem_coordinateSets.mpr hS)).trans (by simpa [regularizedLCD] using hsmall)
  have hEbound : ∀ θ, 0 < θ → θ < 2 * Real.sqrt n →
      L * Real.sqrt (logPlus (θ / L)) ≤ L * Real.sqrt (Real.log n) := by
    intro θ hθ hθB
    have hL0 : 0 < L := zero_lt_one.trans_le hL
    have hθdiv : 0 < θ / L := div_pos hθ hL0
    have hsqrt : 2 * Real.sqrt n ≤ (n : ℝ) := by
      have hsqrtSq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
      have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.sqrt_nonneg (n : ℝ)]
    have hθn : θ / L ≤ (n : ℝ) := by
      have hdivle : θ / L ≤ θ := div_le_self hθ.le hL
      exact hdivle.trans (hθB.le.trans hsqrt)
    have hlogle : logPlus (θ / L) ≤ Real.log n := by
      rw [logPlus]
      exact max_le hlog0 (Real.log_le_log hθdiv hθn)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlogle) (zero_le_one.trans hL)
  have herrorBudget :
      (L * Real.sqrt (Real.log n)) ^ 2 <
        (smallRLCDErrorCount n γ + 1 : ℕ) *
          ((n : ℝ) ^ (-(1 : ℝ) / 2 + 2 * γ)) ^ 2 := by
    have hfloor : (n : ℝ) ^ (1 - 3 * γ) <
        (smallRLCDErrorCount n γ + 1 : ℕ) := by
      simpa [smallRLCDErrorCount] using
        (Nat.lt_floor_add_one ((n : ℝ) ^ (1 - 3 * γ)))
    have hpow : (n : ℝ) ^ (1 - 3 * γ) *
          ((n : ℝ) ^ (-(1 : ℝ) / 2 + 2 * γ)) ^ 2 = (n : ℝ) ^ γ := by
      rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add hn0]
      congr 1
      ring
    calc
      (L * Real.sqrt (Real.log n)) ^ 2 < (n : ℝ) ^ γ := hlog
      _ = (n : ℝ) ^ (1 - 3 * γ) *
          ((n : ℝ) ^ (-(1 : ℝ) / 2 + 2 * γ)) ^ 2 := hpow.symm
      _ < (smallRLCDErrorCount n γ + 1 : ℕ) *
          ((n : ℝ) ^ (-(1 : ℝ) / 2 + 2 * γ)) ^ 2 :=
        mul_lt_mul_of_pos_right hfloor (sq_pos_of_pos hτ)
  have hlargeBudget : ∀ θ, 0 < θ → θ < 2 * Real.sqrt n →
      2 * θ ^ 2 + 2 * (L * Real.sqrt (Real.log n)) ^ 2 <
        (smallRLCDLargeCount n γ + 1 : ℕ) * ((n : ℝ) ^ (2 * γ / 3)) ^ 2 := by
    intro θ hθ hθB
    have hθsq : θ ^ 2 < 4 * (n : ℝ) := by
      have hsqrtSq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
      nlinarith
    have hγone : γ ≤ 1 := by linarith
    have hpowγ : (n : ℝ) ^ γ ≤ (n : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn1 hγone
    have hleft : 2 * θ ^ 2 + 2 * (L * Real.sqrt (Real.log n)) ^ 2 <
        10 * (n : ℝ) := by nlinarith
    have hfloor : 10 * (n : ℝ) ^ (1 - 4 * γ / 3) <
        (smallRLCDLargeCount n γ + 1 : ℕ) := by
      simpa [smallRLCDLargeCount] using
        (Nat.lt_floor_add_one (10 * (n : ℝ) ^ (1 - 4 * γ / 3)))
    have hpow : 10 * (n : ℝ) ^ (1 - 4 * γ / 3) *
          ((n : ℝ) ^ (2 * γ / 3)) ^ 2 = 10 * (n : ℝ) := by
      rw [← Real.rpow_mul_natCast hn0.le]
      calc
        10 * (n : ℝ) ^ (1 - 4 * γ / 3) * (n : ℝ) ^ (2 * γ / 3 * 2) =
            10 * ((n : ℝ) ^ (1 - 4 * γ / 3) *
              (n : ℝ) ^ (2 * γ / 3 * 2)) := by ring
        _ = 10 * (n : ℝ) ^ ((1 - 4 * γ / 3) + (2 * γ / 3 * 2)) := by
          rw [Real.rpow_add hn0]
        _ = 10 * (n : ℝ) := by
          have hexp : (1 - 4 * γ / 3) + (2 * γ / 3 * 2) = (1 : ℝ) := by ring
          rw [hexp, Real.rpow_one]
    calc
      2 * θ ^ 2 + 2 * (L * Real.sqrt (Real.log n)) ^ 2 < 10 * (n : ℝ) := hleft
      _ = 10 * (n : ℝ) ^ (1 - 4 * γ / 3) *
          ((n : ℝ) ^ (2 * γ / 3)) ^ 2 := hpow.symm
      _ < (smallRLCDLargeCount n γ + 1 : ℕ) *
          ((n : ℝ) ^ (2 * γ / 3)) ^ 2 := mul_lt_mul_of_pos_right hfloor (sq_pos_of_pos hT)
  have hrange : (n : ℝ) ^ (2 * γ / 3) < (smallRLCDValueRange n γ + 1 : ℕ) := by
    simpa [smallRLCDValueRange] using
      (Nat.lt_floor_add_one ((n : ℝ) ^ (2 * γ / 3)))
  exact exists_bucketDecomposition_of_small_LCD_of_norm_le
    d (regularizationCard n γ) (smallRLCDBucketCard n γ)
      (Nat.floor ((n : ℝ) ^ (1 - γ))) L (Real.sqrt n)
      ((n : ℝ) ^ (-(1 : ℝ) / 2 + 2 * γ)) (L * Real.sqrt (Real.log n))
      ((n : ℝ) ^ (2 * γ / 3)) ((n : ℝ) ^ ((1 : ℝ) / 2 + 4 * γ))
      (H * n) (smallRLCDValueRange n γ) (smallRLCDErrorCount n γ)
      (smallRLCDLargeCount n γ) hd hblock hsample hL hB hE0 hτ hT hnormPos
      hsupRestrict hLCD hEbound herrorBudget hlargeBudget hrange hcapacity hradius

/-- Kwan--Sah--Sauermann--Sawhney, Lemma 4.12 (small-RLCD bucket
decomposition), with "sufficiently large" represented by `atTop`. -/
theorem KSSS_lemma_4_12 (H γ L : ℝ) (hH : 0 < H) (hγ : 0 < γ)
    (hγ4 : γ < 1 / 4) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (d : Fin n → ℝ),
        (∀ i, 0 ≤ d i) →
        ‖d‖ ≤ H * n →
        (∀ S : Finset (Fin n), S.card = regularizationCard n γ →
          (n : ℝ) ^ ((3 : ℝ) / 2 - 2 * γ) ≤ euclidNorm (restrict d S)) →
        regularizedLCD L γ d ≤ Real.sqrt n →
        ∃ D : BucketDecomposition d (smallRLCDBucketCard n γ)
            ((n : ℝ) ^ ((1 : ℝ) / 2 + 4 * γ)),
          (D.remainder.card : ℝ) ≤ (n : ℝ) ^ (1 - γ) := by
  have hcaplim := ((tendsto_rpow_atTop (div_pos hγ (by norm_num : (0 : ℝ) < 3))).comp
    tendsto_natCast_atTop_atTop).eventually (Filter.eventually_gt_atTop 15)
  have hradlim := ((tendsto_rpow_atTop (mul_pos two_pos hγ)).comp
    tendsto_natCast_atTop_atTop).eventually (Filter.eventually_gt_atTop (2 * H))
  have hhalfg : 0 < γ / 2 := div_pos hγ two_pos
  have hloglim := ((tendsto_rpow_atTop hhalfg).comp
    tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_gt_atTop (L ^ 2 / (γ / 2)))
  filter_upwards [Filter.eventually_ge_atTop 4, hcaplim, hradlim, hloglim] with
      n hn hcapGrowth hradGrowth hlogGrowth
  intro d hd hsup hnorm hsmall
  have hn0 : 0 < (n : ℝ) := by positivity
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogUpper := Real.log_natCast_le_rpow_div n hhalfg
  have hpowhalf : 0 < (n : ℝ) ^ (γ / 2) := Real.rpow_pos_of_pos hn0 _
  have hlog : (L * Real.sqrt (Real.log n)) ^ 2 < (n : ℝ) ^ γ := by
    calc
      (L * Real.sqrt (Real.log n)) ^ 2 = L ^ 2 * Real.log n := by
        rw [mul_pow, Real.sq_sqrt hlog0]
      _ ≤ L ^ 2 * ((n : ℝ) ^ (γ / 2) / (γ / 2)) :=
        mul_le_mul_of_nonneg_left hlogUpper (sq_nonneg L)
      _ = (L ^ 2 / (γ / 2)) * (n : ℝ) ^ (γ / 2) := by ring
      _ < (n : ℝ) ^ (γ / 2) * (n : ℝ) ^ (γ / 2) :=
        mul_lt_mul_of_pos_right hlogGrowth hpowhalf
      _ = (n : ℝ) ^ γ := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring
  have hcapacity := smallRLCD_capacity_of_growth γ hγ hγ4 n (by omega) hcapGrowth
  have hradius : 2 * (H * n) * (n : ℝ) ^ (-(1 : ℝ) / 2 + 2 * γ) ≤
      (n : ℝ) ^ ((1 : ℝ) / 2 + 4 * γ) := by
    have hcore : 2 * H * (n : ℝ) ^ ((1 : ℝ) / 2 + 2 * γ) <
        (n : ℝ) ^ ((1 : ℝ) / 2 + 2 * γ) * (n : ℝ) ^ (2 * γ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_lt_mul_of_pos_left hradGrowth
          (Real.rpow_pos_of_pos hn0 ((1 : ℝ) / 2 + 2 * γ)))
    calc
      2 * (H * n) * (n : ℝ) ^ (-(1 : ℝ) / 2 + 2 * γ) =
          2 * H * (n : ℝ) ^ ((1 : ℝ) / 2 + 2 * γ) := by
        calc
          2 * (H * n) * (n : ℝ) ^ (-(1 : ℝ) / 2 + 2 * γ) =
              2 * H * ((n : ℝ) ^ (1 : ℝ) *
                (n : ℝ) ^ (-(1 : ℝ) / 2 + 2 * γ)) := by
            rw [Real.rpow_one]
            ring
          _ = 2 * H * (n : ℝ) ^
              ((1 : ℝ) + (-(1 : ℝ) / 2 + 2 * γ)) := by
            exact congrArg (fun z : ℝ ↦ 2 * H * z)
              (Real.rpow_add hn0 (1 : ℝ) (-(1 : ℝ) / 2 + 2 * γ)).symm
          _ = 2 * H * (n : ℝ) ^ ((1 : ℝ) / 2 + 2 * γ) := by
            congr 1
            ring
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + 2 * γ) * (n : ℝ) ^ (2 * γ) := hcore.le
      _ = (n : ℝ) ^ ((1 : ℝ) / 2 + 4 * γ) := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring
  obtain ⟨D, hD⟩ := small_RLCD_bucket_decomposition_of_numeric
    H γ L hH hγ hγ4 hL n hn hlog hcapacity hradius d hd hsup hnorm hsmall
  refine ⟨D, ?_⟩
  have hcast : (D.remainder.card : ℝ) ≤
      (Nat.floor ((n : ℝ) ^ (1 - γ)) : ℕ) := by exact_mod_cast hD
  exact hcast.trans (Nat.floor_le
    (Real.rpow_nonneg (show (0 : ℝ) ≤ (n : ℝ) from hn0.le) (1 - γ)))

end RLCD
end Erdos88
