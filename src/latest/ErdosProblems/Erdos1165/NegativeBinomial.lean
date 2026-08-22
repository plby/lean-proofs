/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Probability.Distributions.Geometric

@[expose] public section

/-!
# The negative-binomial law used in the proof of Erdős Problem 1165

Hao--Li--Okada--Zheng expose independent geometric waiting times whose success
probability is `15 / 16`.  The sum of `i` such variables has mass

`choose (i + j - 1) j * (15 / 16)^i * (1 / 16)^j`.

This file develops the algebraic part of that distribution.  We use the
equivalent coefficient `choose (j + (i - 1)) (i - 1)`, because Mathlib's
negative-binomial generating-series lemma is stated in precisely this form.
For positive `i`, `mass_eq_hloz_formula` identifies it with the formula in the
paper.

Mathlib contains the one-variable geometric measure, but (at the time this
file was written) no negative-binomial distribution.  Thus `law` packages the
normalized mass below as a genuine `PMF ℕ`.
-/

open scoped ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory Real Topology

namespace Erdos1165.NegativeBinomial

/-- The stars-and-bars coefficient in the negative-binomial mass. -/
def coefficient (i j : ℕ) : ℕ := (j + (i - 1)).choose (i - 1)

/-- The mass at `j` failures before the `i`-th success, with success probability `p`.

The intended range is `0 < p ≤ 1` and `0 < i`. -/
def mass (p : ℝ) (i j : ℕ) : ℝ := coefficient i j * p ^ i * (1 - p) ^ j

/-- HLOZ's geometric success probability. -/
noncomputable def hlozSuccess : ℝ := 15 / 16

/-- HLOZ's negative-binomial mass `p(i,j)`. -/
noncomputable def hlozMass (i j : ℕ) : ℝ := mass hlozSuccess i j

lemma coefficient_eq_choose_add_sub_one {i : ℕ} (hi : 0 < i) (j : ℕ) :
    coefficient i j = (i + j - 1).choose j := by
  rw [coefficient, show i + j - 1 = j + (i - 1) by omega]
  exact Nat.choose_symm_add.symm

lemma coefficient_eq_multichoose {i : ℕ} (hi : 0 < i) (j : ℕ) :
    coefficient i j = i.multichoose j := by
  rw [coefficient_eq_choose_add_sub_one hi, Nat.multichoose_eq]

lemma coefficient_zero_left (j : ℕ) : coefficient 0 j = 1 := by
  simp [coefficient]

lemma coefficient_zero_right (i : ℕ) : coefficient i 0 = 1 := by
  simp [coefficient]

lemma coefficient_pos {i j : ℕ} (hi : 0 < i) : 0 < coefficient i j := by
  rw [coefficient_eq_multichoose hi, Nat.multichoose_eq]
  exact Nat.choose_pos (by omega)

lemma mass_eq_hloz_formula (p : ℝ) {i : ℕ} (hi : 0 < i) (j : ℕ) :
    mass p i j = (i + j - 1).choose j * p ^ i * (1 - p) ^ j := by
  simp only [mass, coefficient_eq_choose_add_sub_one hi]

lemma mass_zero (p : ℝ) (i : ℕ) : mass p i 0 = p ^ i := by
  simp [mass, coefficient_zero_right]

lemma mass_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i j : ℕ) :
    0 ≤ mass p i j := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

lemma mass_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {i : ℕ} (hi : 0 < i) (j : ℕ) :
    0 < mass p i j := by
  exact mul_pos (mul_pos (Nat.cast_pos.mpr (coefficient_pos hi)) (pow_pos hp0 _))
    (pow_pos (sub_pos.mpr hp1) _)

/-- The ordinary generating series of the negative-binomial coefficients. -/
lemma hasSum_coefficient_mul_pow {r : ℝ} (hr : ‖r‖ < 1) {i : ℕ} (hi : 0 < i) :
    HasSum (fun j : ℕ ↦ (coefficient i j : ℝ) * r ^ j) (1 / (1 - r) ^ i) := by
  simpa only [coefficient, Nat.sub_add_cancel hi] using
    (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (i - 1) hr)

/-- The negative-binomial masses sum to one. -/
lemma hasSum_mass {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {i : ℕ} (hi : 0 < i) :
    HasSum (mass p i) 1 := by
  have hr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have h := (hasSum_coefficient_mul_pow (r := 1 - p) hr hi).mul_left (p ^ i)
  have h' : HasSum (mass p i) (p ^ i * (1 / (1 - (1 - p)) ^ i)) := by
    apply h.congr
    intro j
    simp only [mass]
    ring_nf
  have hv : p ^ i * (1 / (1 - (1 - p)) ^ i) = 1 := by
    have hp : p ≠ 0 := hp0.ne'
    rw [show 1 - (1 - p) = p by ring]
    field_simp
  rw [hv] at h'
  exact h'

lemma summable_mass {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {i : ℕ} (hi : 0 < i) :
    Summable (mass p i) := (hasSum_mass hp0 hp1 hi).summable

lemma tsum_mass {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {i : ℕ} (hi : 0 < i) :
    ∑' j, mass p i j = 1 := (hasSum_mass hp0 hp1 hi).tsum_eq

/-- The negative-binomial probability mass function. -/
noncomputable def law (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (i : ℕ) (hi : 0 < i) : PMF ℕ :=
  ⟨fun j ↦ ENNReal.ofReal (mass p i j), by
    apply ENNReal.hasSum_coe.mpr
    rw [← toNNReal_one]
    exact (hasSum_mass hp0 hp1 hi).toNNReal (mass_nonneg hp0.le hp1 i)⟩

@[simp] lemma law_apply (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (i : ℕ) (hi : 0 < i)
    (j : ℕ) : law p hp0 hp1 i hi j = ENNReal.ofReal (mass p i j) := rfl

lemma coefficient_succ_cross {i : ℕ} (hi : 0 < i) (j : ℕ) :
    coefficient i (j + 1) * (j + 1) = coefficient i j * (i + j) := by
  simp only [coefficient]
  have h := Nat.choose_mul_succ_eq (j + (i - 1)) (i - 1)
  have hsub : j + (i - 1) + 1 - (i - 1) = j + 1 := by omega
  have hsum : j + (i - 1) + 1 = i + j := by omega
  have hsum' : j + 1 + (i - 1) = i + j := by omega
  have hsub' : i + j - (i - 1) = j + 1 := by omega
  simpa only [hsub, hsum, hsum', hsub'] using h.symm

/-- The coefficient identity behind the first moment. -/
lemma coefficient_weighted_succ {i : ℕ} (hi : 0 < i) (j : ℕ) :
    (j + 1) * coefficient i (j + 1) = i * coefficient (i + 1) j := by
  simp only [coefficient]
  have h := Nat.choose_succ_right_eq (j + i) (i - 1)
  have hi' : i - 1 + 1 = i := Nat.sub_add_cancel hi
  have htop : j + 1 + (i - 1) = j + i := by omega
  have htop' : j + (i + 1 - 1) = j + i := by omega
  have hsub : j + i - (i - 1) = j + 1 := by omega
  have hinc : i + 1 - 1 = i := by omega
  simpa only [hi', htop, htop', hsub, hinc, Nat.mul_comm] using h.symm

/-- First derivative of the negative-binomial generating series. -/
lemma hasSum_weighted_coefficient {r : ℝ} (hr : ‖r‖ < 1) {i : ℕ} (hi : 0 < i) :
    HasSum (fun j : ℕ ↦ (j : ℝ) * coefficient i j * r ^ j)
      ((i : ℝ) * r / (1 - r) ^ (i + 1)) := by
  have h := (hasSum_coefficient_mul_pow (r := r) hr (Nat.succ_pos i)).mul_left
    ((i : ℝ) * r)
  have hshift : HasSum
      (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) * coefficient i (j + 1) * r ^ (j + 1))
      ((i : ℝ) * r / (1 - r) ^ (i + 1)) := by
    have heq :
        (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) * coefficient i (j + 1) * r ^ (j + 1)) =
          (fun j : ℕ ↦ (i : ℝ) * r * ((coefficient (i + 1) j : ℝ) * r ^ j)) := by
      funext j
      have hc : (((j + 1) * coefficient i (j + 1) : ℕ) : ℝ) =
          ((i * coefficient (i + 1) j : ℕ) : ℝ) := by
        exact_mod_cast coefficient_weighted_succ hi j
      rw [← Nat.cast_mul, hc, Nat.cast_mul, pow_succ]
      ring
    rw [heq]
    simpa only [Nat.succ_eq_add_one, div_eq_mul_inv, one_mul] using h
  apply (hasSum_nat_add_iff' 1).mp
  simpa [coefficient] using hshift

/-- Second factorial derivative of the negative-binomial generating series. -/
lemma hasSum_factorial_coefficient {r : ℝ} (hr : ‖r‖ < 1) {i : ℕ} (hi : 0 < i) :
    HasSum (fun j : ℕ ↦ (j : ℝ) * (j - 1 : ℕ) * coefficient i j * r ^ j)
      ((i : ℝ) * (i + 1 : ℕ) * r ^ 2 / (1 - r) ^ (i + 2)) := by
  have h := (hasSum_weighted_coefficient (r := r) hr (Nat.succ_pos i)).mul_left
    ((i : ℝ) * r)
  have heq :
      (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) * (j + 1 - 1 : ℕ) * coefficient i (j + 1) *
          r ^ (j + 1)) =
        (fun j : ℕ ↦ (i : ℝ) * r *
          ((j : ℝ) * coefficient (i + 1) j * r ^ j)) := by
    funext j
    have hcNat : (j + 1) * j * coefficient i (j + 1) =
        i * (j * coefficient (i + 1) j) := by
      calc
        (j + 1) * j * coefficient i (j + 1) =
            j * ((j + 1) * coefficient i (j + 1)) := by ring
        _ = j * (i * coefficient (i + 1) j) := by rw [coefficient_weighted_succ hi j]
        _ = i * (j * coefficient (i + 1) j) := by ring
    have hc : (((j + 1) * j * coefficient i (j + 1) : ℕ) : ℝ) =
        ((i * (j * coefficient (i + 1) j) : ℕ) : ℝ) := by
      exact_mod_cast hcNat
    simp only [Nat.add_sub_cancel, ← Nat.cast_mul]
    rw [hc, Nat.cast_mul, pow_succ]
    ring
  have hshift : HasSum
      (fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) * (j + 1 - 1 : ℕ) * coefficient i (j + 1) *
          r ^ (j + 1))
      ((i : ℝ) * (i + 1 : ℕ) * r ^ 2 / (1 - r) ^ (i + 2)) := by
    rw [heq]
    simp only [Nat.succ_eq_add_one] at h
    have hv : (i : ℝ) * r * ((i + 1 : ℕ) * r / (1 - r) ^ (i + 1 + 1)) =
        (i : ℝ) * (i + 1 : ℕ) * r ^ 2 / (1 - r) ^ (i + 2) := by
      rw [show i + 1 + 1 = i + 2 by omega]
      ring
    rw [hv] at h
    exact h
  apply (hasSum_nat_add_iff' 1).mp
  simpa [coefficient] using hshift

/-- The first moment of the negative-binomial law. -/
lemma hasSum_weighted_mass {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {i : ℕ} (hi : 0 < i) :
    HasSum (fun j : ℕ ↦ (j : ℝ) * mass p i j) ((i : ℝ) * (1 - p) / p) := by
  have hr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have h := (hasSum_weighted_coefficient (r := 1 - p) hr hi).mul_left (p ^ i)
  have heq :
      (fun j : ℕ ↦ (j : ℝ) * mass p i j) =
        (fun j : ℕ ↦ p ^ i * ((j : ℝ) * coefficient i j * (1 - p) ^ j)) := by
    funext j
    simp only [mass]
    ring
  rw [heq]
  convert h using 1
  · rfl
  · have hp : p ≠ 0 := hp0.ne'
    rw [show 1 - (1 - p) = p by ring, pow_succ]
    field_simp

lemma tsum_weighted_mass {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {i : ℕ} (hi : 0 < i) :
    ∑' j : ℕ, (j : ℝ) * mass p i j = (i : ℝ) * (1 - p) / p :=
  (hasSum_weighted_mass hp0 hp1 hi).tsum_eq

/-- The second factorial moment of the negative-binomial law. -/
lemma hasSum_factorial_mass {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {i : ℕ} (hi : 0 < i) :
    HasSum (fun j : ℕ ↦ (j : ℝ) * (j - 1 : ℕ) * mass p i j)
      ((i : ℝ) * (i + 1 : ℕ) * (1 - p) ^ 2 / p ^ 2) := by
  have hr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have h := (hasSum_factorial_coefficient (r := 1 - p) hr hi).mul_left (p ^ i)
  have heq :
      (fun j : ℕ ↦ (j : ℝ) * (j - 1 : ℕ) * mass p i j) =
        (fun j : ℕ ↦ p ^ i *
          ((j : ℝ) * (j - 1 : ℕ) * coefficient i j * (1 - p) ^ j)) := by
    funext j
    simp only [mass]
    ring
  rw [heq]
  convert h using 1
  · rfl
  · have hp : p ≠ 0 := hp0.ne'
    rw [show 1 - (1 - p) = p by ring, show i + 2 = (i + 1) + 1 by omega, pow_succ]
    field_simp
    simp only [pow_succ]
    ring

lemma tsum_factorial_mass {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {i : ℕ} (hi : 0 < i) :
    ∑' j : ℕ, (j : ℝ) * (j - 1 : ℕ) * mass p i j =
      (i : ℝ) * (i + 1 : ℕ) * (1 - p) ^ 2 / p ^ 2 :=
  (hasSum_factorial_mass hp0 hp1 hi).tsum_eq

/-- The raw second moment, expressed as factorial moment plus first moment. -/
lemma hasSum_square_mass {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {i : ℕ} (hi : 0 < i) :
    HasSum (fun j : ℕ ↦ (j : ℝ) ^ 2 * mass p i j)
      ((i : ℝ) * (i + 1 : ℕ) * (1 - p) ^ 2 / p ^ 2 +
        (i : ℝ) * (1 - p) / p) := by
  have h := (hasSum_factorial_mass hp0 hp1 hi).add (hasSum_weighted_mass hp0 hp1 hi)
  have heq :
      (fun j : ℕ ↦ (j : ℝ) ^ 2 * mass p i j) =
        (fun j : ℕ ↦ (j : ℝ) * (j - 1 : ℕ) * mass p i j +
          (j : ℝ) * mass p i j) := by
    funext j
    rcases j with _ | j
    · norm_num
    · simp only [Nat.cast_succ, Nat.succ_sub_one]
      ring
  rw [heq]
  exact h

lemma tsum_square_mass {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {i : ℕ} (hi : 0 < i) :
    ∑' j : ℕ, (j : ℝ) ^ 2 * mass p i j =
      (i : ℝ) * (i + 1 : ℕ) * (1 - p) ^ 2 / p ^ 2 +
        (i : ℝ) * (1 - p) / p :=
  (hasSum_square_mass hp0 hp1 hi).tsum_eq

/-- Division-free consecutive-mass ratio identity. -/
lemma mass_succ_cross {p : ℝ} {i : ℕ} (hi : 0 < i) (j : ℕ) :
    mass p i (j + 1) * (j + 1) = mass p i j * (i + j) * (1 - p) := by
  have hc : (coefficient i (j + 1) : ℝ) * (j + 1) =
      (coefficient i j : ℝ) * (i + j) := by
    exact_mod_cast coefficient_succ_cross hi j
  simp only [mass, pow_succ]
  calc
    (coefficient i (j + 1) : ℝ) * p ^ i * ((1 - p) ^ j * (1 - p)) * (j + 1) =
        ((coefficient i (j + 1) : ℝ) * (j + 1)) * p ^ i * (1 - p) ^ j *
          (1 - p) := by ring
    _ = ((coefficient i j : ℝ) * (i + j)) * p ^ i * (1 - p) ^ j * (1 - p) := by
      rw [hc]
    _ = (coefficient i j : ℝ) * p ^ i * (1 - p) ^ j * (i + j) * (1 - p) := by
      ring

/-- Exact ratio of consecutive positive masses. -/
lemma mass_succ_div_mass {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {i : ℕ} (hi : 0 < i)
    (j : ℕ) :
    mass p i (j + 1) / mass p i j = ((i + j : ℕ) : ℝ) * (1 - p) / (j + 1) := by
  have hm : mass p i j ≠ 0 := (mass_pos hp0 hp1 hi j).ne'
  have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  simpa [mul_assoc, mul_left_comm, mul_comm] using mass_succ_cross (p := p) hi j

/-- A comparison form useful for unimodality: the mass rises exactly while the
cross-multiplied ratio is at least one. -/
lemma mass_le_mass_succ_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {i : ℕ} (hi : 0 < i)
    (j : ℕ) :
    mass p i j ≤ mass p i (j + 1) ↔
      (j + 1 : ℝ) ≤ (i + j : ℕ) * (1 - p) := by
  have hm : 0 < mass p i j := mass_pos hp0 hp1 hi j
  have hj : (0 : ℝ) < j + 1 := by positivity
  calc
    mass p i j ≤ mass p i (j + 1) ↔
        mass p i j / mass p i j ≤ mass p i (j + 1) / mass p i j :=
      (div_le_div_iff_of_pos_right hm).symm
    _ ↔ 1 ≤ ((i + j : ℕ) : ℝ) * (1 - p) / (j + 1) := by
      rw [div_self hm.ne', mass_succ_div_mass hp0 hp1 hi]
    _ ↔ (j + 1 : ℝ) ≤ (i + j : ℕ) * (1 - p) := by
      rw [le_div_iff₀ hj]
      simp

lemma mass_succ_le_mass_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {i : ℕ} (hi : 0 < i)
    (j : ℕ) :
    mass p i (j + 1) ≤ mass p i j ↔
      (i + j : ℕ) * (1 - p) ≤ (j + 1 : ℝ) := by
  have hm : 0 < mass p i j := mass_pos hp0 hp1 hi j
  have hj : (0 : ℝ) < j + 1 := by positivity
  calc
    mass p i (j + 1) ≤ mass p i j ↔
        mass p i (j + 1) / mass p i j ≤ mass p i j / mass p i j :=
      (div_le_div_iff_of_pos_right hm).symm
    _ ↔ ((i + j : ℕ) : ℝ) * (1 - p) / (j + 1) ≤ 1 := by
      rw [div_self hm.ne', mass_succ_div_mass hp0 hp1 hi]
    _ ↔ (i + j : ℕ) * (1 - p) ≤ (j + 1 : ℝ) := by
      rw [div_le_iff₀ hj]
      simp

/-- At HLOZ's parameter the exact consecutive-mass ratio is
`(i+j)/(16(j+1))`. -/
lemma hlozMass_succ_div (i : ℕ) (hi : 0 < i) (j : ℕ) :
    hlozMass i (j + 1) / hlozMass i j = (i + j : ℕ) / (16 * (j + 1 : ℕ)) := by
  simp only [hlozMass]
  rw [mass_succ_div_mass (p := hlozSuccess) (by norm_num [hlozSuccess])
    (by norm_num [hlozSuccess]) hi]
  norm_num [hlozSuccess]
  field_simp

/-- Exact rising-side criterion for the HLOZ mass. -/
lemma hlozMass_le_succ_iff {i : ℕ} (hi : 0 < i) (j : ℕ) :
    hlozMass i j ≤ hlozMass i (j + 1) ↔ 15 * j + 16 ≤ i := by
  simp only [hlozMass]
  rw [mass_le_mass_succ_iff (p := hlozSuccess) (by norm_num [hlozSuccess])
    (by norm_num [hlozSuccess]) hi]
  constructor
  · intro h
    have h' : 15 * (j : ℝ) + 16 ≤ (i : ℝ) := by
      norm_num [hlozSuccess] at h
      linarith
    exact_mod_cast h'
  · intro h
    have h' : 15 * (j : ℝ) + 16 ≤ (i : ℝ) := by exact_mod_cast h
    norm_num [hlozSuccess]
    linarith

/-- Exact falling-side criterion for the HLOZ mass.  Together with
`hlozMass_le_succ_iff`, this is the unimodality statement used when comparing
nearby local-time probabilities. -/
lemma hlozMass_succ_le_iff {i : ℕ} (hi : 0 < i) (j : ℕ) :
    hlozMass i (j + 1) ≤ hlozMass i j ↔ i ≤ 15 * j + 16 := by
  simp only [hlozMass]
  rw [mass_succ_le_mass_iff (p := hlozSuccess) (by norm_num [hlozSuccess])
    (by norm_num [hlozSuccess]) hi]
  constructor
  · intro h
    have h' : (i : ℝ) ≤ 15 * (j : ℝ) + 16 := by
      norm_num [hlozSuccess] at h
      linarith
    exact_mod_cast h'
  · intro h
    have h' : (i : ℝ) ≤ 15 * (j : ℝ) + 16 := by exact_mod_cast h
    norm_num [hlozSuccess]
    linarith

lemma hlozMass_nonneg (i j : ℕ) : 0 ≤ hlozMass i j := by
  exact mass_nonneg (by norm_num [hlozSuccess]) (by norm_num [hlozSuccess]) i j

lemma hlozMass_pos {i : ℕ} (hi : 0 < i) (j : ℕ) : 0 < hlozMass i j := by
  exact mass_pos (by norm_num [hlozSuccess]) (by norm_num [hlozSuccess]) hi j

lemma hasSum_hlozMass {i : ℕ} (hi : 0 < i) : HasSum (hlozMass i) 1 := by
  exact hasSum_mass (by norm_num [hlozSuccess]) (by norm_num [hlozSuccess]) hi

lemma tsum_hlozMass {i : ℕ} (hi : 0 < i) : ∑' j, hlozMass i j = 1 :=
  (hasSum_hlozMass hi).tsum_eq

/-- The HLOZ mass packaged as a probability mass function. -/
noncomputable def hlozLaw (i : ℕ) (hi : 0 < i) : PMF ℕ :=
  law hlozSuccess (by norm_num [hlozSuccess]) (by norm_num [hlozSuccess]) i hi

@[simp] lemma hlozLaw_apply (i : ℕ) (hi : 0 < i) (j : ℕ) :
    hlozLaw i hi j = ENNReal.ofReal (hlozMass i j) := rfl

/-- The HLOZ law is centered at `i / 15`. -/
lemma hasSum_weighted_hlozMass {i : ℕ} (hi : 0 < i) :
    HasSum (fun j : ℕ ↦ (j : ℝ) * hlozMass i j) ((i : ℝ) / 15) := by
  have h := hasSum_weighted_mass (p := hlozSuccess) (by norm_num [hlozSuccess])
    (by norm_num [hlozSuccess]) hi
  have hv : (i : ℝ) * (1 - hlozSuccess) / hlozSuccess = (i : ℝ) / 15 := by
    norm_num [hlozSuccess]
    ring
  rw [hv] at h
  simpa only [hlozMass] using h

lemma tsum_weighted_hlozMass {i : ℕ} (hi : 0 < i) :
    ∑' j : ℕ, (j : ℝ) * hlozMass i j = (i : ℝ) / 15 :=
  (hasSum_weighted_hlozMass hi).tsum_eq

/-- The second factorial moment is `i(i+1)/225`. -/
lemma hasSum_factorial_hlozMass {i : ℕ} (hi : 0 < i) :
    HasSum (fun j : ℕ ↦ (j : ℝ) * (j - 1 : ℕ) * hlozMass i j)
      ((i : ℝ) * (i + 1 : ℕ) / 225) := by
  have h := hasSum_factorial_mass (p := hlozSuccess) (by norm_num [hlozSuccess])
    (by norm_num [hlozSuccess]) hi
  have hv : (i : ℝ) * (i + 1 : ℕ) * (1 - hlozSuccess) ^ 2 / hlozSuccess ^ 2 =
      (i : ℝ) * (i + 1 : ℕ) / 225 := by
    norm_num [hlozSuccess]
    ring
  rw [hv] at h
  simpa only [hlozMass] using h

/-- The raw second moment is `i(i+16)/225`. -/
lemma hasSum_square_hlozMass {i : ℕ} (hi : 0 < i) :
    HasSum (fun j : ℕ ↦ (j : ℝ) ^ 2 * hlozMass i j)
      ((i : ℝ) * (i + 16 : ℕ) / 225) := by
  have h := hasSum_square_mass (p := hlozSuccess) (by norm_num [hlozSuccess])
    (by norm_num [hlozSuccess]) hi
  have hv :
      (i : ℝ) * (i + 1 : ℕ) * (1 - hlozSuccess) ^ 2 / hlozSuccess ^ 2 +
          (i : ℝ) * (1 - hlozSuccess) / hlozSuccess =
        (i : ℝ) * (i + 16 : ℕ) / 225 := by
    norm_num [hlozSuccess]
    ring
  rw [hv] at h
  simpa only [hlozMass] using h

/-- The centered second moment (variance) is `16 i / 225`, the value denoted
`i σ²` in HLOZ, where `σ² = 16/225`. -/
lemma hasSum_variance_hlozMass {i : ℕ} (hi : 0 < i) :
    HasSum (fun j : ℕ ↦ ((j : ℝ) - (i : ℝ) / 15) ^ 2 * hlozMass i j)
      (16 * (i : ℝ) / 225) := by
  let μ : ℝ := (i : ℝ) / 15
  have h2 := hasSum_square_hlozMass hi
  have h1 := hasSum_weighted_hlozMass hi
  have h0 := hasSum_hlozMass hi
  have h := (h2.add (h1.mul_left (-2 * μ))).add (h0.mul_left (μ ^ 2))
  have heq :
      (fun j : ℕ ↦ ((j : ℝ) - (i : ℝ) / 15) ^ 2 * hlozMass i j) =
        (fun j : ℕ ↦ (j : ℝ) ^ 2 * hlozMass i j +
          (-2 * μ) * ((j : ℝ) * hlozMass i j) + μ ^ 2 * hlozMass i j) := by
    funext j
    dsimp only [μ]
    ring
  have hv : (i : ℝ) * (i + 16 : ℕ) / 225 + (-2 * μ) * ((i : ℝ) / 15) +
      μ ^ 2 * 1 = 16 * (i : ℝ) / 225 := by
    dsimp only [μ]
    push_cast
    ring
  rw [hv] at h
  rw [heq]
  exact h

lemma tsum_variance_hlozMass {i : ℕ} (hi : 0 < i) :
    ∑' j : ℕ, ((j : ℝ) - (i : ℝ) / 15) ^ 2 * hlozMass i j =
      16 * (i : ℝ) / 225 :=
  (hasSum_variance_hlozMass hi).tsum_eq

/-- The exact HLOZ formula quoted in the paper. -/
lemma hlozMass_formula {i : ℕ} (hi : 0 < i) (j : ℕ) :
    hlozMass i j = (i + j - 1).choose j * (15 / 16 : ℝ) ^ i * (1 / 16 : ℝ) ^ j := by
  rw [hlozMass, mass_eq_hloz_formula _ hi]
  norm_num [hlozSuccess]

end Erdos1165.NegativeBinomial
