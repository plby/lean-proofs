/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Arithmetic for the density-increment step in Erdős 171

This file isolates the real-number bookkeeping in the Dodos--Kanellopoulos--Tyros
proof of density Hales--Jewett.  It contains no combinatorial definitions.  The
constants are

* `theta δ q = δ / (4q)`, where `q` is the number of lines in a fixed cube;
* `eta δ θ = δθ / 48`;
* `gamma δ η k = δη² / k`.

The remaining lemmas are the numerical estimates used in Lemmas 8 and 10,
Corollary 11, and the last tiling/averaging step of that proof.
-/

namespace Erdos171.IncrementArithmetic

open scoped BigOperators

/-- The line-correlation threshold, with `q` possible line templates. -/
noncomputable def theta (δ q : ℝ) : ℝ := δ / (4 * q)

/-- The error parameter in the DKT density-increment argument. -/
noncomputable def eta (δ θ : ℝ) : ℝ := δ * θ / 48

/-- The density increment supplied by a structured set. -/
noncomputable def gamma (δ η k : ℝ) : ℝ := δ * η ^ 2 / k

theorem theta_pos {δ q : ℝ} (hδ : 0 < δ) (hq : 0 < q) :
    0 < theta δ q := by
  unfold theta
  positivity

theorem theta_le_delta_div_four {δ q : ℝ} (hδ : 0 ≤ δ) (hq : 1 ≤ q) :
    theta δ q ≤ δ / 4 := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  unfold theta
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * q) (by norm_num)).2
  nlinarith [mul_le_mul_of_nonneg_left hq hδ]

theorem eta_pos {δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) :
    0 < eta δ θ := by
  unfold eta
  positivity

theorem gamma_pos {δ η k : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hk : 0 < k) :
    0 < gamma δ η k := by
  unfold gamma
  positivity

/-- In the paper `δ ≤ 1`; this very coarse estimate is enough to make the
two large sets in Lemma 8 intersect. -/
theorem eta_lt_theta_div_two {δ θ : ℝ}
    (hδ_one : δ ≤ 1) (hθ : 0 < θ) :
    eta δ θ < θ / 2 := by
  have hmul : δ * θ ≤ θ := by
    simpa using mul_le_mul_of_nonneg_right hδ_one hθ.le
  unfold eta
  nlinarith

/-- A convenient bound ensuring that removing `3η` leaves positive density. -/
theorem three_eta_lt_delta {δ θ : ℝ}
    (hδ : 0 < δ) (hθ_one : θ ≤ 1) :
    3 * eta δ θ < δ := by
  have hmul : δ * θ ≤ δ := by
    simpa using mul_le_mul_of_nonneg_left hθ_one hδ.le
  unfold eta
  nlinarith

theorem eta_lt_one {δ θ : ℝ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) (hθ : 0 < θ) (hθ_one : θ ≤ 1) :
    eta δ θ < 1 := by
  have hη := eta_pos hδ hθ
  have hmul_delta : δ * θ ≤ δ := by
    simpa using mul_le_mul_of_nonneg_left hθ_one hδ.le
  have hmul : δ * θ ≤ 1 := hmul_delta.trans hδ_one
  unfold eta at hη ⊢
  nlinarith

/-- The first branch of Corollary 11 has an increment at least `γ`. -/
theorem gamma_le_eta_sq_div_two {δ η k : ℝ}
    (_hδ_nonneg : 0 ≤ δ) (hδ_one : δ ≤ 1) (hk : 2 ≤ k) :
    gamma δ η k ≤ η ^ 2 / 2 := by
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hηsq : 0 ≤ η ^ 2 := sq_nonneg η
  have hleft : δ * η ^ 2 ≤ η ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right hδ_one hηsq
  have hright : η ^ 2 ≤ (η ^ 2 / 2) * k := by
    nlinarith [mul_le_mul_of_nonneg_left hk hηsq]
  unfold gamma
  rw [div_le_iff₀ hkpos]
  exact hleft.trans hright

/-- The structured-set increment is much smaller than the `3η` relative
increment selected in the partition argument. -/
theorem gamma_lt_three_eta {δ η k : ℝ}
    (hδ_nonneg : 0 ≤ δ) (hδ_one : δ ≤ 1)
    (hη : 0 < η) (hη_one : η < 1) (hk : 2 ≤ k) :
    gamma δ η k < 3 * η := by
  have hγ := gamma_le_eta_sq_div_two (η := η) hδ_nonneg hδ_one hk
  nlinarith [mul_pos hη (sub_pos.mpr hη_one)]

/-- The scalar contradiction used to show that the set `H₁` in Lemma 8 has
density greater than `1 - η`. -/
theorem bad_fiber_average_lt {δ η : ℝ} (hη : 0 < η) :
    η * (δ - 2 * η) + (1 - η) * (δ + η ^ 2 / 2) < δ - η ^ 2 / 2 := by
  nlinarith [sq_pos_of_pos hη, mul_pos (sq_pos_of_pos hη) hη]

/-- The scalar contradiction used to show that the set `H₂` in Lemma 8 has
density greater than `θ/2`. -/
theorem line_rich_average_lt {θ : ℝ} (hθ : 0 < θ) :
    θ / 2 + (1 - θ / 2) * (θ / 2) < θ := by
  nlinarith [sq_pos_of_pos hθ]

/-- The lower bound for the density of the structured set in Lemma 10. -/
theorem theta_div_four_lt {θ η : ℝ} (hθ : 0 < θ) (hη : η < 1 / 2) :
    θ / 4 < (θ / 2) * (1 - η) := by
  have hprod : 0 < θ * (1 - 2 * η) :=
    mul_pos hθ (by nlinarith)
  nlinarith

/-- The main conditional-density calculation in Lemma 10.

After deleting a structured set of density at least `θ/4`, at most `3η` of
the mass of `A` has been lost.  With the paper's choice `η = δθ/48`, the
remaining conditional density is strictly larger than `δ + 6η`.
-/
theorem conditional_density_increment {δ θ : ℝ}
    (hδ : 0 < δ) (hθ : 0 < θ) (hθ_four : θ < 4) :
    δ + 6 * eta δ θ < (δ - 3 * eta δ θ) / (1 - θ / 4) := by
  have hden : 0 < 1 - θ / 4 := by nlinarith
  rw [lt_div_iff₀ hden]
  unfold eta
  have hδθ : 0 < δ * θ := mul_pos hδ hθ
  have hδθθ : 0 ≤ (δ * θ) * θ := mul_nonneg hδθ.le hθ.le
  nlinarith

/-- The multiplicative form of the conditional-density estimate with
parameters frozen at a lower density `δ₀`, but the current density equal to
some `ρ ≥ δ₀`.  This is the form needed for a rigorous density-increment
iteration with a fixed positive increment. -/
theorem fixed_lower_density_increment_mul {δ₀ ρ θ : ℝ}
    (hδ₀ : 0 < δ₀) (hδρ : δ₀ ≤ ρ) (hθ : 0 < θ) :
    (ρ + 6 * eta δ₀ θ) * (1 - θ / 4) < ρ - 3 * eta δ₀ θ := by
  have hρθ : δ₀ * θ ≤ ρ * θ :=
    mul_le_mul_of_nonneg_right hδρ hθ.le
  have hδθ : 0 < δ₀ * θ := mul_pos hδ₀ hθ
  have hδθθ : 0 ≤ (δ₀ * θ) * θ := mul_nonneg hδθ.le hθ.le
  unfold eta
  nlinarith

/-- Quotient form of `fixed_lower_density_increment_mul`.  The paper has
`0 < θ ≤ 1`, which in particular makes the denominator positive. -/
theorem fixed_lower_conditional_density_increment {δ₀ ρ θ : ℝ}
    (hδ₀ : 0 < δ₀) (hδρ : δ₀ ≤ ρ)
    (hθ : 0 < θ) (hθ_one : θ ≤ 1) :
    ρ + 6 * eta δ₀ θ < (ρ - 3 * eta δ₀ θ) / (1 - θ / 4) := by
  have hden : 0 < 1 - θ / 4 := by nlinarith
  rw [lt_div_iff₀ hden]
  exact fixed_lower_density_increment_mul hδ₀ hδρ hθ

/-- The density of the structured piece selected in Corollary 11 exceeds
`γ`.  The hypotheses `δ,θ ≤ 1` are the coarse bounds available in DKT. -/
theorem gamma_lt_structured_piece {δ θ k : ℝ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hθ : 0 < θ) (hθ_one : θ ≤ 1) (hk : 0 < k) :
    gamma δ (eta δ θ) k <
      (3 * eta δ θ / k) * (δ - 3 * eta δ θ) := by
  have hη : 0 < eta δ θ := eta_pos hδ hθ
  have hη_le : eta δ θ ≤ δ / 48 := by
    unfold eta
    have := mul_le_mul_of_nonneg_left hθ_one hδ.le
    nlinarith
  have hδη : δ * eta δ θ ≤ eta δ θ := by
    simpa using mul_le_mul_of_nonneg_right hδ_one hη.le
  have hinside : 0 < 3 * δ - δ * eta δ θ - 9 * eta δ θ := by
    nlinarith
  have hnum : δ * (eta δ θ) ^ 2 <
      3 * eta δ θ * (δ - 3 * eta δ θ) := by
    nlinarith [mul_pos hη hinside]
  unfold gamma
  calc
    δ * eta δ θ ^ 2 / k <
        (3 * eta δ θ * (δ - 3 * eta δ θ)) / k :=
      (div_lt_div_iff_of_pos_right hk).2 hnum
    _ = (3 * eta δ θ / k) * (δ - 3 * eta δ θ) := by ring

/-- The structured-piece estimate at a current density `ρ`, while `eta` and
`gamma` remain frozen at the original lower density `δ₀`. -/
theorem fixed_gamma_lt_structured_piece {δ₀ ρ θ k : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀_one : δ₀ ≤ 1) (hδρ : δ₀ ≤ ρ)
    (hθ : 0 < θ) (hθ_one : θ ≤ 1) (hk : 0 < k) :
    gamma δ₀ (eta δ₀ θ) k <
      (3 * eta δ₀ θ / k) * (ρ - 3 * eta δ₀ θ) := by
  have hbase := gamma_lt_structured_piece hδ₀ hδ₀_one hθ hθ_one hk
  have hcoef : 0 ≤ 3 * eta δ₀ θ / k := by
    exact div_nonneg (mul_nonneg (by norm_num) (eta_pos hδ₀ hθ).le) hk.le
  have hmono :
      (3 * eta δ₀ θ / k) * (δ₀ - 3 * eta δ₀ θ) ≤
        (3 * eta δ₀ θ / k) * (ρ - 3 * eta δ₀ θ) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hcoef
  exact hbase.trans_le hmono

/-- All coarse bounds on the frozen DKT parameters used by the iteration,
packaged so later files do not have to reproduce their arithmetic. -/
theorem fixed_parameter_bounds {δ₀ θ k : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀_one : δ₀ ≤ 1)
    (hθ : 0 < θ) (hθ_one : θ ≤ 1) (hk : 2 ≤ k) :
    let η := eta δ₀ θ
    let γ := gamma δ₀ η k
    0 < η ∧ η < θ / 2 ∧ 3 * η < δ₀ ∧
      0 < γ ∧ γ ≤ η ^ 2 / 2 ∧ γ < 3 * η ∧
      γ < δ₀ ∧ γ < 1 ∧ γ < 2 := by
  dsimp only
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hη : 0 < eta δ₀ θ := eta_pos hδ₀ hθ
  have hηθ : eta δ₀ θ < θ / 2 := eta_lt_theta_div_two hδ₀_one hθ
  have h3η : 3 * eta δ₀ θ < δ₀ := three_eta_lt_delta hδ₀ hθ_one
  have hηone : eta δ₀ θ < 1 := eta_lt_one hδ₀ hδ₀_one hθ hθ_one
  have hγ : 0 < gamma δ₀ (eta δ₀ θ) k := gamma_pos hδ₀ hη hkpos
  have hγsq : gamma δ₀ (eta δ₀ θ) k ≤ (eta δ₀ θ) ^ 2 / 2 :=
    gamma_le_eta_sq_div_two hδ₀.le hδ₀_one hk
  have hγ3 : gamma δ₀ (eta δ₀ θ) k < 3 * eta δ₀ θ :=
    gamma_lt_three_eta hδ₀.le hδ₀_one hη hηone hk
  have hγδ : gamma δ₀ (eta δ₀ θ) k < δ₀ := hγ3.trans h3η
  exact ⟨hη, hηθ, h3η, hγ, hγsq, hγ3, hγδ,
    hγδ.trans_le hδ₀_one,
    lt_trans (hγδ.trans_le hδ₀_one) (by norm_num)⟩

/-- In particular, the frozen increment stays below every later density
`ρ ≥ δ₀`. -/
theorem fixed_gamma_lt_current_density {δ₀ ρ θ k : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀_one : δ₀ ≤ 1) (hδρ : δ₀ ≤ ρ)
    (hθ : 0 < θ) (hθ_one : θ ≤ 1) (hk : 2 ≤ k) :
    gamma δ₀ (eta δ₀ θ) k < ρ := by
  have hbounds := fixed_parameter_bounds hδ₀ hδ₀_one hθ hθ_one hk
  exact hbounds.2.2.2.2.2.2.1.trans_le hδρ

/-- A weighted partition whose total relative density is too large has a
part which is simultaneously non-negligible and has increased relative
density.  This is the averaging step in Corollary 11.

The estimate deliberately overcounts every small-weight part by `3η/k`.
This avoids introducing a filtered subpartition and is convenient in Lean.
-/
theorem exists_large_weight_and_value
    {ι : Type*} (s : Finset ι) (weight value : ι → ℝ)
    {k δ η : ℝ}
    (hk : 0 < k) (hcard : (s.card : ℝ) ≤ k) (hη : 0 < η)
    (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hvalue : ∀ i ∈ s, value i ≤ 1)
    (hweight_sum : ∑ i ∈ s, weight i = 1)
    (hbase : 0 ≤ δ + 3 * η)
    (haverage : δ + 6 * η < ∑ i ∈ s, weight i * value i) :
    ∃ i ∈ s, 3 * η / k < weight i ∧ δ + 3 * η < value i := by
  classical
  by_contra! hnone
  have hlarge : ∀ i ∈ s, 3 * η / k < weight i → value i ≤ δ + 3 * η := by
    intro i hi hwi
    exact hnone i hi hwi
  have hsmall_nonneg : 0 ≤ 3 * η / k := by positivity
  have hpoint : ∀ i ∈ s,
      weight i * value i ≤ 3 * η / k + (δ + 3 * η) * weight i := by
    intro i hi
    by_cases hsmall : weight i ≤ 3 * η / k
    · have hmul : weight i * value i ≤ weight i := by
        simpa using mul_le_mul_of_nonneg_left (hvalue i hi) (hweight i hi)
      have htail : 0 ≤ (δ + 3 * η) * weight i :=
        mul_nonneg hbase (hweight i hi)
      linarith
    · have hwi : 3 * η / k < weight i := lt_of_not_ge hsmall
      have hmul := mul_le_mul_of_nonneg_left (hlarge i hi hwi) (hweight i hi)
      nlinarith
  have hsum_le :
      (∑ i ∈ s, weight i * value i) ≤
        ∑ i ∈ s, (3 * η / k + (δ + 3 * η) * weight i) := by
    gcongr with i hi
    exact hpoint i hi
  have hcard_mul : (s.card : ℝ) * (3 * η / k) ≤ 3 * η := by
    have hmul := mul_le_mul_of_nonneg_right hcard
      (show (0 : ℝ) ≤ 3 * η by positivity)
    have heq : (s.card : ℝ) * (3 * η / k) =
        ((s.card : ℝ) * (3 * η)) / k := by ring
    rw [heq, div_le_iff₀ hk]
    nlinarith [hmul]
  have hsum_rhs :
      (∑ i ∈ s, (3 * η / k + (δ + 3 * η) * weight i)) =
        (s.card : ℝ) * (3 * η / k) + (δ + 3 * η) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum, hweight_sum, mul_one]
  rw [hsum_rhs] at hsum_le
  linarith

/-- Removing mass less than `γ²/2` from a structured set of density greater
than `γ` preserves a density increment of `γ/2` on its covered part.

Here `d` is the mass of the structured set, `u` the covered mass, `r` the
uncovered mass, and `c` the mass of `A` on the covered part.
-/
theorem uncovered_mass_density_increment
    {δ γ d u r c : ℝ}
    (hδ : 0 ≤ δ) (hγ : 0 < γ) (hd : γ < d)
    (hr : r < γ ^ 2 / 2) (hu : u ≤ d)
    (hc : (δ + γ) * d - r ≤ c) :
    (δ + γ / 2) * u < c := by
  have hcoefficient : 0 ≤ δ + γ / 2 := by positivity
  have hutarget : (δ + γ / 2) * u ≤ (δ + γ / 2) * d :=
    mul_le_mul_of_nonneg_left hu hcoefficient
  have hgap : r < (γ / 2) * d := by
    nlinarith [mul_lt_mul_of_pos_left hd hγ]
  nlinarith

/-- The error threshold in the final tiling is exactly `γ²/2`. -/
theorem tiling_error_identity {γ k : ℝ} (hk : k ≠ 0) :
    2 * k * (γ ^ 2 / (4 * k)) = γ ^ 2 / 2 := by
  field_simp
  ring

/-- A positive increment smaller than `2` dominates the final tiling error. -/
theorem tiling_error_lt_gamma {γ : ℝ} (hγ : 0 < γ) (hγ_two : γ < 2) :
    γ ^ 2 / 2 < γ := by
  nlinarith [mul_pos hγ (sub_pos.mpr hγ_two)]

end Erdos171.IncrementArithmetic
