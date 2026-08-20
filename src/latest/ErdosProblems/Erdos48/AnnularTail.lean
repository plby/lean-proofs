/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.LocalZeroMultiplicity

/-!
# Dyadic annular bounds for reciprocal zero sums

The zero detector sees the zeros in a very small disk.  To compare that
finite power sum with the logarithmic derivative, one must bound the zeros
outside the small disk.  This file supplies the purely finite dyadic
decomposition used for that purpose.
-/

namespace Erdos48

open scoped BigOperators
open Metric

noncomputable section

/-- The `k`-th dyadic annulus in the support of a natural-valued `Finsupp`. -/
noncomputable def dyadicAnnularShell (Z : ℂ →₀ ℕ) (z : ℂ) (r : ℝ)
    (k : ℕ) : Finset ℂ :=
  Z.support.filter fun rho ↦
    r * (2 : ℝ) ^ k < dist rho z ∧
      dist rho z ≤ r * (2 : ℝ) ^ (k + 1)

theorem pairwiseDisjoint_dyadicAnnularShell
    (Z : ℂ →₀ ℕ) (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    ((Finset.range N : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (dyadicAnnularShell Z z r) := by
  classical
  intro i hi j hj hij
  change Disjoint (dyadicAnnularShell Z z r i)
    (dyadicAnnularShell Z z r j)
  rw [Finset.disjoint_left]
  intro rho hri hrj
  rw [dyadicAnnularShell, Finset.mem_filter] at hri hrj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hpow : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hrad : r * (2 : ℝ) ^ (i + 1) ≤ r * (2 : ℝ) ^ j :=
      mul_le_mul_of_nonneg_left hpow hr
    linarith [hri.2.2, hrj.2.1]
  · have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ i := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hrad : r * (2 : ℝ) ^ (j + 1) ≤ r * (2 : ℝ) ^ i :=
      mul_le_mul_of_nonneg_left hpow hr
    linarith [hrj.2.2, hri.2.1]

private theorem exists_dyadic_shell_index
    {r d : ℝ} (hr : 0 < r) {N : ℕ}
    (hlower : r < d) (hupper : d ≤ r * (2 : ℝ) ^ N) :
    ∃ k < N,
      r * (2 : ℝ) ^ k < d ∧ d ≤ r * (2 : ℝ) ^ (k + 1) := by
  induction N with
  | zero => simp at hupper; linarith
  | succ N ih =>
      by_cases hN : d ≤ r * (2 : ℝ) ^ N
      · obtain ⟨k, hkN, hk⟩ := ih hN
        exact ⟨k, by omega, hk⟩
      · refine ⟨N, by omega, lt_of_not_ge hN, ?_⟩
        simpa only [Nat.succ_eq_add_one] using hupper

/-- The first `N` dyadic annuli exactly cover the part of the support whose
distance lies in `(r, 2^N r]`. -/
theorem biUnion_dyadicAnnularShell
    (Z : ℂ →₀ ℕ) (z : ℂ) {r : ℝ} (hr : 0 < r) (N : ℕ) :
    (Finset.range N).biUnion (dyadicAnnularShell Z z r) =
      Z.support.filter fun rho ↦
        r < dist rho z ∧ dist rho z ≤ r * (2 : ℝ) ^ N := by
  classical
  ext rho
  constructor
  · intro hrho
    rw [Finset.mem_biUnion] at hrho
    obtain ⟨k, hk, hrhok⟩ := hrho
    rw [dyadicAnnularShell, Finset.mem_filter] at hrhok
    rw [Finset.mem_filter]
    refine ⟨hrhok.1, ?_, ?_⟩
    · have hone : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
        one_le_pow₀ (by norm_num)
      exact lt_of_le_of_lt (by
        simpa using mul_le_mul_of_nonneg_left hone hr.le) hrhok.2.1
    · have hkN : k + 1 ≤ N := by
        have := Finset.mem_range.mp hk
        omega
      exact hrhok.2.2.trans <| mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) hkN) hr.le
  · intro hrho
    rw [Finset.mem_filter] at hrho
    obtain ⟨k, hkN, hk⟩ :=
      exists_dyadic_shell_index hr hrho.2.1 hrho.2.2
    rw [Finset.mem_biUnion]
    refine ⟨k, Finset.mem_range.mpr hkN, ?_⟩
    rw [dyadicAnnularShell, Finset.mem_filter]
    exact ⟨hrho.1, hk⟩

/-- The reciprocal-power contribution of one annulus is bounded by its
multiplicity divided by the inner radius to the given power. -/
theorem norm_sum_dyadicAnnularShell_div_pow_le
    (Z : ℂ →₀ ℕ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (k j : ℕ) :
    ‖∑ rho ∈ dyadicAnnularShell Z z r k,
        (Z rho : ℂ) / (z - rho) ^ j‖ ≤
      (∑ rho ∈ dyadicAnnularShell Z z r k, (Z rho : ℝ)) /
        (r * (2 : ℝ) ^ k) ^ j := by
  calc
    ‖∑ rho ∈ dyadicAnnularShell Z z r k,
        (Z rho : ℂ) / (z - rho) ^ j‖ ≤
        ∑ rho ∈ dyadicAnnularShell Z z r k,
          ‖(Z rho : ℂ) / (z - rho) ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ dyadicAnnularShell Z z r k,
          (Z rho : ℝ) / (r * (2 : ℝ) ^ k) ^ j := by
      apply Finset.sum_le_sum
      intro rho hrho
      rw [dyadicAnnularShell, Finset.mem_filter] at hrho
      rw [norm_div, norm_pow, norm_natCast]
      have hinner : 0 < r * (2 : ℝ) ^ k := by positivity
      have hdist : r * (2 : ℝ) ^ k ≤ ‖z - rho‖ := by
        simpa [dist_eq_norm, norm_sub_rev] using hrho.2.1.le
      have hpow : (r * (2 : ℝ) ^ k) ^ j ≤ ‖z - rho‖ ^ j := by
        exact pow_le_pow_left₀ hinner.le hdist j
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hinner _)
        hpow
    _ = (∑ rho ∈ dyadicAnnularShell Z z r k, (Z rho : ℝ)) /
        (r * (2 : ℝ) ^ k) ^ j := by rw [Finset.sum_div]

/-- Dyadic shell decomposition of a finite reciprocal-power tail. -/
theorem norm_sum_annularTail_div_pow_le
    (Z : ℂ →₀ ℕ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (N j : ℕ) :
    ‖∑ rho ∈ Z.support.filter (fun rho ↦
          r < dist rho z ∧ dist rho z ≤ r * (2 : ℝ) ^ N),
        (Z rho : ℂ) / (z - rho) ^ j‖ ≤
      ∑ k ∈ Finset.range N,
        (∑ rho ∈ dyadicAnnularShell Z z r k, (Z rho : ℝ)) /
          (r * (2 : ℝ) ^ k) ^ j := by
  rw [← biUnion_dyadicAnnularShell Z z hr N,
    Finset.sum_biUnion (pairwiseDisjoint_dyadicAnnularShell Z z hr.le N)]
  calc
    ‖∑ k ∈ Finset.range N,
        ∑ rho ∈ dyadicAnnularShell Z z r k,
          (Z rho : ℂ) / (z - rho) ^ j‖ ≤
        ∑ k ∈ Finset.range N,
          ‖∑ rho ∈ dyadicAnnularShell Z z r k,
            (Z rho : ℂ) / (z - rho) ^ j‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_sum_dyadicAnnularShell_div_pow_le Z z hr k j

/-- A cumulative affine mass bound gives the explicit geometric annular
tail estimate used by the zero detector. -/
theorem norm_sum_annularTail_div_pow_le_of_affine_mass
    (Z : ℂ →₀ ℕ) (z : ℂ) {r a b : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (N j : ℕ) (hj : 2 ≤ j)
    (hmass : ∀ k < N,
      (∑ rho ∈ dyadicAnnularShell Z z r k, (Z rho : ℝ)) ≤
        a + b * (r * (2 : ℝ) ^ (k + 1))) :
    ‖∑ rho ∈ Z.support.filter (fun rho ↦
          r < dist rho z ∧ dist rho z ≤ r * (2 : ℝ) ^ N),
        (Z rho : ℂ) / (z - rho) ^ j‖ ≤
      2 * a / r ^ j + 4 * b / r ^ (j - 1) := by
  refine (norm_sum_annularTail_div_pow_le Z z hr N j).trans ?_
  calc
    (∑ k ∈ Finset.range N,
        (∑ rho ∈ dyadicAnnularShell Z z r k, (Z rho : ℝ)) /
          (r * (2 : ℝ) ^ k) ^ j) ≤
        ∑ k ∈ Finset.range N,
          (a + b * (r * (2 : ℝ) ^ (k + 1))) /
            (r * (2 : ℝ) ^ k) ^ j := by
      apply Finset.sum_le_sum
      intro k hk
      apply div_le_div_of_nonneg_right (hmass k (Finset.mem_range.mp hk))
      positivity
    _ ≤ ∑ k ∈ Finset.range N,
          (a / r ^ j + (2 * b) / r ^ (j - 1)) *
            ((1 : ℝ) / 2) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hpowj : k ≤ k * j := by nlinarith
      have hpowjm : k ≤ k * (j - 1) := by
        have : 1 ≤ j - 1 := by omega
        nlinarith
      have hhalfj : ((1 : ℝ) / 2) ^ (k * j) ≤ ((1 : ℝ) / 2) ^ k := by
        exact pow_le_pow_of_le_one (by positivity) (by norm_num) hpowj
      have hhalfjm : ((1 : ℝ) / 2) ^ (k * (j - 1)) ≤
          ((1 : ℝ) / 2) ^ k := by
        exact pow_le_pow_of_le_one (by positivity) (by norm_num) hpowjm
      have har : 0 ≤ a / r ^ j := by positivity
      have hbr : 0 ≤ (2 * b) / r ^ (j - 1) := by positivity
      calc
        (a + b * (r * (2 : ℝ) ^ (k + 1))) /
            (r * (2 : ℝ) ^ k) ^ j =
            a / r ^ j * ((1 : ℝ) / 2) ^ (k * j) +
              ((2 * b) / r ^ (j - 1)) *
                ((1 : ℝ) / 2) ^ (k * (j - 1)) := by
          have hr0 : r ≠ 0 := hr.ne'
          have hj' : j = (j - 1) + 1 := by omega
          have hrpow : r ^ j = r ^ (j - 1) * r := by
            calc
              r ^ j = r ^ ((j - 1) + 1) := by congr 1
              _ = r ^ (j - 1) * r := pow_succ _ _
          have hkj : k * j = k + k * (j - 1) := by
            conv_lhs => rw [hj']
            ring
          have h2pow : (2 : ℝ) ^ (k * j) =
              (2 : ℝ) ^ k * (2 : ℝ) ^ (k * (j - 1)) := by
            rw [hkj, pow_add]
          have hfirst :
              a / (r * (2 : ℝ) ^ k) ^ j =
                a / r ^ j * ((1 : ℝ) / 2) ^ (k * j) := by
            rw [mul_pow, ← pow_mul, one_div_pow]
            field_simp
          have hsecond :
              (b * (r * (2 : ℝ) ^ (k + 1))) /
                  (r * (2 : ℝ) ^ k) ^ j =
                ((2 * b) / r ^ (j - 1)) *
                  ((1 : ℝ) / 2) ^ (k * (j - 1)) := by
            rw [mul_pow, ← pow_mul, one_div_pow, hrpow, h2pow, pow_succ]
            field_simp
          rw [add_div, hfirst, hsecond]
        _ ≤ a / r ^ j * ((1 : ℝ) / 2) ^ k +
              ((2 * b) / r ^ (j - 1)) * ((1 : ℝ) / 2) ^ k := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hhalfj har)
            (mul_le_mul_of_nonneg_left hhalfjm hbr)
        _ = (a / r ^ j + (2 * b) / r ^ (j - 1)) *
              ((1 : ℝ) / 2) ^ k := by ring
    _ = (a / r ^ j + (2 * b) / r ^ (j - 1)) *
          ∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k := by
      rw [Finset.mul_sum]
    _ ≤ (a / r ^ j + (2 * b) / r ^ (j - 1)) * 2 := by
      apply mul_le_mul_of_nonneg_left (sum_geometric_two_le N)
      positivity
    _ = 2 * a / r ^ j + 4 * b / r ^ (j - 1) := by ring

end

end Erdos48
