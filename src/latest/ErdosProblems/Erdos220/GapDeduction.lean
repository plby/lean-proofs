/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib

/-!
# A reusable empty-window tail deduction

This file contains the elementary ``layer cake'' step used in estimates for
cyclic gaps.  If `E h` is the mass of gaps left above height `h`, then the
second moment is the first moment plus twice the sum of `E h`.  A trivial
bound `E h <= q` treats the small heights.  At large heights, an estimate

`E h * h^2 * phi^2 <= B * q^3`

is summable, since the tail of `sum h^-2` is at most `1 / K`.  Taking a cutoff
`K` between `q / phi` and `2 * q / phi` gives the explicit constant `5 + 2B`.

The theorem is deliberately independent of how the gaps and empty windows
are constructed.  This lets number-theoretic applications discharge the
layer-cake identity and the analytic empty-window estimate separately.
-/

namespace Erdos220

open Finset

/--
The abstract tail argument.  `secondMoment` may be the sum of squares of a
finite sequence of positive cyclic gaps, and `E h` its empty-window mass.

The interval `Ioc 0 N` is `{1, ..., N}`.  The hypotheses on `K` say that it is
a legitimate cutoff comparable with `q / phi`.  The conclusion has the fully
explicit constant `5 + 2 * B`.
-/
theorem emptyWindow_tail_deduction
    (E : ℕ → ℝ) (N K : ℕ) (q phi B secondMoment : ℝ)
    (hq : 0 < q) (hphi : 0 < phi) (hphi_le_q : phi ≤ q) (hB : 0 ≤ B)
    (hK_pos : 0 < K) (hK_le_N : K ≤ N)
    (hK_lower : q / phi ≤ (K : ℝ))
    (hK_upper : (K : ℝ) ≤ 2 * q / phi)
    (hE_nonneg : ∀ h ∈ Ioc 0 N, 0 ≤ E h)
    (hE_trivial : ∀ h ∈ Ioc 0 N, E h ≤ q)
    (hE_analytic : ∀ h ∈ Ioc K N,
      E h * (h : ℝ) ^ 2 * phi ^ 2 ≤ B * q ^ 3)
    (hlayer : secondMoment = q + 2 * ∑ h ∈ Ioc 0 N, E h) :
    secondMoment ≤ (5 + 2 * B) * q ^ 2 / phi := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hphi0 : phi ≠ 0 := ne_of_gt hphi
  have hK_real_pos : 0 < (K : ℝ) := by exact_mod_cast hK_pos
  have hcoeff_nonneg : 0 ≤ B * q ^ 3 / phi ^ 2 := by positivity

  have hsplit :
      ∑ h ∈ Ioc 0 N, E h =
        (∑ h ∈ Ioc 0 K, E h) + ∑ h ∈ Ioc K N, E h := by
    rw [← sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
    rw [Ioc_union_Ioc_eq_Ioc (Nat.zero_le K) hK_le_N]

  have hsmall : ∑ h ∈ Ioc 0 K, E h ≤ (K : ℝ) * q := by
    calc
      ∑ h ∈ Ioc 0 K, E h ≤ ∑ _h ∈ Ioc 0 K, q := by
        apply sum_le_sum
        intro h hh
        exact hE_trivial h (by
          rw [mem_Ioc] at hh ⊢
          exact ⟨hh.1, hh.2.trans hK_le_N⟩)
      _ = (K : ℝ) * q := by simp

  have hlarge_pointwise : ∀ h ∈ Ioc K N,
      E h ≤ (B * q ^ 3 / phi ^ 2) * (((h : ℝ) ^ 2)⁻¹) := by
    intro h hh
    have hh_nat_pos : 0 < h := lt_of_lt_of_le hK_pos (mem_Ioc.mp hh).1.le
    have hh_real_pos : 0 < (h : ℝ) := by exact_mod_cast hh_nat_pos
    have hden_pos : 0 < (h : ℝ) ^ 2 * phi ^ 2 := by positivity
    have hdiv : E h ≤ B * q ^ 3 / ((h : ℝ) ^ 2 * phi ^ 2) := by
      apply (le_div_iff₀ hden_pos).2
      simpa [mul_assoc] using hE_analytic h hh
    calc
      E h ≤ B * q ^ 3 / ((h : ℝ) ^ 2 * phi ^ 2) := hdiv
      _ = (B * q ^ 3 / phi ^ 2) * (((h : ℝ) ^ 2)⁻¹) := by
        field_simp [ne_of_gt hh_real_pos, hphi0]

  have hinv_tail :
      (∑ h ∈ Ioc K N, (((h : ℝ) ^ 2)⁻¹)) ≤ ((K : ℝ)⁻¹) := by
    calc
      (∑ h ∈ Ioc K N, (((h : ℝ) ^ 2)⁻¹))
          ≤ ((K : ℝ)⁻¹) - ((N : ℝ)⁻¹) :=
        sum_Ioc_inv_sq_le_sub (by omega) hK_le_N
      _ ≤ ((K : ℝ)⁻¹) := by
        have hN_inv_nonneg : 0 ≤ ((N : ℝ)⁻¹) := by positivity
        linarith

  have hlarge :
      ∑ h ∈ Ioc K N, E h ≤ (B * q ^ 3 / phi ^ 2) * ((K : ℝ)⁻¹) := by
    calc
      ∑ h ∈ Ioc K N, E h
          ≤ ∑ h ∈ Ioc K N,
              (B * q ^ 3 / phi ^ 2) * (((h : ℝ) ^ 2)⁻¹) := by
        exact sum_le_sum hlarge_pointwise
      _ = (B * q ^ 3 / phi ^ 2) *
            ∑ h ∈ Ioc K N, (((h : ℝ) ^ 2)⁻¹) := by
        rw [mul_sum]
      _ ≤ (B * q ^ 3 / phi ^ 2) * ((K : ℝ)⁻¹) := by
        exact mul_le_mul_of_nonneg_left hinv_tail hcoeff_nonneg

  have hq_le_Kphi : q ≤ (K : ℝ) * phi := by
    exact (div_le_iff₀ hphi).mp hK_lower
  have hinvK_le : ((K : ℝ)⁻¹) ≤ phi / q := by
    apply (le_div_iff₀ hq).2
    have hq_div_K : q / (K : ℝ) ≤ phi := by
      apply (div_le_iff₀ hK_real_pos).2
      simpa [mul_comm] using hq_le_Kphi
    simpa [div_eq_mul_inv, mul_comm] using hq_div_K

  have hlarge_final :
      ∑ h ∈ Ioc K N, E h ≤ B * q ^ 2 / phi := by
    calc
      ∑ h ∈ Ioc K N, E h
          ≤ (B * q ^ 3 / phi ^ 2) * ((K : ℝ)⁻¹) := hlarge
      _ ≤ (B * q ^ 3 / phi ^ 2) * (phi / q) := by
        exact mul_le_mul_of_nonneg_left hinvK_le hcoeff_nonneg
      _ = B * q ^ 2 / phi := by
        field_simp [hq0, hphi0]

  have hsmall_final : ∑ h ∈ Ioc 0 K, E h ≤ 2 * q ^ 2 / phi := by
    calc
      ∑ h ∈ Ioc 0 K, E h ≤ (K : ℝ) * q := hsmall
      _ ≤ (2 * q / phi) * q := by
        exact mul_le_mul_of_nonneg_right hK_upper hq.le
      _ = 2 * q ^ 2 / phi := by ring

  have hfirst_moment : q ≤ q ^ 2 / phi := by
    apply (le_div_iff₀ hphi).2
    nlinarith

  rw [hlayer, hsplit]
  calc
    q + 2 * ((∑ h ∈ Ioc 0 K, E h) + ∑ h ∈ Ioc K N, E h)
        ≤ q + 2 * (2 * q ^ 2 / phi + B * q ^ 2 / phi) := by
      gcongr
    _ ≤ q ^ 2 / phi + 2 * (2 * q ^ 2 / phi + B * q ^ 2 / phi) := by
      gcongr
    _ = (5 + 2 * B) * q ^ 2 / phi := by ring

/--
Specialization of `emptyWindow_tail_deduction` to an actual finite sequence of
gaps.  The layer-cake identity is kept as a hypothesis because applications
may use either linear gaps or cyclic gaps and may normalize endpoint terms in
different ways.
-/
theorem cyclicGap_squareSum_le_of_emptyWindow_bound
    {ι : Type*} [Fintype ι]
    (gap : ι → ℝ) (E : ℕ → ℝ) (N K : ℕ) (q phi B : ℝ)
    (hq : 0 < q) (hphi : 0 < phi) (hphi_le_q : phi ≤ q) (hB : 0 ≤ B)
    (hgap_pos : ∀ i, 0 < gap i)
    (hgap_sum : ∑ i, gap i = q)
    (hK_pos : 0 < K) (hK_le_N : K ≤ N)
    (hK_lower : q / phi ≤ (K : ℝ))
    (hK_upper : (K : ℝ) ≤ 2 * q / phi)
    (hE_nonneg : ∀ h ∈ Ioc 0 N, 0 ≤ E h)
    (hE_trivial : ∀ h ∈ Ioc 0 N, E h ≤ q)
    (hE_analytic : ∀ h ∈ Ioc K N,
      E h * (h : ℝ) ^ 2 * phi ^ 2 ≤ B * q ^ 3)
    (hlayer : ∑ i, (gap i) ^ 2 = q + 2 * ∑ h ∈ Ioc 0 N, E h) :
    ∑ i, (gap i) ^ 2 ≤ (5 + 2 * B) * q ^ 2 / phi := by
  exact emptyWindow_tail_deduction E N K q phi B (∑ i, (gap i) ^ 2)
    hq hphi hphi_le_q hB hK_pos hK_le_N hK_lower hK_upper
    hE_nonneg hE_trivial hE_analytic hlayer

end Erdos220
