/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos175.Phase
import ErdosProblems.Erdos175.ReciprocalDerivatives
import ErdosProblems.Erdos175.MobiusMeanSquareEndpoint
import ErdosProblems.Erdos175.TypeI
import ErdosProblems.Erdos175.TypeII
import ErdosProblems.Erdos175.TypeIINearFar
import ErdosProblems.Erdos175.TypeIIGlobal
import ErdosProblems.Erdos175.VanDerCorput
import ErdosProblems.Erdos175.Vaughan
import ErdosProblems.Erdos175.VaughanFourSums
import ErdosProblems.Erdos175.VaughanTypeIIDyadic
import ErdosProblems.Erdos175.VaughanTypeIICoefficients

/-!
# Granville--Ramaré's reciprocal Mangoldt sum

This file fixes the exact finite sum occurring in the specialization of
Granville--Ramaré, Theorem 9, used for Erdős Problem 175.  It also records
the square-to-`L²` conversions and the numerical rounding steps used when the
two bilinear terms are assembled.

The interval is represented by
`Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n))`.  For an integer `d`, membership
in this interval is exactly `sqrt n < d ∧ d ≤ sqrt (2n)` in the real
sense, so no rounding error is introduced at either endpoint.
-/

namespace Erdos175.GranvilleRamare9

open scoped ArithmeticFunction BigOperators

/-- The reciprocal Mangoldt sum on the square-root interval used in Section 7. -/
noncomputable def mangoldtSum (n : ℕ) (x : ℝ) : ℂ :=
  Vaughan.reciprocalSum
    (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n))) x
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ)

/-- The phase convention in `Vaughan` agrees with the common `e(t)` notation. -/
lemma vaughan_reciprocalPhase_eq_e (x : ℝ) (d : ℕ) :
    Vaughan.reciprocalPhase x d = e (x / (d : ℝ)) := by
  unfold Vaughan.reciprocalPhase e
  congr 1

/-- Expanded finite-sum form of `mangoldtSum`. -/
lemma mangoldtSum_eq (n : ℕ) (x : ℝ) :
    mangoldtSum n x =
      ∑ d ∈ Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)),
        (ArithmeticFunction.vonMangoldt d : ℂ) * e (x / (d : ℝ)) := by
  unfold mangoldtSum Vaughan.reciprocalSum Vaughan.finiteWeightedSum
  apply Finset.sum_congr rfl
  intro d _hd
  rw [vaughan_reciprocalPhase_eq_e]

/-- Every term in the reciprocal phase has norm one. -/
lemma norm_vaughan_reciprocalPhase (x : ℝ) (d : ℕ) :
    ‖Vaughan.reciprocalPhase x d‖ = 1 := by
  rw [vaughan_reciprocalPhase_eq_e, norm_e]

/-! ## The exact four-sum decomposition -/

/-- Vaughan's four-sum identity on the square-root interval, with the
reciprocal phase convention fixed above. -/
lemma mangoldtSum_four_sum
    (n M K : ℕ) (x : ℝ) (hM : 1 ≤ M) (hK : K ≤ Nat.sqrt n) :
    mangoldtSum n x =
      VaughanFourSums.sigma1
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M -
        VaughanFourSums.sigma21
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K -
        VaughanFourSums.sigma22
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K -
        VaughanFourSums.sigma3
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K := by
  unfold mangoldtSum
  exact VaughanFourSums.reciprocal_Ioc_four_sum_identity
    (Nat.sqrt n) (Nat.sqrt (2 * n)) M K x hM hK

/-- The triangle-inequality assembly corresponding to equation (9.2). -/
lemma norm_mangoldtSum_le_four_sums
    (n M K : ℕ) (x : ℝ) (hM : 1 ≤ M) (hK : K ≤ Nat.sqrt n) :
    ‖mangoldtSum n x‖ ≤
      ‖VaughanFourSums.sigma1
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M‖ +
        ‖VaughanFourSums.sigma21
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K‖ +
        ‖VaughanFourSums.sigma22
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K‖ +
        ‖VaughanFourSums.sigma3
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K‖ := by
  rw [mangoldtSum_four_sum n M K x hM hK]
  calc
    ‖VaughanFourSums.sigma1
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M -
        VaughanFourSums.sigma21
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K -
        VaughanFourSums.sigma22
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K -
        VaughanFourSums.sigma3
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K‖
        ≤
          ‖VaughanFourSums.sigma1
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M -
            VaughanFourSums.sigma21
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K -
            VaughanFourSums.sigma22
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖ +
          ‖VaughanFourSums.sigma3
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖ := norm_sub_le _ _
    _ ≤
          (‖VaughanFourSums.sigma1
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M -
            VaughanFourSums.sigma21
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖ +
          ‖VaughanFourSums.sigma22
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖) +
          ‖VaughanFourSums.sigma3
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤
          ((‖VaughanFourSums.sigma1
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M‖ +
            ‖VaughanFourSums.sigma21
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖) +
          ‖VaughanFourSums.sigma22
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖) +
          ‖VaughanFourSums.sigma3
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = _ := by ring

/-! ## The closed Type-I contribution -/

/-- The natural square-root endpoints of the target interval lie in a
factor-two interval. -/
lemma sqrt_two_mul_le_two_sqrt (n : ℕ) (hn : 1 ≤ n) :
    Nat.sqrt (2 * n) ≤ 2 * Nat.sqrt n := by
  rw [← Nat.lt_succ_iff]
  apply Nat.sqrt_lt.mpr
  have hspos : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (by omega)
  have hup := Nat.lt_succ_sqrt n
  nlinarith

/-- The explicit Type-I majorant used below. -/
noncomputable def typeIClosedMajorant (x : ℝ) (y M : ℕ) : ℝ :=
  (2 * Real.log (2 * y : ℕ) + Real.log M) *
    (TypeI.threeBranchOuterNumerator x y M * TypeI.dyadicCount M)

/-- Insert the fully summed Type-I estimate into the exact four-piece
Vaughan identity for the square-root interval.  The two Type-II norms are
eliminated by the dyadic near--far assembly below. -/
theorem norm_mangoldtSum_le_typeIClosed_add_typeII
    (n M : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : 0 < x)
    (hM : 1 ≤ M) (hMy : M ≤ Nat.sqrt n)
    (hglobal : 12 * x * (M : ℝ) ^ 3 ≤ (Nat.sqrt n : ℝ) ^ 4) :
    ‖mangoldtSum n x‖ ≤
      typeIClosedMajorant x (Nat.sqrt n) M +
        ‖VaughanFourSums.sigma22
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M M‖ +
        ‖VaughanFourSums.sigma3
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M M‖ := by
  have hyy' : Nat.sqrt n ≤ Nat.sqrt (2 * n) :=
    Nat.sqrt_le_sqrt (by omega)
  have hy' : Nat.sqrt (2 * n) ≤ 2 * Nat.sqrt n :=
    sqrt_two_mul_le_two_sqrt n hn
  have hI := TypeI.norm_sigma1_add_sigma21_le_closed
    x (Nat.sqrt n) (Nat.sqrt (2 * n)) M M
    hx hM hMy hyy' hy' hglobal
  have hall := norm_mangoldtSum_le_four_sums n M M x hM hMy
  calc
    ‖mangoldtSum n x‖ ≤
        (‖VaughanFourSums.sigma1
            (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
            (Vaughan.reciprocalPhase x) M‖ +
          ‖VaughanFourSums.sigma21
            (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
            (Vaughan.reciprocalPhase x) M M‖) +
          ‖VaughanFourSums.sigma22
            (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
            (Vaughan.reciprocalPhase x) M M‖ +
          ‖VaughanFourSums.sigma3
            (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
            (Vaughan.reciprocalPhase x) M M‖ := hall
    _ ≤ typeIClosedMajorant x (Nat.sqrt n) M +
          ‖VaughanFourSums.sigma22
            (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
            (Vaughan.reciprocalPhase x) M M‖ +
          ‖VaughanFourSums.sigma3
            (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
            (Vaughan.reciprocalPhase x) M M‖ := by
      unfold typeIClosedMajorant
      gcongr

/-! ## Converting squared coefficient estimates to `L²` estimates -/

/-- A pointwise bound on a coefficient sequence gives the expected finite
`L²` bound. -/
lemma sum_norm_sq_le_card_mul_sq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ A) :
    (∑ i ∈ s, ‖a i‖ ^ 2) ≤ (s.card : ℝ) * A ^ 2 := by
  calc
    (∑ i ∈ s, ‖a i‖ ^ 2) ≤ ∑ _i ∈ s, A ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [norm_nonneg (a i), ha i hi]
    _ = (s.card : ℝ) * A ^ 2 := by simp

/-- Product form of the preceding estimate, matching the coefficient factor
in a Type-II bound. -/
lemma l2Norm_sq_mul_l2Norm_sq_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (a : ι → ℂ) (b : κ → ℂ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ A)
    (hb : ∀ j ∈ t, ‖b j‖ ≤ B) :
    TypeII.l2Norm s a ^ 2 * TypeII.l2Norm t b ^ 2 ≤
      ((s.card : ℝ) * (t.card : ℝ)) * (A ^ 2 * B ^ 2) := by
  rw [TypeII.l2Norm_sq, TypeII.l2Norm_sq]
  have hs := sum_norm_sq_le_card_mul_sq s a A hA ha
  have ht := sum_norm_sq_le_card_mul_sq t b B hB hb
  have ht0 : 0 ≤ ∑ j ∈ t, ‖b j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ j ∈ t, ‖b j‖ ^ 2) ≤
        ((s.card : ℝ) * A ^ 2) * ((t.card : ℝ) * B ^ 2) :=
      mul_le_mul hs ht ht0 (by positivity)
    _ = ((s.card : ℝ) * (t.card : ℝ)) * (A ^ 2 * B ^ 2) := by ring

/-- The special coefficient product used for `Σ₂,₂`: the first coefficient
is identically one and the second is bounded by `L`. -/
lemma one_l2Norm_sq_mul_l2Norm_sq_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (b : κ → ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hb : ∀ j ∈ t, ‖b j‖ ≤ L) :
    TypeII.l2Norm s (fun _ => (1 : ℂ)) ^ 2 *
        TypeII.l2Norm t b ^ 2 ≤
      ((s.card : ℝ) * (t.card : ℝ)) * L ^ 2 := by
  have h := l2Norm_sq_mul_l2Norm_sq_le s t (fun _ => (1 : ℂ)) b
    1 L (by norm_num) hL (by simp) hb
  simpa using h

/-- On a dyadic block, the elementary Vaughan coefficient estimate becomes
the uniform bound `|b_r| ≤ log (2R)`. -/
lemma norm_bCoeff_le_log_two_mul
    (M K R r : ℕ) (hr : r ∈ Finset.Ioc R (2 * R)) :
    ‖((VaughanFourSums.bCoeff M K r : ℝ) : ℂ)‖ ≤
      Real.log (2 * R : ℕ) := by
  have hrI : R < r ∧ r ≤ 2 * R := by
    exact Finset.mem_Ioc.mp hr
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hlog : Real.log (r : ℝ) ≤ Real.log (2 * R : ℕ) :=
    Real.log_le_log hrpos (by exact_mod_cast hrI.2)
  have hb := VaughanFourSums.abs_bCoeff_le_log M K r
  simpa using hb.trans hlog

/-- The concrete `L²` estimate for the `b_r` coefficient on `(R,2R]`.
This is the first coefficient estimate on page 40 of Granville--Ramaré,
before the later numerical replacement of the logarithm. -/
lemma l2Norm_bCoeff_sq_le (M K R : ℕ) (hR : 1 ≤ R) :
    TypeII.l2Norm (Finset.Ioc R (2 * R))
        (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ)) ^ 2 ≤
      (R : ℝ) * Real.log (2 * R : ℕ) ^ 2 := by
  rw [TypeII.l2Norm_sq]
  have hlog : 0 ≤ Real.log (2 * R : ℕ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * R by omega)
  have hcard : (Finset.Ioc R (2 * R)).card = R := by
    simp
    omega
  simpa [hcard] using sum_norm_sq_le_card_mul_sq
    (Finset.Ioc R (2 * R))
    (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ))
    (Real.log (2 * R : ℕ)) hlog
    (fun r hr => norm_bCoeff_le_log_two_mul M K R r hr)

/-- The `a_l` coefficient in Vaughan's identity is exactly the truncated
Möbius divisor sum appearing in Proposition 10.1. -/
lemma aCoeff_eq_truncatedMobiusDivisorSum
    (M : ℕ) {l : ℕ} (hl : l ≠ 0) :
    VaughanFourSums.aCoeff M l = truncatedMobiusDivisorSum M l := by
  rw [VaughanFourSums.aCoeff, ArithmeticFunction.coe_mul_zeta_apply,
    truncatedMobiusDivisorSum]
  change (∑ d ∈ l.divisors,
      (if d ≤ M then (ArithmeticFunction.moebius d : ℝ) else 0)) = _
  rw [← Finset.sum_filter]
  have hsets :
      l.divisors.filter (fun d => d ≤ M) =
        (Finset.Icc 1 M).filter (fun d => d ∣ l) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdl, _⟩, hdM⟩
      have hd0 : d ≠ 0 := by
        intro hd
        subst d
        exact hl (Nat.eq_zero_of_zero_dvd hdl)
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0, hdM⟩, hdl⟩
    · rintro ⟨⟨hd1, hdM⟩, hdl⟩
      exact ⟨⟨hdl, hl⟩, hdM⟩
  rw [hsets]

/-- Proposition 10.1 transferred to the actual Vaughan coefficient. -/
lemma l2Norm_aCoeff_sq_le
    (M L : ℕ) (hM : 1 ≤ M) :
    TypeII.l2Norm (Finset.Ioc L (2 * L))
        (fun l => ((VaughanFourSums.aCoeff M l : ℝ) : ℂ)) ^ 2 ≤
      (8 / 9 : ℝ) * (L : ℝ) * (Real.log M + 3) ^ 3 := by
  rw [TypeII.l2Norm_sq]
  have hprop := granville_ramare_prop_10_1
    (N := L) (z := M) hM
  calc
    (∑ l ∈ Finset.Ioc L (2 * L),
        ‖((VaughanFourSums.aCoeff M l : ℝ) : ℂ)‖ ^ 2) =
        ∑ l ∈ Finset.Ioc L (2 * L), truncatedMobiusDivisorSum M l ^ 2 := by
      apply Finset.sum_congr rfl
      intro l hlmem
      have hl0 : l ≠ 0 := by
        have := (Finset.mem_Ioc.mp hlmem).1
        omega
      rw [aCoeff_eq_truncatedMobiusDivisorSum M hl0]
      simp
    _ ≤ (8 / 9 : ℝ) * (L : ℝ) * (Real.log M + 3) ^ 3 := hprop

/-- Elementary von Mangoldt second moment on a dyadic block. -/
lemma l2Norm_vonMangoldt_sq_le (R : ℕ) (hR : 1 ≤ R) :
    TypeII.l2Norm (Finset.Ioc R (2 * R))
        (fun r => ((ArithmeticFunction.vonMangoldt r : ℝ) : ℂ)) ^ 2 ≤
      (R : ℝ) * Real.log (2 * R : ℕ) ^ 2 := by
  rw [TypeII.l2Norm_sq]
  have hterm (r : ℕ) (hr : r ∈ Finset.Ioc R (2 * R)) :
      ‖((ArithmeticFunction.vonMangoldt r : ℝ) : ℂ)‖ ^ 2 ≤
        Real.log (2 * R : ℕ) ^ 2 := by
    have hrI := Finset.mem_Ioc.mp hr
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hlogle : Real.log (r : ℝ) ≤ Real.log (2 * R : ℕ) :=
      Real.log_le_log hrpos (by exact_mod_cast hrI.2)
    have hlam0 : 0 ≤ ArithmeticFunction.vonMangoldt r :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hlam : ArithmeticFunction.vonMangoldt r ≤ Real.log (2 * R : ℕ) :=
      ArithmeticFunction.vonMangoldt_le_log.trans hlogle
    rw [Complex.norm_of_nonneg hlam0]
    exact pow_le_pow_left₀ hlam0 hlam 2
  calc
    (∑ r ∈ Finset.Ioc R (2 * R),
        ‖((ArithmeticFunction.vonMangoldt r : ℝ) : ℂ)‖ ^ 2) ≤
        ∑ _r ∈ Finset.Ioc R (2 * R), Real.log (2 * R : ℕ) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact hterm r hr
    _ = (R : ℝ) * Real.log (2 * R : ℕ) ^ 2 := by
      have hcard : (Finset.Ioc R (2 * R)).card = R := by
        simp
        omega
      simp [hcard]

/-! ## Shifted dyadic coefficient bounds

The exact Vaughan Type-II decomposition uses the half-open power block
`[2^j,2^(j+1))`, rather than the unshifted interval `(R,2R]`.  The bridge
module proves the corresponding squared estimates for the masked
coefficients.  The next elementary lemma turns each such estimate into the
square-root form consumed by the near--far bilinear bound. -/

lemma l2Norm_le_sqrt_of_sq_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : TypeII.l2Norm s a ^ 2 ≤ C) :
    TypeII.l2Norm s a ≤ Real.sqrt C := by
  calc
    TypeII.l2Norm s a = Real.sqrt (TypeII.l2Norm s a ^ 2) := by
      rw [Real.sqrt_sq (TypeII.l2Norm_nonneg s a)]
    _ ≤ Real.sqrt C := Real.sqrt_le_sqrt h

/-- A support mask can only reduce the `L²` mass of the constant-one
coefficient on a shifted dyadic block. -/
lemma l2Norm_restrict_one_dyadicBlock_sq_le
    (support : Finset ℕ) (j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (VaughanTypeIIDyadic.restrictCoeff support (fun _ => (1 : ℂ))) ^ 2 ≤
      (2 ^ j : ℕ) := by
  rw [TypeII.l2Norm_sq]
  calc
    (∑ n ∈ TypeI.dyadicBlock j,
        ‖VaughanTypeIIDyadic.restrictCoeff support
          (fun _ => (1 : ℂ)) n‖ ^ 2) ≤
        ∑ _n ∈ TypeI.dyadicBlock j, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hns : n ∈ support
      · simp [VaughanTypeIIDyadic.restrictCoeff, hns]
      · simp [VaughanTypeIIDyadic.restrictCoeff, hns]
    _ = (2 ^ j : ℕ) := by simp [TypeI.card_dyadicBlock]

/-- Square-root form of the masked `b`-coefficient estimate. -/
lemma l2Norm_restrict_bCoeff_dyadicBlock_le
    (support : Finset ℕ) (M K j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (VaughanTypeIIDyadic.restrictCoeff support
          (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ))) ≤
      Real.sqrt ((2 ^ j : ℕ) *
        Real.log (2 * (2 ^ j : ℕ)) ^ 2) := by
  apply l2Norm_le_sqrt_of_sq_le
  · positivity
  · exact VaughanTypeIIDyadic.l2Norm_restrict_bCoeff_dyadicBlock_sq_le
      support M K j

/-- Square-root form of the masked constant-one estimate. -/
lemma l2Norm_restrict_one_dyadicBlock_le
    (support : Finset ℕ) (j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (VaughanTypeIIDyadic.restrictCoeff support (fun _ => (1 : ℂ))) ≤
      Real.sqrt (2 ^ j : ℕ) := by
  apply l2Norm_le_sqrt_of_sq_le
  · positivity
  · exact l2Norm_restrict_one_dyadicBlock_sq_le support j

/-- Square-root form of Proposition 10.1 on the shifted, masked block. -/
lemma l2Norm_restrict_aCoeff_dyadicBlock_le
    (support : Finset ℕ) (M j : ℕ) (hM : 1 ≤ M) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (VaughanTypeIIDyadic.restrictCoeff support
          (fun l => ((VaughanFourSums.aCoeff M l : ℝ) : ℂ))) ≤
      Real.sqrt ((8 / 9 : ℝ) * (2 ^ j : ℕ) *
        (Real.log M + 3) ^ 3 + 1) := by
  apply l2Norm_le_sqrt_of_sq_le
  · have hlog : 0 ≤ Real.log M + 3 := by
      have : 0 ≤ Real.log (M : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hM)
      linarith
    positivity
  · exact VaughanTypeIIDyadic.l2Norm_restrict_aCoeff_dyadicBlock_sq_le
      support M j hM

/-- Square-root form of the elementary shifted-block Mangoldt estimate. -/
lemma l2Norm_restrict_vonMangoldt_dyadicBlock_le
    (support : Finset ℕ) (j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (VaughanTypeIIDyadic.restrictCoeff support
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))) ≤
      Real.sqrt ((2 ^ j : ℕ) *
        Real.log (2 * (2 ^ j : ℕ)) ^ 2) := by
  apply l2Norm_le_sqrt_of_sq_le
  · positivity
  · exact VaughanTypeIIDyadic.l2Norm_restrict_vonMangoldt_dyadicBlock_sq_le
      support j

/-- On a sufficiently large active rectangle, orienting the larger power
block first automatically gives the upper-frequency condition needed by
the zero-threshold reciprocal estimate.  The proof keeps the correlated
product `U*V`; no separate lower cutoff for `V` is required. -/
lemma honescale_of_active_oriented_large
    (x : ℝ) (y U V : ℕ)
    (hx : x ≤ 12 * (y : ℝ) ^ 2)
    (hy : 4 * 2304 ^ 2 ≤ y)
    (hactive : y < 4 * (U * V)) (hVU : V ≤ U) (hV : 0 < V) :
    12 * (x / (V : ℝ)) ≤ (U : ℝ) ^ 4 := by
  have hU : 2304 ≤ U := by
    by_contra hnot
    have hUlt : U < 2304 := Nat.lt_of_not_ge hnot
    have hUU : U * U < 2304 ^ 2 := by nlinarith
    have hUV : U * V ≤ U * U := Nat.mul_le_mul_left U hVU
    omega
  have hVUreal : (V : ℝ) ≤ U := by exact_mod_cast hVU
  have hUreal : (2304 : ℝ) ≤ U := by exact_mod_cast hU
  have h2304 : (2304 : ℝ) * V ≤ (U : ℝ) ^ 2 := by
    calc
      (2304 : ℝ) * V ≤ (U : ℝ) * V := by gcongr
      _ ≤ (U : ℝ) * U := by gcongr
      _ = (U : ℝ) ^ 2 := by ring
  have hactiveR : (y : ℝ) ≤ 4 * ((U : ℝ) * V) := by
    exact_mod_cast (Nat.le_of_lt hactive)
  have hy2 : (y : ℝ) ^ 2 ≤ 16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 := by
    calc
      (y : ℝ) ^ 2 ≤ (4 * ((U : ℝ) * V)) ^ 2 := by gcongr
      _ = 16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 := by ring
  have hscale : 144 * (y : ℝ) ^ 2 ≤ (U : ℝ) ^ 4 * V := by
    calc
      144 * (y : ℝ) ^ 2 ≤ 144 * (16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2) := by
        gcongr
      _ = (U : ℝ) ^ 2 * V * ((2304 : ℝ) * V) := by ring
      _ ≤ (U : ℝ) ^ 2 * V * (U : ℝ) ^ 2 := by gcongr
      _ = (U : ℝ) ^ 4 * V := by ring
  rw [show 12 * (x / (V : ℝ)) = (12 * x) / (V : ℝ) by ring,
    div_le_iff₀ (by positivity : (0 : ℝ) < V)]
  calc
    12 * x ≤ 144 * (y : ℝ) ^ 2 := by linarith
    _ ≤ (U : ℝ) ^ 4 * V := hscale

/-! ## Premise-free Type-II block assembly -/

/-- The analytic square-root factor of the premise-free near--far bound,
with the two coefficient norms removed. -/
noncomputable def dyadicAnalyticFactor
    (x : ℝ) (y y' j k T : ℕ) : ℝ :=
  Real.sqrt
    (2 * (2 ^ j : ℕ) * (2 * T + 1) +
      TypeII.threeBranchFarQ x y y'
        (2 ^ j - 1) (2 ^ (j + 1) - 1)
        (2 ^ k - 1) (2 ^ (k + 1) - 1) T * (2 ^ k : ℕ))

/-- The exact dyadic majorant for a `Σ₂,₂` block after replacing both
masked coefficient norms by their proved square-root estimates. -/
noncomputable def sigma22DyadicMajorant
    (x : ℝ) (y y' M K j k T : ℕ) : ℝ :=
  Real.sqrt ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2) *
    dyadicAnalyticFactor x y y' j k T *
      Real.sqrt (2 ^ k : ℕ)

/-- The exact dyadic majorant for a `Σ₃` block.  The extra `+1` is the
single shifted endpoint needed to transfer Proposition 10.1 to
`[2^j,2^(j+1))`. -/
noncomputable def sigma3DyadicMajorant
    (x : ℝ) (y y' M j k T : ℕ) : ℝ :=
  Real.sqrt ((8 / 9 : ℝ) * (2 ^ j : ℕ) *
      (Real.log M + 3) ^ 3 + 1) *
    dyadicAnalyticFactor x y y' j k T *
      Real.sqrt ((2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2)

/-- Fully concrete `Σ₂,₂` estimate: Vaughan's identity, dyadic
decomposition, the premise-free reciprocal near--far estimate, and both
coefficient `L²` bounds are all incorporated. -/
theorem norm_sigma22_le_dyadicMajorants
    (x : ℝ) (y y' M K : ℕ) (threshold : ℕ → ℕ → ℕ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if VaughanTypeIIDyadic.blockActive y y' j k then
            sigma22DyadicMajorant x y y' M K j k (threshold j k)
          else 0 := by
  have hraw := VaughanTypeIIDyadic.norm_sigma22_le_sum_dyadic_near_far_active
    y y' M K x threshold hx
  refine hraw.trans ?_
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro k hk
  by_cases hactive : VaughanTypeIIDyadic.blockActive y y' j k
  · rw [if_pos hactive, if_pos hactive]
    unfold VaughanTypeIIDyadic.dyadicNearFarFactor
      sigma22DyadicMajorant dyadicAnalyticFactor
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right
        (l2Norm_restrict_bCoeff_dyadicBlock_le
          (Finset.Ioc M (M * K)) M K j) (Real.sqrt_nonneg _)
    · exact l2Norm_restrict_one_dyadicBlock_le (Finset.Icc 1 y') k
    · exact TypeII.l2Norm_nonneg _ _
    · positivity
  · rw [if_neg hactive, if_neg hactive]

/-- Fully concrete `Σ₃` estimate with the Proposition 10.1 and Mangoldt
second-moment factors inserted block by block. -/
theorem norm_sigma3_le_dyadicMajorants
    (x : ℝ) (y y' M K : ℕ) (threshold : ℕ → ℕ → ℕ)
    (hx : 0 < x) (hM : 1 ≤ M) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if VaughanTypeIIDyadic.blockActive y y' j k then
            sigma3DyadicMajorant x y y' M j k (threshold j k)
          else 0 := by
  have hraw := VaughanTypeIIDyadic.norm_sigma3_le_sum_dyadic_near_far_active
    y y' M K x threshold hx
  refine hraw.trans ?_
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro k hk
  by_cases hactive : VaughanTypeIIDyadic.blockActive y y' j k
  · rw [if_pos hactive, if_pos hactive]
    unfold VaughanTypeIIDyadic.dyadicNearFarFactor
      sigma3DyadicMajorant dyadicAnalyticFactor
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right
        (l2Norm_restrict_aCoeff_dyadicBlock_le
          (Finset.Ioc M y') M j hM) (Real.sqrt_nonneg _)
    · exact l2Norm_restrict_vonMangoldt_dyadicBlock_le
        (Finset.Ioc K y') k
    · exact TypeII.l2Norm_nonneg _ _
    · positivity
  · rw [if_neg hactive, if_neg hactive]

/-- The complete, premise-free Section 9 upper majorant.  The threshold is
allowed to vary by dyadic rectangle; it is a parameter of an explicit
finite expression, not an analytic assumption. -/
noncomputable def gr9UpperMajorantWithThreshold
    (n M : ℕ) (x : ℝ) (threshold : ℕ → ℕ → ℕ) : ℝ :=
  let y := Nat.sqrt n
  let y' := Nat.sqrt (2 * n)
  typeIClosedMajorant x y M +
    (∑ j ∈ Finset.range (TypeI.dyadicCount (M * M)),
      ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
        if VaughanTypeIIDyadic.blockActive y y' j k then
          sigma22DyadicMajorant x y y' M M j k (threshold j k)
        else 0) +
    (∑ j ∈ Finset.range (TypeI.dyadicCount y'),
      ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
        if VaughanTypeIIDyadic.blockActive y y' j k then
          sigma3DyadicMajorant x y y' M j k (threshold j k)
        else 0)

/-- Granville--Ramaré Section 9, specialized to the reciprocal Mangoldt sum
used for Erdős 175.  This theorem combines the exact Vaughan identity, the
closed Type-I estimate, the premise-free near--far reciprocal estimate,
and the coefficient `L²` bounds. -/
theorem norm_mangoldtSum_le_gr9UpperMajorantWithThreshold
    (n M : ℕ) (x : ℝ) (threshold : ℕ → ℕ → ℕ)
    (hn : 1 ≤ n) (hx : 0 < x) (hM : 1 ≤ M)
    (hMy : M ≤ Nat.sqrt n)
    (hglobal : 12 * x * (M : ℝ) ^ 3 ≤ (Nat.sqrt n : ℝ) ^ 4) :
    ‖mangoldtSum n x‖ ≤
      gr9UpperMajorantWithThreshold n M x threshold := by
  have hmain := norm_mangoldtSum_le_typeIClosed_add_typeII
    n M x hn hx hM hMy hglobal
  have h22 := norm_sigma22_le_dyadicMajorants x
    (Nat.sqrt n) (Nat.sqrt (2 * n)) M M threshold hx
  have h3 := norm_sigma3_le_dyadicMajorants x
    (Nat.sqrt n) (Nat.sqrt (2 * n)) M M threshold hx hM
  unfold gr9UpperMajorantWithThreshold
  dsimp only
  exact hmain.trans (add_le_add (add_le_add le_rfl h22) h3)

/-- A canonical completely closed choice, taking the near-pair threshold
to be zero on every dyadic rectangle. -/
noncomputable def gr9UpperMajorant (n M : ℕ) (x : ℝ) : ℝ :=
  gr9UpperMajorantWithThreshold n M x (fun _ _ => 0)

theorem norm_mangoldtSum_le_gr9UpperMajorant
    (n M : ℕ) (x : ℝ)
    (hn : 1 ≤ n) (hx : 0 < x) (hM : 1 ≤ M)
    (hMy : M ≤ Nat.sqrt n)
    (hglobal : 12 * x * (M : ℝ) ^ 3 ≤ (Nat.sqrt n : ℝ) ^ 4) :
    ‖mangoldtSum n x‖ ≤ gr9UpperMajorant n M x := by
  exact norm_mangoldtSum_le_gr9UpperMajorantWithThreshold
    n M x (fun _ _ => 0) hn hx hM hMy hglobal

/-! ### Coarse explicit specialization of the Type-I numerator -/

lemma sixth_root_scale_le {x y : ℝ}
    (hy : 1 ≤ y) (hx : 0 ≤ x) (hxy : x ≤ 24 * y ^ 2) :
    y * (x / y ^ 4) ^ (1 / 6 : ℝ) ≤
      24 * y ^ (23 / 24 : ℝ) := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hbase : 0 ≤ x / y ^ 4 := by positivity
  have hlpow :
      (y * (x / y ^ 4) ^ (1 / 6 : ℝ)) ^ 6 = x * y ^ 2 := by
    rw [mul_pow, ← Real.rpow_mul_natCast hbase]
    norm_num [Real.rpow_one]
    field_simp
  have hrpow :
      (24 * y ^ (23 / 24 : ℝ)) ^ 6 =
        24 ^ 6 * y ^ (23 / 4 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hy0]
    norm_num
  have hyexp : y ^ 4 ≤ y ^ (23 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hy
      (show (4 : ℝ) ≤ 23 / 4 by norm_num)
    simpa [Real.rpow_natCast] using h
  apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (by positivity)
  rw [hlpow, hrpow]
  calc
    x * y ^ 2 ≤ (24 * y ^ 2) * y ^ 2 := by gcongr
    _ = 24 * y ^ 4 := by ring
    _ ≤ 24 * y ^ (23 / 4 : ℝ) := by gcongr
    _ ≤ 24 ^ 6 * y ^ (23 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hy0 _)

lemma fourth_root_scale_le {y L : ℝ} (hy : 1 ≤ y) (hL : 0 ≤ L) :
    Real.sqrt (Real.sqrt ((2 * y) ^ 3 * Real.sqrt (2 * y) * L ^ 2)) ≤
      2 * y ^ (23 / 24 : ℝ) * Real.sqrt L := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hyp : 0 < y := lt_of_lt_of_le zero_lt_one hy
  let X : ℝ := (2 * y) ^ 3 * Real.sqrt (2 * y) * L ^ 2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hsqrt : Real.sqrt (2 * y) ≤ 2 * y ^ (5 / 6 : ℝ) := by
    calc
      Real.sqrt (2 * y) ≤ Real.sqrt (4 * y) :=
        Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * Real.sqrt y := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      _ ≤ 2 * y ^ (5 / 6 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  have hpowadd : y ^ (23 / 6 : ℝ) = y ^ 3 * y ^ (5 / 6 : ℝ) := by
    rw [show (23 / 6 : ℝ) = 3 + 5 / 6 by norm_num, Real.rpow_add hyp]
    norm_num [Real.rpow_natCast]
  have hXupper : X ≤ 16 * y ^ (23 / 6 : ℝ) * L ^ 2 := by
    dsimp [X]
    calc
      (2 * y) ^ 3 * Real.sqrt (2 * y) * L ^ 2 ≤
          (2 * y) ^ 3 * (2 * y ^ (5 / 6 : ℝ)) * L ^ 2 := by gcongr
      _ = 16 * (y ^ 3 * y ^ (5 / 6 : ℝ)) * L ^ 2 := by ring
      _ = 16 * y ^ (23 / 6 : ℝ) * L ^ 2 := by rw [hpowadd]
  have hlpow : Real.sqrt (Real.sqrt X) ^ 4 = X := by
    calc
      Real.sqrt (Real.sqrt X) ^ 4 =
          (Real.sqrt (Real.sqrt X) ^ 2) ^ 2 := by ring
      _ = Real.sqrt X ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg X)]
      _ = X := Real.sq_sqrt hX
  have hrpow :
      (2 * y ^ (23 / 24 : ℝ) * Real.sqrt L) ^ 4 =
        16 * y ^ (23 / 6 : ℝ) * L ^ 2 := by
    have hypow : (y ^ (23 / 24 : ℝ)) ^ 4 = y ^ (23 / 6 : ℝ) := by
      rw [← Real.rpow_mul_natCast hy0]
      norm_num
    rw [mul_pow, mul_pow, hypow]
    rw [show Real.sqrt L ^ 4 = L ^ 2 by
      calc
        Real.sqrt L ^ 4 = (Real.sqrt L ^ 2) ^ 2 := by ring
        _ = L ^ 2 := by rw [Real.sq_sqrt hL]]
    ring
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity)
  rw [hlpow, hrpow]
  exact hXupper

/-- The sixth-root Type-I contribution remains on the same power scale
when the Vaughan cutoff satisfies `M^3 ≤ y`. -/
lemma sixth_root_scale_with_M_le {x y m : ℝ}
    (hy : 1 ≤ y) (hx : 0 ≤ x) (hxy : x ≤ 24 * y ^ 2)
    (hm : 0 ≤ m) (hm3 : m ^ 3 ≤ y) :
    y * (x * m ^ 3 / y ^ 4) ^ (1 / 6 : ℝ) ≤
      24 * y ^ (23 / 24 : ℝ) := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hbase : 0 ≤ x * m ^ 3 / y ^ 4 := by positivity
  have hlpow :
      (y * (x * m ^ 3 / y ^ 4) ^ (1 / 6 : ℝ)) ^ 6 =
        x * m ^ 3 * y ^ 2 := by
    rw [mul_pow, ← Real.rpow_mul_natCast hbase]
    norm_num [Real.rpow_one]
    field_simp
  have hrpow :
      (24 * y ^ (23 / 24 : ℝ)) ^ 6 =
        24 ^ 6 * y ^ (23 / 4 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hy0]
    norm_num
  have hyexp : y ^ 5 ≤ y ^ (23 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hy
      (show (5 : ℝ) ≤ 23 / 4 by norm_num)
    simpa [Real.rpow_natCast] using h
  apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (by positivity)
  rw [hlpow, hrpow]
  calc
    x * m ^ 3 * y ^ 2 ≤ (24 * y ^ 2) * y * y ^ 2 := by gcongr
    _ = 24 * y ^ 5 := by ring
    _ ≤ 24 * y ^ (23 / 4 : ℝ) := by gcongr
    _ ≤ 24 ^ 6 * y ^ (23 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hy0 _)

/-- The nested-square-root Type-I contribution with a general cutoff
`M^3 ≤ y`.  Taking twelfth powers makes the fractional exponents exact. -/
lemma fourth_root_scale_with_M_le {y m L : ℝ}
    (hy : 1 ≤ y) (hm : 0 ≤ m) (hm3 : m ^ 3 ≤ y) (hL : 0 ≤ L) :
    Real.sqrt (Real.sqrt
        ((2 * y) ^ 3 * Real.sqrt (2 * y) * m * L ^ 2)) ≤
      2 * y ^ (23 / 24 : ℝ) * Real.sqrt L := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hyp : 0 < y := lt_of_lt_of_le zero_lt_one hy
  let X : ℝ := (2 * y) ^ 3 * Real.sqrt (2 * y) * m * L ^ 2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hsqrt : Real.sqrt (2 * y) ≤ 2 * y ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt (2 * y) ≤ Real.sqrt (4 * y) :=
        Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * Real.sqrt y := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      _ = 2 * y ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
  have hpowadd : y ^ (7 / 2 : ℝ) = y ^ 3 * y ^ (1 / 2 : ℝ) := by
    rw [show (7 / 2 : ℝ) = 3 + 1 / 2 by norm_num, Real.rpow_add hyp]
    norm_num [Real.rpow_natCast]
  have hXupper : X ≤ 16 * y ^ (7 / 2 : ℝ) * m * L ^ 2 := by
    dsimp [X]
    calc
      (2 * y) ^ 3 * Real.sqrt (2 * y) * m * L ^ 2 ≤
          (2 * y) ^ 3 * (2 * y ^ (1 / 2 : ℝ)) * m * L ^ 2 := by
        gcongr
      _ = 16 * (y ^ 3 * y ^ (1 / 2 : ℝ)) * m * L ^ 2 := by ring
      _ = 16 * y ^ (7 / 2 : ℝ) * m * L ^ 2 := by rw [hpowadd]
  have hXpow : X ^ 3 ≤ 4096 * y ^ (23 / 2 : ℝ) * L ^ 6 := by
    calc
      X ^ 3 ≤ (16 * y ^ (7 / 2 : ℝ) * m * L ^ 2) ^ 3 := by gcongr
      _ = 4096 * y ^ (21 / 2 : ℝ) * m ^ 3 * L ^ 6 := by
        have hy3 : (y ^ (7 / 2 : ℝ)) ^ 3 = y ^ (21 / 2 : ℝ) := by
          rw [← Real.rpow_mul_natCast hy0]
          norm_num
        rw [mul_pow, mul_pow, mul_pow, hy3]
        ring
      _ ≤ 4096 * y ^ (21 / 2 : ℝ) * y * L ^ 6 := by gcongr
      _ = 4096 * y ^ (23 / 2 : ℝ) * L ^ 6 := by
        have hyadd : y ^ (23 / 2 : ℝ) = y ^ (21 / 2 : ℝ) * y := by
          rw [show (23 / 2 : ℝ) = 21 / 2 + 1 by norm_num,
            Real.rpow_add hyp]
          norm_num [Real.rpow_one]
        rw [hyadd]
        ring
  have hlpow : Real.sqrt (Real.sqrt X) ^ 12 = X ^ 3 := by
    calc
      Real.sqrt (Real.sqrt X) ^ 12 =
          (Real.sqrt (Real.sqrt X) ^ 4) ^ 3 := by ring
      _ = X ^ 3 := by
        rw [show Real.sqrt (Real.sqrt X) ^ 4 = X by
          calc
            Real.sqrt (Real.sqrt X) ^ 4 =
                (Real.sqrt (Real.sqrt X) ^ 2) ^ 2 := by ring
            _ = Real.sqrt X ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg X)]
            _ = X := Real.sq_sqrt hX]
  have hrpow :
      (2 * y ^ (23 / 24 : ℝ) * Real.sqrt L) ^ 12 =
        4096 * y ^ (23 / 2 : ℝ) * L ^ 6 := by
    have hypow : (y ^ (23 / 24 : ℝ)) ^ 12 = y ^ (23 / 2 : ℝ) := by
      rw [← Real.rpow_mul_natCast hy0]
      norm_num
    rw [mul_pow, mul_pow, hypow]
    rw [show Real.sqrt L ^ 12 = L ^ 6 by
      calc
        Real.sqrt L ^ 12 = (Real.sqrt L ^ 2) ^ 6 := by ring
        _ = L ^ 6 := by rw [Real.sq_sqrt hL]]
    norm_num
  apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by positivity)
  rw [hlpow, hrpow]
  exact hXpow

/-- With `M=1`, all three Type-I branches lie below the common
`y^(23/24)` scale. -/
lemma threeBranchOuterNumerator_one_le
    (x : ℝ) (y : ℕ) (hx : 0 < x) (hy : 1 ≤ y)
    (hylower : (y : ℝ) ^ 2 ≤ x)
    (hyupper : x ≤ 24 * (y : ℝ) ^ 2) :
    TypeI.threeBranchOuterNumerator x y 1 ≤
      6192 * (y : ℝ) ^ (23 / 24 : ℝ) *
        Real.sqrt (1 + Real.log (2 * y : ℕ)) := by
  let yr : ℝ := y
  let L : ℝ := 1 + Real.log (2 * y : ℕ)
  have hyr : 1 ≤ yr := by
    dsimp only [yr]
    exact_mod_cast hy
  have hlog : 0 ≤ Real.log (2 * y : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * y by omega))
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hsqrtL : 1 ≤ Real.sqrt L := by rw [Real.one_le_sqrt]; exact hL
  have hpow : 1 ≤ yr ^ (23 / 24 : ℝ) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hyr
      (by norm_num : (0 : ℝ) ≤ 23 / 24)
  have hfirst : 16 * yr ^ 2 / x ≤ 16 := by
    rw [div_le_iff₀ hx]
    nlinarith
  have hsixth := sixth_root_scale_le hyr hx.le hyupper
  have hfourth := fourth_root_scale_le hyr hL0
  unfold TypeI.threeBranchOuterNumerator
  norm_num only [Nat.cast_one, one_pow, mul_one]
  change 16 * yr ^ 2 / x +
      256 * yr * (x / yr ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt L +
      16 * Real.sqrt (Real.sqrt
        ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * L ^ 2)) ≤ _
  have hfirst' : 16 * yr ^ 2 / x ≤
      16 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
    calc
      16 * yr ^ 2 / x ≤ 16 := hfirst
      _ ≤ 16 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
        have honeprod : 1 ≤ yr ^ (23 / 24 : ℝ) * Real.sqrt L :=
          by
            simpa using (mul_le_mul hpow hsqrtL (by norm_num)
              (Real.rpow_nonneg (le_trans (by norm_num) hyr) _))
        nlinarith
  have hsixth' :
      256 * yr * (x / yr ^ 4) ^ (1 / 6 : ℝ) * Real.sqrt L ≤
        6144 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
    calc
      256 * yr * (x / yr ^ 4) ^ (1 / 6 : ℝ) * Real.sqrt L =
          256 * (yr * (x / yr ^ 4) ^ (1 / 6 : ℝ)) * Real.sqrt L := by ring
      _ ≤ 256 * (24 * yr ^ (23 / 24 : ℝ)) * Real.sqrt L := by gcongr
      _ = 6144 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by ring
  have hfourth' :
      16 * Real.sqrt (Real.sqrt
        ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * L ^ 2)) ≤
        32 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
    calc
      16 * Real.sqrt (Real.sqrt
          ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * L ^ 2)) ≤
          16 * (2 * yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by gcongr
      _ = 32 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by ring
  calc
    16 * yr ^ 2 / x +
        256 * yr * (x / yr ^ 4) ^ (1 / 6 : ℝ) * Real.sqrt L +
        16 * Real.sqrt (Real.sqrt
          ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * L ^ 2)) ≤
      16 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) +
        6144 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) +
        32 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) :=
      add_le_add (add_le_add hfirst' hsixth') hfourth'
    _ = 6192 * yr ^ (23 / 24 : ℝ) * Real.sqrt L := by ring

/-- The closed Type-I numerator with the standard cubic cutoff condition.
All three branches remain below `y^(23/24)`. -/
lemma threeBranchOuterNumerator_le
    (x : ℝ) (y M : ℕ) (hx : 0 < x) (hy : 1 ≤ y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y)
    (hylower : (y : ℝ) ^ 2 ≤ x)
    (hyupper : x ≤ 24 * (y : ℝ) ^ 2) :
    TypeI.threeBranchOuterNumerator x y M ≤
      6192 * (y : ℝ) ^ (23 / 24 : ℝ) *
        Real.sqrt (1 + Real.log (2 * y : ℕ)) := by
  let yr : ℝ := y
  let mr : ℝ := M
  let L : ℝ := 1 + Real.log (2 * y : ℕ)
  have hyr : 1 ≤ yr := by dsimp only [yr]; exact_mod_cast hy
  have hmr : 0 ≤ mr := by dsimp only [mr]; positivity
  have hm3r : mr ^ 3 ≤ yr := by
    dsimp only [mr, yr]
    exact_mod_cast hM3
  have hlog : 0 ≤ Real.log (2 * y : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * y by omega))
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hsqrtL : 1 ≤ Real.sqrt L := by rw [Real.one_le_sqrt]; exact hL
  have hpow : 1 ≤ yr ^ (23 / 24 : ℝ) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hyr
      (by norm_num : (0 : ℝ) ≤ 23 / 24)
  have hfirst : 16 * yr ^ 2 / x ≤ 16 := by
    rw [div_le_iff₀ hx]
    nlinarith
  have hsixth :=
    sixth_root_scale_with_M_le hyr hx.le hyupper hmr hm3r
  have hfourth := fourth_root_scale_with_M_le hyr hmr hm3r hL0
  unfold TypeI.threeBranchOuterNumerator
  change 16 * yr ^ 2 / x +
      256 * yr * (x * mr ^ 3 / yr ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt L +
      16 * Real.sqrt (Real.sqrt
        ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * mr * L ^ 2)) ≤ _
  have hfirst' : 16 * yr ^ 2 / x ≤
      16 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
    calc
      16 * yr ^ 2 / x ≤ 16 := hfirst
      _ ≤ 16 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
        have honeprod : 1 ≤ yr ^ (23 / 24 : ℝ) * Real.sqrt L := by
          simpa using (mul_le_mul hpow hsqrtL (by norm_num)
            (Real.rpow_nonneg (le_trans (by norm_num) hyr) _))
        nlinarith
  have hsixth' :
      256 * yr * (x * mr ^ 3 / yr ^ 4) ^ (1 / 6 : ℝ) * Real.sqrt L ≤
        6144 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
    calc
      256 * yr * (x * mr ^ 3 / yr ^ 4) ^ (1 / 6 : ℝ) * Real.sqrt L =
          256 * (yr * (x * mr ^ 3 / yr ^ 4) ^ (1 / 6 : ℝ)) *
            Real.sqrt L := by ring
      _ ≤ 256 * (24 * yr ^ (23 / 24 : ℝ)) * Real.sqrt L := by gcongr
      _ = 6144 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by ring
  have hfourth' :
      16 * Real.sqrt (Real.sqrt
        ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * mr * L ^ 2)) ≤
        32 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
    calc
      16 * Real.sqrt (Real.sqrt
          ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * mr * L ^ 2)) ≤
          16 * (2 * yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by gcongr
      _ = 32 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by ring
  calc
    16 * yr ^ 2 / x +
        256 * yr * (x * mr ^ 3 / yr ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt L +
        16 * Real.sqrt (Real.sqrt
          ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * mr * L ^ 2)) ≤
      16 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) +
        6144 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) +
        32 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) :=
      add_le_add (add_le_add hfirst' hsixth') hfourth'
    _ = 6192 * yr ^ (23 / 24 : ℝ) * Real.sqrt L := by ring

/-- For the convenient choice `M=K=1`, the sole Type-I scale condition is
automatic on the target interval once the integer square root is at least
`12`. -/
lemma typeI_global_condition_M_one
    (n : ℕ) (x : ℝ) (hx : x ≤ 6 * (n : ℝ))
    (hy : 12 ≤ Nat.sqrt n) :
    12 * x * (1 : ℝ) ^ 3 ≤ (Nat.sqrt n : ℝ) ^ 4 := by
  let y := Nat.sqrt n
  have hyR : (12 : ℝ) ≤ y := by exact_mod_cast hy
  have hnupperNat : n < (y + 1) ^ 2 := by
    dsimp only [y]
    simpa only [pow_two] using Nat.lt_succ_sqrt n
  have hnupper : (n : ℝ) < ((y + 1 : ℕ) : ℝ) ^ 2 := by
    norm_num [Nat.succ_eq_add_one, pow_two] at hnupperNat ⊢
    exact_mod_cast hnupperNat
  have hycast : (((y + 1 : ℕ) : ℝ)) = (y : ℝ) + 1 := by norm_num
  rw [hycast] at hnupper
  have hn2 : (n : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by nlinarith
  dsimp only [y] at hyR hn2 ⊢
  norm_num
  nlinarith [sq_nonneg ((Nat.sqrt n : ℝ) ^ 2 - 144)]

/-- At `M = K = 1`, the two Type-I pieces have the required
`n^(23/48)` saving, with a deliberately coarse logarithmic factor. -/
theorem norm_typeI_part_le_explicit
    (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hxlower : (n : ℝ) ≤ x) (hxupper : x ≤ 6 * (n : ℝ))
    (hy : 12 ≤ Nat.sqrt n) :
    ‖VaughanFourSums.sigma1
        (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
        (Vaughan.reciprocalPhase x) 1‖ +
      ‖VaughanFourSums.sigma21
        (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
        (Vaughan.reciprocalPhase x) 1 1‖ ≤
      12384 * (n : ℝ) ^ (23 / 48 : ℝ) *
        Real.log (256 * (n : ℝ)) ^ 2 := by
  let y := Nat.sqrt n
  let y' := Nat.sqrt (2 * n)
  let L : ℝ := 1 + Real.log (2 * y : ℕ)
  let H : ℝ := Real.log (256 * (n : ℝ))
  have hx : 0 < x := lt_of_lt_of_le (by exact_mod_cast hn) hxlower
  have hyone : 1 ≤ y := by dsimp [y]; omega
  have hyy' : y ≤ y' := by
    dsimp [y, y']
    exact Nat.sqrt_le_sqrt (by omega)
  have hy' : y' ≤ 2 * y := by
    dsimp [y, y']
    exact sqrt_two_mul_le_two_sqrt n hn
  have hnupperNat := Nat.lt_succ_sqrt n
  have hnupper : (n : ℝ) < ((y + 1 : ℕ) : ℝ) ^ 2 := by
    norm_num [Nat.succ_eq_add_one, pow_two] at hnupperNat ⊢
    exact_mod_cast hnupperNat
  have hycast : (((y + 1 : ℕ) : ℝ)) = (y : ℝ) + 1 := by norm_num
  rw [hycast] at hnupper
  have hyR : (12 : ℝ) ≤ y := by exact_mod_cast hy
  have hn2 : (n : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by nlinarith
  have hysq : (y : ℝ) ^ 2 ≤ (n : ℝ) := by
    dsimp [y]
    norm_num [pow_two]
    exact_mod_cast Nat.sqrt_le n
  have hyx : (y : ℝ) ^ 2 ≤ x := hysq.trans hxlower
  have hxy : x ≤ 24 * (y : ℝ) ^ 2 := by linarith
  have hglobal := typeI_global_condition_M_one n x hxupper hy
  have hraw := TypeI.norm_sigma1_add_sigma21_le_closed
    x y y' 1 1 hx (by norm_num) hyone hyy' hy' (by simpa using hglobal)
  have hnum := threeBranchOuterNumerator_one_le x y hx hyone hyx hxy
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  have hLle8 : L ≤ Real.log (8 * y : ℕ) := by
    have hlogmul : Real.log (8 * y : ℕ) =
        Real.log 4 + Real.log (2 * y : ℕ) := by
      rw [show 8 * y = 4 * (2 * y) by omega]
      push_cast
      rw [Real.log_mul (by norm_num) (by positivity)]
    dsimp [L]
    rw [hlogmul]
    linarith
  have h8le : 8 * y ≤ 256 * n := by
    have hyn : y ≤ n := Nat.sqrt_le_self n
    omega
  have hlog8H : Real.log (8 * y : ℕ) ≤ H := by
    dsimp [H]
    apply Real.log_le_log
    · positivity
    · exact_mod_cast h8le
  have hLH : L ≤ H := hLle8.trans hlog8H
  have hLone : 1 ≤ L := by
    dsimp [L]
    have hlognonneg : 0 ≤ Real.log (2 * y : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * y by omega))
    linarith
  have hHone : 1 ≤ H := hLone.trans hLH
  have hsqrtLH : Real.sqrt L ≤ H := by
    calc
      Real.sqrt L ≤ Real.sqrt H := Real.sqrt_le_sqrt hLH
      _ ≤ H := Real.sqrt_le_self_iff.mpr (Or.inr hHone)
  have hyPowEq : (y : ℝ) ^ (23 / 24 : ℝ) =
      ((y : ℝ) ^ 2) ^ (23 / 48 : ℝ) := by
    rw [show (23 / 24 : ℝ) = 2 * (23 / 48) by norm_num,
      Real.rpow_mul (by positivity)]
    norm_num [Real.rpow_natCast]
  have hyPow : (y : ℝ) ^ (23 / 24 : ℝ) ≤
      (n : ℝ) ^ (23 / 48 : ℝ) := by
    rw [hyPowEq]
    exact Real.rpow_le_rpow (by positivity) hysq (by norm_num)
  have hlogyH : Real.log (2 * y : ℕ) ≤ H := by
    have : 2 * y ≤ 256 * n := by omega
    dsimp [H]
    apply Real.log_le_log
    · positivity
    · exact_mod_cast this
  have hnum0 : 0 ≤ TypeI.threeBranchOuterNumerator x y 1 :=
    TypeI.threeBranchOuterNumerator_nonneg y 1 hx
  have houter :
      (2 * Real.log (2 * y : ℕ) + Real.log 1) *
        (TypeI.threeBranchOuterNumerator x y 1 * TypeI.dyadicCount 1) ≤
      12384 * (n : ℝ) ^ (23 / 48 : ℝ) * H ^ 2 := by
    rw [show TypeI.dyadicCount 1 = 1 by norm_num [TypeI.dyadicCount],
      Nat.cast_one, mul_one, Real.log_one, add_zero]
    calc
      2 * Real.log (2 * y : ℕ) * TypeI.threeBranchOuterNumerator x y 1 ≤
          2 * H *
            (6192 * (y : ℝ) ^ (23 / 24 : ℝ) * Real.sqrt L) := by
        gcongr
      _ ≤ 2 * H * (6192 * (n : ℝ) ^ (23 / 48 : ℝ) * H) := by
        gcongr
      _ = 12384 * (n : ℝ) ^ (23 / 48 : ℝ) * H ^ 2 := by ring
  exact hraw.trans (by simpa [y, y', L, H] using houter)

/-- Explicit Type-I estimate at the cubic Vaughan cutoff.  This is the
form used by the power-of-two specialization: `M^3 ≤ sqrt n` and
`sqrt n ≥ 144` imply the full scale condition in the closed Type-I theorem. -/
theorem norm_typeI_part_le_explicit_general
    (n M : ℕ) (x : ℝ) (hn : 1 ≤ n) (hM : 1 ≤ M)
    (hM3 : M ^ 3 ≤ Nat.sqrt n)
    (hxlower : (n : ℝ) ≤ x) (hxupper : x ≤ 6 * (n : ℝ))
    (hy : 144 ≤ Nat.sqrt n) :
    ‖VaughanFourSums.sigma1
        (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
        (Vaughan.reciprocalPhase x) M‖ +
      ‖VaughanFourSums.sigma21
        (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
        (Vaughan.reciprocalPhase x) M M‖ ≤
      55728 * (n : ℝ) ^ (27 / 56 : ℝ) *
        Real.log (256 * (n : ℝ)) ^ 3 := by
  let y := Nat.sqrt n
  let y' := Nat.sqrt (2 * n)
  let L : ℝ := 1 + Real.log (2 * y : ℕ)
  let H : ℝ := Real.log (256 * (n : ℝ))
  have hx : 0 < x := lt_of_lt_of_le (by exact_mod_cast hn) hxlower
  have hyone : 1 ≤ y := by dsimp [y]; omega
  have hyy' : y ≤ y' := by
    dsimp [y, y']
    exact Nat.sqrt_le_sqrt (by omega)
  have hy' : y' ≤ 2 * y := by
    dsimp [y, y']
    exact sqrt_two_mul_le_two_sqrt n hn
  have hMy : M ≤ y := by
    dsimp [y]
    have hMM3 : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) M
    omega
  have hnupperNat := Nat.lt_succ_sqrt n
  have hnupper : (n : ℝ) < ((y + 1 : ℕ) : ℝ) ^ 2 := by
    norm_num [Nat.succ_eq_add_one, pow_two] at hnupperNat ⊢
    exact_mod_cast hnupperNat
  have hycast : (((y + 1 : ℕ) : ℝ)) = (y : ℝ) + 1 := by norm_num
  rw [hycast] at hnupper
  have hyR : (144 : ℝ) ≤ y := by exact_mod_cast hy
  have hn2 : (n : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by nlinarith
  have hysq : (y : ℝ) ^ 2 ≤ (n : ℝ) := by
    dsimp [y]
    norm_num [pow_two]
    exact_mod_cast Nat.sqrt_le n
  have hyx : (y : ℝ) ^ 2 ≤ x := hysq.trans hxlower
  have hxy : x ≤ 24 * (y : ℝ) ^ 2 := by linarith
  have hM3R : (M : ℝ) ^ 3 ≤ (y : ℝ) := by exact_mod_cast hM3
  have hglobal : 12 * x * (M : ℝ) ^ 3 ≤ (y : ℝ) ^ 4 := by
    calc
      12 * x * (M : ℝ) ^ 3 ≤ 12 * (12 * (y : ℝ) ^ 2) * (y : ℝ) := by
        gcongr
        linarith
      _ = 144 * (y : ℝ) ^ 3 := by ring
      _ ≤ (y : ℝ) * (y : ℝ) ^ 3 := by gcongr
      _ = (y : ℝ) ^ 4 := by ring
  have hraw := TypeI.norm_sigma1_add_sigma21_le_closed
    x y y' M M hx hM hMy hyy' hy' hglobal
  have hnum :=
    threeBranchOuterNumerator_le x y M hx hyone hM hM3 hyx hxy
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  have hLle8 : L ≤ Real.log (8 * y : ℕ) := by
    have hlogmul : Real.log (8 * y : ℕ) =
        Real.log 4 + Real.log (2 * y : ℕ) := by
      rw [show 8 * y = 4 * (2 * y) by omega]
      push_cast
      rw [Real.log_mul (by norm_num) (by positivity)]
    dsimp [L]
    rw [hlogmul]
    linarith
  have h8le : 8 * y ≤ 256 * n := by
    have hyn : y ≤ n := Nat.sqrt_le_self n
    omega
  have hlog8H : Real.log (8 * y : ℕ) ≤ H := by
    dsimp [H]
    apply Real.log_le_log
    · positivity
    · exact_mod_cast h8le
  have hLH : L ≤ H := hLle8.trans hlog8H
  have hLone : 1 ≤ L := by
    dsimp [L]
    have hlognonneg : 0 ≤ Real.log (2 * y : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * y by omega))
    linarith
  have hHone : 1 ≤ H := hLone.trans hLH
  have hsqrtLH : Real.sqrt L ≤ H := by
    calc
      Real.sqrt L ≤ Real.sqrt H := Real.sqrt_le_sqrt hLH
      _ ≤ H := Real.sqrt_le_self_iff.mpr (Or.inr hHone)
  have hlogyH : Real.log (2 * y : ℕ) ≤ H := by
    have : 2 * y ≤ 256 * n := by omega
    dsimp [H]
    apply Real.log_le_log
    · positivity
    · exact_mod_cast this
  have hlogMH : Real.log M ≤ H := by
    dsimp [H]
    apply Real.log_le_log
    · positivity
    · exact_mod_cast (show M ≤ 256 * n by omega)
  have houterCoeff :
      2 * Real.log (2 * y : ℕ) + Real.log M ≤ 3 * H := by
    linarith
  have hlogM0 : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : Real.log M / Real.log 2 ≤ 2 * Real.log M := by
    rw [div_le_iff₀ hlog2]
    nlinarith [Real.log_two_gt_d9]
  have hcountRaw := TypeI.dyadicCount_cast_le_log_div_add_one
    (show M ≠ 0 by omega)
  have hcount : (TypeI.dyadicCount M : ℝ) ≤ 3 * H := by
    calc
      (TypeI.dyadicCount M : ℝ) ≤ Real.log M / Real.log 2 + 1 := hcountRaw
      _ ≤ 2 * Real.log M + 1 := by linarith
      _ ≤ 3 * H := by linarith
  have hyPowEq : (y : ℝ) ^ (23 / 24 : ℝ) =
      ((y : ℝ) ^ 2) ^ (23 / 48 : ℝ) := by
    rw [show (23 / 24 : ℝ) = 2 * (23 / 48) by norm_num,
      Real.rpow_mul (by positivity)]
    norm_num [Real.rpow_natCast]
  have hyPow : (y : ℝ) ^ (23 / 24 : ℝ) ≤
      (n : ℝ) ^ (27 / 56 : ℝ) := by
    calc
      (y : ℝ) ^ (23 / 24 : ℝ) =
          ((y : ℝ) ^ 2) ^ (23 / 48 : ℝ) := hyPowEq
      _ ≤ (n : ℝ) ^ (23 / 48 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hysq (by norm_num)
      _ ≤ (n : ℝ) ^ (27 / 56 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hn) (by norm_num)
  have hnum0 : 0 ≤ TypeI.threeBranchOuterNumerator x y M :=
    TypeI.threeBranchOuterNumerator_nonneg y M hx
  have houter :
      (2 * Real.log (2 * y : ℕ) + Real.log M) *
        (TypeI.threeBranchOuterNumerator x y M * TypeI.dyadicCount M) ≤
      55728 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 3 := by
    calc
      (2 * Real.log (2 * y : ℕ) + Real.log M) *
          (TypeI.threeBranchOuterNumerator x y M * TypeI.dyadicCount M) ≤
        (3 * H) *
          ((6192 * (y : ℝ) ^ (23 / 24 : ℝ) * Real.sqrt L) *
            (3 * H)) := by gcongr
      _ ≤ (3 * H) *
          ((6192 * (n : ℝ) ^ (27 / 56 : ℝ) * H) * (3 * H)) := by
        gcongr
      _ = 55728 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 3 := by ring
  exact hraw.trans (by simpa [y, y', L, H] using houter)

/-- The dyadic Vaughan cutoff used in the final power-of-two argument has
cube at most the square-root endpoint. -/
lemma vaughanCutoff_cube_le_sqrt (k : ℕ) :
    (2 ^ (k / 6)) ^ 3 ≤ Nat.sqrt (2 ^ k) := by
  rw [Nat.le_sqrt']
  calc
    ((2 ^ (k / 6)) ^ 3) ^ 2 = 2 ^ (6 * (k / 6)) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    _ ≤ 2 ^ k := by
      apply Nat.pow_le_pow_right (by norm_num)
      have := Nat.div_mul_le_self k 6
      omega

/-- The square-root endpoint is within the fixed factor `8` of the cube
of the dyadic Vaughan cutoff.  This is the complementary rounding estimate
to `vaughanCutoff_cube_le_sqrt`; its only loss is the residue of `k` modulo
six. -/
lemma sqrt_two_pow_le_eight_vaughanCutoff_cube (k : ℕ) :
    Nat.sqrt (2 ^ k) ≤ 8 * (2 ^ (k / 6)) ^ 3 := by
  have hkdiv : k ≤ 6 * (k / 6) + 6 := by
    omega
  have hp : 2 ^ k ≤ 2 ^ (6 * (k / 6) + 6) := by
    exact Nat.pow_le_pow_right (by norm_num) hkdiv
  calc
    Nat.sqrt (2 ^ k) ≤ Nat.sqrt ((8 * (2 ^ (k / 6)) ^ 3) ^ 2) := by
      apply Nat.sqrt_le_sqrt
      calc
        2 ^ k ≤ 2 ^ (6 * (k / 6) + 6) := hp
        _ = (8 * (2 ^ (k / 6)) ^ 3) ^ 2 := by
          have hcut : ((2 ^ (k / 6)) ^ 3) ^ 2 =
              2 ^ (6 * (k / 6)) := by
            rw [← pow_mul, ← pow_mul]
            congr 1
            omega
          rw [mul_pow, hcut, pow_add]
          norm_num
          simp [mul_comm]
    _ = 8 * (2 ^ (k / 6)) ^ 3 := Nat.sqrt_eq' _

lemma one_le_vaughanCutoff (k : ℕ) : 1 ≤ 2 ^ (k / 6) := by
  exact Nat.one_le_pow (k / 6) 2 (by norm_num)

lemma large_sqrt_two_pow (k : ℕ) (hk : 30 ≤ k) :
    144 ≤ Nat.sqrt (2 ^ k) := by
  rw [Nat.le_sqrt]
  calc
    144 * 144 ≤ 2 ^ 15 := by norm_num
    _ ≤ 2 ^ k := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega

/-- Above the final cutoff, the dyadic Vaughan parameter is large enough
for the uniform Type-II block estimate. -/
lemma large_vaughanCutoff (k : ℕ) (hk : 8192 ≤ k) :
    4608 ≤ 2 ^ (k / 6) := by
  calc
    4608 ≤ 2 ^ 13 := by norm_num
    _ ≤ 2 ^ (k / 6) := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega

/-- Power-of-two specialization of the explicit Type-I estimate, using
the dyadic cutoff `2^(k/6)`. -/
theorem norm_typeI_part_two_pow_le
    (k : ℕ) (x : ℝ) (hk : 30 ≤ k)
    (hxlower : ((2 ^ k : ℕ) : ℝ) ≤ x)
    (hxupper : x ≤ 6 * ((2 ^ k : ℕ) : ℝ)) :
    ‖VaughanFourSums.sigma1
        (Finset.Ioc (Nat.sqrt (2 ^ k)) (Nat.sqrt (2 * 2 ^ k)))
        (Vaughan.reciprocalPhase x) (2 ^ (k / 6))‖ +
      ‖VaughanFourSums.sigma21
        (Finset.Ioc (Nat.sqrt (2 ^ k)) (Nat.sqrt (2 * 2 ^ k)))
        (Vaughan.reciprocalPhase x) (2 ^ (k / 6)) (2 ^ (k / 6))‖ ≤
      55728 * (((2 ^ k : ℕ) : ℝ)) ^ (27 / 56 : ℝ) *
        Real.log (256 * (((2 ^ k : ℕ) : ℝ))) ^ 3 := by
  exact norm_typeI_part_le_explicit_general
    (2 ^ k) (2 ^ (k / 6)) x (Nat.one_le_pow k 2 (by norm_num))
      (one_le_vaughanCutoff k) (vaughanCutoff_cube_le_sqrt k)
      hxlower hxupper (large_sqrt_two_pow k hk)

/-- The complete Granville--Ramaré upper estimate on a power of two.
The deliberately generous coefficient `10^12` absorbs the three explicit
Vaughan contributions; the exponent and six logarithms are kept in the
exact form consumed by the final numerical cutoff. -/
theorem norm_mangoldtSum_two_pow_le_final
    (k : ℕ) (x : ℝ) (hk : 8192 ≤ k)
    (hxlower : (((2 : ℕ) ^ k : ℕ) : ℝ) ≤ x)
    (hxupper : x ≤ 6 * (((2 : ℕ) ^ k : ℕ) : ℝ)) :
    ‖mangoldtSum (2 ^ k) x‖ ≤
      (10 ^ 12 : ℝ) * (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (27 / 56 : ℝ) *
        Real.log (256 * (((2 : ℕ) ^ k : ℕ) : ℝ)) ^ 6 := by
  let n : ℕ := 2 ^ k
  let y : ℕ := Nat.sqrt n
  let y' : ℕ := Nat.sqrt (2 * n)
  let M : ℕ := 2 ^ (k / 6)
  let H : ℝ := Real.log (256 * (n : ℝ))
  have hn : 1 ≤ n := by
    dsimp only [n]
    exact Nat.one_le_pow k 2 (by norm_num)
  have hy : 1 ≤ y := by
    dsimp only [y]
    exact Nat.sqrt_pos.mpr (by omega)
  have hyy' : y ≤ y' := by
    dsimp only [y, y', n]
    exact Nat.sqrt_le_sqrt (by omega)
  have hy' : y' ≤ 2 * y := by
    dsimp only [y, y']
    exact sqrt_two_mul_le_two_sqrt n hn
  have hM : 1 ≤ M := by
    dsimp only [M]
    exact one_le_vaughanCutoff k
  have hM3 : M ^ 3 ≤ y := by
    simpa only [M, y, n] using vaughanCutoff_cube_le_sqrt k
  have hyM : y ≤ 8 * M ^ 3 := by
    simpa only [M, y, n] using
      sqrt_two_pow_le_eight_vaughanCutoff_cube k
  have hMlarge : 4608 ≤ M := by
    simpa only [M] using large_vaughanCutoff k hk
  have hMy : M ≤ y := by
    exact (Nat.le_self_pow (by norm_num) M).trans hM3
  have hysq : y ^ 2 ≤ n := by
    dsimp only [y]
    exact Nat.sqrt_le' n
  have hysqR : (y : ℝ) ^ 2 ≤ (n : ℝ) := by
    exact_mod_cast hysq
  have hxYlower : (y : ℝ) ^ 2 ≤ x := hysqR.trans (by
    simpa only [n] using hxlower)
  have hy144 : 144 ≤ y := by
    simpa only [y, n] using large_sqrt_two_pow k (by omega)
  have hnupperNat : n < (y + 1) ^ 2 := by
    dsimp only [y]
    simpa only [pow_two] using Nat.lt_succ_sqrt n
  have hnupper : (n : ℝ) < (y + 1 : ℝ) ^ 2 := by
    have hycast : (((y + 1 : ℕ) : ℝ)) = (y : ℝ) + 1 := by norm_num
    rw [← hycast]
    exact_mod_cast hnupperNat
  have hyR : (144 : ℝ) ≤ y := by exact_mod_cast hy144
  have hn2 : (n : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by
    nlinarith
  have hxYupper : x ≤ 12 * (y : ℝ) ^ 2 := by
    calc
      x ≤ 6 * (n : ℝ) := by simpa only [n] using hxupper
      _ ≤ 12 * (y : ℝ) ^ 2 := by nlinarith
  have hI :
      ‖VaughanFourSums.sigma1 (Finset.Ioc y y')
          (Vaughan.reciprocalPhase x) M‖ +
        ‖VaughanFourSums.sigma21 (Finset.Ioc y y')
          (Vaughan.reciprocalPhase x) M M‖ ≤
        55728 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 3 := by
    simpa only [n, y, y', M, H] using
      norm_typeI_part_two_pow_le k x (by omega) hxlower hxupper
  have h22 := TypeIIGlobal.norm_sigma22_le_closed_original
    (x := x) (n := n) (y := y) (y' := y') (M := M)
      hy hyy' hy' hM hM3 hyM hMlarge hysq hxYlower hxYupper
  have h3 := TypeIIGlobal.norm_sigma3_le_closed_original
    (x := x) (n := n) (y := y) (y' := y') (M := M)
      hy hyy' hy' hM hM3 hyM hMlarge hysq hxYlower hxYupper
  have hmain := norm_mangoldtSum_le_four_sums n M M x hM hMy
  have hlog256 : (1 : ℝ) ≤ Real.log 256 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    have hlog2 := Real.log_two_gt_d9
    norm_num at hlog2 ⊢
    nlinarith
  have harg : (256 : ℝ) ≤ 256 * (n : ℝ) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hH : 1 ≤ H := by
    dsimp only [H]
    exact hlog256.trans (Real.log_le_log (by norm_num) harg)
  have hH36 : H ^ 3 ≤ H ^ 6 := by
    have hH3 : 1 ≤ H ^ 3 := one_le_pow₀ hH
    calc
      H ^ 3 = H ^ 3 * 1 := by ring
      _ ≤ H ^ 3 * H ^ 3 :=
        mul_le_mul_of_nonneg_left hH3 (by positivity)
      _ = H ^ 6 := by ring
  have hscale0 : 0 ≤ (n : ℝ) ^ (27 / 56 : ℝ) := by positivity
  have hH60 : 0 ≤ H ^ 6 := by positivity
  calc
    ‖mangoldtSum (2 ^ k) x‖ = ‖mangoldtSum n x‖ := by rfl
    _ ≤
        (‖VaughanFourSums.sigma1 (Finset.Ioc y y')
            (Vaughan.reciprocalPhase x) M‖ +
          ‖VaughanFourSums.sigma21 (Finset.Ioc y y')
            (Vaughan.reciprocalPhase x) M M‖) +
          ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
            (Vaughan.reciprocalPhase x) M M‖ +
          ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
            (Vaughan.reciprocalPhase x) M M‖ := hmain
    _ ≤ 55728 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 3 +
          18432 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 +
          36864 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 :=
      add_le_add (add_le_add hI h22) h3
    _ ≤ 55728 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 +
          18432 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 +
          36864 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 := by
      gcongr
    _ = (111024 : ℝ) * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 := by ring
    _ ≤ (10 ^ 12 : ℝ) * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 := by
      gcongr <;> norm_num
    _ = (10 ^ 12 : ℝ) * (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (27 / 56 : ℝ) *
        Real.log (256 * (((2 : ℕ) ^ k : ℕ) : ℝ)) ^ 6 := by rfl

/-- A completely instantiated Section 9 bound with `M=K=1` and zero
near-pair threshold.  Its right hand side is a closed finite expression in
`n` and `x`; no scale or analytic premise remains. -/
theorem norm_mangoldtSum_le_gr9UpperMajorant_one
    (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : 0 < x)
    (hxupper : x ≤ 6 * (n : ℝ)) (hy : 12 ≤ Nat.sqrt n) :
    ‖mangoldtSum n x‖ ≤ gr9UpperMajorant n 1 x := by
  apply norm_mangoldtSum_le_gr9UpperMajorant n 1 x hn hx (by norm_num)
  · omega
  · simpa using typeI_global_condition_M_one n x hxupper hy

/-- The complete elementary `Σ₃` coefficient product.  The weakened
Proposition 10.1 contributes three logarithms and the elementary Mangoldt
second moment contributes two. -/
lemma sigma3_l2_product_sq_le
    (M L R : ℕ) (y Q : ℝ) (hM : 1 ≤ M) (hR : 1 ≤ R)
    (hLR : ((L : ℝ) * (R : ℝ)) ≤ y)
    (hlogM : Real.log M + 3 ≤ Q)
    (hlogR : Real.log (2 * R : ℕ) ≤ Q) :
    TypeII.l2Norm (Finset.Ioc L (2 * L))
          (fun l => ((VaughanFourSums.aCoeff M l : ℝ) : ℂ)) ^ 2 *
        TypeII.l2Norm (Finset.Ioc R (2 * R))
          (fun r => ((ArithmeticFunction.vonMangoldt r : ℝ) : ℂ)) ^ 2 ≤
      (8 / 9 : ℝ) * y * Q ^ 5 := by
  have hlogM0 : 0 ≤ Real.log M + 3 := by
    have : 0 ≤ Real.log (M : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hM)
    linarith
  have hlogR0 : 0 ≤ Real.log (2 * R : ℕ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * R by omega)
  have hQ0 : 0 ≤ Q := hlogM0.trans hlogM
  have hy : 0 ≤ y :=
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hLR
  have ha := l2Norm_aCoeff_sq_le M L hM
  have hb := l2Norm_vonMangoldt_sq_le R hR
  have hb0 : 0 ≤ TypeII.l2Norm (Finset.Ioc R (2 * R))
      (fun r => ((ArithmeticFunction.vonMangoldt r : ℝ) : ℂ)) ^ 2 :=
    sq_nonneg _
  calc
    TypeII.l2Norm (Finset.Ioc L (2 * L))
          (fun l => ((VaughanFourSums.aCoeff M l : ℝ) : ℂ)) ^ 2 *
        TypeII.l2Norm (Finset.Ioc R (2 * R))
          (fun r => ((ArithmeticFunction.vonMangoldt r : ℝ) : ℂ)) ^ 2 ≤
        ((8 / 9 : ℝ) * (L : ℝ) * (Real.log M + 3) ^ 3) *
          ((R : ℝ) * Real.log (2 * R : ℕ) ^ 2) := by
      exact mul_le_mul ha hb hb0 (by positivity)
    _ = (8 / 9 : ℝ) * ((L : ℝ) * (R : ℝ)) *
          ((Real.log M + 3) ^ 3 * Real.log (2 * R : ℕ) ^ 2) := by ring
    _ ≤ (8 / 9 : ℝ) * y *
          ((Real.log M + 3) ^ 3 * Real.log (2 * R : ℕ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLR (by norm_num))
        (mul_nonneg (pow_nonneg hlogM0 3) (pow_nonneg hlogR0 2))
    _ ≤ (8 / 9 : ℝ) * y * (Q ^ 3 * Q ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul
          (pow_le_pow_left₀ hlogM0 hlogM 3)
          (pow_le_pow_left₀ hlogR0 hlogR 2)
          (pow_nonneg hlogR0 2) (pow_nonneg hQ0 3))
        (mul_nonneg (by norm_num) hy)
    _ = (8 / 9 : ℝ) * y * Q ^ 5 := by ring

/-- The complete `Σ₂,₂` dyadic coefficient product.  If the two block
lengths satisfy `L*R ≤ y`, its squared `L² × L²` factor is bounded by
`y log(2R)^2`. -/
lemma sigma22_l2_product_sq_le
    (M K L R : ℕ) (y Q : ℝ) (hR : 1 ≤ R)
    (hLR : ((L : ℝ) * (R : ℝ)) ≤ y)
    (hQ : Real.log (2 * R : ℕ) ≤ Q) :
    TypeII.l2Norm (Finset.Ioc L (2 * L)) (fun _ => (1 : ℂ)) ^ 2 *
        TypeII.l2Norm (Finset.Ioc R (2 * R))
          (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ)) ^ 2 ≤
      y * Q ^ 2 := by
  have hlog0 : 0 ≤ Real.log (2 * R : ℕ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * R by omega)
  have hQ0 : 0 ≤ Q := hlog0.trans hQ
  have hones :
      TypeII.l2Norm (Finset.Ioc L (2 * L)) (fun _ => (1 : ℂ)) ^ 2 = L := by
    rw [TypeII.l2Norm_sq]
    have hcard : (Finset.Ioc L (2 * L)).card = L := by
      simp
      omega
    simp [hcard]
  rw [hones]
  calc
    (L : ℝ) *
          TypeII.l2Norm (Finset.Ioc R (2 * R))
            (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ)) ^ 2 ≤
        (L : ℝ) * ((R : ℝ) * Real.log (2 * R : ℕ) ^ 2) := by
      gcongr
      exact l2Norm_bCoeff_sq_le M K R hR
    _ = ((L : ℝ) * (R : ℝ)) * Real.log (2 * R : ℕ) ^ 2 := by ring
    _ ≤ y * Real.log (2 * R : ℕ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hLR (pow_nonneg hlog0 2)
    _ ≤ y * Q ^ 2 := by
      have hy : 0 ≤ y :=
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hLR
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlog0 hQ 2) hy

/-- Coarse coefficient assembly for `Σ₃` when Proposition 10.1 is used with
one extra logarithm.  The hypotheses are exactly the two mean-square bounds
and the hyperbola constraint `L*R ≤ y`; the conclusion is the common
`y*Q^4` scale needed by the Type-II estimate. -/
lemma sigma3_coefficient_sq_product_le_coarse
    {A₂ B₂ L R y Q : ℝ}
    (hB₂ : 0 ≤ B₂) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (ha : A₂ ≤ (4 / 3 : ℝ) * L * Q ^ 3)
    (hb : B₂ ≤ 2 * R * Q)
    (hLR : L * R ≤ y) :
    A₂ * B₂ ≤ (8 / 3 : ℝ) * y * Q ^ 4 := by
  calc
    A₂ * B₂ ≤ ((4 / 3 : ℝ) * L * Q ^ 3) * (2 * R * Q) := by
      exact mul_le_mul ha hb hB₂ (by positivity)
    _ = (8 / 3 : ℝ) * (L * R) * Q ^ 4 := by ring
    _ ≤ (8 / 3 : ℝ) * y * Q ^ 4 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLR (by norm_num)) (pow_nonneg hQ 4)

/-- Fully elementary variant of the preceding assembly, using the pointwise
bound `Λ(r) ≤ log r`.  It costs two logarithms in the von Mangoldt second
moment, hence the common coefficient scale is `y*Q^5`. -/
lemma sigma3_coefficient_sq_product_le_elementary
    {A₂ B₂ L R y Q : ℝ}
    (hB₂ : 0 ≤ B₂) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (ha : A₂ ≤ (4 / 3 : ℝ) * L * Q ^ 3)
    (hb : B₂ ≤ R * Q ^ 2)
    (hLR : L * R ≤ y) :
    A₂ * B₂ ≤ (4 / 3 : ℝ) * y * Q ^ 5 := by
  calc
    A₂ * B₂ ≤ ((4 / 3 : ℝ) * L * Q ^ 3) * (R * Q ^ 2) := by
      exact mul_le_mul ha hb hB₂ (by positivity)
    _ = (4 / 3 : ℝ) * (L * R) * Q ^ 5 := by ring
    _ ≤ (4 / 3 : ℝ) * y * Q ^ 5 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLR (by norm_num)) (pow_nonneg hQ 5)

/-- Coarse coefficient assembly for `Σ₂,₂`. -/
lemma sigma22_coefficient_sq_product_le_coarse
    {A₂ B₂ L R y Q : ℝ}
    (hB₂ : 0 ≤ B₂) (hL : 0 ≤ L) (hR : 0 ≤ R) (hQ : 1 ≤ Q)
    (ha : A₂ ≤ L)
    (hb : B₂ ≤ R * Q ^ 2)
    (hLR : L * R ≤ y) :
    A₂ * B₂ ≤ y * Q ^ 4 := by
  have hQ0 : 0 ≤ Q := le_trans (by norm_num) hQ
  have hy : 0 ≤ y := (mul_nonneg hL hR).trans hLR
  calc
    A₂ * B₂ ≤ L * (R * Q ^ 2) := by
      exact mul_le_mul ha hb hB₂ hL
    _ = (L * R) * Q ^ 2 := by ring
    _ ≤ y * Q ^ 2 := by
      exact mul_le_mul_of_nonneg_right hLR (pow_nonneg hQ0 2)
    _ ≤ y * Q ^ 4 := by
      gcongr
      nlinarith [sq_nonneg (Q ^ 2 - 1)]

/-- Put the two elementary coefficient estimates on the common `y*Q^5`
scale.  This intentionally sacrifices the small decimal constants in favor
of the round factor `2`, appropriate for the coarse final constant `100`. -/
lemma combined_coefficient_product_le_two
    {A₁ B₁ A₂ B₂ y Q : ℝ}
    (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (hA₂ : 0 ≤ A₂) (hB₂ : 0 ≤ B₂)
    (hy : 0 ≤ y) (hQ : 1 ≤ Q)
    (h₁ : A₁ ^ 2 * B₁ ^ 2 ≤ y * Q ^ 2)
    (h₂ : A₂ ^ 2 * B₂ ^ 2 ≤ (8 / 9 : ℝ) * y * Q ^ 5) :
    A₁ * B₁ + A₂ * B₂ ≤ 2 * Real.sqrt (y * Q ^ 5) := by
  have hQ0 : 0 ≤ Q := le_trans (by norm_num) hQ
  have hQpow : Q ^ 2 ≤ Q ^ 5 := by
    have hQ2 : 1 ≤ Q ^ 2 := one_le_pow₀ hQ
    have hQ3 : 1 ≤ Q ^ 3 := one_le_pow₀ hQ
    calc
      Q ^ 2 ≤ Q ^ 2 * Q ^ 3 := by nlinarith [pow_nonneg hQ0 2]
      _ = Q ^ 5 := by ring
  have hcommon0 : 0 ≤ y * Q ^ 5 := mul_nonneg hy (pow_nonneg hQ0 5)
  have h₁' : A₁ ^ 2 * B₁ ^ 2 ≤ y * Q ^ 5 :=
    h₁.trans (mul_le_mul_of_nonneg_left hQpow hy)
  have h₂' : A₂ ^ 2 * B₂ ^ 2 ≤ y * Q ^ 5 := by
    calc
      A₂ ^ 2 * B₂ ^ 2 ≤ (8 / 9 : ℝ) * y * Q ^ 5 := h₂
      _ = (8 / 9 : ℝ) * (y * Q ^ 5) := by ring
      _ ≤ 1 * (y * Q ^ 5) :=
        mul_le_mul_of_nonneg_right (by norm_num) hcommon0
      _ = y * Q ^ 5 := by ring
  have hp₁ : A₁ * B₁ ≤ Real.sqrt (y * Q ^ 5) := by
    apply (sq_le_sq₀ (mul_nonneg hA₁ hB₁) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hcommon0]
    nlinarith
  have hp₂ : A₂ * B₂ ≤ Real.sqrt (y * Q ^ 5) := by
    apply (sq_le_sq₀ (mul_nonneg hA₂ hB₂) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hcommon0]
    nlinarith
  linarith

/-- If nonnegative `A,B` satisfy a bound on `A²B²`, their product is
bounded by the corresponding square root.  This is the exact ordered-field
step needed after the coefficient mean-square estimates. -/
lemma mul_le_sqrt_of_sq_mul_sq_le {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : A ^ 2 * B ^ 2 ≤ C) :
    A * B ≤ Real.sqrt C := by
  apply (sq_le_sq₀ (mul_nonneg hA hB) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hC]
  nlinarith

/-- The `0.023` coefficient estimate in the form consumed by a bilinear
`L² × L²` estimate. -/
lemma coefficient_product_le_sqrt_023 {A B y L : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hy : 0 ≤ y) (hL : 0 ≤ L)
    (h : A ^ 2 * B ^ 2 ≤ (23 / 1000 : ℝ) * y * L ^ 3) :
    A * B ≤ Real.sqrt ((23 / 1000 : ℝ) * y * L ^ 3) := by
  exact mul_le_sqrt_of_sq_mul_sq_le hA hB (by positivity) h

/-- The `0.62` coefficient estimate in the form consumed by a bilinear
`L² × L²` estimate. -/
lemma coefficient_product_le_sqrt_062 {A B y L : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hy : 0 ≤ y) (hL : 0 ≤ L)
    (h : A ^ 2 * B ^ 2 ≤ (31 / 50 : ℝ) * y * L ^ 3) :
    A * B ≤ Real.sqrt ((31 / 50 : ℝ) * y * L ^ 3) := by
  exact mul_le_sqrt_of_sq_mul_sq_le hA hB (by positivity) h

/-- A rational enclosure for the two square-root coefficients. -/
lemma sqrt_023_add_sqrt_062_le :
    Real.sqrt (23 / 1000 : ℝ) + Real.sqrt (31 / 50 : ℝ) ≤ 47 / 50 := by
  have h23 : Real.sqrt (23 / 1000 : ℝ) ≤ 19 / 125 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have h62 : Real.sqrt (31 / 50 : ℝ) ≤ 197 / 250 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  linarith

/-- A tight rational enclosure, retained separately for the published
`9.52` calculation. -/
lemma sqrt_023_add_sqrt_062_le_tight :
    Real.sqrt (23 / 1000 : ℝ) + Real.sqrt (31 / 50 : ℝ) ≤
      939059 / 1000000 := by
  have h23 : Real.sqrt (23 / 1000 : ℝ) ≤ 75829 / 500000 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have h62 : Real.sqrt (31 / 50 : ℝ) ≤ 787401 / 1000000 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  linarith

/-- Multiplication by the Corollary 9.7 coefficient gives a coefficient
strictly below `10`.  The paper obtains the sharper `9.52` after retaining
the separate scales of the two bilinear terms; this coarser joint estimate
is useful for checking the common coefficient bookkeeping. -/
lemma corollary_9_7_two_coefficients_lt_ten :
    (527 / 50 : ℝ) *
        (Real.sqrt (23 / 1000 : ℝ) + Real.sqrt (31 / 50 : ℝ)) < 10 := by
  calc
    (527 / 50 : ℝ) *
          (Real.sqrt (23 / 1000 : ℝ) + Real.sqrt (31 / 50 : ℝ)) ≤
        (527 / 50 : ℝ) * (47 / 50) := by
      gcongr
      exact sqrt_023_add_sqrt_062_le
    _ < 10 := by norm_num

/-- The exact numerical rounding in Granville--Ramaré (9.8).  The factor
`2 / (3 log 2)` is the dyadic-block count in (9.2); retaining it recovers the
published coefficient `9.52`. -/
lemma gr_bilinear_coefficient_le_952 :
    (527 / 50 : ℝ) * (2 / (3 * Real.log 2)) *
        (Real.sqrt (23 / 1000 : ℝ) + Real.sqrt (31 / 50 : ℝ)) ≤
      238 / 25 := by
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdenpos : 0 < 3 * Real.log 2 := mul_pos (by norm_num) hlogpos
  have hdecimalpos : (0 : ℝ) < 3 * 0.6931471803 := by norm_num
  have hratio :
      (2 : ℝ) / (3 * Real.log 2) ≤ 2 / (3 * 0.6931471803) := by
    rw [div_le_div_iff₀ hdenpos hdecimalpos]
    nlinarith [Real.log_two_gt_d9]
  calc
    (527 / 50 : ℝ) * (2 / (3 * Real.log 2)) *
          (Real.sqrt (23 / 1000 : ℝ) + Real.sqrt (31 / 50 : ℝ)) ≤
        (527 / 50 : ℝ) * (2 / (3 * 0.6931471803)) *
          (939059 / 1000000) := by
      gcongr
      exact sqrt_023_add_sqrt_062_le_tight
    _ ≤ 238 / 25 := by norm_num

/-- The final coefficient specialization in Theorem 9.  After substituting
`x ≤ 20 n` and `y = sqrt n`, the power term contributes `20^(1/12)`;
rewriting `log (16 sqrt n) = (1/2) log (256 n)` contributes
`2^(-11/4)`.  Raising the remaining comparison to the twelfth power turns
it into an exact rational calculation. -/
lemma gr_specialization_coefficient_le_32 :
    (50 / 3 : ℝ) *
        ((20 : ℝ) ^ (1 / 12 : ℝ) / (2 : ℝ) ^ (11 / 4 : ℝ)) ≤
      16 / 5 := by
  have hnum :
      ((20 : ℝ) ^ (1 / 12 : ℝ)) ^ 12 = 20 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 20)]
    norm_num [Real.rpow_one]
  have hden :
      ((2 : ℝ) ^ (11 / 4 : ℝ)) ^ 12 = 2 ^ 33 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.rpow_natCast]
  have hpow :
      ((20 : ℝ) ^ (1 / 12 : ℝ) / (2 : ℝ) ^ (11 / 4 : ℝ)) ^ 12 ≤
        (24 / 125 : ℝ) ^ 12 := by
    rw [div_pow, hnum, hden]
    norm_num
  have hratio :
      (20 : ℝ) ^ (1 / 12 : ℝ) / (2 : ℝ) ^ (11 / 4 : ℝ) ≤
        24 / 125 := by
    exact le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0)
      (by norm_num) hpow
  calc
    (50 / 3 : ℝ) *
          ((20 : ℝ) ^ (1 / 12 : ℝ) / (2 : ℝ) ^ (11 / 4 : ℝ)) ≤
        (50 / 3 : ℝ) * (24 / 125 : ℝ) := by gcongr
    _ = 16 / 5 := by norm_num

/-! ## Norm assembly -/

/-- Add two independently estimated bilinear pieces and propagate the
published `10.54` block constant together with the two coefficient bounds.
The conclusion deliberately keeps the square roots unfactored, avoiding any
extra positivity assumptions on the scale variables. -/
lemma norm_add_bilinear_pieces_le
    {z₁ z₂ : ℂ} {A₁ B₁ A₂ B₂ y L T : ℝ}
    (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (hA₂ : 0 ≤ A₂) (hB₂ : 0 ≤ B₂)
    (hy : 0 ≤ y) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hc₁ : A₁ ^ 2 * B₁ ^ 2 ≤ (23 / 1000 : ℝ) * y * L ^ 3)
    (hc₂ : A₂ ^ 2 * B₂ ^ 2 ≤ (31 / 50 : ℝ) * y * L ^ 3)
    (hz₁ : ‖z₁‖ ≤ (527 / 50 : ℝ) * (A₁ * B₁) * T)
    (hz₂ : ‖z₂‖ ≤ (527 / 50 : ℝ) * (A₂ * B₂) * T) :
    ‖z₁ + z₂‖ ≤
      (527 / 50 : ℝ) *
        (Real.sqrt ((23 / 1000 : ℝ) * y * L ^ 3) +
          Real.sqrt ((31 / 50 : ℝ) * y * L ^ 3)) * T := by
  have hc₁' := coefficient_product_le_sqrt_023 hA₁ hB₁ hy hL hc₁
  have hc₂' := coefficient_product_le_sqrt_062 hA₂ hB₂ hy hL hc₂
  calc
    ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_add_le _ _
    _ ≤ (527 / 50 : ℝ) * (A₁ * B₁) * T +
        (527 / 50 : ℝ) * (A₂ * B₂) * T := add_le_add hz₁ hz₂
    _ ≤ (527 / 50 : ℝ) *
        Real.sqrt ((23 / 1000 : ℝ) * y * L ^ 3) * T +
        (527 / 50 : ℝ) *
          Real.sqrt ((31 / 50 : ℝ) * y * L ^ 3) * T := by
      gcongr
    _ = (527 / 50 : ℝ) *
        (Real.sqrt ((23 / 1000 : ℝ) * y * L ^ 3) +
          Real.sqrt ((31 / 50 : ℝ) * y * L ^ 3)) * T := by ring

/-- Equation (9.8): after the dyadic factor from (9.2), the two coefficient
mean-square estimates and Corollary 9.7 give the combined constant `9.52`.
This lemma contains precisely the final `L²` and decimal assembly; its
premises are the two concrete bilinear estimates to be produced by the
preceding analytic argument. -/
lemma norm_add_bilinear_pieces_le_952
    {z₁ z₂ : ℂ} {A₁ B₁ A₂ B₂ y L T : ℝ}
    (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (hA₂ : 0 ≤ A₂) (hB₂ : 0 ≤ B₂)
    (hy : 0 ≤ y) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hc₁ : A₁ ^ 2 * B₁ ^ 2 ≤ (23 / 1000 : ℝ) * y * L ^ 3)
    (hc₂ : A₂ ^ 2 * B₂ ^ 2 ≤ (31 / 50 : ℝ) * y * L ^ 3)
    (hz₁ : ‖z₁‖ ≤ (527 / 50 : ℝ) * (2 / (3 * Real.log 2)) *
      (A₁ * B₁) * T)
    (hz₂ : ‖z₂‖ ≤ (527 / 50 : ℝ) * (2 / (3 * Real.log 2)) *
      (A₂ * B₂) * T) :
    ‖z₁ + z₂‖ ≤
      (238 / 25 : ℝ) * Real.sqrt (y * L ^ 3) * T := by
  have hc₁' := coefficient_product_le_sqrt_023 hA₁ hB₁ hy hL hc₁
  have hc₂' := coefficient_product_le_sqrt_062 hA₂ hB₂ hy hL hc₂
  have hroot₁ :
      Real.sqrt ((23 / 1000 : ℝ) * y * L ^ 3) =
        Real.sqrt (23 / 1000 : ℝ) * Real.sqrt (y * L ^ 3) := by
    rw [show (23 / 1000 : ℝ) * y * L ^ 3 =
      (23 / 1000 : ℝ) * (y * L ^ 3) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 23 / 1000)]
  have hroot₂ :
      Real.sqrt ((31 / 50 : ℝ) * y * L ^ 3) =
        Real.sqrt (31 / 50 : ℝ) * Real.sqrt (y * L ^ 3) := by
    rw [show (31 / 50 : ℝ) * y * L ^ 3 =
      (31 / 50 : ℝ) * (y * L ^ 3) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 31 / 50)]
  have hscale : 0 ≤ Real.sqrt (y * L ^ 3) * T :=
    mul_nonneg (Real.sqrt_nonneg _) hT
  calc
    ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_add_le _ _
    _ ≤ (527 / 50 : ℝ) * (2 / (3 * Real.log 2)) *
          (A₁ * B₁) * T +
        (527 / 50 : ℝ) * (2 / (3 * Real.log 2)) *
          (A₂ * B₂) * T := add_le_add hz₁ hz₂
    _ ≤ (527 / 50 : ℝ) * (2 / (3 * Real.log 2)) *
          Real.sqrt ((23 / 1000 : ℝ) * y * L ^ 3) * T +
        (527 / 50 : ℝ) * (2 / (3 * Real.log 2)) *
          Real.sqrt ((31 / 50 : ℝ) * y * L ^ 3) * T := by
      have hfactor : 0 ≤ (527 / 50 : ℝ) * (2 / (3 * Real.log 2)) := by
        positivity
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc₁' hfactor) hT)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc₂' hfactor) hT)
    _ = ((527 / 50 : ℝ) * (2 / (3 * Real.log 2)) *
          (Real.sqrt (23 / 1000 : ℝ) + Real.sqrt (31 / 50 : ℝ))) *
        (Real.sqrt (y * L ^ 3) * T) := by
      rw [hroot₁, hroot₂]
      ring
    _ ≤ (238 / 25 : ℝ) * (Real.sqrt (y * L ^ 3) * T) :=
      mul_le_mul_of_nonneg_right gr_bilinear_coefficient_le_952 hscale
    _ = (238 / 25 : ℝ) * Real.sqrt (y * L ^ 3) * T := by ring

#print axioms mul_le_sqrt_of_sq_mul_sq_le
#print axioms mangoldtSum_four_sum
#print axioms l2Norm_bCoeff_sq_le
#print axioms l2Norm_aCoeff_sq_le
#print axioms sigma22_l2_product_sq_le
#print axioms sigma3_l2_product_sq_le
#print axioms combined_coefficient_product_le_two
#print axioms norm_add_bilinear_pieces_le
#print axioms gr_bilinear_coefficient_le_952
#print axioms gr_specialization_coefficient_le_32
#print axioms norm_add_bilinear_pieces_le_952

end Erdos175.GranvilleRamare9
