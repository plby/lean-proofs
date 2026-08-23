/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos721.DensityIncrement
import APAP.Physics.DRC
import APAP.Physics.Unbalancing
import APAP.Prereqs.Convolution.Norm
import APAP.Prereqs.FourierTransform.Convolution
import APAP.Prereqs.Inner.Hoelder.Discrete
import Mathlib.Analysis.RCLike.Inner

/-!
# The density-increment implication

This file develops the algebraic half of the cyclic density-increment
dichotomy.  Once sifting has produced two auxiliary dense sets and the tested
almost-periodicity theorem has preserved their mass on a high-correlation
set, the theorem below converts that mass into an actual increase of the
relative density of the original set on a translate of the smoothing set.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicDensityIncrement

private noncomputable def curLog (x : ℝ) : ℝ := 1 + Real.log x⁻¹

private lemma curLog_pos {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    0 < curLog x := by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp [curLog]
  have : 0 ≤ Real.log x⁻¹ := by bound
  simp only [curLog]
  positivity

private lemma one_le_curLog {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    1 ≤ curLog x := by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp [curLog]
  have : 0 ≤ Real.log x⁻¹ := by bound
  simp only [curLog]
  linarith

private lemma rpow_inv_neg_curLog_le {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    x⁻¹ ^ (curLog x)⁻¹ ≤ Real.exp 1 := by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp [curLog, (Real.exp_pos _).le]
  obtain rfl | hx₁ := hx₁.eq_or_lt
  · simp [curLog]
  have hx := (one_lt_inv₀ hx₀).2 hx₁
  calc
    x⁻¹ ^ (curLog x)⁻¹ ≤ x⁻¹ ^ (Real.log x⁻¹)⁻¹ := by
      gcongr
      · exact hx.le
      · exact Real.log_pos hx
      · simp [curLog]
    _ ≤ Real.exp 1 := x⁻¹.rpow_inv_log_le_exp_one

/-- A large correlation with a set of density at least `gamma` forces a large
weighted norm of the balanced self-correlation.  This finite-group statement
is the global analytic input to the unbalancing step; it does not use vector
space structure. -/
theorem cyclic_global_dichotomy
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (A C : Finset G) {gamma epsilon : ℝ}
    (hA : A.Nonempty) (hgammaC : gamma ≤ C.dens) (hgamma : 0 < gamma)
    (hAC : epsilon ≤
      |Fintype.card G * ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] C⟫_[ℝ] - 1|) :
    epsilon / (2 * Fintype.card G) ≤
      ‖balance (μ_[ℝ] A) ○ᵈ balance (μ_[ℝ] A)‖_[↑(2 * ⌈curLog gamma⌉₊),
        μ Finset.univ] := by
  have hC : C.Nonempty := by simpa using hgamma.trans_le hgammaC
  have hgamma1 : gamma ≤ 1 := hgammaC.trans (by norm_cast; exact dens_le_one)
  set p := 2 * ⌈curLog gamma⌉₊
  have hp : 1 < p :=
    Nat.succ_le_iff.1
      (le_mul_of_one_le_right zero_le <| Nat.ceil_pos.2 <| curLog_pos hgamma.le hgamma1)
  have hp' : (p⁻¹ : ℝ≥0) < 1 := inv_lt_one_of_one_lt₀ <| mod_cast hp
  have hp'' : (p : ℝ≥0).HolderConjugate _ := .conjExponent <| mod_cast hp
  have : (p : ℝ≥0∞).HolderConjugate _ := hp''.coe_ennreal
  rw [mul_comm, ← div_div, div_le_iff₀ (zero_lt_two' ℝ)]
  calc
    _ ≤ _ := div_le_div_of_nonneg_right hAC (Fintype.card G).cast_nonneg
    _ = |⟪balance (μ_[ℝ] A) ∗ᵈ balance (μ_[ℝ] A), μ_[ℝ] C⟫_[ℝ]| := by
      rw [← balance_ddconv, balance, wInner_sub_left, wInner_one_const_left,
        expect_ddconv, sum_mu ℝ hA, expect_mu ℝ hA, sum_mu ℝ hC, conj_trivial,
        one_mul, one_mul, ← mul_inv_cancel₀, ← mul_sub, abs_mul, abs_of_nonneg,
        mul_div_cancel_left₀] <;> positivity
    _ ≤ ‖balance (μ_[ℝ] A) ∗ᵈ balance (μ_[ℝ] A)‖_[p] *
        ‖μ_[ℝ] C‖_[NNReal.conjExponent p] :=
      abs_wInner_one_le_dLpNorm_mul_dLpNorm _ _
    _ ≤ ‖balance (μ_[ℝ] A) ○ᵈ balance (μ_[ℝ] A)‖_[p] *
        (Fintype.card G ^ (-(p : ℝ)⁻¹) * gamma ^ (-(p : ℝ)⁻¹)) :=
      mul_le_mul (dLpNorm_ddconv_le_dLpNorm_dddconv' (by positivity)
        (even_two_mul _) _) (by
          rw [dLpNorm_mu hp''.symm.lt.le hC, hp''.symm.coe.inv_sub_one,
            NNReal.coe_natCast, ← mul_rpow]
          any_goals positivity
          rw [nnratCast_dens, le_div_iff₀, mul_comm] at hgammaC
          any_goals positivity
          exact rpow_le_rpow_of_nonpos (by positivity) hgammaC (neg_nonpos.2 <| by positivity))
        (by positivity) (by positivity)
    _ = ‖balance (μ_[ℝ] A) ○ᵈ balance (μ_[ℝ] A)‖_[↑(2 * ⌈curLog gamma⌉₊),
          μ Finset.univ] *
        gamma ^ (-(p : ℝ)⁻¹) := by
      rw [mul_comm, mu_univ_eq_const, wLpNorm_const_right, mul_right_comm,
        rpow_neg, ← inv_rpow]
      any_goals positivity
      · congr
      · exact ENNReal.natCast_ne_top _
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      have : 1 ≤ gamma⁻¹ := (one_le_inv₀ hgamma).2 hgamma1
      have : 0 ≤ Real.log gamma⁻¹ := by bound
      calc
        gamma ^ (-(↑p)⁻¹ : ℝ) =
            √(gamma⁻¹ ^ ((↑⌈curLog gamma⌉₊)⁻¹ : ℝ)) := by
          rw [rpow_neg hgamma.le, inv_rpow hgamma.le]
          unfold p
          push_cast
          rw [mul_inv_rev, rpow_mul, sqrt_eq_rpow, one_div, inv_rpow]
          all_goals positivity
        _ ≤ √(gamma⁻¹ ^ ((curLog gamma)⁻¹ : ℝ)) := by
          grw [← Nat.le_ceil]
          exact curLog_pos hgamma.le hgamma1
        _ ≤ √(Real.exp 1) := by
          gcongr
          exact rpow_inv_neg_curLog_le hgamma.le hgamma1
        _ ≤ √2.7182818286 := by
          gcongr
          exact exp_one_lt_d9.le
        _ ≤ 2 := by rw [sqrt_le_iff]; norm_num) (by positivity)

/-- Unbalancing followed by dependent random choice.  Starting from the
global correlation gap, this produces two dense auxiliary sets and a
nonempty high-self-correlation test set on which their difference convolution
has almost all of its mass. -/
theorem cyclic_unbalancing_sifting
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (A C : Finset G) {gamma epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hA : A.Nonempty) (hgammaC : gamma ≤ C.dens) (hgamma : 0 < gamma)
    (hAC : epsilon ≤
      |Fintype.card G * ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] C⟫_[ℝ] - 1|) :
    ∃ (q : ℕ) (A₁ A₂ U : Finset G),
      0 < q ∧ Even q ∧
      q ≤ 2 ^ 16 * curLog gamma / epsilon ^ 2 ∧
      A₁.Nonempty ∧ A₂.Nonempty ∧ U.Nonempty ∧
      1 - epsilon / 32 ≤ ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x ∧
      (4⁻¹ : ℝ) * A.dens ^ (2 * q) ≤ A₁.dens ∧
      (4⁻¹ : ℝ) * A.dens ^ (2 * q) ≤ A₂.dens ∧
      ∀ x ∈ U,
        1 + epsilon / 8 ≤
          Fintype.card G • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x := by
  have hgamma1 : gamma ≤ 1 := hgammaC.trans (by norm_cast; exact dens_le_one)
  have hloginv : 0 ≤ Real.log gamma⁻¹ :=
    Real.log_nonneg <| (one_le_inv₀ hgamma).2 hgamma1
  have hcurLog0 : 0 < curLog gamma := curLog_pos hgamma.le hgamma1
  have hcurLog1 : 1 ≤ curLog gamma := one_le_curLog hgamma.le hgamma1
  have hepsilonInv : 1 ≤ epsilon⁻¹ :=
    (one_le_inv₀ hepsilon0).2 hepsilon1.le
  let p : ℕ := 2 * ⌈curLog gamma⌉₊
  have hpupper : p ≤ 4 * curLog gamma := by
    unfold p
    push_cast
    grw [Nat.ceil_le_two_mul (by linarith)]
    grind
  have hp0 : 0 < p := by positivity
  let f : G → ℝ := balance (μ_[ℝ] A)
  obtain ⟨p', hp'upper, hunbalance⟩ :
      ∃ p' : ℕ,
        p' ≤ 2 ^ 10 * (epsilon / 2)⁻¹ ^ 2 * p ∧
        1 + epsilon / 2 / 2 ≤
          ‖Fintype.card G • (f ○ᵈ f) + 1‖_[p', μ Finset.univ] := by
    refine unbalancing p hp0.ne' (epsilon / 2) (by positivity)
      (div_le_one_of_le₀ (hepsilon1.le.trans <| by norm_num) <| by norm_num)
      (Fintype.card G • (balance (μ_[ℝ] A) ○ᵈ balance (μ_[ℝ] A)))
      (Real.sqrt (Fintype.card G) • balance (μ_[ℂ] A))
      (μ_[ℂ] Finset.univ) ?_ ?_ ?_
    · ext a : 1
      simp [smul_dddconv, dddconv_smul, ← mul_assoc, ← sq, ← Complex.ofReal_pow]
    · simp
    · have hglobal := cyclic_global_dichotomy A C hA hgammaC hgamma hAC
      simpa [p, wLpNorm_nsmul, ← nsmul_eq_mul,
        div_le_iff₀' (show (0 : ℝ) < Fintype.card G by positivity), ← div_div,
        rpow_neg, inv_rpow] using hglobal
  have hp'0 : 0 < p' := by
    apply pos_iff_ne_zero.2
    rintro rfl
    simp at hunbalance
    linarith
  let q : ℕ := max (2 * p') (2 ^ 4 * ⌈epsilon⁻¹ * Real.log (64 / epsilon)⌉₊)
  have hq0 : 0 < q := by positivity
  have hqeven : Even q := by grind
  have hp'q : p' ≤ q := by
    unfold q
    grw [← le_max_left]
    lia
  have hqlower : 2 ^ 4 * epsilon⁻¹ * Real.log (64 / epsilon) ≤ q := by
    unfold q
    grw [mul_assoc, ← le_max_right]
    push_cast
    grw [← Nat.le_ceil]
    norm_num
  have hqupper : q ≤ 2 ^ 16 * curLog gamma / epsilon ^ 2 := by
    unfold q
    push_cast
    grw [hp'upper, hpupper, max_le_add_of_nonneg (by positivity) (by positivity),
      (64 / epsilon).log_le_self (by positivity)]
    ring_nf
    grw [Nat.ceil_le_two_mul <| by grw [← hepsilonInv]; norm_num]
    ring_nf
    calc
      epsilon⁻¹ ^ 2 * 2048 + epsilon⁻¹ ^ 2 * curLog gamma * 32768 ≤
          epsilon⁻¹ ^ 2 * curLog gamma * 2048 +
            epsilon⁻¹ ^ 2 * curLog gamma * 32768 := by
        gcongr
        nlinarith [mul_nonneg (sq_nonneg epsilon⁻¹)
          (sub_nonneg.mpr hcurLog1)]
      _ ≤ epsilon⁻¹ ^ 2 * curLog gamma * 65536 := by
        nlinarith [mul_nonneg (sq_nonneg epsilon⁻¹) hcurLog0.le]
  have hlog6 : 0 < Real.log (6 / epsilon) :=
    Real.log_pos <| (one_lt_div hepsilon0).2 (by linarith)
  have hlog64 : 0 < Real.log (64 / epsilon) :=
    Real.log_pos <| (one_lt_div hepsilon0).2 (by linarith)
  obtain ⟨A₁, A₂, hmassSmall, hA₁dens, hA₂dens⟩ :
      ∃ (A₁ A₂ : Finset G),
        1 - epsilon / 32 ≤
            ∑ x ∈ s q (epsilon / 16) Finset.univ Finset.univ A,
              (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x ∧
          (4⁻¹ : ℝ) * A.dens ^ (2 * q) ≤ A₁.dens ∧
          (4⁻¹ : ℝ) * A.dens ^ (2 * q) ≤ A₂.dens := by
    refine sifting_cor (by positivity) (by linarith) (by positivity)
      hqeven (by positivity) ?_ hA
    calc
      (epsilon / 16)⁻¹ * Real.log (2 / (epsilon / 32)) =
          2 ^ 4 * epsilon⁻¹ * Real.log (64 / epsilon) := by ring_nf
      _ ≤ q := hqlower
  have hbalanced :
      Fintype.card G • (f ○ᵈ f) + 1 =
        Fintype.card G • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) := by
    unfold f
    rw [← balance_dddconv, balance, smul_sub, smul_const,
      Fintype.card_smul_expect]
    simp [sum_dddconv, hA]
  have hnorm :
      1 + epsilon / 4 ≤
        Fintype.card G •
          ‖(μ_[ℝ] A ○ᵈ μ_[ℝ] A)‖_[q, μ Finset.univ] := by
    calc
      1 + epsilon / 4 = 1 + epsilon / 2 / 2 := by ring
      _ ≤ ‖Fintype.card G • (f ○ᵈ f) + 1‖_[p', μ Finset.univ] :=
        hunbalance
      _ = Fintype.card G •
          ‖(μ_[ℝ] A ○ᵈ μ_[ℝ] A)‖_[p', μ Finset.univ] := by
        simp [hbalanced, wLpNorm_nsmul, -nsmul_eq_mul]
      _ ≤ Fintype.card G •
          ‖(μ_[ℝ] A ○ᵈ μ_[ℝ] A)‖_[q, μ Finset.univ] := by
        have : Nonempty G := hA.to_type
        gcongr
        exact mod_cast sum_mu ℝ≥0 Finset.univ_nonempty
  let U : Finset G :=
    {x | 1 + epsilon / 8 ≤
      Fintype.card G • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x}
  have hsmallSub :
      s q (epsilon / 16) Finset.univ Finset.univ A ⊆ U := by
    simp only [subset_iff, mem_s', ENNReal.coe_natCast,
      mu_univ_dddconv_mu_univ, mem_filter, mem_univ, true_and, U]
    rintro x hx
    calc
      1 + epsilon / 8 ≤ (1 - epsilon / 16) * (1 + epsilon / 4) :=
        one_add_le_one_sub_mul_one_add <| by
          calc
            epsilon / 8 + epsilon / 16 + epsilon / 16 * (epsilon / 4) ≤
                epsilon / 8 + epsilon / 16 + epsilon / 16 * (1 / 4) := by
              gcongr
            _ ≤ epsilon / 4 := by linarith
      _ ≤ (1 - epsilon / 16) * Fintype.card G •
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[q, μ Finset.univ] := by
        gcongr
        linarith
      _ = Fintype.card G • ((1 - epsilon / 16) *
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[q, μ Finset.univ]) := mul_smul_comm ..
      _ ≤ Fintype.card G • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x := by gcongr
  have hcorrNonneg : 0 ≤ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂ :=
    dddconv_nonneg mu_nonneg mu_nonneg
  have hmass :
      1 - epsilon / 32 ≤ ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x :=
    hmassSmall.trans <| Finset.sum_le_sum_of_subset_of_nonneg hsmallSub
      (fun x _ _ ↦ hcorrNonneg x)
  have hA₁ : A₁.Nonempty := by
    have hleft : 0 < (4⁻¹ : ℝ) * A.dens ^ (2 * q) := by positivity
    by_contra hne
    rw [not_nonempty_iff_eq_empty.mp hne] at hA₁dens
    simp at hA₁dens
    exact (not_lt_of_ge hA₁dens) hleft
  have hA₂ : A₂.Nonempty := by
    have hleft : 0 < (4⁻¹ : ℝ) * A.dens ^ (2 * q) := by positivity
    by_contra hne
    rw [not_nonempty_iff_eq_empty.mp hne] at hA₂dens
    simp at hA₂dens
    exact (not_lt_of_ge hA₂dens) hleft
  have hU : U.Nonempty := by
    by_contra hU
    rw [not_nonempty_iff_eq_empty.mp hU] at hmass
    simp at hmass
    linarith
  refine ⟨q, A₁, A₂, U, hq0, hqeven, hqupper, hA₁, hA₂, hU,
    hmass, hA₁dens, hA₂dens, ?_⟩
  intro x hx
  exact (mem_filter.1 hx).2

variable {N : ℕ} [NeZero N]

/-- The final Hölder/convolution step of the density-increment argument.  It
is independent of how the auxiliary sets and the smoothing set were
constructed. -/
theorem density_increment_of_large_smoothed_test_sum
    (A A₁ A₂ C U : Finset (ZMod N)) {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤
        N • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x)
    (hmass :
      1 - epsilon / 16 ≤
        ∑ x ∈ U, (μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) :
    (1 + epsilon / 32) * A.dens ≤
      ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C‖_[∞] := by
  have htriple :
      0 ≤ μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂ :=
    dddconv_nonneg (ddconv_nonneg mu_nonneg mu_nonneg) mu_nonneg
  have hdens : (A.dens : ℝ) * N = A.card := by
    rw [nnratCast_dens, ZMod.card]
    field_simp [NeZero.ne N]
  rw [← le_div_iff₀ (show (0 : ℝ) < (A.dens : ℝ) by positivity)]
  calc
    1 + epsilon / 32 ≤
        (1 + epsilon / 8) * (1 - epsilon / 16) :=
      one_add_le_one_add_mul_one_sub <| by
        calc
          epsilon / 32 + epsilon / 16 + epsilon / 8 * (epsilon / 16) ≤
              epsilon / 32 + epsilon / 16 + epsilon / 8 * (1 / 16) := by
            gcongr
          _ ≤ epsilon / 8 := by linarith
    _ ≤ (1 + epsilon / 8) *
        ∑ x ∈ U, (μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
      gcongr
    _ = ∑ x ∈ U, (1 + epsilon / 8) *
        (μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
      rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ U,
        (N • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x) *
          (μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
      gcongr with x hx
      · exact htriple x
      · exact hhigh x hx
    _ ≤ ∑ x : ZMod N,
        (N • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x) *
          (μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro x _hx _hxU
      have hAA : 0 ≤ μ_[ℝ] A ○ᵈ μ_[ℝ] A :=
        dddconv_nonneg mu_nonneg mu_nonneg
      exact mul_nonneg (nsmul_nonneg (hAA x) N) (htriple x)
    _ = N •
        ⟪μ_[ℝ] C ∗ᵈ μ_[ℝ] A,
          μ_[ℝ] A ∗ᵈ μ_[ℝ] A₂ ○ᵈ μ_[ℝ] A₁⟫_[ℝ] := by
      rw [← wInner_one_dddconv_eq_ddconv_wInner_one, dddconv_right_comm,
        ddconv_dddconv_right_comm (μ_[ℝ] A),
        wInner_one_dddconv_eq_ddconv_wInner_one,
        ← dddconv_wInner_one_eq_wInner_one_ddconv, ← conj_wInner_symm]
      simp only [nsmul_eq_mul, mul_assoc, wInner_one_eq_sum, inner_apply,
        conj_trivial, map_sum, smul_sum]
    _ ≤ N •
        (‖μ_[ℝ] C ∗ᵈ μ_[ℝ] A‖_[∞] *
          ‖μ_[ℝ] A ∗ᵈ μ_[ℝ] A₂ ○ᵈ μ_[ℝ] A₁‖_[1]) := by
      gcongr
      exact wInner_one_le_dLpNorm_mul_dLpNorm _ _
    _ = ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C‖_[∞] / A.dens := by
      rw [dL1Norm_dddconv, dL1Norm_ddconv]
      · simp [eq_div_iff, hA.dens_ne_zero, hdens, hA, hA₁, hA₂, ← card_smul_mu,
          smul_ddconv, dLpNorm_nsmul, -nsmul_eq_mul]
        all_goals simp [← mul_assoc, mul_comm, ddconv_comm, hdens]
      · exact mu_nonneg
      · exact mu_nonneg
      · exact ddconv_nonneg mu_nonneg mu_nonneg
      · exact mu_nonneg

/-- Relative version of the algebraic tail.  The normalization scale may be
the cardinality of an ambient Bohr carrier rather than the cardinality of the
whole cyclic group. -/
theorem density_increment_of_large_smoothed_test_sum_relative
    (A A₁ A₂ C U : Finset (ZMod N)) (scale : ℕ) {alpha epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (halpha : 0 < alpha) (hdensity : alpha * scale = A.card)
    (hA : A.Nonempty) (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤
        scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x)
    (hmass :
      1 - epsilon / 16 ≤
        ∑ x ∈ U, (μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) :
    (1 + epsilon / 32) * alpha ≤
      ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C‖_[∞] := by
  have htriple :
      0 ≤ μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂ :=
    dddconv_nonneg (ddconv_nonneg mu_nonneg mu_nonneg) mu_nonneg
  rw [← le_div_iff₀ halpha]
  calc
    1 + epsilon / 32 ≤
        (1 + epsilon / 8) * (1 - epsilon / 16) :=
      one_add_le_one_add_mul_one_sub <| by
        calc
          epsilon / 32 + epsilon / 16 + epsilon / 8 * (epsilon / 16) ≤
              epsilon / 32 + epsilon / 16 + epsilon / 8 * (1 / 16) := by
            gcongr
          _ ≤ epsilon / 8 := by linarith
    _ ≤ (1 + epsilon / 8) *
        ∑ x ∈ U, (μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
      gcongr
    _ = ∑ x ∈ U, (1 + epsilon / 8) *
        (μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
      rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ U,
        (scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x) *
          (μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
      gcongr with x hx
      · exact htriple x
      · exact hhigh x hx
    _ ≤ ∑ x : ZMod N,
        (scale • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x) *
          (μ_[ℝ] C ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro x _hx _hxU
      have hAA : 0 ≤ μ_[ℝ] A ○ᵈ μ_[ℝ] A :=
        dddconv_nonneg mu_nonneg mu_nonneg
      exact mul_nonneg (nsmul_nonneg (hAA x) scale) (htriple x)
    _ = scale •
        ⟪μ_[ℝ] C ∗ᵈ μ_[ℝ] A,
          μ_[ℝ] A ∗ᵈ μ_[ℝ] A₂ ○ᵈ μ_[ℝ] A₁⟫_[ℝ] := by
      rw [← wInner_one_dddconv_eq_ddconv_wInner_one, dddconv_right_comm,
        ddconv_dddconv_right_comm (μ_[ℝ] A),
        wInner_one_dddconv_eq_ddconv_wInner_one,
        ← dddconv_wInner_one_eq_wInner_one_ddconv, ← conj_wInner_symm]
      simp only [nsmul_eq_mul, mul_assoc, wInner_one_eq_sum, inner_apply,
        conj_trivial, map_sum, smul_sum]
    _ ≤ scale •
        (‖μ_[ℝ] C ∗ᵈ μ_[ℝ] A‖_[∞] *
          ‖μ_[ℝ] A ∗ᵈ μ_[ℝ] A₂ ○ᵈ μ_[ℝ] A₁‖_[1]) := by
      gcongr
      exact wInner_one_le_dLpNorm_mul_dLpNorm _ _
    _ = ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C‖_[∞] / alpha := by
      rw [dL1Norm_dddconv, dL1Norm_ddconv]
      · simp [eq_div_iff, halpha.ne', hA, hA₁, hA₂, ← card_smul_mu,
          smul_ddconv, dLpNorm_nsmul, -nsmul_eq_mul]
        all_goals simp [← mul_assoc, mul_comm, ddconv_comm, hdensity]
      · exact mu_nonneg
      · exact mu_nonneg
      · exact ddconv_nonneg mu_nonneg mu_nonneg
      · exact mu_nonneg

/-- Turn any analytic `L∞` lower bound into the next combinatorial iterate:
a translate-reflection of the old set contained in the new Bohr carrier and
with the same three-progression-free property. -/
theorem exists_normalizedSlice_of_dLinfty_bound
    (A : Finset (ZMod N)) (C : CyclicBohr.Set N) {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (hAfree : ThreeAPFree (A : Set (ZMod N)))
    (hinc : beta ≤
      ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C.carrier‖_[∞]) :
    ∃ x : ZMod N,
      normalizedSlice A C.carrier x ⊆ C.carrier ∧
      ThreeAPFree (normalizedSlice A C.carrier x : Set (ZMod N)) ∧
      beta ≤
        (normalizedSlice A C.carrier x).card / (C.carrier.card : ℝ) := by
  obtain ⟨x, hx⟩ := exists_translatedSlice_of_dLinfty_increment
    A C.carrier C.carrier_nonempty hbeta hinc
  refine ⟨x, normalizedSlice_subset_right A C.carrier x,
    threeAPFree_normalizedSlice A C.carrier x hAfree, ?_⟩
  rwa [card_normalizedSlice_eq_card_translatedSlice]

/-- Specialization of `exists_normalizedSlice_of_dLinfty_bound` to the
global density used by the first density-increment stage. -/
theorem exists_normalizedSlice_of_density_increment
    (A : Finset (ZMod N)) (C : CyclicBohr.Set N) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hAfree : ThreeAPFree (A : Set (ZMod N)))
    (hinc :
      (1 + epsilon / 32) * A.dens ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C.carrier‖_[∞]) :
    ∃ x : ZMod N,
      normalizedSlice A C.carrier x ⊆ C.carrier ∧
      ThreeAPFree (normalizedSlice A C.carrier x : Set (ZMod N)) ∧
      (1 + epsilon / 32) * A.dens ≤
        (normalizedSlice A C.carrier x).card / (C.carrier.card : ℝ) := by
  exact exists_normalizedSlice_of_dLinfty_bound A C
    (mul_nonneg (by positivity) (by positivity)) hAfree hinc

/-- The local almost-periodicity estimate and the algebraic tail assembled
into one density-increment step.  The hypothesis `hsmall` is precisely the
remaining numerical choice of the smoothing parameters: it says that the
explicit Croot--Sisask--Chang error is at most `epsilon / 32` for every set
meeting the guaranteed lower cardinality bound. -/
theorem exists_local_bohr_density_increment
    (B : CyclicBohr.Set N) (A A₁ A₂ U : Finset (ZMod N))
    {t delta alpha epsilon apError eta rho : ℝ} (k : ℕ)
    (halpha0 : 0 < alpha) (halphahalf : alpha ≤ 1 / 2)
    (hdelta : 0 ≤ delta) (hdeltat : delta ≤ t)
    (hAinner : A₁ ⊆ (B.dilate (t - delta)).carrier)
    (hAdense : alpha * (B.dilate (t - delta)).carrier.card ≤ A₁.card)
    (hregular :
      10 * (B.dilate (t + delta)).carrier.card ≤
        11 * (B.dilate (t - delta)).carrier.card)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hapError0 : 0 < apError) (hapError1 : apError ≤ 1)
    (hk : k ≠ 0) (hA : A.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (heta : 0 < eta) (hrho : 0 ≤ rho)
    (hbase :
      1 - epsilon / 32 ≤
        ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x)
    (hhigh : ∀ x ∈ U,
      1 + epsilon / 8 ≤ N • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) x)
    (hsmall : ∀ T : Finset (ZMod N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / apError ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card →
      2 * apError +
          ((CyclicChang.changRankBound T eta : ℝ) * rho +
            2 * eta ^ k) *
              (Real.sqrt ((N : ℝ) / A₁.card) *
                Real.sqrt ((U.card : ℝ) / N)) ≤ epsilon / 32) :
    ∃ (T : Finset (ZMod N)) (C : CyclicBohr.Set N),
      (11 / (10 * alpha)) ^ (-4096 *
          ((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
          (k : ℝ) ^ 2 / apError ^ 2) *
          ((B.dilate delta).carrier.card : ℝ) ≤ T.card ∧
      C.rank ≤ B.rank + CyclicChang.changRankBound T eta ∧
      C.carrier ⊆ (B.dilate delta).carrier ∧
      (1 + epsilon / 32) * A.dens ≤
        ‖𝟭_[(A : Set (ZMod N)), ℝ] ∗ᵈ μ_[ℝ] C.carrier‖_[∞] := by
  obtain ⟨T, C, hT, hCrank, hCsub, hsmooth⟩ :=
    exists_local_bohr_tested_correlation_real B A₁ A₂ U k halpha0
      halphahalf hdelta hdeltat hAinner hAdense hregular hapError0 hapError1
      hk hA₁ hA₂ hU heta hrho
  refine ⟨T, C, hT, hCrank, hCsub, ?_⟩
  apply density_increment_of_large_smoothed_test_sum A A₁ A₂ C.carrier U
    hepsilon0 hepsilon1 hA hA₁ hA₂ hhigh
  calc
    1 - epsilon / 16 = 1 - epsilon / 32 - epsilon / 32 := by ring
    _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
        |(∑ x ∈ U,
            (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x| := by
      gcongr
      exact hsmooth.trans (hsmall T hT)
    _ ≤ (∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
        -((∑ x ∈ U,
            (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) -
          ∑ x ∈ U, (μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x) := by
      gcongr
      exact neg_le_abs _
    _ = ∑ x ∈ U,
        (μ_[ℝ] C.carrier ∗ᵈ μ_[ℝ] A₁ ○ᵈ μ_[ℝ] A₂) x := by ring

end CyclicDensityIncrement
end Erdos721
