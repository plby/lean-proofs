/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This is the small, proof-complete interface needed by the q-sensitive
Vaughan estimate used for Erdős 471.  It extracts the elementary Type-I
distance estimate from the larger ternary-Goldbach development without
importing that development's unfinished bridge layer.
-/

import Wikipedia.VinogradovsTheorem.External.MathExtras.NumberTheory.Vinogradov.MinorArcVaughan
import Wikipedia.VinogradovsTheorem.External.MathExtras.Analysis.AbelSummation
import Wikipedia.VinogradovsTheorem.External.AnalyticNT.Bilinear.TypeII

noncomputable section

namespace Vinogradov

theorem addChar_eq_addChar_one_pow (β : ℝ) (m : ℕ) :
    addChar β m = (addChar β 1) ^ m := by
  rw [addChar, addChar, ← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

theorem addChar_one_eq_one_iff (β : ℝ) :
    addChar β 1 = 1 ↔ ∃ k : ℤ, (k : ℝ) = β := by
  unfold addChar
  simp only [Nat.cast_one, mul_one]
  constructor
  · intro h
    rw [Complex.exp_eq_one_iff] at h
    rcases h with ⟨k, hk⟩
    have hfactor : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
    have hβk : (β : ℂ) = (k : ℂ) := by
      apply mul_right_cancel₀ hfactor
      simpa [mul_assoc, mul_comm, mul_left_comm] using hk
    refine ⟨k, ?_⟩
    exact Complex.ofReal_inj.mp (by simpa using hβk.symm)
  · rintro ⟨k, hk⟩
    rw [Complex.exp_eq_one_iff]
    refine ⟨k, ?_⟩
    rw [← hk]
    push_cast
    ring

theorem norm_addChar_one_sub_one_eq_two_abs_sin (β : ℝ) :
    ‖addChar β 1 - 1‖ = 2 * |Real.sin (Real.pi * β)| := by
  unfold addChar
  simp only [Nat.cast_one, mul_one]
  have harg :
      2 * Real.pi * Complex.I * (β : ℂ) =
        Complex.I * ((2 * Real.pi * β : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : (2 * Real.pi * β) / 2 = Real.pi * β := by ring
  rw [hhalf]
  simp [Real.norm_eq_abs]

theorem sin_pi_lower_bound_dist_int (x : ℝ) :
    2 * |x - (round x : ℝ)| ≤ |Real.sin (Real.pi * x)| := by
  set δ : ℝ := x - (round x : ℝ) with hδdef
  have hδ_abs : |δ| ≤ 1 / 2 := by
    rw [hδdef]
    simpa using abs_sub_round x
  have hpi_abs : |Real.pi * δ| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, hδ_abs]
  have hsin : 2 * |δ| ≤ |Real.sin (Real.pi * δ)| := by
    have h := Real.mul_abs_le_abs_sin hpi_abs
    rw [abs_mul, abs_of_pos Real.pi_pos] at h
    have hleft : 2 / Real.pi * (Real.pi * |δ|) = 2 * |δ| := by
      field_simp [Real.pi_ne_zero]
    simpa [hleft] using h
  have hperiod_sin :
      Real.sin (Real.pi * x) = (-1 : ℝ) ^ (round x) * Real.sin (Real.pi * δ) := by
    have hxsplit : Real.pi * x = Real.pi * δ + (round x : ℝ) * Real.pi := by
      rw [hδdef]
      ring
    rw [hxsplit]
    exact Real.sin_add_int_mul_pi (Real.pi * δ) (round x)
  have habs_eq : |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * δ)| := by
    rw [hperiod_sin, abs_mul]
    have hpow : |((-1 : ℝ) ^ (round x))| = 1 := by
      rw [abs_zpow]
      simp
    rw [hpow, one_mul]
  rw [habs_eq, hδdef]
  exact hsin

end Vinogradov

namespace MathExtras
namespace Helfgott

open Finset

noncomputable def hardCutoffVaughanPeriodicEndpointWindow
    (n : ℕ) (α : ℝ) : Prop :=
  ∃ k : ℤ, |α - (k : ℝ)| ≤ 1 / (2 * (n : ℝ))

def hardCutoffVaughanTypeILogDistanceSensitiveBound
    (K : ℝ) (n : ℕ) (α : ℝ) : Prop :=
  ‖Vinogradov.arithmeticExpSum
      (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ ≤
      K * Real.log (n : ℝ) * (n : ℝ) ∧
    ((round α : ℝ) ≠ α →
      ‖Vinogradov.arithmeticExpSum
          (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ ≤
        K * Real.log (n : ℝ) / |α - (round α : ℝ)|)

noncomputable def hardCutoffVaughanTypeIIVinogradovEnvelope (n q : ℕ) : ℝ :=
  ((n : ℝ) / Real.sqrt (q : ℝ) + (n : ℝ) ^ ((4 : ℝ) / 5) +
      Real.sqrt ((q : ℝ) * (n : ℝ))) * (Real.log (n : ℝ)) ^ 4

def hardCutoffVaughanTypeIILambdaSubLogQSensitiveBound
    (K : ℝ) (n q : ℕ) (α : ℝ) : Prop :=
  ‖Vinogradov.arithmeticExpSum
      (ArithmeticFunction.vonMangoldt - ArithmeticFunction.log) n α‖ ≤
    K * hardCutoffVaughanTypeIIVinogradovEnvelope n q

def hardCutoffVaughanTypeIIHighDenominatorCenterQSensitiveTargetParam
    (U : ℕ → ℕ) : Prop :=
  ∃ Npow : ℕ, ∃ Kpow : ℝ, 0 < Kpow ∧
    ∀ n : ℕ, Npow ≤ n → 2 ≤ n →
      ∀ α ∈ Vinogradov.minorArcs n (U n),
        ¬ hardCutoffVaughanPeriodicEndpointWindow n α →
          ∀ a q : ℕ,
            (a, q) ∈ Vinogradov.majorArcCenters n →
              |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * (n : ℝ)) →
                U n < q →
                  hardCutoffVaughanTypeIILambdaSubLogQSensitiveBound Kpow n q α

theorem norm_addChar_sum_Ioc_le_round (α : ℝ)
    (h : (round α : ℝ) ≠ α) (k : ℕ) :
    ‖∑ m ∈ Finset.Ioc 0 k, Vinogradov.addChar α m‖ ≤
      1 / (2 * |α - (round α : ℝ)|) := by
  have hd_pos : 0 < |α - (round α : ℝ)| :=
    abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
  have hnotint : ¬ ∃ j : ℤ, (j : ℝ) = α := by
    rintro ⟨j, rfl⟩
    exact h (by rw [round_intCast])
  have hζ : Vinogradov.addChar α 1 ≠ 1 := by
    intro hc
    exact hnotint ((Vinogradov.addChar_one_eq_one_iff α).mp hc)
  have hIoc : Finset.Ioc 0 k = Finset.Ico 1 (k + 1) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hsum : (∑ m ∈ Finset.Ico 1 (k + 1), Vinogradov.addChar α m)
      = ((Vinogradov.addChar α 1) ^ (k + 1) - (Vinogradov.addChar α 1) ^ 1) /
          (Vinogradov.addChar α 1 - 1) := by
    rw [show (∑ m ∈ Finset.Ico 1 (k + 1), Vinogradov.addChar α m)
        = ∑ m ∈ Finset.Ico 1 (k + 1), (Vinogradov.addChar α 1) ^ m from
      Finset.sum_congr rfl fun m _ => Vinogradov.addChar_eq_addChar_one_pow α m]
    exact geom_sum_Ico hζ (by omega)
  rw [hIoc, hsum, norm_div]
  have hnum : ‖(Vinogradov.addChar α 1) ^ (k + 1) -
      (Vinogradov.addChar α 1) ^ 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_pow, Vinogradov.norm_addChar]
    norm_num
  have hden : 2 * (2 * |α - (round α : ℝ)|) ≤ ‖Vinogradov.addChar α 1 - 1‖ := by
    rw [Vinogradov.norm_addChar_one_sub_one_eq_two_abs_sin]
    have hj := Vinogradov.sin_pi_lower_bound_dist_int α
    linarith
  have h4d : 0 < 2 * (2 * |α - (round α : ℝ)|) := by linarith
  calc
    ‖(Vinogradov.addChar α 1) ^ (k + 1) - (Vinogradov.addChar α 1) ^ 1‖ /
          ‖Vinogradov.addChar α 1 - 1‖
        ≤ 2 / (2 * (2 * |α - (round α : ℝ)|)) :=
          div_le_div₀ (by norm_num) hnum h4d hden
    _ = 1 / (2 * |α - (round α : ℝ)|) := by
      have hd_ne : |α - (round α : ℝ)| ≠ 0 := ne_of_gt hd_pos
      field_simp

theorem abel_norm_bound_monotone_increasing
    (a : ℕ → ℂ) (b : ℕ → ℝ) (M N : ℕ) (hMN : M ≤ N)
    (A : ℝ) (hA_nonneg : 0 ≤ A)
    (hA : ∀ k ∈ Finset.Ioc M N, ‖∑ n ∈ Finset.Ioc M k, a n‖ ≤ A)
    (hb_nonneg : ∀ k, 0 ≤ b k)
    (hb_inc : ∀ k, M ≤ k → k < N → b k ≤ b (k + 1)) :
    ‖∑ n ∈ Finset.Ioc M N, a n * ((b n : ℝ) : ℂ)‖ ≤ 2 * A * b N := by
  rcases Nat.eq_or_lt_of_le hMN with rfl | hMN'
  · simp only [Finset.Ioc_self, Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hA_nonneg) (hb_nonneg M)
  · rw [MathExtras.AbelSummation.abel_summation_Ioc_complex a
      (fun n => ((b n : ℝ) : ℂ)) M N hMN]
    refine (norm_sub_le _ _).trans ?_
    have hAN : ‖∑ n ∈ Finset.Ioc M N, a n‖ ≤ A :=
      hA N (Finset.mem_Ioc.mpr ⟨hMN', le_rfl⟩)
    have htop : ‖(∑ n ∈ Finset.Ioc M N, a n) * ((b N : ℝ) : ℂ)‖ ≤ A * b N := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hb_nonneg N)]
      exact mul_le_mul_of_nonneg_right hAN (hb_nonneg N)
    have hrem : ‖∑ k ∈ Finset.Ioc M (N - 1),
          (∑ n ∈ Finset.Ioc M k, a n) *
            (((b (k + 1) : ℝ) : ℂ) - ((b k : ℝ) : ℂ))‖
        ≤ A * (b N - b (M + 1)) := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ k ∈ Finset.Ioc M (N - 1),
          ‖(∑ n ∈ Finset.Ioc M k, a n) *
              (((b (k + 1) : ℝ) : ℂ) - ((b k : ℝ) : ℂ))‖
            ≤ A * (b (k + 1) - b k) := by
        intro k hk
        obtain ⟨hMk, hkN1⟩ := Finset.mem_Ioc.mp hk
        have hkN : k < N := by omega
        have hbk : b k ≤ b (k + 1) := hb_inc k (le_of_lt hMk) hkN
        rw [norm_mul]
        have hdiff : ‖((b (k + 1) : ℝ) : ℂ) - ((b k : ℝ) : ℂ)‖
            = b (k + 1) - b k := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr hbk)]
        rw [hdiff]
        exact mul_le_mul_of_nonneg_right
          (hA k (Finset.mem_Ioc.mpr ⟨hMk, le_of_lt hkN⟩))
          (sub_nonneg.mpr hbk)
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum]
      have htel : ∑ k ∈ Finset.Ioc M (N - 1), (b (k + 1) - b k)
          = b N - b (M + 1) := by
        have ht := MathExtras.AbelSummation.telescope_Ioc_sub b hMN'
        have h2 : ∑ k ∈ Finset.Ioc M (N - 1), (b (k + 1) - b k)
            = -∑ k ∈ Finset.Ioc M (N - 1), (b k - b (k + 1)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [h2, ht]
        ring
      rw [htel]
    calc
      ‖(∑ n ∈ Finset.Ioc M N, a n) * ((b N : ℝ) : ℂ)‖ +
          ‖∑ k ∈ Finset.Ioc M (N - 1),
            (∑ n ∈ Finset.Ioc M k, a n) *
              (((b (k + 1) : ℝ) : ℂ) - ((b k : ℝ) : ℂ))‖
          ≤ A * b N + A * (b N - b (M + 1)) := add_le_add htop hrem
      _ ≤ 2 * A * b N := by
        have := mul_nonneg hA_nonneg (hb_nonneg (M + 1))
        linarith

theorem arithmeticExpSum_eq_sum_Ioc (F : ArithmeticFunction ℝ) (n : ℕ)
    (α : ℝ) :
    Vinogradov.arithmeticExpSum F n α =
      ∑ m ∈ Finset.Ioc 0 n, ((F m : ℝ) : ℂ) * Vinogradov.addChar α m := by
  rw [Vinogradov.arithmeticExpSum]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_Ioc] at hx
    rw [Finset.mem_range]
    omega
  · intro x hx hnot
    rw [Finset.mem_range] at hx
    rw [Finset.mem_Ioc] at hnot
    have hx0 : x = 0 := by omega
    subst hx0
    simp

theorem norm_arithmeticExpSum_log_le_linear (n : ℕ) (α : ℝ) :
    ‖Vinogradov.arithmeticExpSum
        (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ ≤
      Real.log (n : ℝ) * (n : ℝ) := by
  rw [arithmeticExpSum_eq_sum_Ioc]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ Finset.Ioc 0 n,
      ‖((ArithmeticFunction.log m : ℝ) : ℂ) * Vinogradov.addChar α m‖ ≤
        Real.log (n : ℝ) := by
    intro m hm
    obtain ⟨h0, hn⟩ := Finset.mem_Ioc.mp hm
    rw [norm_mul, Vinogradov.norm_addChar, mul_one, Complex.norm_real,
      Real.norm_eq_abs, ArithmeticFunction.log_apply,
      abs_of_nonneg (Real.log_natCast_nonneg m)]
    exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  exact le_of_eq (mul_comm _ _)

theorem norm_arithmeticExpSum_log_le_round (n : ℕ) (α : ℝ)
    (h : (round α : ℝ) ≠ α) :
    ‖Vinogradov.arithmeticExpSum
        (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ ≤
      Real.log (n : ℝ) / |α - (round α : ℝ)| := by
  have hd_pos : 0 < |α - (round α : ℝ)| :=
    abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
  have hd_ne : |α - (round α : ℝ)| ≠ 0 := ne_of_gt hd_pos
  set A : ℝ := 1 / (2 * |α - (round α : ℝ)|) with hA_def
  have hA_nonneg : 0 ≤ A := by positivity
  rw [arithmeticExpSum_eq_sum_Ioc]
  have hsum_eq : (∑ m ∈ Finset.Ioc 0 n,
        ((ArithmeticFunction.log m : ℝ) : ℂ) * Vinogradov.addChar α m)
      = ∑ m ∈ Finset.Ioc 0 n,
          Vinogradov.addChar α m * ((Real.log (m : ℝ) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ArithmeticFunction.log_apply, mul_comm]
  rw [hsum_eq]
  have hmain := abel_norm_bound_monotone_increasing
    (fun m => Vinogradov.addChar α m) (fun m => Real.log (m : ℝ))
    0 n (Nat.zero_le n) A hA_nonneg
    (fun k _ => norm_addChar_sum_Ioc_le_round α h k)
    (fun k => Real.log_natCast_nonneg k)
    (fun k _ _ => by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · exact Real.log_le_log (by exact_mod_cast hk)
          (by exact_mod_cast Nat.le_succ k))
  calc
    ‖∑ m ∈ Finset.Ioc 0 n,
        Vinogradov.addChar α m * ((Real.log (m : ℝ) : ℝ) : ℂ)‖
        ≤ 2 * A * Real.log (n : ℝ) := hmain
    _ = Real.log (n : ℝ) / |α - (round α : ℝ)| := by
      rw [hA_def]
      field_simp

theorem hardCutoffVaughanTypeILogDistanceSensitiveBound_holds
    (n : ℕ) (α : ℝ) :
    hardCutoffVaughanTypeILogDistanceSensitiveBound 1 n α := by
  constructor
  · simpa using norm_arithmeticExpSum_log_le_linear n α
  · intro h
    simpa using norm_arithmeticExpSum_log_le_round n α h

theorem hardCutoffVaughanTypeILogDistanceSensitiveBound_separation
    {K : ℝ} {n : ℕ} {α δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (hsep : ∀ k : ℤ, δ ≤ |α - (k : ℝ)|)
    (hb : hardCutoffVaughanTypeILogDistanceSensitiveBound K n α) :
    ‖Vinogradov.arithmeticExpSum
        (ArithmeticFunction.log : ArithmeticFunction ℝ) n α‖ ≤
      K * Real.log (n : ℝ) / δ := by
  have hne : (round α : ℝ) ≠ α := by
    intro hc
    have h0 := hsep (round α)
    rw [hc] at h0
    simp only [sub_self, abs_zero] at h0
    linarith
  exact (hb.2 hne).trans
    (div_le_div_of_nonneg_left
      (mul_nonneg hK (Real.log_natCast_nonneg n)) hδ (hsep (round α)))

end Helfgott
end MathExtras
