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
import ErdosProblems.Erdos387.UniformAnalyticInputs
import Wikipedia.VinogradovsTheorem.SingularSeries
import Wikipedia.VinogradovsTheorem.External.MathExtras.Analysis.AbelSummation

/-!
# A qualitative major-arc approximation

This file contains the finite algebra and Abel summation which turn a uniform
von-Mangoldt progression discrepancy into the local approximation

`SΛ(a/q + β) = μ(q)/φ(q) · L(β) + error`.

The analytic progression estimate itself is supplied by the proved
Bombieri--Vinogradov theorem through `Erdos387.UniformAnalyticInputs`.
-/

noncomputable section

namespace VinogradovsTheorem.Analytic

open scoped BigOperators Topology ArithmeticFunction.vonMangoldt
open Filter Finset

/-- The natural-endpoint Chebyshev sum in one residue class. -/
noncomputable def psiAP (N q r : ℕ) : ℝ :=
  BoundedGaps.Maynard.chebyshevProgressionSum N q r

/-- The beta-twisted von-Mangoldt sum in one residue class. -/
noncomputable def twistedPsiAP (N q r : ℕ) (β : ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (N + 1)).filter (fun n ↦ n % q = r),
    (ArithmeticFunction.vonMangoldt n : ℂ) * Vinogradov.addChar β n

lemma psiAP_eq_range_filter (N q r : ℕ) :
    psiAP N q r =
      ∑ n ∈ (Finset.range (N + 1)).filter (fun n ↦ n % q = r % q),
        ArithmeticFunction.vonMangoldt n := by
  classical
  unfold psiAP BoundedGaps.Maynard.chebyshevProgressionSum
  let s := (Finset.Icc 1 N).filter (fun n ↦ n % q = r % q)
  let t := (Finset.range (N + 1)).filter (fun n ↦ n % q = r % q)
  have hst : s ⊆ t := by
    intro n hn
    simp only [s, t, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_range] at hn ⊢
    exact ⟨by omega, hn.2⟩
  exact Finset.sum_subset hst (by
    intro n hnt hns
    have hn0 : n = 0 := by
      simp only [s, t, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_range] at hnt hns
      omega
    subst n
    simp)

private theorem sum_residue_classes_eq_sum
    (N q : ℕ) (hq : q ≠ 0) (f : ℕ → ℂ) :
    (∑ r ∈ Finset.range q,
      ∑ n ∈ (Finset.range (N + 1)).filter (fun n ↦ n % q = r), f n) =
      ∑ n ∈ Finset.range (N + 1), f n := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hmod : n % q ∈ Finset.range q :=
    Finset.mem_range.mpr (Nat.mod_lt n (Nat.pos_of_ne_zero hq))
  calc
    (∑ r ∈ Finset.range q, if n % q = r then f n else 0) =
        (if n % q = n % q then f n else 0) :=
      Finset.sum_eq_single (n % q)
        (fun r hr hne ↦ by rw [if_neg hne.symm])
        (fun h ↦ (h hmod).elim)
    _ = f n := by rw [if_pos rfl]

lemma vonMangoldtExpSum_residue_partition
    (α : ℝ) (N q : ℕ) (hq : q ≠ 0) :
    Vinogradov.vonMangoldtExpSum α N =
      ∑ r ∈ Finset.range q,
        ∑ n ∈ (Finset.range (N + 1)).filter (fun n ↦ n % q = r),
          (ArithmeticFunction.vonMangoldt n : ℂ) * Vinogradov.addChar α n := by
  unfold Vinogradov.vonMangoldtExpSum
  exact (sum_residue_classes_eq_sum N q hq
    (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) *
      Vinogradov.addChar α n)).symm

lemma addChar_add_left (α β : ℝ) (n : ℕ) :
    Vinogradov.addChar (α + β) n =
      Vinogradov.addChar α n * Vinogradov.addChar β n := by
  unfold Vinogradov.addChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma addChar_rationalCenter_eq_of_mod {a q n r : ℕ}
    (hq : q ≠ 0) (hr : n % q = r) :
    Vinogradov.addChar (Vinogradov.rationalCenter a q) n =
      Vinogradov.addChar (Vinogradov.rationalCenter a q) r := by
  have hn : n = q * (n / q) + r := by
    rw [← hr]
    exact (Nat.div_add_mod n q).symm
  rw [hn, Vinogradov.addChar_add_right]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have htrivial :
      Vinogradov.addChar (Vinogradov.rationalCenter a q) (q * (n / q)) = 1 := by
    unfold Vinogradov.addChar Vinogradov.rationalCenter
    have harg :
        2 * Real.pi * Complex.I * ((q * (n / q) : ℕ) : ℂ) *
            ((((a : ℝ) / (q : ℝ) : ℝ) : ℂ)) =
          ((a * (n / q) : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp [hqC]
    rw [harg, Complex.exp_nat_mul_two_pi_mul_I]
  rw [htrivial, one_mul]

/-- Residue-class decomposition at a rational center. -/
theorem vonMangoldtExpSum_majorArc_residue_decomposition
    (N a q : ℕ) (β : ℝ) (hq : q ≠ 0) :
    Vinogradov.vonMangoldtExpSum
        (Vinogradov.rationalCenter a q + β) N =
      ∑ r ∈ Finset.range q,
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β := by
  rw [vonMangoldtExpSum_residue_partition
    (Vinogradov.rationalCenter a q + β) N q hq]
  refine Finset.sum_congr rfl ?_
  intro r hr
  unfold twistedPsiAP
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hmod : n % q = r := (Finset.mem_filter.mp hn).2
  rw [addChar_add_left,
    addChar_rationalCenter_eq_of_mod hq hmod]
  ring

private theorem norm_addChar_succ_sub_le (β : ℝ) (n : ℕ) :
    ‖Vinogradov.addChar β (n + 1) - Vinogradov.addChar β n‖ ≤
      2 * Real.pi * |β| := by
  have hfactor :
      Vinogradov.addChar β (n + 1) - Vinogradov.addChar β n =
        Vinogradov.addChar β n * (Vinogradov.addChar β 1 - 1) := by
    rw [Vinogradov.addChar_add_right]
    ring
  have hsin : |Real.sin (Real.pi * β)| ≤ Real.pi * |β| := by
    calc
      |Real.sin (Real.pi * β)| ≤ |Real.pi * β| := Real.abs_sin_le_abs
      _ = Real.pi * |β| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  calc
    ‖Vinogradov.addChar β (n + 1) - Vinogradov.addChar β n‖
        = ‖Vinogradov.addChar β 1 - 1‖ := by
          rw [hfactor, norm_mul, Vinogradov.norm_addChar, one_mul]
    _ = 2 * |Real.sin (Real.pi * β)| :=
      Vinogradov.norm_addChar_one_sub_one_eq_two_abs_sin β
    _ ≤ 2 * Real.pi * |β| := by nlinarith

private theorem AP_error_partial_sum_bound
    {N q r : ℕ} {E : ℝ} (hr : r < q) (hE : 0 ≤ E)
    (hAP : ∀ n : ℕ, n ≤ N →
      |psiAP n q r - (n : ℝ) / (Nat.totient q : ℝ)| ≤ E)
    {k : ℕ} (hk : k ≤ N + 1) :
    ‖∑ n ∈ Finset.range k,
        (((if n % q = r then ArithmeticFunction.vonMangoldt n else 0) -
          1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖ ≤
      E + ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖ := by
  rcases k with _ | k
  · simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact add_nonneg hE (norm_nonneg _)
  · have hkN : k ≤ N := Nat.succ_le_succ_iff.mp hk
    have hmod : r % q = r := Nat.mod_eq_of_lt hr
    have hsum_real :
        (∑ n ∈ Finset.range (k + 1),
            ((if n % q = r then ArithmeticFunction.vonMangoldt n else 0) -
              1 / (Nat.totient q : ℝ) : ℝ)) =
          psiAP k q r - (k + 1 : ℝ) / (Nat.totient q : ℝ) := by
      rw [Finset.sum_sub_distrib]
      have hcoeff :
          (∑ n ∈ Finset.range (k + 1),
              (if n % q = r then ArithmeticFunction.vonMangoldt n else 0)) =
            psiAP k q r := by
        rw [psiAP_eq_range_filter]
        rw [← hmod]
        simp [Finset.sum_filter]
      rw [hcoeff]
      simp [div_eq_mul_inv, mul_comm]
    have hrewrite :
        psiAP k q r - (k + 1 : ℝ) / (Nat.totient q : ℝ) =
          (psiAP k q r - (k : ℝ) / (Nat.totient q : ℝ)) -
            1 / (Nat.totient q : ℝ) := by ring
    have htriangle :
        |psiAP k q r - (k + 1 : ℝ) / (Nat.totient q : ℝ)| ≤
          E + |1 / (Nat.totient q : ℝ)| := by
      rw [hrewrite]
      exact (abs_sub _ _).trans
        (add_le_add (hAP k hkN) le_rfl)
    calc
      ‖∑ n ∈ Finset.range (k + 1),
          (((if n % q = r then ArithmeticFunction.vonMangoldt n else 0) -
            1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖
          = ‖(((∑ n ∈ Finset.range (k + 1),
              ((if n % q = r then ArithmeticFunction.vonMangoldt n else 0) -
                1 / (Nat.totient q : ℝ) : ℝ)) : ℝ) : ℂ)‖ := by
              congr 1
              simp
      _ = |∑ n ∈ Finset.range (k + 1),
              ((if n % q = r then ArithmeticFunction.vonMangoldt n else 0) -
                1 / (Nat.totient q : ℝ) : ℝ)| := by
            simpa [Real.norm_eq_abs] using
              (Complex.norm_real (∑ n ∈ Finset.range (k + 1),
                ((if n % q = r then ArithmeticFunction.vonMangoldt n else 0) -
                  1 / (Nat.totient q : ℝ) : ℝ)))
      _ = |psiAP k q r - (k + 1 : ℝ) / (Nat.totient q : ℝ)| := by
            rw [hsum_real]
      _ ≤ E + |1 / (Nat.totient q : ℝ)| := htriangle
      _ = E + ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖ := by simp

private theorem twistedPsiAP_sub_main_eq_error_sum
    (N q r : ℕ) (β : ℝ) :
    twistedPsiAP N q r β -
        (((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) *
          Vinogradov.linearExpSum N β) =
      ∑ n ∈ Finset.range (N + 1),
        (((if n % q = r then ArithmeticFunction.vonMangoldt n else 0) -
          1 / (Nat.totient q : ℝ) : ℝ) : ℂ) *
            Vinogradov.addChar β n := by
  rw [twistedPsiAP, Vinogradov.linearExpSum, Finset.sum_filter,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro n hn
  by_cases hnr : n % q = r
  · simp [hnr, sub_mul]
  · simp [hnr]

/-- Discrete Abel summation for a twisted progression sum. -/
theorem twistedPsiAP_main_approx
    {N q r : ℕ} {β E : ℝ} (hr : r < q) (hE : 0 ≤ E)
    (hAP : ∀ n : ℕ, n ≤ N →
      |psiAP n q r - (n : ℝ) / (Nat.totient q : ℝ)| ≤ E) :
    ‖twistedPsiAP N q r β -
        (((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) *
          Vinogradov.linearExpSum N β)‖ ≤
      (E + ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖) *
        (1 + 2 * Real.pi * |β| * (N : ℝ)) := by
  let c : ℝ := 1 / (Nat.totient q : ℝ)
  let b : ℕ → ℂ := fun n ↦
    (((if n % q = r then ArithmeticFunction.vonMangoldt n else 0) - c : ℝ) : ℂ)
  have hG : ∀ k ≤ N + 1,
      ‖∑ n ∈ Finset.range k, b n‖ ≤ E + ‖((c : ℝ) : ℂ)‖ := by
    intro k hk
    simpa [b, c] using AP_error_partial_sum_bound
      (N := N) (q := q) (r := r) (E := E) hr hE hAP hk
  have hweighted :
      twistedPsiAP N q r β -
          (((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) *
            Vinogradov.linearExpSum N β) =
        ∑ n ∈ Finset.range (N + 1), b n * Vinogradov.addChar β n := by
    simpa [b, c, mul_comm] using twistedPsiAP_sub_main_eq_error_sum N q r β
  rw [hweighted]
  have hAbel := Finset.sum_range_by_parts (R := ℂ) (M := ℂ)
    (fun n : ℕ ↦ Vinogradov.addChar β n) b (N + 1)
  have hleft :
      (∑ n ∈ Finset.range (N + 1), b n * Vinogradov.addChar β n) =
        ∑ n ∈ Finset.range (N + 1), Vinogradov.addChar β n • b n := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [mul_comm]
  rw [hleft, hAbel]
  have hmain :
      ‖Vinogradov.addChar β (N + 1 - 1) •
          ∑ i ∈ Finset.range (N + 1), b i‖ ≤
        E + ‖((c : ℝ) : ℂ)‖ := by
    simpa [Vinogradov.norm_addChar] using hG (N + 1) le_rfl
  have hsum :
      ‖∑ i ∈ Finset.range (N + 1 - 1),
          (Vinogradov.addChar β (i + 1) - Vinogradov.addChar β i) •
            ∑ x ∈ Finset.range (i + 1), b x‖ ≤
        (N : ℝ) * ((2 * Real.pi * |β|) *
          (E + ‖((c : ℝ) : ℂ)‖)) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N + 1 - 1),
          ‖(Vinogradov.addChar β (i + 1) - Vinogradov.addChar β i) •
            ∑ x ∈ Finset.range (i + 1), b x‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range (N + 1 - 1),
          (2 * Real.pi * |β|) * (E + ‖((c : ℝ) : ℂ)‖) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hiN : i + 1 ≤ N + 1 := by
          exact Nat.succ_le_succ (Nat.le_of_lt (Finset.mem_range.mp (by simpa using hi)))
        rw [norm_smul]
        exact mul_le_mul (norm_addChar_succ_sub_le β i) (hG (i + 1) hiN)
          (norm_nonneg _) (by positivity)
      _ = (N : ℝ) * ((2 * Real.pi * |β|) *
          (E + ‖((c : ℝ) : ℂ)‖)) := by simp
  exact (norm_sub_le _ _).trans <| by
    calc
      ‖Vinogradov.addChar β (N + 1 - 1) •
          ∑ i ∈ Finset.range (N + 1), b i‖ +
          ‖∑ i ∈ Finset.range (N + 1 - 1),
            (Vinogradov.addChar β (i + 1) - Vinogradov.addChar β i) •
              ∑ x ∈ Finset.range (i + 1), b x‖
          ≤ (E + ‖((c : ℝ) : ℂ)‖) +
            (N : ℝ) * ((2 * Real.pi * |β|) *
              (E + ‖((c : ℝ) : ℂ)‖)) := add_le_add hmain hsum
      _ = (E + ‖((c : ℝ) : ℂ)‖) *
          (1 + 2 * Real.pi * |β| * (N : ℝ)) := by ring

/-- Reduced-residue phase aggregation in the Ramanujan-sum convention. -/
lemma reduced_addChar_sum_eq_ramanujanSum (a q : ℕ) :
    (∑ r ∈ (Finset.range q).filter (fun r ↦ Nat.Coprime r q),
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r) =
      Vinogradov.ramanujanSum q a := by
  rfl

/-- A common reduced-residue main term aggregates to a Ramanujan sum. -/
lemma reduced_main_term_aggregates_to_ramanujan (a q : ℕ) (main : ℂ) :
    (∑ r ∈ (Finset.range q).filter (fun r ↦ Nat.Coprime r q),
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r * main) =
      Vinogradov.ramanujanSum q a * main := by
  rw [← Finset.sum_mul, reduced_addChar_sum_eq_ramanujanSum]

/-- Uniform errors over reduced residue classes lose at most a factor `q`. -/
lemma reduced_residue_error_aggregation
    (N a q : ℕ) (β : ℝ) (main : ℂ) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hbound : ∀ r : ℕ, r < q → Nat.Coprime r q →
      ‖twistedPsiAP N q r β - main‖ ≤ δ) :
    ‖∑ r ∈ (Finset.range q).filter (fun r ↦ Nat.Coprime r q),
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          (twistedPsiAP N q r β - main)‖ ≤
      (q : ℝ) * δ := by
  let s := (Finset.range q).filter (fun r ↦ Nat.Coprime r q)
  have hsum_norm :
      ‖∑ r ∈ s, Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          (twistedPsiAP N q r β - main)‖ ≤
        ∑ r ∈ s, ‖Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          (twistedPsiAP N q r β - main)‖ := norm_sum_le _ _
  have hsum_le :
      (∑ r ∈ s, ‖Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          (twistedPsiAP N q r β - main)‖) ≤ ∑ _r ∈ s, δ := by
    refine Finset.sum_le_sum ?_
    intro r hr
    have hrq : r < q := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hcop : Nat.Coprime r q := (Finset.mem_filter.mp hr).2
    simpa [norm_mul, Vinogradov.norm_addChar] using hbound r hrq hcop
  have hcard : (s.card : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (by
      simpa [s] using Finset.card_filter_le (Finset.range q)
        (fun r ↦ Nat.Coprime r q))
  calc
    ‖∑ r ∈ (Finset.range q).filter (fun r ↦ Nat.Coprime r q),
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          (twistedPsiAP N q r β - main)‖
        ≤ ∑ r ∈ s, ‖Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          (twistedPsiAP N q r β - main)‖ := by simpa [s] using hsum_norm
    _ ≤ ∑ _r ∈ s, δ := hsum_le
    _ = (s.card : ℝ) * δ := by simp [nsmul_eq_mul]
    _ ≤ (q : ℝ) * δ := mul_le_mul_of_nonneg_right hcard hδ

private theorem norm_twistedPsiAP_le_sum (N q r : ℕ) (β : ℝ) :
    ‖twistedPsiAP N q r β‖ ≤
      ∑ n ∈ (Finset.range (N + 1)).filter (fun n ↦ n % q = r),
        ArithmeticFunction.vonMangoldt n := by
  unfold twistedPsiAP
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro n _hn
  rw [norm_mul, Vinogradov.norm_addChar]
  have hnonneg : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg, mul_one]

private theorem fixed_prime_power_vonMangoldt_sum_le_log_succ
    (N p : ℕ) (hp : p.Prime) :
    (∑ n ∈ (Finset.range (N + 1)).filter
        (fun n ↦ IsPrimePow n ∧ n.minFac = p),
        ArithmeticFunction.vonMangoldt n) ≤
      Real.log ((N : ℝ) + 1) := by
  let K := Nat.log p (N + 1)
  let T := (Finset.range (N + 1)).filter
    (fun n ↦ IsPrimePow n ∧ n.minFac = p)
  have hp_pow_ne_zero : p ^ K ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hsubset : T ⊆ (p ^ K).divisors := by
    intro n hn
    have hn_range : n < N + 1 :=
      Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hn_pp : IsPrimePow n := (Finset.mem_filter.mp hn).2.1
    have hn_min : n.minFac = p := (Finset.mem_filter.mp hn).2.2
    have hn_repr : n.minFac ^ n.factorization n.minFac = n :=
      hn_pp.minFac_pow_factorization_eq
    have hpow_le : p ^ n.factorization n.minFac ≤ N + 1 := by
      calc
        p ^ n.factorization n.minFac = n := by simpa [hn_min] using hn_repr
        _ ≤ N + 1 := by omega
    have hexp_le : n.factorization n.minFac ≤ K :=
      Nat.le_log_of_pow_le hp.one_lt hpow_le
    have hdvd : n ∣ p ^ K := by
      rw [← hn_repr, hn_min]
      exact Nat.pow_dvd_pow p (by simpa [hn_min] using hexp_le)
    exact Nat.mem_divisors.mpr ⟨hdvd, hp_pow_ne_zero⟩
  have hnonneg : ∀ n ∈ (p ^ K).divisors, n ∉ T →
      0 ≤ ArithmeticFunction.vonMangoldt n := by
    intro n _hn _hnot
    exact ArithmeticFunction.vonMangoldt_nonneg
  have hsum_divisors :
      (∑ n ∈ T, ArithmeticFunction.vonMangoldt n) ≤
        ∑ n ∈ (p ^ K).divisors, ArithmeticFunction.vonMangoldt n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have hdivisor_sum :
      (∑ n ∈ (p ^ K).divisors, ArithmeticFunction.vonMangoldt n) =
        Real.log ((p ^ K : ℕ) : ℝ) := ArithmeticFunction.vonMangoldt_sum
  have hpow_le_succ : p ^ K ≤ N + 1 :=
    Nat.pow_log_le_self p (Nat.succ_ne_zero N)
  have hlog_le :
      Real.log ((p ^ K : ℕ) : ℝ) ≤ Real.log ((N : ℝ) + 1) := by
    have hpow_pos : (0 : ℝ) < ((p ^ K : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hp_pow_ne_zero
    have hcast_le : ((p ^ K : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
      exact_mod_cast hpow_le_succ
    exact Real.log_le_log hpow_pos hcast_le
  calc
    (∑ n ∈ (Finset.range (N + 1)).filter
        (fun n ↦ IsPrimePow n ∧ n.minFac = p),
        ArithmeticFunction.vonMangoldt n) =
        ∑ n ∈ T, ArithmeticFunction.vonMangoldt n := rfl
    _ ≤ ∑ n ∈ (p ^ K).divisors, ArithmeticFunction.vonMangoldt n :=
      hsum_divisors
    _ = Real.log ((p ^ K : ℕ) : ℝ) := hdivisor_sum
    _ ≤ Real.log ((N : ℝ) + 1) := hlog_le

private theorem nonReduced_vonMangoldt_pointwise_le_primeFactors_sum
    {q n : ℕ} (hq : 0 < q) :
    (if ¬ Nat.Coprime (n % q) q then ArithmeticFunction.vonMangoldt n else 0) ≤
      ∑ p ∈ q.primeFactors,
        if IsPrimePow n ∧ n.minFac = p then
          ArithmeticFunction.vonMangoldt n else 0 := by
  by_cases hnonred : ¬ Nat.Coprime (n % q) q
  · by_cases hzero : ArithmeticFunction.vonMangoldt n = 0
    · simp [hnonred, hzero]
    · have hpos : 0 < ArithmeticFunction.vonMangoldt n :=
        lt_of_le_of_ne ArithmeticFunction.vonMangoldt_nonneg (Ne.symm hzero)
      have hnpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_pos_iff.mp hpos
      have hpmin : n.minFac.Prime := Nat.minFac_prime hnpp.ne_one
      rcases Nat.Prime.not_coprime_iff_dvd.mp hnonred with
        ⟨ell, hell_prime, hell_mod, hell_q⟩
      have hell_n : ell ∣ n := (Nat.dvd_mod_iff hell_q).mp hell_mod
      have hn_repr : n.minFac ^ n.factorization n.minFac = n :=
        hnpp.minFac_pow_factorization_eq
      have hell_pow : ell ∣ n.minFac ^ n.factorization n.minFac := by
        simpa [hn_repr] using hell_n
      have hell_min : ell ∣ n.minFac := hell_prime.dvd_of_dvd_pow hell_pow
      have hmin_eq : n.minFac = ell :=
        (hpmin.dvd_iff_eq hell_prime.ne_one).mp hell_min
      have hmin_q : n.minFac ∣ q := by simpa [hmin_eq] using hell_q
      have hmem : n.minFac ∈ q.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpmin, hmin_q, Nat.ne_of_gt hq⟩
      have hterms : ∀ p ∈ q.primeFactors,
          0 ≤ if IsPrimePow n ∧ n.minFac = p then
            ArithmeticFunction.vonMangoldt n else 0 := by
        intro p _hp
        split_ifs
        · exact ArithmeticFunction.vonMangoldt_nonneg
        · exact le_rfl
      have hsingle := Finset.single_le_sum hterms hmem
      simpa [hnonred, hnpp] using hsingle
  · rw [if_neg hnonred]
    exact Finset.sum_nonneg (by
      intro p _hp
      split_ifs
      · exact ArithmeticFunction.vonMangoldt_nonneg
      · exact le_rfl)

private theorem nonReduced_residue_vonMangoldt_sum_eq_filter
    (q N : ℕ) (hq : 0 < q) :
    (∑ r ∈ (Finset.range q).filter (fun r ↦ ¬ Nat.Coprime r q),
        ∑ n ∈ (Finset.range (N + 1)).filter (fun n ↦ n % q = r),
          ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.range (N + 1),
        if ¬ Nat.Coprime (n % q) q then
          ArithmeticFunction.vonMangoldt n else 0 := by
  simp_rw [Finset.sum_filter]
  have hpush :
      (∑ r ∈ Finset.range q,
        if ¬ Nat.Coprime r q then
          ∑ n ∈ Finset.range (N + 1),
            if n % q = r then ArithmeticFunction.vonMangoldt n else 0
        else 0) =
      ∑ r ∈ Finset.range q,
        ∑ n ∈ Finset.range (N + 1),
          if ¬ Nat.Coprime r q then
            if n % q = r then ArithmeticFunction.vonMangoldt n else 0
          else 0 := by
    refine Finset.sum_congr rfl ?_
    intro r _hr
    by_cases hr : ¬ Nat.Coprime r q <;> simp [hr]
  rw [hpush, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  have hmem : n % q ∈ Finset.range q :=
    Finset.mem_range.mpr (Nat.mod_lt n hq)
  calc
    (∑ r ∈ Finset.range q,
        if ¬ Nat.Coprime r q then
          if n % q = r then ArithmeticFunction.vonMangoldt n else 0
        else 0) =
        (if ¬ Nat.Coprime (n % q) q then
          if n % q = n % q then ArithmeticFunction.vonMangoldt n else 0
        else 0) := by
          refine Finset.sum_eq_single (a := n % q) ?_ ?_
          · intro r _hr hne
            simp [hne.symm]
          · intro hnot
            exact (hnot hmem).elim
    _ = (if ¬ Nat.Coprime (n % q) q then
          ArithmeticFunction.vonMangoldt n else 0) := by simp

private theorem nonReduced_residue_vonMangoldt_mass_le_primeFactors
    (q N : ℕ) (hq : 0 < q) :
    (∑ r ∈ (Finset.range q).filter (fun r ↦ ¬ Nat.Coprime r q),
        ∑ n ∈ (Finset.range (N + 1)).filter (fun n ↦ n % q = r),
          ArithmeticFunction.vonMangoldt n) ≤
      ∑ p ∈ q.primeFactors,
        ∑ n ∈ (Finset.range (N + 1)).filter
          (fun n ↦ IsPrimePow n ∧ n.minFac = p),
          ArithmeticFunction.vonMangoldt n := by
  rw [nonReduced_residue_vonMangoldt_sum_eq_filter q N hq]
  calc
    (∑ n ∈ Finset.range (N + 1),
        if ¬ Nat.Coprime (n % q) q then
          ArithmeticFunction.vonMangoldt n else 0) ≤
        ∑ n ∈ Finset.range (N + 1),
          ∑ p ∈ q.primeFactors,
            if IsPrimePow n ∧ n.minFac = p then
              ArithmeticFunction.vonMangoldt n else 0 := by
          refine Finset.sum_le_sum ?_
          intro n _hn
          exact nonReduced_vonMangoldt_pointwise_le_primeFactors_sum hq
    _ = ∑ p ∈ q.primeFactors,
        ∑ n ∈ Finset.range (N + 1),
          if IsPrimePow n ∧ n.minFac = p then
            ArithmeticFunction.vonMangoldt n else 0 := by rw [Finset.sum_comm]
    _ = ∑ p ∈ q.primeFactors,
        ∑ n ∈ (Finset.range (N + 1)).filter
          (fun n ↦ IsPrimePow n ∧ n.minFac = p),
          ArithmeticFunction.vonMangoldt n := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          rw [Finset.sum_filter]

/-- Prime-power support makes the non-reduced residue contribution logarithmic. -/
theorem nonReduced_residue_contribution_bound
    (a q N : ℕ) (β : ℝ) (hq : 0 < q) :
    ‖∑ r ∈ (Finset.range q).filter (fun r ↦ ¬ Nat.Coprime r q),
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β‖ ≤
      (q.primeFactors.card : ℝ) * Real.log ((N : ℝ) + 1) := by
  let s := (Finset.range q).filter (fun r ↦ ¬ Nat.Coprime r q)
  have hsum_norm :
      ‖∑ r ∈ s, Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β‖ ≤
        ∑ r ∈ s, ‖Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β‖ := norm_sum_le _ _
  have hterm :
      (∑ r ∈ s, ‖Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β‖) ≤
        ∑ r ∈ s,
          ∑ n ∈ (Finset.range (N + 1)).filter (fun n ↦ n % q = r),
            ArithmeticFunction.vonMangoldt n := by
    refine Finset.sum_le_sum ?_
    intro r _hr
    simpa [norm_mul, Vinogradov.norm_addChar] using
      norm_twistedPsiAP_le_sum N q r β
  have hsupport :
      (∑ r ∈ s,
          ∑ n ∈ (Finset.range (N + 1)).filter (fun n ↦ n % q = r),
            ArithmeticFunction.vonMangoldt n) ≤
        ∑ p ∈ q.primeFactors,
          ∑ n ∈ (Finset.range (N + 1)).filter
            (fun n ↦ IsPrimePow n ∧ n.minFac = p),
            ArithmeticFunction.vonMangoldt n := by
    simpa [s] using nonReduced_residue_vonMangoldt_mass_le_primeFactors q N hq
  have hper_prime :
      (∑ p ∈ q.primeFactors,
          ∑ n ∈ (Finset.range (N + 1)).filter
            (fun n ↦ IsPrimePow n ∧ n.minFac = p),
            ArithmeticFunction.vonMangoldt n) ≤
        ∑ _p ∈ q.primeFactors, Real.log ((N : ℝ) + 1) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact fixed_prime_power_vonMangoldt_sum_le_log_succ N p
      (Nat.prime_of_mem_primeFactors hp)
  calc
    ‖∑ r ∈ (Finset.range q).filter (fun r ↦ ¬ Nat.Coprime r q),
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β‖
        ≤ ∑ r ∈ s, ‖Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β‖ := by simpa [s] using hsum_norm
    _ ≤ ∑ r ∈ s,
          ∑ n ∈ (Finset.range (N + 1)).filter (fun n ↦ n % q = r),
            ArithmeticFunction.vonMangoldt n := hterm
    _ ≤ ∑ p ∈ q.primeFactors,
          ∑ n ∈ (Finset.range (N + 1)).filter
            (fun n ↦ IsPrimePow n ∧ n.minFac = p),
            ArithmeticFunction.vonMangoldt n := hsupport
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log ((N : ℝ) + 1) := hper_prime
    _ = (q.primeFactors.card : ℝ) * Real.log ((N : ℝ) + 1) := by
      simp [nsmul_eq_mul]

private theorem residue_bridge_split
    (N a q : ℕ) (β : ℝ) (main : ℂ) :
    (∑ r ∈ Finset.range q,
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β) -
        (∑ r ∈ (Finset.range q).filter (fun r ↦ Nat.Coprime r q),
          Vinogradov.addChar (Vinogradov.rationalCenter a q) r * main) =
      (∑ r ∈ (Finset.range q).filter (fun r ↦ Nat.Coprime r q),
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          (twistedPsiAP N q r β - main)) +
      (∑ r ∈ (Finset.range q).filter (fun r ↦ ¬ Nat.Coprime r q),
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β) := by
  set s := (Finset.range q).filter (fun r ↦ Nat.Coprime r q)
  set t := (Finset.range q).filter (fun r ↦ ¬ Nat.Coprime r q)
  have hsplit :
      (∑ r ∈ Finset.range q,
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β) =
        (∑ r ∈ s, Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β) +
        (∑ r ∈ t, Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
          twistedPsiAP N q r β) := by
    have h := (Finset.sum_filter_add_sum_filter_not (s := Finset.range q)
      (p := fun r ↦ Nat.Coprime r q)
      (f := fun r ↦ Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
        twistedPsiAP N q r β)).symm
    simpa [s, t] using h
  have hred :
      (∑ r ∈ s, Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
        twistedPsiAP N q r β) -
        (∑ r ∈ s, Vinogradov.addChar (Vinogradov.rationalCenter a q) r * main) =
      ∑ r ∈ s, Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
        (twistedPsiAP N q r β - main) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    ring
  rw [hsplit]
  simp only [s, t] at hred ⊢
  rw [← hred]
  abel

/-- A uniform finite progression estimate gives the local major-arc model,
with all losses explicit. -/
theorem vonMangoldtExpSum_local_approximation
    {N a q : ℕ} {β E : ℝ}
    (hq : 0 < q) (haq : a.Coprime q) (hE : 0 ≤ E)
    (hAP : ∀ r : ℕ, r < q → r.Coprime q → ∀ n : ℕ, n ≤ N →
      |psiAP n q r - (n : ℝ) / (Nat.totient q : ℝ)| ≤ E) :
    ‖Vinogradov.vonMangoldtExpSum
        (Vinogradov.rationalCenter a q + β) N -
      (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
          (Nat.totient q : ℝ) : ℝ) : ℂ) *
        Vinogradov.linearExpSum N β)‖ ≤
      (q : ℝ) *
          ((E + ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖) *
            (1 + 2 * Real.pi * |β| * (N : ℝ))) +
        (q.primeFactors.card : ℝ) * Real.log ((N : ℝ) + 1) := by
  let main : ℂ :=
    ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * Vinogradov.linearExpSum N β
  let redErr : ℂ :=
    ∑ r ∈ (Finset.range q).filter (fun r ↦ Nat.Coprime r q),
      Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
        (twistedPsiAP N q r β - main)
  let nonred : ℂ :=
    ∑ r ∈ (Finset.range q).filter (fun r ↦ ¬ Nat.Coprime r q),
      Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
        twistedPsiAP N q r β
  have hphi : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hphiC : (Nat.totient q : ℂ) ≠ 0 := by exact_mod_cast hphi.ne'
  have hram :
      Vinogradov.ramanujanSum q a =
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) :=
    Vinogradov.ramanujanSum_eq_moebius_of_coprime haq
  have hmain_coeff :
      (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
          (Nat.totient q : ℝ) : ℝ) : ℂ) *
        Vinogradov.linearExpSum N β) =
      Vinogradov.ramanujanSum q a * main := by
    rw [hram]
    simp only [main]
    push_cast
    field_simp [hphiC]
  have hmain_sum :
      (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
          (Nat.totient q : ℝ) : ℝ) : ℂ) *
        Vinogradov.linearExpSum N β) =
      ∑ r ∈ (Finset.range q).filter (fun r ↦ Nat.Coprime r q),
        Vinogradov.addChar (Vinogradov.rationalCenter a q) r * main := by
    rw [hmain_coeff]
    exact (reduced_main_term_aggregates_to_ramanujan a q main).symm
  have hdecomp :
      Vinogradov.vonMangoldtExpSum
          (Vinogradov.rationalCenter a q + β) N =
        ∑ r ∈ Finset.range q,
          Vinogradov.addChar (Vinogradov.rationalCenter a q) r *
            twistedPsiAP N q r β :=
    vonMangoldtExpSum_majorArc_residue_decomposition N a q β hq.ne'
  have hsplit :
      Vinogradov.vonMangoldtExpSum
          (Vinogradov.rationalCenter a q + β) N -
        (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
            (Nat.totient q : ℝ) : ℝ) : ℂ) *
          Vinogradov.linearExpSum N β) = redErr + nonred := by
    rw [hdecomp, hmain_sum]
    exact residue_bridge_split N a q β main
  let δ : ℝ :=
    (E + ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖) *
      (1 + 2 * Real.pi * |β| * (N : ℝ))
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hred : ‖redErr‖ ≤ (q : ℝ) * δ := by
    apply reduced_residue_error_aggregation N a q β main δ hδ
    intro r hr hcop
    simpa [main, δ] using
      twistedPsiAP_main_approx (N := N) (q := q) (r := r)
        (β := β) (E := E) hr hE (hAP r hr hcop)
  have hnonred :
      ‖nonred‖ ≤
        (q.primeFactors.card : ℝ) * Real.log ((N : ℝ) + 1) := by
    simpa [nonred] using nonReduced_residue_contribution_bound a q N β hq
  calc
    ‖Vinogradov.vonMangoldtExpSum
        (Vinogradov.rationalCenter a q + β) N -
      (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
          (Nat.totient q : ℝ) : ℝ) : ℂ) *
        Vinogradov.linearExpSum N β)‖ = ‖redErr + nonred‖ := by rw [hsplit]
    _ ≤ ‖redErr‖ + ‖nonred‖ := norm_add_le _ _
    _ ≤ (q : ℝ) * δ +
        (q.primeFactors.card : ℝ) * Real.log ((N : ℝ) + 1) :=
      add_le_add hred hnonred
    _ = (q : ℝ) *
          ((E + ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖) *
            (1 + 2 * Real.pi * |β| * (N : ℝ))) +
        (q.primeFactors.card : ℝ) * Real.log ((N : ℝ) + 1) := by rfl

end VinogradovsTheorem.Analytic
