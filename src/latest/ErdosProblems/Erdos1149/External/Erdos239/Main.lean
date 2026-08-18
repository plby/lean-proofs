/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 239

Every real-valued multiplicative function taking only the values `-1` and `1`
has a Cesàro mean.  This is the Erdős--Wintner conjecture, proved by Wirsing
in 1967 and subsequently generalized by Halász.

The statement below intentionally agrees with the statement in the
`google-deepmind/formal-conjectures` repository.  In particular,
multiplicativity is required only for coprime arguments.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos239

syntax (name := answerSyntax239) "answer(" term ")" : term

macro_rules
  | `(answer($t)) => `($t)

/-- The normalized summatory function occurring in Problem 239. -/
noncomputable def meanUpTo (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 N, f n) / N

/-- The hypotheses in Problem 239, packaged for use by the auxiliary lemmas. -/
def IsSignMultiplicative (f : ℕ → ℝ) : Prop :=
  (∀ n ≥ 1, f n = 1 ∨ f n = -1) ∧
  (∀ m n, m.Coprime n → f (m * n) = f m * f n) ∧
  f 1 = 1

lemma IsSignMultiplicative.sign {f : ℕ → ℝ} (hf : IsSignMultiplicative f)
    {n : ℕ} (hn : 1 ≤ n) : f n = 1 ∨ f n = -1 :=
  hf.1 n hn

lemma IsSignMultiplicative.abs_eq_one {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {n : ℕ} (hn : 1 ≤ n) : |f n| = 1 := by
  rcases hf.sign hn with h | h <;> simp [h]

lemma IsSignMultiplicative.norm_eq_one {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {n : ℕ} (hn : 1 ≤ n) : ‖f n‖ = 1 := by
  simpa [Real.norm_eq_abs] using hf.abs_eq_one hn

lemma IsSignMultiplicative.mem_Icc {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {n : ℕ} (hn : 1 ≤ n) : f n ∈ Set.Icc (-1) 1 := by
  rcases hf.sign hn with h | h <;> simp [h]

lemma IsSignMultiplicative.mul {f : ℕ → ℝ} (hf : IsSignMultiplicative f)
    {m n : ℕ} (hmn : m.Coprime n) : f (m * n) = f m * f n :=
  hf.2.1 m n hmn

lemma IsSignMultiplicative.one {f : ℕ → ℝ} (hf : IsSignMultiplicative f) :
    f 1 = 1 :=
  hf.2.2

/-- Prime-factorization formula for a sign-valued multiplicative function. -/
lemma IsSignMultiplicative.eq_factorization_prod {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) {n : ℕ} (hn : n ≠ 0) :
    f n = n.factorization.prod fun p k => f (p ^ k) := by
  exact Nat.multiplicative_factorization f (fun m n hmn => hf.mul hmn) hf.one hn

/-- The averages are uniformly bounded by one. -/
lemma abs_meanUpTo_le_one {f : ℕ → ℝ} (hf : IsSignMultiplicative f) (N : ℕ) :
    |meanUpTo f N| ≤ 1 := by
  by_cases hN : N = 0
  · simp [meanUpTo, hN]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hterm : ∀ n ∈ Finset.Icc 1 N, |f n| ≤ 1 := by
    intro n hn
    rw [hf.abs_eq_one (Finset.mem_Icc.mp hn).1]
  calc
    |meanUpTo f N|
        = |∑ n ∈ Finset.Icc 1 N, f n| / (N : ℝ) := by
            simp [meanUpTo, abs_div, abs_of_pos hNpos]
    _ ≤ (∑ n ∈ Finset.Icc 1 N, |f n|) / (N : ℝ) := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _n ∈ Finset.Icc 1 N, (1 : ℝ)) / (N : ℝ) := by
          exact div_le_div_of_nonneg_right (Finset.sum_le_sum hterm) hNpos.le
    _ = 1 := by
          simp [Nat.card_Icc, hNpos.ne']

/-! ## The Wintner summable-convolution lemma

This is the soft half of Wirsing's dichotomy.  If an arithmetic function is
the Dirichlet convolution of `g` with the constant-one arithmetic function,
and `∑ |g(n)| / n` converges, then its Cesàro mean is `∑ g(n) / n`.
-/

open scoped ArithmeticFunction.zeta

/-- For fixed positive `d`, the density of multiples of `d` in an initial
interval tends to `1 / d`. -/
lemma tendsto_natDiv_div (d : ℕ) (_hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) atTop
      (𝓝 ((d : ℝ)⁻¹)) := by
  have h := tendsto_nat_floor_mul_div_atTop
    (R := ℝ) (a := (d : ℝ)⁻¹) (inv_nonneg.mpr (Nat.cast_nonneg d))
  have h' := h.comp tendsto_natCast_atTop_atTop
  refine h'.congr' (Eventually.of_forall fun N => ?_)
  simp only [Function.comp_apply]
  rw [show (d : ℝ)⁻¹ * (N : ℝ) = (N : ℝ) / (d : ℝ) by
    simp [div_eq_mul_inv, mul_comm]]
  rw [Nat.floor_div_eq_div]

/-- Wintner's averaging lemma, in the exact `Finset.Ioc 0 N` convention used
by Mathlib's summatory-convolution identity. -/
theorem tendsto_mean_dirichlet_mul_zeta (g : ArithmeticFunction ℝ)
    (hg : Summable fun n : ℕ => |g n| / (n : ℝ)) :
    Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Ioc 0 N, (g * ζ) n) / (N : ℝ))
      atTop (𝓝 (∑' n : ℕ, g n / (n : ℝ))) := by
  let a : ℕ → ℕ → ℝ := fun N n =>
    if n ∈ Finset.Ioc 0 N then
      g n * (((N / n : ℕ) : ℝ) / (N : ℝ))
    else 0
  have ha_lim : ∀ n : ℕ,
      Tendsto (fun N : ℕ => a N n) atTop (𝓝 (g n / (n : ℝ))) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [a]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hevent : ∀ᶠ N : ℕ in atTop, n ∈ Finset.Ioc 0 N :=
        eventually_atTop.2 ⟨n, fun N hN => Finset.mem_Ioc.mpr ⟨hnpos, hN⟩⟩
      change Tendsto (fun N : ℕ => a N n) atTop (𝓝 (g n * (n : ℝ)⁻¹))
      refine (tendsto_const_nhds.mul (tendsto_natDiv_div n hnpos)).congr' ?_
      filter_upwards [hevent] with N hN
      dsimp [a]
      rw [if_pos hN]
  have ha_bound : ∀ᶠ N : ℕ in atTop,
      ∀ n : ℕ, ‖a N n‖ ≤ |g n| / (n : ℝ) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with N hN
    intro n
    by_cases hmem : n ∈ Finset.Ioc 0 N
    · have hnpos : 0 < n := (Finset.mem_Ioc.mp hmem).1
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
      have hratio_nonneg :
          0 ≤ ((N / n : ℕ) : ℝ) / (N : ℝ) := by positivity
      have hratio : ((N / n : ℕ) : ℝ) / (N : ℝ) ≤ (n : ℝ)⁻¹ := by
        calc
          ((N / n : ℕ) : ℝ) / (N : ℝ)
              ≤ ((N : ℝ) / (n : ℝ)) / (N : ℝ) := by
                exact div_le_div_of_nonneg_right Nat.cast_div_le hNpos.le
          _ = (n : ℝ)⁻¹ := by
                field_simp
      simp only [a, if_pos hmem, norm_mul, Real.norm_eq_abs,
        Real.norm_of_nonneg hratio_nonneg]
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hratio (abs_nonneg _)
    · simp only [a, if_neg hmem, norm_zero]
      positivity
  have htannery := tendsto_tsum_of_dominated_convergence hg ha_lim ha_bound
  convert htannery using 1
  · ext N
    rw [ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
    rw [Finset.sum_div]
    simp only [a]
    rw [tsum_eq_sum (s := Finset.Ioc 0 N)]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [hn, mul_div_assoc]
    · intro n hn
      simp [hn]

/-- The arithmetic-function version of `f`, with the required value zero at
the natural number zero. -/
noncomputable def arithmeticFunction (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

@[simp] lemma arithmeticFunction_zero (f : ℕ → ℝ) : arithmeticFunction f 0 = 0 := by
  simp [arithmeticFunction]

lemma arithmeticFunction_apply_of_pos (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    arithmeticFunction f n = f n := by
  simp [arithmeticFunction, hn.ne']

lemma arithmeticFunction_isMultiplicative {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) :
    (arithmeticFunction f).IsMultiplicative := by
  refine ⟨by simp [arithmeticFunction, hf.one], ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · subst m
    simp
  by_cases hn : n = 0
  · subst n
    simp
  simp only [arithmeticFunction_apply_of_pos f (Nat.pos_of_ne_zero hm),
    arithmeticFunction_apply_of_pos f (Nat.pos_of_ne_zero hn),
    arithmeticFunction_apply_of_pos f (Nat.mul_pos
      (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn))]
  exact hf.mul hmn

/-- Möbius correction `g = f * μ`; thus `f = g * 1`. -/
noncomputable def correction (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  arithmeticFunction f * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

lemma correction_isMultiplicative {f : ℕ → ℝ}
    (hf : IsSignMultiplicative f) : (correction f).IsMultiplicative :=
  (arithmeticFunction_isMultiplicative hf).mul
    ArithmeticFunction.isMultiplicative_moebius.intCast

lemma correction_mul_zeta (f : ℕ → ℝ) :
    correction f * ζ = arithmeticFunction f := by
  simp [correction, mul_assoc]

/-- On prime powers the Möbius correction is the first difference of the
local values of `f`. -/
lemma correction_prime_pow_succ (f : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    correction f (p ^ (k + 1)) = f (p ^ (k + 1)) - f (p ^ k) := by
  have hsucc := congrArg (fun F : ArithmeticFunction ℝ => F (p ^ (k + 1)))
    (correction_mul_zeta f)
  have hbase := congrArg (fun F : ArithmeticFunction ℝ => F (p ^ k))
    (correction_mul_zeta f)
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at hsucc hbase
  rw [Finset.sum_range_succ] at hsucc
  rw [arithmeticFunction_apply_of_pos f (pow_pos hp.pos _)] at hsucc hbase
  linarith

/-- The convergent branch of Wirsing's theorem, isolated with its exact
Möbius-correction summability hypothesis. -/
theorem tendsto_mean_of_correction_summable {f : ℕ → ℝ}
    (_hf : IsSignMultiplicative f)
    (hsum : Summable fun n : ℕ => |correction f n| / (n : ℝ)) :
    Tendsto (meanUpTo f) atTop
      (𝓝 (∑' n : ℕ, correction f n / (n : ℝ))) := by
  have h := tendsto_mean_dirichlet_mul_zeta (correction f) hsum
  rw [correction_mul_zeta] at h
  convert h using 1
  ext N
  have hsets : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hsets]
  simp only [meanUpTo]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact (arithmeticFunction_apply_of_pos f (Finset.mem_Icc.mp hn).1).symm

end Erdos239
