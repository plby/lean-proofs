import ErdosProblems.Erdos67.MRHalaszDistancePropagation
import ErdosProblems.Erdos67.MRHalaszEuler
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Euler suppression for merely multiplicative one-bounded coefficients

The complex MR theorem is stated for multiplicative functions, not only
completely multiplicative ones.  This file supplies the corresponding Euler
product estimate.  Higher prime powers are retained in each local factor and
cost an absolutely summable quadratic error.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset Filter

namespace Erdos67.MRMultiplicativeEuler

noncomputable section

open Erdos67 Erdos67.MRHalaszEuler Erdos67.EulerResidue
  Erdos67.EulerQuantitative

theorem norm_one_add_le_one_add_re_add_norm_sq
    (z : ℂ) : ‖1 + z‖ ≤ 1 + z.re + ‖z‖ ^ 2 := by
  let r := ‖z‖
  let a := z.re
  have ha : -r ≤ a := by
    dsimp [r, a]
    exact neg_le_of_abs_le (Complex.abs_re_le_norm z)
  have hr : 0 ≤ r := norm_nonneg z
  have hv : 0 ≤ 1 + a + r ^ 2 := by
    nlinarith [sq_nonneg (r - (1 / 2 : ℝ))]
  have hdiff :
      0 ≤ (1 + a + r ^ 2) ^ 2 - (1 + 2 * a + r ^ 2) := by
    have h₁ : 0 ≤ a ^ 2 := sq_nonneg a
    have h₂ : 0 ≤ 2 * r ^ 2 * (a + r) :=
      mul_nonneg (by positivity) (by linarith)
    have h₃ : 0 ≤ r ^ 2 * (r - 1) ^ 2 := by positivity
    nlinarith
  have hsquare : ‖1 + z‖ ^ 2 = 1 + 2 * a + r ^ 2 := by
    dsimp [a, r]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    norm_num
    ring
  nlinarith [norm_nonneg (1 + z)]

/-- A local Euler factor with arbitrary one-bounded prime-power
coefficients.  Its linear term is kept exactly; every higher prime power is
absorbed into `3 * ‖x‖²`. -/
theorem norm_localEulerFactor_le_exp
    (a : ℕ → ℂ) (ha0 : a 0 = 1) (ha : ∀ e, ‖a e‖ ≤ 1)
    (x : ℂ) (hx : ‖x‖ ≤ (1 / 2 : ℝ)) :
    ‖∑' e : ℕ, a e * x ^ e‖ ≤
      Real.exp ((a 1 * x).re + 3 * ‖x‖ ^ 2) := by
  let r := ‖x‖
  have hr0 : 0 ≤ r := norm_nonneg x
  have hr : r ≤ 1 / 2 := hx
  have hr1 : r < 1 := by linarith
  have hgeom : Summable (fun e : ℕ ↦ r ^ e) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hnorm : Summable (fun e : ℕ ↦ ‖a e * x ^ e‖) := by
    apply hgeom.of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    rw [norm_mul, norm_pow]
    simpa using mul_le_mul_of_nonneg_right (ha e) (pow_nonneg hr0 e)
  have hterm : Summable (fun e : ℕ ↦ a e * x ^ e) := hnorm.of_norm
  let R : ℂ := ∑' e : ℕ, a (e + 2) * x ^ (e + 2)
  have hsplit : (∑' e : ℕ, a e * x ^ e) = 1 + a 1 * x + R := by
    have hs := hterm.sum_add_tsum_nat_add 2
    rw [show (∑ e ∈ Finset.range 2, a e * x ^ e) = 1 + a 1 * x by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp [ha0]] at hs
    exact hs.symm
  have hhalf : Summable (fun e : ℕ ↦ r ^ 2 * (1 / 2 : ℝ) ^ e) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have htailNorm :
      Summable (fun e : ℕ ↦ ‖a (e + 2) * x ^ (e + 2)‖) :=
    hnorm.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  have hR : ‖R‖ ≤ 2 * r ^ 2 := by
    calc
      ‖R‖ ≤ ∑' e : ℕ, ‖a (e + 2) * x ^ (e + 2)‖ :=
        norm_tsum_le_tsum_norm htailNorm
      _ ≤ ∑' e : ℕ, r ^ 2 * (1 / 2 : ℝ) ^ e := by
        apply Summable.tsum_le_tsum
        · intro e
          rw [norm_mul, norm_pow, pow_add]
          calc
            ‖a (e + 2)‖ * (r ^ e * r ^ 2) ≤
                1 * (r ^ e * r ^ 2) :=
              mul_le_mul_of_nonneg_right (ha _) (by positivity)
            _ = r ^ 2 * r ^ e := by ring
            _ ≤ r ^ 2 * (1 / 2 : ℝ) ^ e := by gcongr
        · exact htailNorm
        · exact hhalf
      _ = 2 * r ^ 2 := by
        rw [tsum_mul_left, tsum_geometric_two]
        ring
  rw [hsplit]
  let z := a 1 * x
  have hz : ‖z‖ ≤ r := by
    dsimp [z, r]
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (ha 1) (norm_nonneg x)
  calc
    ‖1 + a 1 * x + R‖ ≤ ‖1 + z‖ + ‖R‖ := by
      dsimp [z]
      exact norm_add_le _ _
    _ ≤ (1 + z.re + ‖z‖ ^ 2) + 2 * r ^ 2 := by
      gcongr
      exact norm_one_add_le_one_add_re_add_norm_sq z
    _ ≤ 1 + z.re + 3 * r ^ 2 := by
      have hzsq : ‖z‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg z]
      linarith
    _ ≤ Real.exp (z.re + 3 * r ^ 2) := by
      calc
        1 + z.re + 3 * r ^ 2 = (z.re + 3 * r ^ 2) + 1 := by ring
        _ ≤ Real.exp (z.re + 3 * r ^ 2) :=
          Real.add_one_le_exp (z.re + 3 * r ^ 2)
    _ = _ := by rfl

/-- The summand used by the Euler product is exactly Mathlib's `LSeries`
summand, including its value zero at the natural number zero. -/
def multiplicativeLSeriesTerm (f : ℕ → ℂ) (s : ℂ) : ℕ → ℂ :=
  LSeries.term f s

@[simp]
theorem multiplicativeLSeriesTerm_zero (f : ℕ → ℂ) (s : ℂ) :
    multiplicativeLSeriesTerm f s 0 = 0 := by
  simp [multiplicativeLSeriesTerm, LSeries.term]

theorem multiplicativeLSeriesTerm_one
    {f : ℕ → ℂ} (hf : IsMultiplicativeOnPositiveNat f) (s : ℂ) :
    multiplicativeLSeriesTerm f s 1 = 1 := by
  simp [multiplicativeLSeriesTerm, LSeries.term, hf.1]

theorem multiplicativeLSeriesTerm_mul_of_coprime
    {f : ℕ → ℂ} (hf : IsMultiplicativeOnPositiveNat f) (s : ℂ)
    {m n : ℕ} (hcop : m.Coprime n) :
    multiplicativeLSeriesTerm f s (m * n) =
      multiplicativeLSeriesTerm f s m * multiplicativeLSeriesTerm f s n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hcop
    subst n
    simp [multiplicativeLSeriesTerm, LSeries.term]
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.Coprime.symm] using hcop
    subst m
    simp [multiplicativeLSeriesTerm, LSeries.term]
  rw [multiplicativeLSeriesTerm,
    LSeries.term_of_ne_zero (mul_ne_zero hm hn),
    LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn,
    hf.2 m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hcop,
    Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

theorem multiplicativeLSeriesTerm_prime_pow
    (f : ℕ → ℂ) (s : ℂ) (p e : ℕ) (hp : 0 < p) :
    multiplicativeLSeriesTerm f s (p ^ e) =
      f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
  rw [multiplicativeLSeriesTerm,
    LSeries.term_of_ne_zero (pow_ne_zero e (Nat.ne_of_gt hp)),
    div_eq_mul_inv, ← Complex.cpow_neg]
  congr 1
  push_cast
  calc
    ((p : ℂ) ^ e) ^ (-s) = (p : ℂ) ^ ((e : ℂ) * (-s)) :=
      (Complex.natCast_cpow_natCast_mul p e (-s)).symm
    _ = (p : ℂ) ^ ((-s) * e) := by congr 1 <;> ring
    _ = ((p : ℂ) ^ (-s)) ^ e := Complex.cpow_mul_nat _ _ _

theorem summable_norm_multiplicativeLSeriesTerm
    {f : ℕ → ℂ} (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ ‖multiplicativeLSeriesTerm f s n‖) := by
  have hL : LSeriesSummable f s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n hn ↦ hf n (Nat.pos_of_ne_zero hn)) hs
  exact hL.norm

/-- Euler product convergence for the exact merely-multiplicative
coefficient class used in `MRComplexNonpretentiousMeanSquareInput`. -/
theorem tendsto_multiplicative_eulerProduct
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun N : ℕ ↦ ∏ p ∈ N.primesBelow,
        ∑' e : ℕ, f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e)
      atTop (nhds (LSeries f s)) := by
  have hEuler := EulerProduct.eulerProduct
    (multiplicativeLSeriesTerm_one hmul s)
    (multiplicativeLSeriesTerm_mul_of_coprime hmul s)
    (summable_norm_multiplicativeLSeriesTerm hbound hs)
    (multiplicativeLSeriesTerm_zero f s)
  convert hEuler using 1
  · funext N
    apply Finset.prod_congr rfl
    intro p hp
    apply tsum_congr
    intro e
    exact (multiplicativeLSeriesTerm_prime_pow f s p e
      (Nat.Prime.pos (Nat.prime_of_mem_primesBelow hp))).symm
  · rfl

/-- The linear loss in a merely-multiplicative local Euler factor. -/
def multiplicativeEulerDeficit (f : ℕ → ℂ) (s : ℂ) (p : ℕ) : ℝ :=
  ‖(p : ℂ) ^ (-s)‖ - (f p * (p : ℂ) ^ (-s)).re

def finiteMultiplicativeEulerDeficit
    (f : ℕ → ℂ) (s : ℂ) (X : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE X, multiplicativeEulerDeficit f s p

theorem multiplicativeEulerDeficit_nonneg
    {f : ℕ → ℂ} (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (s : ℂ) {p : ℕ} (hp : p.Prime) :
    0 ≤ multiplicativeEulerDeficit f s p := by
  unfold multiplicativeEulerDeficit
  have hre : (f p * (p : ℂ) ^ (-s)).re ≤
      ‖f p * (p : ℂ) ^ (-s)‖ := Complex.re_le_norm _
  rw [norm_mul] at hre
  have hmul : ‖f p‖ * ‖(p : ℂ) ^ (-s)‖ ≤
      ‖(p : ℂ) ^ (-s)‖ := by
    simpa using mul_le_mul_of_nonneg_right (hf p hp.pos)
      (norm_nonneg ((p : ℂ) ^ (-s)))
  linarith

theorem norm_prime_cpow_halaszPoint_le_half
    {X p : ℕ} (hX : 1 < X) (hp : p.Prime) (t : ℝ) :
    ‖(p : ℂ) ^ (-halaszPoint X t)‖ ≤ (1 / 2 : ℝ) := by
  rw [halaszPoint,
    Erdos67.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul
      hp.pos (taoExponent X) t]
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpow : (p : ℝ) ^ (-taoExponent X) ≤ (p : ℝ) ^ (-1 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hpOne
    have := one_lt_taoExponent hX
    linarith
  rw [Real.rpow_neg_one] at hpow
  calc
    (p : ℝ) ^ (-taoExponent X) ≤ (p : ℝ)⁻¹ := hpow
    _ ≤ (2 : ℝ)⁻¹ := by
      apply inv_anti₀ (by norm_num)
      exact_mod_cast hp.two_le
    _ = 1 / 2 := by norm_num

/-- Every local factor on the Halasz line has the required linear-loss
bound, uniformly for merely multiplicative one-bounded coefficients. -/
theorem norm_multiplicative_localEulerFactor_halaszPoint_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X p : ℕ} (hX : 1 < X) (hp : p.Prime) (t : ℝ) :
    ‖∑' e : ℕ,
        f (p ^ e) * ((p : ℂ) ^ (-halaszPoint X t)) ^ e‖ ≤
      Real.exp
        (‖(p : ℂ) ^ (-halaszPoint X t)‖ -
            multiplicativeEulerDeficit f (halaszPoint X t) p +
          3 * ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2) := by
  have hlocal := norm_localEulerFactor_le_exp
    (fun e ↦ f (p ^ e))
    (by simpa using hmul.1)
    (fun e ↦ hbound (p ^ e) (pow_pos hp.pos e))
    ((p : ℂ) ^ (-halaszPoint X t))
    (norm_prime_cpow_halaszPoint_le_half hX hp t)
  have hlocal' :
      ‖∑' e : ℕ,
          f (p ^ e) * ((p : ℂ) ^ (-halaszPoint X t)) ^ e‖ ≤
        Real.exp
          ((f p * (p : ℂ) ^ (-halaszPoint X t)).re +
            3 * ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2) := by
    simpa only [pow_one] using hlocal
  have hexp :
      Real.exp
          ((f p * (p : ℂ) ^ (-halaszPoint X t)).re +
            3 * ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2) =
        Real.exp
          (‖(p : ℂ) ^ (-halaszPoint X t)‖ -
              multiplicativeEulerDeficit f (halaszPoint X t) p +
            3 * ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2) := by
    congr 1
    unfold multiplicativeEulerDeficit
    ring
  exact hlocal'.trans_eq hexp

/-- The smoothed finite linear loss dominates the usual pretentious
distance also for coefficients of norm at most one. -/
theorem exp_neg_one_mul_pretentiousDistSq_le_finiteMultiplicativeEulerDeficit
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 1 < X) (t : ℝ) :
    Real.exp (-1) * pretentiousDistSq f (archimedeanTwist t) X ≤
      finiteMultiplicativeEulerDeficit f (halaszPoint X t) X := by
  have hsets : Nat.primesLE X = primesUpTo X := by
    ext p
    rw [Nat.mem_primesLE, mem_primesUpTo]
    tauto
  rw [pretentiousDistSq, finiteMultiplicativeEulerDeficit, hsets,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := mem_primesUpTo.mp hp
  have hz : (f p * conj (archimedeanTwist t p)).re ≤ 1 := by
    calc
      (f p * conj (archimedeanTwist t p)).re ≤
          ‖f p * conj (archimedeanTwist t p)‖ := Complex.re_le_norm _
      _ ≤ 1 := by
        rw [norm_mul, norm_conj, norm_archimedeanTwist hp'.1.pos, mul_one]
        exact hbound p hp'.1.pos
  have hlocal :=
    Erdos67.HalaszCpowDeficit.exp_neg_one_mul_pretentiousTerm_le_prime_cpow_deficit
      ⟨p, hp'.1⟩ hX hp'.2 (f p) t hz
  simpa only [pretentiousTerm, multiplicativeEulerDeficit, halaszPoint,
    taoExponent, inv_eq_one_div] using hlocal

theorem sum_primesBelow_le_tsum
    {G : Nat.Primes → ℝ} (hG : Summable G)
    (hG0 : ∀ p, 0 ≤ G p) (N : ℕ) :
    (∑ p : {p // p ∈ N.primesBelow},
      G ⟨p, Nat.prime_of_mem_primesBelow p.property⟩) ≤
      ∑' p : Nat.Primes, G p := by
  let e : {p // p ∈ N.primesBelow} ↪ Nat.Primes :=
    ⟨fun p ↦ ⟨p, Nat.prime_of_mem_primesBelow p.property⟩,
      fun a b hab ↦ by
        apply Subtype.ext
        exact congrArg (fun z : Nat.Primes ↦ (z : ℕ)) hab⟩
  let S : Finset Nat.Primes := Finset.univ.map e
  have hle := hG.sum_le_tsum S (fun p hp ↦ hG0 p)
  unfold S at hle
  rw [Finset.sum_map] at hle
  exact hle

/-- Uniform finite-product majorant.  Once the Euler product includes all
primes through `X`, its norm already sees the full finite pretentious loss
at level `X`. -/
theorem norm_finiteMultiplicativeEulerProduct_halaszPoint_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X N : ℕ} (hX : 1 < X) (hXN : X < N) (t : ℝ) :
    ‖∏ p ∈ N.primesBelow,
        ∑' e : ℕ, f (p ^ e) * ((p : ℂ) ^ (-halaszPoint X t)) ^ e‖ ≤
      Real.exp
        ((∑' p : Nat.Primes,
            ‖(p : ℂ) ^ (-halaszPoint X t)‖) -
          finiteMultiplicativeEulerDeficit f (halaszPoint X t) X +
          3 * ∑' p : Nat.Primes,
            ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2) := by
  let r : ℕ → ℝ := fun p ↦ ‖(p : ℂ) ^ (-halaszPoint X t)‖
  let d : ℕ → ℝ := fun p ↦
    multiplicativeEulerDeficit f (halaszPoint X t) p
  have hs : 1 < (halaszPoint X t).re := by
    rw [halaszPoint_re]
    exact one_lt_taoExponent hX
  have hrSum := summable_primeCpowNorm hs
  have hrSqSum := summable_primeCpowNorm_sq hs
  have hprime :
      (∑ p ∈ N.primesBelow, r p) ≤
        ∑' p : Nat.Primes, ‖(p : ℂ) ^ (-halaszPoint X t)‖ := by
    calc
      (∑ p ∈ N.primesBelow, r p) =
          ∑ p : {p // p ∈ N.primesBelow},
            ‖((p : ℕ) : ℂ) ^ (-halaszPoint X t)‖ := by
        rw [Finset.sum_subtype N.primesBelow (fun _ ↦ Iff.rfl)]
      _ ≤ _ := sum_primesBelow_le_tsum hrSum (fun p ↦ norm_nonneg _) N
  have hsquare :
      (∑ p ∈ N.primesBelow, r p ^ 2) ≤
        ∑' p : Nat.Primes, ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2 := by
    calc
      (∑ p ∈ N.primesBelow, r p ^ 2) =
          ∑ p : {p // p ∈ N.primesBelow},
            ‖((p : ℕ) : ℂ) ^ (-halaszPoint X t)‖ ^ 2 := by
        rw [Finset.sum_subtype N.primesBelow (fun _ ↦ Iff.rfl)]
      _ ≤ _ := sum_primesBelow_le_tsum hrSqSum (fun p ↦ sq_nonneg _) N
  have hsubset : Nat.primesLE X ⊆ N.primesBelow := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesBelow.mpr ⟨hp'.1.trans_lt hXN, hp'.2⟩
  have hdeficit :
      finiteMultiplicativeEulerDeficit f (halaszPoint X t) X ≤
        ∑ p ∈ N.primesBelow, d p := by
    unfold finiteMultiplicativeEulerDeficit
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p hp hnot
    exact multiplicativeEulerDeficit_nonneg hbound _
      (Nat.prime_of_mem_primesBelow hp)
  calc
    ‖∏ p ∈ N.primesBelow,
        ∑' e : ℕ, f (p ^ e) * ((p : ℂ) ^ (-halaszPoint X t)) ^ e‖ =
        ∏ p ∈ N.primesBelow,
          ‖∑' e : ℕ,
            f (p ^ e) * ((p : ℂ) ^ (-halaszPoint X t)) ^ e‖ := by
      rw [norm_prod]
    _ ≤ ∏ p ∈ N.primesBelow,
        Real.exp (r p - d p + 3 * r p ^ 2) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact norm_nonneg _
      · intro p hp
        exact norm_multiplicative_localEulerFactor_halaszPoint_le
          hmul hbound hX (Nat.prime_of_mem_primesBelow hp) t
    _ = Real.exp (∑ p ∈ N.primesBelow,
        (r p - d p + 3 * r p ^ 2)) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp
        ((∑' p : Nat.Primes,
            ‖(p : ℂ) ^ (-halaszPoint X t)‖) -
          finiteMultiplicativeEulerDeficit f (halaszPoint X t) X +
          3 * ∑' p : Nat.Primes,
            ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have heq :
          (∑ p ∈ N.primesBelow, (r p - d p + 3 * r p ^ 2)) =
            (∑ p ∈ N.primesBelow, r p) -
              (∑ p ∈ N.primesBelow, d p) +
                3 * (∑ p ∈ N.primesBelow, r p ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
      rw [heq]
      linarith

/-- Complete Euler suppression for the exact multiplicativity hypothesis of
the complex MR theorem. -/
theorem norm_LSeries_halaszPoint_le_exp_logZeta_sub_pretentiousDistSq
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 1 < X) (t : ℝ) :
    ‖LSeries f (halaszPoint X t)‖ ≤
      Real.exp
        (Real.log (riemannZeta (taoExponent X : ℂ)).re -
          Real.exp (-1) * pretentiousDistSq f (archimedeanTwist t) X +
          3 * primeQuadraticConstant) := by
  let E : ℝ :=
    (∑' p : Nat.Primes, ‖(p : ℂ) ^ (-halaszPoint X t)‖) -
      finiteMultiplicativeEulerDeficit f (halaszPoint X t) X +
      3 * ∑' p : Nat.Primes, ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2
  have hlim := tendsto_multiplicative_eulerProduct hmul hbound
    (s := halaszPoint X t) (by rw [halaszPoint_re]; exact one_lt_taoExponent hX)
  have hnorm := hlim.norm
  have hfinite : ∀ᶠ N : ℕ in atTop,
      ‖∏ p ∈ N.primesBelow,
          ∑' e : ℕ, f (p ^ e) * ((p : ℂ) ^ (-halaszPoint X t)) ^ e‖ ≤
        Real.exp E := by
    filter_upwards [eventually_gt_atTop X] with N hN
    exact norm_finiteMultiplicativeEulerProduct_halaszPoint_le
      hmul hbound hX hN t
  have hbase : ‖LSeries f (halaszPoint X t)‖ ≤ Real.exp E :=
    le_of_tendsto hnorm hfinite
  refine hbase.trans (Real.exp_le_exp.mpr ?_)
  dsimp [E]
  have hprime := tsum_primeCpowNorm_halaszPoint_le_logZeta hX t
  have hdist :=
    exp_neg_one_mul_pretentiousDistSq_le_finiteMultiplicativeEulerDeficit
      hbound hX t
  have hsquare := tsum_primeCpowNorm_sq_halaszPoint_le_constant hX t
  calc
    (∑' p : Nat.Primes, ‖(p : ℂ) ^ (-halaszPoint X t)‖) -
          finiteMultiplicativeEulerDeficit f (halaszPoint X t) X +
          3 * ∑' p : Nat.Primes,
            ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2 ≤
        Real.log (riemannZeta (taoExponent X : ℂ)).re -
          finiteMultiplicativeEulerDeficit f (halaszPoint X t) X +
          3 * primeQuadraticConstant := by
      exact add_le_add
        (sub_le_sub_right hprime _)
        (mul_le_mul_of_nonneg_left hsquare (by norm_num))
    _ ≤ Real.log (riemannZeta (taoExponent X : ℂ)).re -
          Real.exp (-1) * pretentiousDistSq f (archimedeanTwist t) X +
          3 * primeQuadraticConstant := by
      simpa only [add_comm] using
        add_le_add_right
          (sub_le_sub_left hdist
            (Real.log (riemannZeta (taoExponent X : ℂ)).re))
          (3 * primeQuadraticConstant)

theorem norm_LSeries_halaszPoint_le_of_archimedeanNonpretentious
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {A X : ℕ} (hX : 1 < X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {t : ℝ} (ht : |t| ≤ X) :
    ‖LSeries f (halaszPoint X t)‖ ≤
      Real.exp
        (Real.log (riemannZeta (taoExponent X : ℂ)).re -
          Real.exp (-1) * (A : ℝ) + 3 * primeQuadraticConstant) := by
  refine
    (norm_LSeries_halaszPoint_le_exp_logZeta_sub_pretentiousDistSq
      hmul hbound hX t).trans (Real.exp_le_exp.mpr ?_)
  have hdist := hnonpret t ht
  have hexp : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  nlinarith

/-- Varying-cutoff Euler suppression.  This is the form needed on the
near-frequency portion of Proposition A.3: nonpretentiousness is known at
the top scale `X`, while the Euler/Perron line is taken at a smaller scale
`Y`.  The only loss is the explicit Mertens reciprocal-prime tail. -/
theorem exists_uniform_norm_LSeries_lower_halaszPoint_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : ℕ → ℂ} {A X Y : ℕ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X →
        MRArchimedeanNonpretentious f A X →
        ∀ t : ℝ, |t| ≤ X →
          ‖LSeries f (halaszPoint Y t)‖ ≤
            Real.exp
              (Real.log (riemannZeta (taoExponent Y : ℂ)).re -
                Real.exp (-1) *
                  ((A : ℝ) -
                    2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
                      Real.log (Y + 1 : ℝ)) +
                3 * primeQuadraticConstant) := by
  obtain ⟨C, hC, hprop⟩ :=
    Erdos67.MRHalaszDistancePropagation.exists_uniform_archimedean_distance_ge_at_lower_cutoff
  refine ⟨C, hC, ?_⟩
  intro f A X Y hmul hbound hY hYX hnonpret t ht
  have hbase :=
    norm_LSeries_halaszPoint_le_exp_logZeta_sub_pretentiousDistSq
      hmul hbound (show 1 < Y by omega) t
  refine hbase.trans (Real.exp_le_exp.mpr ?_)
  have hdist := hprop hY hYX
    (fun p hp ↦ hbound p hp.pos) hnonpret t ht
  have hexp : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  nlinarith

end

end Erdos67.MRMultiplicativeEuler
