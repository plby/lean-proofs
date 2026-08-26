import ErdosProblems.Erdos67b.TwistSeparationAnalytic
import ErdosProblems.Erdos67b.EulerResidue
import ErdosProblems.Erdos67b.PrimeEulerTail

/-!
# Truncated Euler logarithms and Dirichlet L-functions

This file gives the exact comparison between the finite Euler logarithm used
in the polynomial-height twist-separation argument and the full Euler
product for a Dirichlet L-function.  The comparison is valid uniformly in
the character, endpoint, and height.  It isolates the sole remaining
elementary tail estimate as an explicit, absolutely convergent `tsum`.
-/

open scoped BigOperators
open Complex Finset

namespace Erdos67b.TruncatedEulerLSeries

noncomputable section

/-- The primes at most `Y`, regarded as a finite set of `Nat.Primes`. -/
def primeSubtypesUpTo (Y : ℕ) : Finset Nat.Primes :=
  (primesUpTo Y).attach.map
    { toFun := fun p ↦ (⟨p.1, (mem_primesUpTo.mp p.2).1⟩ : Nat.Primes)
      inj' := fun a b h ↦ by
        apply Subtype.ext
        exact congrArg (fun p : Nat.Primes ↦ p.1) h }

@[simp] theorem mem_primeSubtypesUpTo {Y : ℕ} {p : Nat.Primes} :
    p ∈ primeSubtypesUpTo Y ↔ (p : ℕ) ≤ Y := by
  unfold primeSubtypesUpTo
  simp only [Finset.mem_map, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact (mem_primesUpTo.mp a.2).2
  · intro hpY
    let a : {n // n ∈ primesUpTo Y} :=
      ⟨p.1, mem_primesUpTo.mpr ⟨p.2, hpY⟩⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    rfl

/-- The local Euler logarithm at the shifted polynomial-height point. -/
def localEulerLog {N : ℕ} (ψ : DirichletCharacter ℂ N)
    (Y : ℕ) (v : ℝ) (p : Nat.Primes) : ℂ :=
  -Complex.log (1 - ψ p * (p : ℂ) ^ (-polynomialHeightEulerPoint Y v))

theorem localEulerLog_eq {N Y : ℕ} (ψ : DirichletCharacter ℂ N)
    (v : ℝ) (p : Nat.Primes) :
    localEulerLog ψ Y v p =
      -Complex.log (1 - polynomialHeightEulerPrimeTerm ψ Y v p) := by
  rfl

theorem polynomialHeightEulerPoint_re (Y : ℕ) (v : ℝ) :
    (polynomialHeightEulerPoint Y v).re =
      1 + (Real.log (Y : ℝ))⁻¹ := by
  simp only [polynomialHeightEulerPoint, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
    Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero]

theorem one_lt_polynomialHeightEulerPoint_re {Y : ℕ} (hY : 2 ≤ Y)
    (v : ℝ) : 1 < (polynomialHeightEulerPoint Y v).re := by
  rw [polynomialHeightEulerPoint_re]
  have hlog : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  linarith [inv_pos.mpr hlog]

theorem summable_localEulerLog {N Y : ℕ}
    (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    Summable (localEulerLog ψ Y v) := by
  exact DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow ψ
    (one_lt_polynomialHeightEulerPoint_re hY v)

/-- The positive weight of a prime in the Euler product at the shifted
point. -/
def shiftedPrimeWeight (Y : ℕ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-(1 : ℝ) - (Real.log (Y : ℝ))⁻¹)

theorem norm_polynomialHeightEulerPrimeTerm_eq_shiftedPrimeWeight
    {N Y : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ)
    (p : Nat.Primes) :
    ‖polynomialHeightEulerPrimeTerm ψ Y v p‖ =
      ‖ψ p‖ * shiftedPrimeWeight Y p := by
  unfold polynomialHeightEulerPrimeTerm polynomialHeightEulerPoint
    shiftedPrimeWeight
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_zero, add_zero]
  congr 2
  ring

theorem norm_localEulerLog_le_shiftedPrimeWeight_add_inv_sq
    {N Y : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ)
    (hY : 2 ≤ Y) (p : Nat.Primes) :
    ‖localEulerLog ψ Y v p‖ ≤
      shiftedPrimeWeight Y p + (p : ℝ) ^ (-(2 : ℝ)) := by
  have hrem := norm_eulerLog_sub_linear_le_inv_sq ψ v hY p.2
  have hterm := norm_polynomialHeightEulerPrimeTerm_eq_shiftedPrimeWeight
    (Y := Y) ψ v p
  have hψ := ψ.norm_le_one p
  calc
    ‖localEulerLog ψ Y v p‖ ≤
        ‖localEulerLog ψ Y v p -
            polynomialHeightEulerPrimeTerm ψ Y v p‖ +
          ‖polynomialHeightEulerPrimeTerm ψ Y v p‖ := by
      have := norm_add_le
        (localEulerLog ψ Y v p - polynomialHeightEulerPrimeTerm ψ Y v p)
        (polynomialHeightEulerPrimeTerm ψ Y v p)
      simpa only [sub_add_cancel] using this
    _ ≤ (p : ℝ) ^ (-(2 : ℝ)) +
          ‖ψ p‖ * shiftedPrimeWeight Y p :=
      add_le_add hrem hterm.le
    _ ≤ (p : ℝ) ^ (-(2 : ℝ)) + shiftedPrimeWeight Y p := by
      have hw : 0 ≤ shiftedPrimeWeight Y p := by
        exact Real.rpow_nonneg (Nat.cast_nonneg p.1) _
      exact add_le_add_right
        (mul_le_of_le_one_left hw hψ) _
    _ = shiftedPrimeWeight Y p + (p : ℝ) ^ (-(2 : ℝ)) := by ring

theorem summable_shiftedPrimeWeight {Y : ℕ} (hY : 2 ≤ Y) :
    Summable (shiftedPrimeWeight Y) := by
  have hlog : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  exact (Real.summable_nat_rpow.mpr (by
    linarith [inv_pos.mpr hlog] :
      -(1 : ℝ) - (Real.log (Y : ℝ))⁻¹ < -1)).subtype Nat.Prime

theorem summable_prime_inv_sq :
    Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (-(2 : ℝ))) :=
  (Real.summable_nat_rpow.mpr (by norm_num)).subtype Nat.Prime

/-- The source finite sum is exactly the sum of the local factors indexed by
the corresponding finite set of prime subtypes. -/
theorem truncatedPolynomialHeightEulerLog_eq_sum_subtypes {N Y : ℕ}
    (ψ : DirichletCharacter ℂ N) (v : ℝ) :
    truncatedPolynomialHeightEulerLog ψ Y v =
      ∑ p ∈ primeSubtypesUpTo Y, (localEulerLog ψ Y v p).re := by
  unfold truncatedPolynomialHeightEulerLog
  apply Finset.sum_bij
    (fun p hp ↦ (⟨p, (mem_primesUpTo.mp hp).1⟩ : Nat.Primes))
  · intro p hp
    exact mem_primeSubtypesUpTo.mpr (mem_primesUpTo.mp hp).2
  · intro p₁ hp₁ p₂ hp₂ heq
    exact congrArg Subtype.val heq
  · intro p hp
    refine ⟨p.1, mem_primesUpTo.mpr ⟨p.2,
      mem_primeSubtypesUpTo.mp hp⟩, ?_⟩
    apply Subtype.ext
    rfl
  · intro p hp
    rfl

/-- The full real Euler logarithm is the logarithm of the norm of the
Dirichlet L-series.  This equality is branch-free: it follows by taking
norms in Mathlib's exponential Euler-product identity. -/
theorem tsum_re_localEulerLog_eq_log_norm_LSeries {N Y : ℕ}
    (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    (∑' p : Nat.Primes, (localEulerLog ψ Y v p).re) =
      Real.log ‖LSeries (fun n : ℕ ↦ ψ n)
        (polynomialHeightEulerPoint Y v)‖ := by
  have hs := one_lt_polynomialHeightEulerPoint_re hY v
  have hsum := summable_localEulerLog ψ v hY
  have heuler := DirichletCharacter.LSeries_eulerProduct_exp_log ψ hs
  have hnorm := congrArg norm heuler
  rw [Complex.norm_exp] at hnorm
  have hre :
      (∑' p : Nat.Primes, localEulerLog ψ Y v p).re =
        ∑' p : Nat.Primes, (localEulerLog ψ Y v p).re :=
    Complex.re_tsum hsum
  change Real.exp (∑' p : Nat.Primes, localEulerLog ψ Y v p).re = _ at hnorm
  rw [hre] at hnorm
  rw [← hnorm, Real.log_exp]

/-- The same identity in terms of the analytically continued L-function. -/
theorem tsum_re_localEulerLog_eq_log_norm_LFunction {N Y : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    (∑' p : Nat.Primes, (localEulerLog ψ Y v p).re) =
      Real.log ‖DirichletCharacter.LFunction ψ
        (polynomialHeightEulerPoint Y v)‖ := by
  rw [DirichletCharacter.LFunction_eq_LSeries ψ
    (one_lt_polynomialHeightEulerPoint_re hY v)]
  exact tsum_re_localEulerLog_eq_log_norm_LSeries ψ v hY

/-- Exact finite/full decomposition.  The second term is the contribution
of the omitted primes `p > Y`; no asymptotic assertion is used here. -/
theorem truncated_add_tail_eq_log_norm_LFunction {N Y : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    truncatedPolynomialHeightEulerLog ψ Y v +
        (∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          (localEulerLog ψ Y v p).re) =
      Real.log ‖DirichletCharacter.LFunction ψ
        (polynomialHeightEulerPoint Y v)‖ := by
  rw [truncatedPolynomialHeightEulerLog_eq_sum_subtypes]
  have hs := summable_localEulerLog ψ v hY
  have hsre : Summable (fun p : Nat.Primes ↦ (localEulerLog ψ Y v p).re) :=
    (Complex.hasSum_re hs.hasSum).summable
  rw [hsre.sum_add_tsum_subtype_compl]
  exact tsum_re_localEulerLog_eq_log_norm_LFunction ψ v hY

/-- One-sided form of the exact comparison, with the absolute Euler tail as
an explicit error term. -/
theorem truncated_le_log_norm_LFunction_add_tail_norm {N Y : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    truncatedPolynomialHeightEulerLog ψ Y v ≤
      Real.log ‖DirichletCharacter.LFunction ψ
          (polynomialHeightEulerPoint Y v)‖ +
        ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          ‖localEulerLog ψ Y v p‖ := by
  have hdecomp := truncated_add_tail_eq_log_norm_LFunction ψ v hY
  let tail := ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
    (localEulerLog ψ Y v p).re
  have htail :
      |tail| ≤ ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
        ‖localEulerLog ψ Y v p‖ := by
    have hs := (summable_localEulerLog ψ v hY).subtype
      (fun p : Nat.Primes ↦ p ∉ primeSubtypesUpTo Y)
    have hre : Summable (fun p : {p : Nat.Primes //
        p ∉ primeSubtypesUpTo Y} ↦ (localEulerLog ψ Y v p).re) :=
      (Complex.hasSum_re hs.hasSum).summable
    have hnorm := hs.norm
    calc
      |tail| = ‖∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          (localEulerLog ψ Y v p).re‖ := by simp [tail]
      _ ≤ ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          ‖(localEulerLog ψ Y v p).re‖ := norm_tsum_le_tsum_norm hre.norm
      _ ≤ ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          ‖localEulerLog ψ Y v p‖ := by
        exact Summable.tsum_le_tsum
          (fun p ↦ by simpa using Complex.abs_re_le_norm (localEulerLog ψ Y v p))
          hre.norm hnorm
  change truncatedPolynomialHeightEulerLog ψ Y v ≤ _
  change truncatedPolynomialHeightEulerLog ψ Y v + tail = _ at hdecomp
  rw [← hdecomp]
  have hneg :
      -(∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          ‖localEulerLog ψ Y v p‖) ≤ tail :=
    neg_le_of_abs_le htail
  linarith

/-- The explicit scalar tail which remains after the exact L-function
comparison. -/
def shiftedEulerTail (Y : ℕ) : ℝ :=
  ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
    shiftedPrimeWeight Y p

theorem shiftedEulerTail_nonneg (Y : ℕ) : 0 ≤ shiftedEulerTail Y := by
  exact tsum_nonneg fun p ↦ Real.rpow_nonneg (by positivity) _

/-- An absolute uniform upper bound for the omitted linear prime tail. -/
def shiftedEulerTailConstant : ℝ :=
  4 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2

theorem shiftedEulerTailConstant_nonneg : 0 ≤ shiftedEulerTailConstant := by
  unfold shiftedEulerTailConstant
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hM : 0 ≤ Real.log 2 + primeLogIntervalMertensConstant :=
    add_nonneg hlog.le primeLogIntervalMertensConstant_nonneg
  positivity

/-- The omitted linear Euler tail is bounded by an absolute constant,
uniformly in its moving endpoint. -/
theorem shiftedEulerTail_le_constant {Y : ℕ} (hY : 4 ≤ Y) :
    shiftedEulerTail Y ≤ shiftedEulerTailConstant := by
  unfold shiftedEulerTail
  have hsummable := (summable_shiftedPrimeWeight (show 2 ≤ Y by omega)).subtype
    (fun p : Nat.Primes ↦ p ∉ primeSubtypesUpTo Y)
  apply hsummable.tsum_le_of_sum_le
  intro s
  let e : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y} ↪ ℕ :=
    { toFun := fun p ↦ p.1.1
      inj' := fun a b h ↦ by
        apply Subtype.ext
        apply Subtype.ext
        exact h }
  let t : Finset ℕ := s.map e
  let Z : ℕ := t.sup id
  have ht : t ⊆ primesBetween Y Z := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hp
    have hnot : ¬(a.1.1 : ℕ) ≤ Y := by
      intro hle
      exact a.2 (mem_primeSubtypesUpTo.mpr hle)
    refine mem_primesBetween.mpr ⟨a.1.2, Nat.lt_of_not_ge hnot, ?_⟩
    have hsup : (fun n : ℕ ↦ n) (e a) ≤
        t.sup (fun n : ℕ ↦ n) :=
      Finset.le_sup (f := fun n : ℕ ↦ n) hp
    change a.1.1 ≤ t.sup id at hsup
    exact hsup
  have hnonneg : ∀ p ∈ primesBetween Y Z, p ∉ t →
      0 ≤ (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
    intro p hp hpt
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  calc
    (∑ p ∈ s, shiftedPrimeWeight Y p) =
        ∑ p ∈ t, (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro p hp
      unfold shiftedPrimeWeight e
      congr 1
      ring
    _ ≤ ∑ p ∈ primesBetween Y Z,
          (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) :=
      Finset.sum_le_sum_of_subset_of_nonneg ht hnonneg
    _ ≤ shiftedEulerTailConstant := by
      exact reciprocalLog_primeRpow_tail_le hY

theorem tail_prime_inv_sq_le_remainderBound (Y : ℕ) :
    (∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
        (p : ℝ) ^ (-(2 : ℝ))) ≤
      polynomialHeightPrimePowerRemainderBound := by
  have hNat : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hPrime : Summable (fun p : Nat.Primes ↦
      (p : ℝ) ^ (-(2 : ℝ))) := hNat.subtype Nat.Prime
  calc
    (∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
        (p : ℝ) ^ (-(2 : ℝ))) ≤
        ∑' p : Nat.Primes, (p : ℝ) ^ (-(2 : ℝ)) :=
      hPrime.tsum_subtype_le
        (fun p : Nat.Primes ↦ (p : ℝ) ^ (-(2 : ℝ)))
        {p : Nat.Primes | p ∉ primeSubtypesUpTo Y}
        (fun p ↦ Real.rpow_nonneg (by positivity) _)
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ)) :=
      hNat.tsum_subtype_le
        (fun n : ℕ ↦ (n : ℝ) ^ (-(2 : ℝ)))
        {n : ℕ | n.Prime}
        (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = polynomialHeightPrimePowerRemainderBound := rfl

/-- Fully explicit finite/full comparison.  The square-power contribution
is absorbed into the fixed constant already used in the finite
linear-to-logarithmic reduction; only `shiftedEulerTail Y` remains. -/
theorem truncated_le_log_norm_LFunction_add_shiftedEulerTail {N Y : ℕ}
    [NeZero N] (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    truncatedPolynomialHeightEulerLog ψ Y v ≤
      Real.log ‖DirichletCharacter.LFunction ψ
          (polynomialHeightEulerPoint Y v)‖ +
        shiftedEulerTail Y + polynomialHeightPrimePowerRemainderBound := by
  have hmain := truncated_le_log_norm_LFunction_add_tail_norm ψ v hY
  have hweight := (summable_shiftedPrimeWeight hY).subtype
    (fun p : Nat.Primes ↦ p ∉ primeSubtypesUpTo Y)
  have hsq := summable_prime_inv_sq.subtype
    (fun p : Nat.Primes ↦ p ∉ primeSubtypesUpTo Y)
  have hlocal := (summable_localEulerLog ψ v hY).subtype
    (fun p : Nat.Primes ↦ p ∉ primeSubtypesUpTo Y) |>.norm
  have htail :
      (∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          ‖localEulerLog ψ Y v p‖) ≤
        shiftedEulerTail Y +
          ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
            (p : ℝ) ^ (-(2 : ℝ)) := by
    calc
      (∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
          ‖localEulerLog ψ Y v p‖) ≤
          ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
            (shiftedPrimeWeight Y p + (p : ℝ) ^ (-(2 : ℝ))) := by
        exact Summable.tsum_le_tsum
          (fun p ↦ norm_localEulerLog_le_shiftedPrimeWeight_add_inv_sq
            ψ v hY p)
          hlocal (hweight.add hsq)
      _ = (∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
            shiftedPrimeWeight Y p) +
          ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
            (p : ℝ) ^ (-(2 : ℝ)) := by
        simpa only [Function.comp_apply] using hweight.tsum_add hsq
      _ = shiftedEulerTail Y +
          ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
            (p : ℝ) ^ (-(2 : ℝ)) := rfl
  have hsqBound := tail_prime_inv_sq_le_remainderBound Y
  calc
    truncatedPolynomialHeightEulerLog ψ Y v ≤
        Real.log ‖DirichletCharacter.LFunction ψ
            (polynomialHeightEulerPoint Y v)‖ +
          ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
            ‖localEulerLog ψ Y v p‖ := hmain
    _ ≤ Real.log ‖DirichletCharacter.LFunction ψ
            (polynomialHeightEulerPoint Y v)‖ +
          (shiftedEulerTail Y +
            ∑' p : {p : Nat.Primes // p ∉ primeSubtypesUpTo Y},
              (p : ℝ) ^ (-(2 : ℝ))) := by gcongr
    _ ≤ Real.log ‖DirichletCharacter.LFunction ψ
            (polynomialHeightEulerPoint Y v)‖ +
          shiftedEulerTail Y + polynomialHeightPrimePowerRemainderBound := by
      linarith

/-- Uniform `O(1)` bridge from the truncated Euler logarithm to the
Dirichlet L-function at `1 + 1 / log Y + i v`. -/
theorem truncated_le_log_norm_LFunction_add_uniformConstant {N Y : ℕ}
    [NeZero N] (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 4 ≤ Y) :
    truncatedPolynomialHeightEulerLog ψ Y v ≤
      Real.log ‖DirichletCharacter.LFunction ψ
          (polynomialHeightEulerPoint Y v)‖ +
        (shiftedEulerTailConstant +
          polynomialHeightPrimePowerRemainderBound) := by
  have hbridge := truncated_le_log_norm_LFunction_add_shiftedEulerTail
    ψ v (show 2 ≤ Y by omega)
  have htail := shiftedEulerTail_le_constant hY
  linarith

end

end Erdos67b.TruncatedEulerLSeries
