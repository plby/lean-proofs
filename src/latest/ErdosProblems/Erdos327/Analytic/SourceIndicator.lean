import ErdosProblems.Erdos327.Analytic.CoordinateCounting
import ErdosProblems.Erdos327.Analytic.FactorCounts

/-!
# The localized source-coordinate indicator

This file connects the exact parity identity
`2b = u(u+v)d` to the localized factor count controlled by source
regularity.
-/

namespace Erdos327.Analytic

open Finset Real
open scoped ArithmeticFunction.Omega

noncomputable section

/-- If `n` divides twice an `L`-rough number, at most one factor of
`n` is invisible to the localized count: the possible factor `2`. -/
theorem cardFactors_le_primeFactorCountBetween_add_one_of_dvd_two
    {L X b n : ℕ}
    (hL : 3 ≤ L) (hn : 0 < n) (hnX : n ≤ X)
    (hrough : Rough L b) (hndvd : n ∣ 2 * b) :
    ArithmeticFunction.cardFactors n ≤
      primeFactorCountBetween L X n + 1 := by
  rcases Nat.even_or_odd n with heven | hodd
  · rcases heven with ⟨k, hk⟩
    have hnEq : n = 2 * k := by omega
    have hk0 : 0 < k := by omega
    have hkX : k ≤ X := by omega
    rcases hndvd with ⟨c, hc⟩
    have hbEq : b = k * c := by
      have htwoEq : 2 * b = 2 * (k * c) := by
        rw [hc, hnEq]
        ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) htwoEq
    have hkDvd : k ∣ b := ⟨c, hbEq⟩
    have hkRough : Rough L k := hrough.of_dvd hkDvd
    have hlocalized :=
      primeFactorCountBetween_eq_cardFactors_of_rough
        hk0 hkX hkRough
    rw [hnEq,
      ArithmeticFunction.cardFactors_mul (by norm_num) hk0.ne',
      ArithmeticFunction.cardFactors_apply_prime Nat.prime_two,
      primeFactorCountBetween_two_mul hL hk0.ne',
      hlocalized]
    omega
  · have hnDvdB : n ∣ b :=
      hodd.coprime_two_right.dvd_of_dvd_mul_left hndvd
    have hnRough : Rough L n := hrough.of_dvd hnDvdB
    have hlocalized :=
      primeFactorCountBetween_eq_cardFactors_of_rough
        hn hnX hnRough
    omega

/-- The two full factor counts and the residual localized count are
controlled by the localized count of the reconstructed source vertex.
The constant two comes from applying the harmless possible-factor-`2`
loss separately to `u` and `u+v`. -/
theorem source_factorCount_le_vertexCount_add_two
    {L N : ℕ} {A K : ℝ} {q : SourceTriple}
    (hL : 3 ≤ L) (hq : q ∈ sourceCoordinateSet L N A K) :
    ArithmeticFunction.cardFactors (sourceU q) +
          ArithmeticFunction.cardFactors (sourceU q + sourceV q) +
          primeFactorCountBetween L (sourceU q + sourceV q)
            (sourceD q) ≤
      primeFactorCountBetween L (sourceU q + sourceV q)
          (sourceVertex q) + 2 := by
  rw [sourceCoordinateSet, mem_filter] at hq
  rcases hq with
    ⟨hqBox, hcop, _hv3u, _hscore, _hpair, hexact, _hLsum,
      _hbLower, _hbUpper, _hoddU, _hoddSum, _hoddD,
      hrough, _hregular⟩
  rcases mem_product.mp hqBox with ⟨huvBox, hdBox⟩
  rcases mem_product.mp huvBox with ⟨huBox, hvBox⟩
  have hu0 : 0 < sourceU q := (mem_Icc.mp huBox).1
  have hv0 : 0 < sourceV q := (mem_Icc.mp hvBox).1
  have hd0 : 0 < sourceD q := (mem_Icc.mp hdBox).1
  have hsum0 : 0 < sourceU q + sourceV q := by omega
  have hb0 : 0 < sourceVertex q := by
    have hrhs0 :
        0 < sourceU q * (sourceU q + sourceV q) * sourceD q :=
      Nat.mul_pos (Nat.mul_pos hu0 hsum0) hd0
    have : 0 < 2 * sourceVertex q := by
      rw [hexact]
      exact hrhs0
    omega
  have huDvd : sourceU q ∣ 2 * sourceVertex q := by
    refine ⟨(sourceU q + sourceV q) * sourceD q, ?_⟩
    rw [hexact]
    ring
  have hsumDvd :
      sourceU q + sourceV q ∣ 2 * sourceVertex q := by
    refine ⟨sourceU q * sourceD q, ?_⟩
    rw [hexact]
    ring
  have huLeSum : sourceU q ≤ sourceU q + sourceV q := by omega
  have huCount :=
    cardFactors_le_primeFactorCountBetween_add_one_of_dvd_two
      hL hu0 huLeSum hrough huDvd
  have hsumCount :=
    cardFactors_le_primeFactorCountBetween_add_one_of_dvd_two
      hL hsum0 le_rfl hrough hsumDvd
  have hprodCount :
      primeFactorCountBetween L (sourceU q + sourceV q)
          (sourceU q * (sourceU q + sourceV q) * sourceD q) =
        primeFactorCountBetween L (sourceU q + sourceV q)
            (sourceU q) +
          primeFactorCountBetween L (sourceU q + sourceV q)
            (sourceU q + sourceV q) +
          primeFactorCountBetween L (sourceU q + sourceV q)
            (sourceD q) := by
    rw [primeFactorCountBetween_mul
      (Nat.mul_ne_zero hu0.ne' hsum0.ne') hd0.ne',
      primeFactorCountBetween_mul hu0.ne' hsum0.ne']
  have hcount :
      primeFactorCountBetween L (sourceU q + sourceV q)
            (sourceU q) +
          primeFactorCountBetween L (sourceU q + sourceV q)
            (sourceU q + sourceV q) +
          primeFactorCountBetween L (sourceU q + sourceV q)
            (sourceD q) =
        primeFactorCountBetween L (sourceU q + sourceV q)
          (sourceVertex q) := by
    calc
      _ = primeFactorCountBetween L (sourceU q + sourceV q)
          (sourceU q * (sourceU q + sourceV q) *
            sourceD q) := hprodCount.symm
      _ = primeFactorCountBetween L (sourceU q + sourceV q)
          (2 * sourceVertex q) := by rw [hexact]
      _ = _ :=
        primeFactorCountBetween_two_mul hL hb0.ne'
  omega

/-- Source regularity turns the combinatorial count bridge into the
explicit real-valued budget used in the exponential indicator. -/
theorem source_factorCount_real_le_regularity_add_two
    {L N : ℕ} {A K : ℝ} {q : SourceTriple}
    (hL : 3 ≤ L) (hq : q ∈ sourceCoordinateSet L N A K) :
    ((ArithmeticFunction.cardFactors (sourceU q) +
        ArithmeticFunction.cardFactors (sourceU q + sourceV q) +
        primeFactorCountBetween L (sourceU q + sourceV q)
          (sourceD q) : ℕ) : ℝ) ≤
      A * log
          (log (sourceU q + sourceV q) / log L) +
        K + 2 := by
  have hcount :=
    source_factorCount_le_vertexCount_add_two hL hq
  have hqData := hq
  rw [sourceCoordinateSet, mem_filter] at hqData
  rcases hqData.2 with
    ⟨_hcop, _hv3u, _hscore, _hpair, _hexact, hLsum,
      _hbLower, _hbUpper, _hoddU, _hoddSum, _hoddD,
      _hrough, hregular⟩
  have hreg :=
    hregular (sourceU q + sourceV q) hLsum
  have hcountReal :
      ((ArithmeticFunction.cardFactors (sourceU q) +
          ArithmeticFunction.cardFactors
            (sourceU q + sourceV q) +
          primeFactorCountBetween L (sourceU q + sourceV q)
            (sourceD q) : ℕ) : ℝ) ≤
        ((primeFactorCountBetween L
            (sourceU q + sourceV q) (sourceVertex q) + 2 : ℕ) :
          ℝ) := by
    exact_mod_cast hcount
  push_cast at hcountReal
  push_cast at hreg ⊢
  linarith

/-- Lean-friendly exponential form of the source indicator inequality.
It says that the regularity budget minus the three localized counts is
nonnegative after multiplication by `log 4`. -/
theorem one_le_sourceIndicatorExp
    {L N : ℕ} {A K : ℝ} {q : SourceTriple}
    (hL : 3 ≤ L) (hq : q ∈ sourceCoordinateSet L N A K) :
    (1 : ℝ) ≤
      exp (log 4 *
        (A * log
            (log (sourceU q + sourceV q) / log L) +
          K + 2 -
          (ArithmeticFunction.cardFactors (sourceU q) +
            ArithmeticFunction.cardFactors
              (sourceU q + sourceV q) +
            primeFactorCountBetween L (sourceU q + sourceV q)
              (sourceD q) : ℕ))) := by
  apply one_le_exp
  apply mul_nonneg (log_pos (by norm_num)).le
  exact sub_nonneg.mpr
    (source_factorCount_real_le_regularity_add_two hL hq)

/-- Factored majorant matching the paper's source-indicator weight,
with `K+2` reflecting the deliberately coarse parity loss. -/
noncomputable def sourceIndicatorMajorant
    (L : ℕ) (A K : ℝ) (q : SourceTriple) : ℝ :=
  exp (log 4 *
      (A * log
          (log (sourceU q + sourceV q) / log L) +
        K + 2)) *
    (1 / 4 : ℝ) ^
      ArithmeticFunction.cardFactors (sourceU q) *
    (1 / 4 : ℝ) ^
      ArithmeticFunction.cardFactors (sourceU q + sourceV q) *
    (1 / 4 : ℝ) ^
      primeFactorCountBetween L (sourceU q + sourceV q)
        (sourceD q)

/-- Regular source coordinates have indicator at most the explicit
factored majorant. -/
theorem one_le_sourceIndicatorMajorant
    {L N : ℕ} {A K : ℝ} {q : SourceTriple}
    (hL : 3 ≤ L) (hq : q ∈ sourceCoordinateSet L N A K) :
    (1 : ℝ) ≤ sourceIndicatorMajorant L A K q := by
  let countU := ArithmeticFunction.cardFactors (sourceU q)
  let countSum :=
    ArithmeticFunction.cardFactors (sourceU q + sourceV q)
  let countD :=
    primeFactorCountBetween L (sourceU q + sourceV q) (sourceD q)
  let budget : ℝ :=
    A * log (log (sourceU q + sourceV q) / log L) + K + 2
  have hpow (n : ℕ) :
      (1 / 4 : ℝ) ^ n = exp (-(n : ℝ) * log 4) := by
    have hbase : exp (-log 4) = (1 / 4 : ℝ) := by
      rw [exp_neg, exp_log (by norm_num : (0 : ℝ) < 4)]
      norm_num
    calc
      (1 / 4 : ℝ) ^ n = exp (-log 4) ^ n := by rw [hbase]
      _ = exp ((n : ℝ) * (-log 4)) :=
        (exp_nat_mul (-log 4) n).symm
      _ = exp (-(n : ℝ) * log 4) := by ring_nf
  have hmajor :
      sourceIndicatorMajorant L A K q =
        exp (log 4 * (budget -
          ((countU + countSum + countD : ℕ) : ℝ))) := by
    unfold sourceIndicatorMajorant
    dsimp [budget, countU, countSum, countD]
    rw [hpow, hpow, hpow, ← exp_add, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  rw [hmajor]
  exact one_le_sourceIndicatorExp hL hq

end

end Erdos327.Analytic
