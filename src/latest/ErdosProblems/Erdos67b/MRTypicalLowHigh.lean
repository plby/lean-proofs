import ErdosProblems.Erdos67b.MRHighPrimeInvariance
import ErdosProblems.Erdos67b.MRTypicalCofactorEuler
import ErdosProblems.Erdos67b.MRGSA10PositiveLine

/-!
# One low factor for the actual typical cofactor

The unique low/high prime factorization reconstructs the typical
denominator-weighted coefficient in one convolution. The low coefficient
need not be multiplicative.
-/

open scoped BigOperators Classical LSeries.notation
open Finset

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrConvolution_primeBand_of_low_high_identity
    (g f : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P]
    (hproduct : ∀ d e, PrimeSupported P d → PrimeSupported (fun p ↦ ¬ P p) e →
      g d * f e = g (d * e)) {n : ℕ} (hn : 0 < n) :
    LSeries.convolution (primeBandCoefficient g P)
      (primeBandCoefficient f (fun p ↦ ¬ P p)) n = g n := by
  rw [LSeries.convolution_def]
  dsimp only
  let d := primeBandPart P n
  let e := primeBandPart (fun p ↦ ¬ P p) n
  have hde : d * e = n := primeBandPart_mul_compl P hn.ne'
  have hd : PrimeSupported P d := primeSupported_primeBandPart P n
  have he : PrimeSupported (fun p ↦ ¬ P p) e := primeSupported_primeBandPart _ n
  have hmem : (d, e) ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨hde, hn.ne'⟩
  rw [Finset.sum_eq_single (d, e)]
  · rw [primeBandCoefficient_eq_of_supported g P hd,
      primeBandCoefficient_eq_of_supported f (fun p ↦ ¬ P p) he,
      hproduct d e hd he, hde]
  · intro q hq hqne
    by_cases hqP : PrimeSupported P q.1
    · by_cases hqC : PrimeSupported (fun p ↦ ¬ P p) q.2
      · have hu := eq_primeBandParts_of_mul_eq P (Nat.mem_divisorsAntidiagonal.mp hq).1 hqP hqC
        exact (hqne (Prod.ext hu.1 hu.2)).elim
      · simp [primeBandCoefficient, hqC]
    · simp [primeBandCoefficient, hqP]
  · exact fun hnot ↦ (hnot hmem).elim

theorem mrPrimeBlockHit_mul_high_iff
    {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {y d e : ℕ}
    (hsmall : ∀ p ∈ B, p ≤ y) (he : PrimeSupported (fun p ↦ ¬ p ≤ y) e) :
    mrPrimeBlockHit B (d * e) ↔ mrPrimeBlockHit B d := by
  constructor
  · rintro ⟨p, hp, hpd⟩
    rcases (hB p hp).dvd_mul.mp hpd with hpd | hpe
    · exact ⟨p, hp, hpd⟩
    · have hpf : p ∈ e.primeFactors := Nat.mem_primeFactors.mpr ⟨hB p hp, hpe, he.1⟩
      exact (he.2 p hpf (hsmall p hp)).elim
  · rintro ⟨p, hp, hpd⟩
    exact ⟨p, hp, dvd_mul_of_dvd_left hpd e⟩

def mrIndexedTypicalCofactorCoefficient {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  mrIndexedTypicalCoefficient J B f n / (mrCommonDenominator A n : ℂ)

theorem mrIndexedTypicalCofactorCoefficient_mul_high {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) {y d e : ℕ}
    (hAsmall : ∀ p ∈ A, p ≤ y) (hBsmall : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    (hd : PrimeSupported (fun p ↦ p ≤ y) d) (he : PrimeSupported (fun p ↦ ¬ p ≤ y) e) :
    mrIndexedTypicalCofactorCoefficient A J B f d * f e =
      mrIndexedTypicalCofactorCoefficient A J B f (d * e) := by
  have hcop := coprime_of_complementary_primeSupported (fun p ↦ p ≤ y) hd he
  have hcount : primeDivisorCount A (d * e) = primeDivisorCount A d := by
    rw [primeDivisorCount_mul_of_coprime hA hcop, mrPrimeDivisorCount_high_eq_zero hA hAsmall he, add_zero]
  have hdenom : mrCommonDenominator A (d * e) = mrCommonDenominator A d := by
    simp only [mrCommonDenominator, hcount]
  have htyp : (∀ j ∈ J, mrPrimeBlockHit (B j) (d * e)) ↔ ∀ j ∈ J, mrPrimeBlockHit (B j) d := by
    constructor
    · intro h j hj
      exact (mrPrimeBlockHit_mul_high_iff (hB j hj) (hBsmall j hj) he).mp (h j hj)
    · intro h j hj
      exact (mrPrimeBlockHit_mul_high_iff (hB j hj) (hBsmall j hj) he).mpr (h j hj)
  unfold mrIndexedTypicalCofactorCoefficient mrIndexedTypicalCoefficient
  rw [hdenom]
  split_ifs with ht ht' ht''
  · rw [hmul.2 d e (Nat.pos_of_ne_zero hd.1) (Nat.pos_of_ne_zero he.1) hcop]
    ring
  · exact (ht' (htyp.mpr ht)).elim
  · exact (ht (htyp.mp ht'')).elim
  · simp

theorem mrTypicalCofactor_low_high_convolution {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (y : ℕ)
    (hAsmall : ∀ p ∈ A, p ≤ y) (hBsmall : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    {n : ℕ} (hn : 0 < n) :
    LSeries.convolution (gsA9Low (mrIndexedTypicalCofactorCoefficient A J B f) y)
      (gsA9High f y) n = mrIndexedTypicalCofactorCoefficient A J B f n := by
  exact mrConvolution_primeBand_of_low_high_identity _ _ (fun p ↦ p ≤ y)
    (fun d e hd he ↦ mrIndexedTypicalCofactorCoefficient_mul_high A hA J B hB hmul
      hAsmall hBsmall hd he) hn

def mrTypicalCofactorLowArithmetic {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ) (f : ℕ → ℂ) (y : ℕ) :
    ArithmeticFunction ℂ :=
  toArithmeticFunction (gsA9Low (mrIndexedTypicalCofactorCoefficient A J B f) y)

theorem mrTypicalCofactorLowArithmetic_mul_high {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (y : ℕ)
    (hAsmall : ∀ p ∈ A, p ≤ y) (hBsmall : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y) :
    mrTypicalCofactorLowArithmetic A J B f y * gsA9HighArithmetic f y =
      toArithmeticFunction (mrIndexedTypicalCofactorCoefficient A J B f) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  have hconv := mrTypicalCofactor_low_high_convolution A hA J B hB hmul y hAsmall hBsmall
    (Nat.pos_of_ne_zero hn)
  have hwrap := congrFun (LSeries.convolution_congr
    (f := mrTypicalCofactorLowArithmetic A J B f y)
    (f' := gsA9Low (mrIndexedTypicalCofactorCoefficient A J B f) y)
    (g := gsA9HighArithmetic f y) (g' := gsA9High f y)
    (fun {m} hm ↦ by simp [mrTypicalCofactorLowArithmetic, toArithmeticFunction, hm])
    (fun {m} hm ↦ gsA9HighArithmetic_apply_of_ne_zero f y hm)) n
  have heq := congrFun (ArithmeticFunction.coe_mul
    (mrTypicalCofactorLowArithmetic A J B f y) (gsA9HighArithmetic f y)) n
  calc
    _ = LSeries.convolution (mrTypicalCofactorLowArithmetic A J B f y) (gsA9HighArithmetic f y) n := heq.symm
    _ = LSeries.convolution (gsA9Low (mrIndexedTypicalCofactorCoefficient A J B f) y) (gsA9High f y) n := hwrap
    _ = mrIndexedTypicalCofactorCoefficient A J B f n := hconv
    _ = _ := by simp [toArithmeticFunction, hn]

/-- Finite prime support, not multiplicativity, is what gives positive-line
absolute convergence for a bounded low coefficient. -/
theorem mrPrimeBandCoefficient_LSeriesSummable_of_bounded_pos_re
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] (y : ℕ)
    (hP : ∀ p, P p → p ≤ y) {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (primeBandCoefficient f P) s := by
  have honeMul : IsMultiplicativeOnPositiveNat (fun _ : ℕ ↦ (1 : ℂ)) :=
    ⟨rfl, fun _ _ _ _ _ ↦ by simp⟩
  have hmajor := primeBandCoefficient_LSeriesSummable_of_pos_re honeMul
    (fun _ _ ↦ by simp) P y hP hs
  apply Summable.of_norm
  apply hmajor.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  by_cases hn : PrimeSupported P n
  · simpa only [primeBandCoefficient, if_pos hn, norm_one] using
      hbound n (Nat.pos_of_ne_zero hn.1)
  · simp [primeBandCoefficient, hn]

theorem mrIndexedTypicalCofactorCoefficient_norm_le_one {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    ‖mrIndexedTypicalCofactorCoefficient A J B f n‖ ≤ 1 := by
  exact mrCommonCofactorCoefficient_norm_le_one A
    (fun m hm ↦ mrIndexedTypicalCoefficient_norm_le J B hbound hm) hn

theorem mrTypicalCofactorLowArithmetic_LSeriesSummable_of_pos_re {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (mrTypicalCofactorLowArithmetic A J B f y) s := by
  have hbase := mrPrimeBandCoefficient_LSeriesSummable_of_bounded_pos_re
    (fun n hn ↦ mrIndexedTypicalCofactorCoefficient_norm_le_one A J B hbound hn)
    (fun p ↦ p ≤ y) y (fun _ hp ↦ hp) hs
  exact (LSeriesSummable_congr s
    (f := mrTypicalCofactorLowArithmetic A J B f y)
    (g := gsA9Low (mrIndexedTypicalCofactorCoefficient A J B f) y)
    (fun {n} hn ↦ by
      simp [mrTypicalCofactorLowArithmetic, toArithmeticFunction, hn])).2 hbase

/-- The actual typical cofactor series factors with the common original
high series on the absolutely convergent half-plane. -/
theorem mrLSeries_typicalCofactorLow_mul_high {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (y : ℕ)
    (hAsmall : ∀ p ∈ A, p ≤ y) (hBsmall : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (mrTypicalCofactorLowArithmetic A J B f y) s *
      LSeries (gsA9HighArithmetic f y) s =
      mrCofactorLSeries A (mrIndexedTypicalCoefficient J B f) s := by
  have hlo := mrTypicalCofactorLowArithmetic_LSeriesSummable_of_pos_re A J B hbound y
    (zero_lt_one.trans hs)
  have hhi : LSeriesSummable (gsA9HighArithmetic f y) s :=
    (LSeriesSummable_congr s (fun {n} hn ↦ gsA9HighArithmetic_apply_of_ne_zero f y hn)).2
      (primeBandCoefficient_LSeriesSummable hbound _ hs)
  rw [← LSeries_convolution' hlo hhi, ArithmeticFunction.coe_mul,
    mrTypicalCofactorLowArithmetic_mul_high A hA J B hB hmul y hAsmall hBsmall]
  apply LSeries_congr
  intro n hn
  simp [toArithmeticFunction, hn, mrIndexedTypicalCofactorCoefficient]

end

end Erdos67b
