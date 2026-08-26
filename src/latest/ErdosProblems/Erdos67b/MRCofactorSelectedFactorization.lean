import ErdosProblems.Erdos67b.MRTypicalLowHigh
import ErdosProblems.Erdos67b.MRLowMaskInclusion

/-!
# Splitting off the selected-prime factor in the actual cofactor

The selected primes are disjoint from all typicality blocks. Entire prime
powers are retained, the denominator stays on the selected factor, and
the typicality condition stays on the complementary factor.
-/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrPrimeDivisorCount_avoiding_eq_zero
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) {n : ℕ}
    (hn : PrimeSupported (fun p ↦ p ∉ A) n) : primeDivisorCount A n = 0 := by
  have hempty : primeDivisorSet A n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpA, hpn⟩ := mem_primeDivisorSet.mp hp
    exact hn.2 p (Nat.mem_primeFactors.mpr ⟨hA p hpA, hpn, hn.1⟩) hpA
  simp only [primeDivisorCount, hempty, Finset.card_empty]

theorem mrPrimeBlockHit_selected_mul_iff
    {A B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (hdisj : Disjoint A B)
    {d e : ℕ} (hd : PrimeSupported (fun p ↦ p ∈ A) d) :
    mrPrimeBlockHit B (d * e) ↔ mrPrimeBlockHit B e := by
  constructor
  · rintro ⟨p, hp, hpd⟩
    rcases (hB p hp).dvd_mul.mp hpd with hpd | hpe
    · have hpA := hd.2 p (Nat.mem_primeFactors.mpr ⟨hB p hp, hpd, hd.1⟩)
      exact (Finset.disjoint_left.mp hdisj hpA hp).elim
    · exact ⟨p, hp, hpe⟩
  · rintro ⟨p, hp, hpe⟩
    exact ⟨p, hp, dvd_mul_of_dvd_right hpe d⟩

theorem mrTypicalCofactor_selected_mul_identity {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    (hdisj : ∀ j ∈ J, Disjoint A (B j))
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) {d e : ℕ}
    (hd : PrimeSupported (fun p ↦ p ∈ A) d)
    (he : PrimeSupported (fun p ↦ p ∉ A) e) :
    (f d / (mrCommonDenominator A d : ℂ)) * mrIndexedTypicalCoefficient J B f e =
      mrIndexedTypicalCofactorCoefficient A J B f (d * e) := by
  have hcop := coprime_of_complementary_primeSupported (fun p ↦ p ∈ A) hd he
  have hdenom : mrCommonDenominator A (d * e) = mrCommonDenominator A d := by
    simp only [mrCommonDenominator, primeDivisorCount_mul_of_coprime hA hcop,
      mrPrimeDivisorCount_avoiding_eq_zero A hA he, add_zero]
  have htyp : (∀ j ∈ J, mrPrimeBlockHit (B j) (d * e)) ↔
      ∀ j ∈ J, mrPrimeBlockHit (B j) e := by
    constructor
    · intro h j hj
      exact (mrPrimeBlockHit_selected_mul_iff (hB j hj) (hdisj j hj) hd).mp (h j hj)
    · intro h j hj
      exact (mrPrimeBlockHit_selected_mul_iff (hB j hj) (hdisj j hj) hd).mpr (h j hj)
  unfold mrIndexedTypicalCofactorCoefficient mrIndexedTypicalCoefficient
  rw [hdenom]
  split_ifs with ht ht' ht''
  · rw [hmul.2 d e (Nat.pos_of_ne_zero hd.1) (Nat.pos_of_ne_zero he.1) hcop]
    ring
  · exact (ht' (htyp.mpr ht)).elim
  · exact (ht (htyp.mp ht'')).elim
  · simp

def mrSelectedCofactorFactor (A : Finset ℕ) (f : ℕ → ℂ) : ℕ → ℂ :=
  primeBandCoefficient (fun n ↦ f n / (mrCommonDenominator A n : ℂ)) (fun p ↦ p ∈ A)

theorem mrTypicalCofactor_selected_convolution {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    (hdisj : ∀ j ∈ J, Disjoint A (B j))
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) {n : ℕ} (hn : 0 < n) :
    LSeries.convolution (mrSelectedCofactorFactor A f)
      (mrIndexedTypicalCoefficient J B (gsDeletePrimeBand f (fun p ↦ p ∈ A))) n =
        mrIndexedTypicalCofactorCoefficient A J B f n := by
  classical
  unfold gsDeletePrimeBand
  rw [← mrPrimeBand_indexedTypical_comm, LSeries.convolution_def]
  dsimp only
  let d := primeBandPart (fun p ↦ p ∈ A) n
  let e := primeBandPart (fun p ↦ p ∉ A) n
  have hde : d * e = n := primeBandPart_mul_compl (fun p ↦ p ∈ A) hn.ne'
  have hd : PrimeSupported (fun p ↦ p ∈ A) d := primeSupported_primeBandPart _ _
  have he : PrimeSupported (fun p ↦ p ∉ A) e := primeSupported_primeBandPart _ _
  have hmem : (d, e) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨hde, hn.ne'⟩
  rw [Finset.sum_eq_single (d, e)]
  · rw [mrSelectedCofactorFactor, primeBandCoefficient_eq_of_supported _ _ hd,
      primeBandCoefficient_eq_of_supported _ _ he,
      mrTypicalCofactor_selected_mul_identity A hA J B hB hdisj hmul hd he, hde]
  · intro q hq hqne
    by_cases hqA : PrimeSupported (fun p ↦ p ∈ A) q.1
    · by_cases hqC : PrimeSupported (fun p ↦ p ∉ A) q.2
      · have hu := eq_primeBandParts_of_mul_eq (fun p ↦ p ∈ A)
          (Nat.mem_divisorsAntidiagonal.mp hq).1 hqA hqC
        exact (hqne (Prod.ext hu.1 hu.2)).elim
      · simp [primeBandCoefficient, hqC]
    · simp [mrSelectedCofactorFactor, primeBandCoefficient, hqA]
  · exact fun hnot ↦ (hnot hmem).elim

theorem mrSelectedCofactorFactor_eq_zero_of_not_supported
    (A : Finset ℕ) (f : ℕ → ℂ) {n : ℕ}
    (hn : ¬ PrimeSupported (fun p ↦ p ∈ A) n) : mrSelectedCofactorFactor A f n = 0 := by
  simp [mrSelectedCofactorFactor, primeBandCoefficient, hn]

theorem norm_mrSelectedCofactorFactor_le_one
    (A : Finset ℕ) {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (n : ℕ) : ‖mrSelectedCofactorFactor A f n‖ ≤ 1 := by
  classical
  by_cases hn : PrimeSupported (fun p ↦ p ∈ A) n
  · rw [mrSelectedCofactorFactor, primeBandCoefficient_eq_of_supported _ _ hn,
      norm_div, Complex.norm_natCast]
    have hdenom : (1 : ℝ) ≤ mrCommonDenominator A n := by
      exact_mod_cast (show 1 ≤ mrCommonDenominator A n by
        unfold mrCommonDenominator; omega)
    exact (div_le_self (norm_nonneg _) hdenom).trans (hbound n (Nat.pos_of_ne_zero hn.1))
  · rw [mrSelectedCofactorFactor_eq_zero_of_not_supported A f hn, norm_zero]
    norm_num

end

end Erdos67b
