/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTResidueModel
import BoundedGaps.BombieriVinogradov.Analytic.PrimePowerCorrectionBound

/-! # Counting exceptional residue primes by the product of differences -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def residueCollisionProduct (N : Finset ℤ) : ℕ :=
  ∏ ab ∈ N.offDiag, (ab.2 - ab.1).natAbs

def residueCollisionPrimes (S : Finset ℕ) (N : Finset ℤ) : Finset ℕ :=
  S.filter fun p => (occupiedResidues p N).card ≠ N.card

theorem residueCollisionProduct_pos (N : Finset ℤ) : 0 < residueCollisionProduct N := by
  apply Finset.prod_pos
  intro ab hab
  have hne := (Finset.mem_offDiag.mp hab).2.2
  exact Int.natAbs_pos.mpr (sub_ne_zero.mpr hne.symm)

theorem prime_dvd_residueCollisionProduct {p : ℕ} (hp : 0 < p) {N : Finset ℤ}
    (hcard : (occupiedResidues p N).card ≠ N.card) : p ∣ residueCollisionProduct N := by
  by_contra hnodvd
  apply hcard
  apply Finset.card_image_of_injOn
  intro a ha b hb heq
  by_contra hne
  have hmod := (integerResidueIndex_eq_iff hp a b).mp heq
  have hdiv : p ∣ (b - a).natAbs := Int.natCast_dvd.mp (Int.modEq_iff_dvd.mp hmod)
  have hab : (a, b) ∈ N.offDiag := Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩
  have hf : (b - a).natAbs ∣ residueCollisionProduct N :=
    Finset.dvd_prod_of_mem (fun ab : ℤ × ℤ => (ab.2 - ab.1).natAbs) hab
  exact hnodvd (hdiv.trans hf)

theorem residueCollisionPrimes_subset_primeFactors {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (N : Finset ℤ) :
    residueCollisionPrimes S N ⊆ (residueCollisionProduct N).primeFactors := by
  intro p hp
  obtain ⟨hpS, hbad⟩ := Finset.mem_filter.mp hp
  have hprime := hS p hpS
  exact Nat.mem_primeFactors.mpr ⟨hprime,
    prime_dvd_residueCollisionProduct hprime.pos hbad, (residueCollisionProduct_pos N).ne'⟩

theorem log_residueCollisionProduct_le {N : Finset ℤ} {H : ℝ}
    (hH : 1 ≤ H) (hN : ∀ n ∈ N, |(n : ℝ)| ≤ H) :
    Real.log (residueCollisionProduct N : ℝ) ≤ (N.card : ℝ) ^ 2 * Real.log (2 * H) := by
  have hHpos : 0 < H := by linarith
  have hlog : 0 ≤ Real.log (2 * H) := Real.log_nonneg (by linarith)
  have hbound (ab : ℤ × ℤ) (hab : ab ∈ N.offDiag) :
      Real.log ((ab.2 - ab.1).natAbs : ℝ) ≤ Real.log (2 * H) := by
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
    have hdpos : 0 < (ab.2 - ab.1).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne.symm)
    apply Real.log_le_log (by exact_mod_cast hdpos)
    have hh := abs_sub (ab.2 : ℝ) (ab.1 : ℝ)
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
    linarith [hN ab.1 ha, hN ab.2 hb]
  have hcard : N.offDiag.card ≤ N.card ^ 2 := by
    rw [Finset.offDiag_card, pow_two]
    exact Nat.sub_le _ _
  calc
    _ = ∑ ab ∈ N.offDiag, Real.log ((ab.2 - ab.1).natAbs : ℝ) := by
      rw [residueCollisionProduct, Nat.cast_prod, Real.log_prod]
      intro ab hab
      have hne := (Finset.mem_offDiag.mp hab).2.2
      exact_mod_cast (Int.natAbs_pos.mpr (sub_ne_zero.mpr hne.symm)).ne'
    _ ≤ ∑ _ab ∈ N.offDiag, Real.log (2 * H) := Finset.sum_le_sum hbound
    _ = (N.offDiag.card : ℝ) * Real.log (2 * H) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlog

theorem residueCollisionPrimes_card_le {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {N : Finset ℤ} {H : ℝ}
    (hH : 1 ≤ H) (hN : ∀ n ∈ N, |(n : ℝ)| ≤ H) :
    ((residueCollisionPrimes S N).card : ℝ) ≤ 2 * (N.card : ℝ) ^ 2 * Real.log (2 * H) := by
  have hcard : ((residueCollisionPrimes S N).card : ℝ) ≤
      ((residueCollisionProduct N).primeFactors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (residueCollisionPrimes_subset_primeFactors hS N)
  have hlog := BoundedGaps.Maynard.card_primeFactors_le_two_mul_log
    (Nat.succ_le_iff.mpr (residueCollisionProduct_pos N))
  have hheight := log_residueCollisionProduct_le hH hN
  linarith

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.prime_dvd_residueCollisionProduct
#print axioms Erdos4b.FGKMT.residueCollisionPrimes_card_le
