import ErdosProblems.Erdos67b.MRLowMaskInclusion
import ErdosProblems.Erdos67b.MRGSA9SmallPrimeRestore

/-!
# Fixed small-prime restoration for an indexed typical low coefficient

All small primes survive every typicality mask when the blocks contain
only primes at least 23. The restored factor is common to the finite mask
sum, including for a scaled coefficient. It may still depend on the scale.
-/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrLSeries_low_primeBand_eq_smallPrime_mul_delete
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] {y : ℕ} (hy : 23 ≤ y)
    (hsmallP : ∀ p ∈ gsA9SmallPrimeFinset, P p) {s : ℂ} (hs : 0 < s.re) :
    LSeries (gsA9Low (primeBandCoefficient f P) y) s =
      gsA9SmallPrimeEulerProduct f s *
        LSeries (gsA9Low (primeBandCoefficient (gsDeletePrimeBand f gsA9SmallPrime) P) y) s := by
  rw [mrLSeries_low_primeBand_eq_finiteEulerProduct hmul hbound P y hs,
    mrLSeries_low_primeBand_eq_finiteEulerProduct
      (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime)
      (fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn) P y hs]
  exact prod_filter_eq_smallPrimeEulerProduct_mul_delete hmul P hy hsmallP s

theorem mrLSeries_low_indexedTypical_eq_smallPrime_mul_delete {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    (hlarge : ∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y : ℕ} (hy : 23 ≤ y)
    {s : ℂ} (hs : 0 < s.re) :
    LSeries (gsA9Low (mrIndexedTypicalCoefficient J B f) y) s =
      gsA9SmallPrimeEulerProduct f s *
        LSeries (gsA9Low (mrIndexedTypicalCoefficient J B (gsDeletePrimeBand f gsA9SmallPrime)) y) s := by
  classical
  rw [mrLSeries_low_indexedTypical_eq_mask_sum J B hB hbound y hs,
    mrLSeries_low_indexedTypical_eq_mask_sum J B hB
      (fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn) y hs,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hsmall : ∀ p ∈ gsA9SmallPrimeFinset, p ∉ S.biUnion B := by
    intro p hp hpmem
    have hp23 : p < 23 := Finset.mem_range.1 (Finset.mem_filter.1 hp).1
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.1 hpmem
    exact (not_lt_of_ge (hlarge j (Finset.mem_powerset.1 hS hj) p hpj)) hp23
  rw [mrLSeries_low_primeBand_eq_smallPrime_mul_delete hmul hbound
    (fun p ↦ p ∉ S.biUnion B) hy hsmall hs]
  ring

theorem mrPrimeScaled_deletePrimeBand (A : Finset ℕ) (f : ℕ → ℂ) (u : ℝ)
    (P : ℕ → Prop) [DecidablePred P] :
    gsDeletePrimeBand (mrPrimeScaledCoefficient A f u) P =
      mrPrimeScaledCoefficient A (gsDeletePrimeBand f P) u := by
  unfold gsDeletePrimeBand
  exact (mrPrimeScaled_primeBandCoefficient A f (fun p ↦ ¬ P p) u).symm

theorem mrLSeries_low_scaledTypical_eq_smallPrime_mul_delete {ι : Type*} [DecidableEq ι]
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    (hlarge : ∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y : ℕ} (hy : 23 ≤ y)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    LSeries (gsA9Low (mrIndexedTypicalCoefficient J B (mrPrimeScaledCoefficient A f u)) y) s =
      gsA9SmallPrimeEulerProduct (mrPrimeScaledCoefficient A f u) s *
        LSeries (gsA9Low (mrIndexedTypicalCoefficient J B
          (mrPrimeScaledCoefficient A (gsDeletePrimeBand f gsA9SmallPrime) u)) y) s := by
  rw [mrLSeries_low_indexedTypical_eq_smallPrime_mul_delete J B hB hlarge
    (mrPrimeScaledCoefficient_isMultiplicative hA hmul u)
    (fun n hn ↦ norm_mrPrimeScaledCoefficient_le_one hbound hu0 hu1 hn) hy hs,
    mrPrimeScaled_deletePrimeBand]

end

end Erdos67b
