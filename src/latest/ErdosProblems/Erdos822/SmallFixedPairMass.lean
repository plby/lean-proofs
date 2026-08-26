/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SmallQuadraticMass
import ErdosProblems.Erdos822.FixedCommonDivisorFiber

/-! # Sharp uncharged mass of a fixed small common-divisor fiber -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem exists_eventually_small_fixedPair_mass_bound (C : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (B : Finset ℕ) (k m' h cutoff : ℕ),
        B ⊆ squarefreeLargeGcdFreeOddCofactors N cutoff → m' ∈ B → k ∈ oddSmallFactors N →
        0 < h → h ≤ N ^ 3 → primeDivisorReciprocalMass h ≤ C → roughPart h cutoff = h →
        cutoff < N ^ 21 →
        (∑ rq ∈ fixedCommonDivisorPrimePairs B N (N ^ 60) k m' h,
          (1 : ℝ) / (rq.1 * rq.2 : ℕ)) ≤ A * (4 : ℝ) ^ h.primeFactors.card / (h : ℝ) ^ 2 := by
  obtain ⟨A, hA, hbound⟩ := exists_eventually_small_quadraticPairClasses_bound C
  refine ⟨A ^ 2, by positivity, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 2] with N hbound hN
  intro B k m' h cutoff hB hm' hk hh hhN hmass hrough hcutoff
  by_cases hne : (fixedCommonDivisorPrimePairs B N (N ^ 60) k m' h).Nonempty
  · obtain ⟨r₀, q₀, hbase, hcover⟩ := exists_quadraticClasses_cover_fixedCommonDivisorPrimePairs
      hN rfl hcutoff hk hB hm' hne
    rw [hrough] at hcover
    have hsupport : ∀ p : ℕ, p.Prime → p ∣ h → cutoff < p := by
      intro p hp hpd
      apply prime_dvd_roughPart_gt hp
      rwa [hrough]
    have hbaseData := mem_fixedCommonDivisorPrimePairs_iff.mp hbase
    have hsq : Squarefree h := commonDivisor_squarefree_of_squarefreeLargeGcdFree
      (hB hbaseData.2.2.1) hbaseData.2.2.2.2 hsupport
    calc
      _ ≤ ∑ rq ∈ (quadraticMiddlePrimeClasses N h (r₀ * q₀) (r₀ + q₀)).product
          (quadraticLargePrimeClasses N h (r₀ * q₀) (r₀ + q₀) cutoff),
          (1 : ℝ) / (rq.1 * rq.2 : ℕ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun rq hrq hnot ↦ by positivity)
      _ = ∑ r ∈ quadraticMiddlePrimeClasses N h (r₀ * q₀) (r₀ + q₀),
          ∑ q ∈ quadraticLargePrimeClasses N h (r₀ * q₀) (r₀ + q₀) cutoff,
            (1 : ℝ) / (r * q : ℕ) := by
        change (∑ rq ∈ (quadraticMiddlePrimeClasses N h (r₀ * q₀) (r₀ + q₀)) ×ˢ
          (quadraticLargePrimeClasses N h (r₀ * q₀) (r₀ + q₀) cutoff),
          (1 : ℝ) / (rq.1 * rq.2 : ℕ)) = _
        rw [Finset.sum_product]
      _ ≤ _ := hbound h (r₀ * q₀) (r₀ + q₀) cutoff hsq hhN hmass
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]
    positivity

#print axioms exists_eventually_small_fixedPair_mass_bound

end Erdos822
