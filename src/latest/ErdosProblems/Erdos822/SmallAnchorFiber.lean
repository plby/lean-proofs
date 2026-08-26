/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SmallFixedPairSingular
import ErdosProblems.Erdos822.GILSmoothSupport

/-! # Reassembling small-range fibers while retaining their smooth class -/

namespace Erdos822

open scoped BigOperators Classical

noncomputable def smallSupportedDivisorCofactors (N S : ℕ) (C : ℝ) (m' h : ℕ) : Finset ℕ :=
  (gilCofactors N S C).filter (fun m ↦ m ≠ m' ∧
    (outerCollisionPairs (N ^ 60) m m').Nonempty ∧ h ∣ shiftedCoefficientGcd m m')

theorem sum_smallOffDiagonalPrimePairs_eq (N S : ℕ) (C : ℝ) (k m' h : ℕ)
    (f : ℕ → ℕ → ℝ) :
    (∑ rq ∈ smallOffDiagonalPrimePairs N S C k m' h, f rq.1 rq.2) =
      ∑ r ∈ middlePrimes N, ∑ q ∈ largePrimes N,
        if k * r * q ∈ gilCofactors N S C ∧ k * r * q ≠ m' ∧
            (outerCollisionPairs (N ^ 60) (k * r * q) m').Nonempty ∧
            h ∣ shiftedCoefficientGcd (k * r * q) m' then f r q else 0 := by
  unfold smallOffDiagonalPrimePairs fixedCommonDivisorPrimePairs
  rw [Finset.sum_filter, Finset.sum_filter]
  change (∑ rq ∈ middlePrimes N ×ˢ largePrimes N,
    if k * rq.1 * rq.2 ∈ gilCofactors N S C ∧
        (outerCollisionPairs (N ^ 60) (k * rq.1 * rq.2) m').Nonempty ∧
        h ∣ shiftedCoefficientGcd (k * rq.1 * rq.2) m' then
      (if k * rq.1 * rq.2 ≠ m' then f rq.1 rq.2 else 0) else 0) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hm : k * r * q ∈ gilCofactors N S C <;>
    by_cases hne : k * r * q ≠ m' <;>
    by_cases hs : (outerCollisionPairs (N ^ 60) (k * r * q) m').Nonempty <;>
    by_cases hd : h ∣ shiftedCoefficientGcd (k * r * q) m' <;> simp [hm, hne, hs, hd]

theorem sum_smallSupportedDivisorCofactors_eq_fixedPairs {N S : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (m' h U : ℕ) :
    (∑ m ∈ smallSupportedDivisorCofactors N S C m' h,
      ((1 : ℝ) / m) * Erdos851.singularFactor (reducedTotientDet m m') 2 U) =
      ∑ k ∈ oddSmallFactors N, ((1 : ℝ) / k) *
        ∑ rq ∈ smallOffDiagonalPrimePairs N S C k m' h,
          ((1 : ℝ) / (rq.1 * rq.2 : ℕ)) *
            Erdos851.singularFactor (reducedTotientDet (k * rq.1 * rq.2) m') 2 U := by
  unfold smallSupportedDivisorCofactors
  rw [Finset.sum_filter, sum_subset_oddRawCofactors_eq_triple_if hN (gilCofactors_subset_oddRaw N S C)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sum_smallOffDiagonalPrimePairs_eq N S C k m' h
    (fun r q ↦ ((1 : ℝ) / (r * q : ℕ)) *
      Erdos851.singularFactor (reducedTotientDet (k * r * q) m') 2 U)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hm : k * r * q ∈ gilCofactors N S C <;>
    by_cases hne : k * r * q ≠ m' <;>
    by_cases hs : (outerCollisionPairs (N ^ 60) (k * r * q) m').Nonempty <;>
    by_cases hd : h ∣ shiftedCoefficientGcd (k * r * q) m' <;>
    simp [hm, hne, hs, hd] <;> ring

theorem smallOffDiagonalPrimePairs_empty_of_smoothPart_ne {N S k m' h : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hk : k ∈ oddSmallFactors N) (hm' : m' ∈ gilCofactors N S C)
    (hclass : smoothPart k (b1Cutoff N) ≠ smoothPart m' (b1Cutoff N)) :
    smallOffDiagonalPrimePairs N S C k m' h = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨⟨r, q⟩, hrq⟩
  have hd := mem_fixedCommonDivisorPrimePairs_iff.mp (Finset.mem_filter.mp hrq).1
  exact hclass (gil_smallFactor_smoothPart_eq_anchor_of_supported hN
    (mem_oddCofactorTriples_iff.mpr ⟨hk, hd.1, hd.2.1⟩) hd.2.2.1 hm' hd.2.2.2.1)

#print axioms sum_smallSupportedDivisorCofactors_eq_fixedPairs

end Erdos822
