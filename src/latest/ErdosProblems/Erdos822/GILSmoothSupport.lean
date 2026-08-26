/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.MediumRangeGcdMass
import ErdosProblems.Erdos822.SmoothCollisionSupport

/-! # Exact smooth-class support for the actual GIL family -/

namespace Erdos822

theorem b1Cutoff_le_nat (N : ℕ) : b1Cutoff N ≤ N :=
  (nthRoot_le_self_of_pos (by norm_num : 0 < 4)).trans
    ((Nat.log_le_self 2 (Nat.log 2 N)).trans (Nat.log_le_self 2 N))

theorem oddRawCofactors_ge_nat {N m : ℕ} (hN : 2 ≤ N) (hm : m ∈ oddRawCofactors N) : N ≤ m := by
  have hpow : N ^ 1 ≤ N ^ 25 := Nat.pow_le_pow_right (by omega) (by omega)
  have hNN : N ≤ N ^ 25 := by simpa using hpow
  exact hNN.trans (oddRawCofactors_ge_pow_twenty_five hN hm)

theorem gilCofactors_mem_smoothPreserving {N S m : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hm : m ∈ gilCofactors N S C) :
    m ∈ smoothPreservingOddCofactors N (b1Cutoff N) :=
  mem_smoothPreservingOddCofactors_iff.mpr
    ⟨gilCofactors_subset_oddRaw N S C hm, gilCofactors_preserving hN hm⟩

theorem gil_smoothPart_eq_of_supported {N S m m' : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hm : m ∈ gilCofactors N S C) (hm' : m' ∈ gilCofactors N S C)
    (hsupport : (outerCollisionPairs (N ^ 60) m m').Nonempty) :
    smoothPart m (b1Cutoff N) = smoothPart m' (b1Cutoff N) := by
  have hmraw := gilCofactors_subset_oddRaw N S C hm
  have hmraw' := gilCofactors_subset_oddRaw N S C hm'
  have hym : b1Cutoff N ≤ m := (b1Cutoff_le_nat N).trans (oddRawCofactors_ge_nat hN hmraw)
  have hym' : b1Cutoff N ≤ m' := (b1Cutoff_le_nat N).trans (oddRawCofactors_ge_nat hN hmraw')
  exact smoothPart_eq_of_nonempty_outerCollisionPairs_smoothPreserving
    (gilCofactors_mem_smoothPreserving hN hm) (gilCofactors_mem_smoothPreserving hN hm')
    (fun p hp ↦ oddOuterPrime_large_of_mem hN hmraw hp)
    (fun p hp ↦ oddOuterPrime_large_of_mem hN hmraw' hp)
    (fun p hp ↦ hym.trans_lt (oddOuterPrime_large_of_mem hN hmraw hp))
    (fun p hp ↦ hym'.trans_lt (oddOuterPrime_large_of_mem hN hmraw' hp)) hsupport

theorem gil_gcd_eq_anchor_smooth_mul_rough {N S m m' : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hm : m ∈ gilCofactors N S C) (hm' : m' ∈ gilCofactors N S C)
    (hsupport : (outerCollisionPairs (N ^ 60) m m').Nonempty) :
    shiftedCoefficientGcd m m' = smoothPart m' (b1Cutoff N) *
      roughPart (shiftedCoefficientGcd m m') (b1Cutoff N) := by
  have hmraw := gilCofactors_subset_oddRaw N S C hm
  have hmraw' := gilCofactors_subset_oddRaw N S C hm'
  apply shiftedCoefficientGcd_eq_smooth_mul_rough_of_class (oddRawCofactors_pos hmraw) (oddRawCofactors_pos hmraw')
  · exact (smoothPart_shiftedTotient_eq (oddRawCofactors_pos hmraw) (gilCofactors_preserving hN hm)).trans
      (gil_smoothPart_eq_of_supported hN hm hm' hsupport)
  · exact smoothPart_shiftedTotient_eq (oddRawCofactors_pos hmraw') (gilCofactors_preserving hN hm')

theorem smoothPart_oddTriple_eq_small {N k r q : ℕ} (hN : 2 ≤ N)
    (ht : (k, r, q) ∈ oddCofactorTriples N) :
    smoothPart (k * r * q) (b1Cutoff N) = smoothPart k (b1Cutoff N) := by
  have hd := mem_oddCofactorTriples_iff.mp ht
  have hk := oddSmallFactors_pos hd.1
  have hr := (mem_middlePrimes_iff.mp hd.2.1).2.2
  have hq := (mem_largePrimes_iff.mp hd.2.2).2.2
  have hN4 : N < N ^ 4 := by
    simpa using Nat.pow_lt_pow_right (by omega : 1 < N) (by omega : 1 < 4)
  have hyr : b1Cutoff N < r :=
    (b1Cutoff_le_nat N).trans_lt (hN4.trans_le (mem_middlePrimes_iff.mp hd.2.1).1)
  have hrq : r < q := (Nat.le_mul_of_pos_left r hk).trans_lt (oddCofactorTriples_separated hN ht).2.2
  rw [smoothPart_mul_prime_eq_of_lt (mul_pos hk hr.pos) hq (hyr.trans hrq),
    smoothPart_mul_prime_eq_of_lt hk hr hyr]

theorem gil_smallFactor_smoothPart_eq_anchor_of_supported {N S k r q m' : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (ht : (k, r, q) ∈ oddCofactorTriples N)
    (hm : k * r * q ∈ gilCofactors N S C) (hm' : m' ∈ gilCofactors N S C)
    (hsupport : (outerCollisionPairs (N ^ 60) (k * r * q) m').Nonempty) :
    smoothPart k (b1Cutoff N) = smoothPart m' (b1Cutoff N) := by
  rw [← smoothPart_oddTriple_eq_small hN ht]
  exact gil_smoothPart_eq_of_supported hN hm hm' hsupport

#print axioms gil_gcd_eq_anchor_smooth_mul_rough

end Erdos822
