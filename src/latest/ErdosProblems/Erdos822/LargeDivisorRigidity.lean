/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.InnerRatioRigidity
import ErdosProblems.Erdos822.GILDivisorBounds

/-! # A large supported common divisor forces equal inner factors -/

namespace Erdos822

theorem inner_cross_modEq_of_shifted_divisibility {l l' q q' h : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hql : ¬ q ∣ l) (hq'l' : ¬ q' ∣ l')
    (hdiv : h ∣ shiftedTotient (l * q)) (hdiv' : h ∣ shiftedTotient (l' * q'))
    (hprod : l * q ≡ l' * q' [MOD h]) :
    l * Nat.totient l * shiftedTotient l' ≡
      l' * Nat.totient l' * shiftedTotient l [MOD h] := by
  have hmod : shiftedTotient l * q ≡ Nat.totient l [MOD h] := by
    rw [← shiftedTotient_mul_prime_add_totient_basic hq hql]
    simpa using hdiv.modEq_zero_nat.add_right (Nat.totient l)
  have hmod' : shiftedTotient l' * q' ≡ Nat.totient l' [MOD h] := by
    rw [← shiftedTotient_mul_prime_add_totient_basic hq' hq'l']
    simpa using hdiv'.modEq_zero_nat.add_right (Nat.totient l')
  have h1 := (ZMod.natCast_eq_natCast_iff _ _ h).mpr hmod
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ h).mpr hmod'
  have h3 := (ZMod.natCast_eq_natCast_iff _ _ h).mpr hprod
  apply (ZMod.natCast_eq_natCast_iff _ _ h).mp
  push_cast at h1 h2 h3 ⊢
  linear_combination
    -(l : ZMod h) * (shiftedTotient l' : ZMod h) * h1 +
    (l' : ZMod h) * (shiftedTotient l : ZMod h) * h2 +
    (shiftedTotient l : ZMod h) * (shiftedTotient l' : ZMod h) * h3

theorem inner_cross_lt_of_bounds {N l l' h : ℕ} (hN : 2 ≤ N)
    (hl : l ≤ N ^ 6) (hl' : l' ≤ N ^ 6) (hh : N ^ 20 < h) :
    l * Nat.totient l * shiftedTotient l' < h := by
  have hφ := (Nat.totient_le l).trans hl
  have hshift := (shiftedTotient_le_two_mul l').trans (Nat.mul_le_mul_left 2 hl')
  have hN2 : 2 ≤ N ^ 2 := by nlinarith only [hN]
  calc
    _ ≤ N ^ 6 * N ^ 6 * (2 * N ^ 6) := Nat.mul_le_mul (Nat.mul_le_mul hl hφ) hshift
    _ = 2 * N ^ 18 := by ring
    _ ≤ N ^ 2 * N ^ 18 := Nat.mul_le_mul_right _ hN2
    _ = N ^ 20 := by ring
    _ < h := hh

theorem inner_factors_eq_of_large_supported_gcd
    {N k r q k' r' q' : ℕ} (hN : 2 ≤ N)
    (ht : (k, r, q) ∈ oddCofactorTriples N)
    (ht' : (k', r', q') ∈ oddCofactorTriples N)
    (hne : (outerCollisionPairs (N ^ 60) (k * r * q) (k' * r' * q')).Nonempty)
    (hlarge : N ^ 20 < shiftedCoefficientGcd (k * r * q) (k' * r' * q')) :
    k = k' ∧ r = r' := by
  have hdata := mem_oddCofactorTriples_iff.mp ht
  have hdata' := mem_oddCofactorTriples_iff.mp ht'
  have hsep := oddCofactorTriples_separated hN ht
  have hsep' := oddCofactorTriples_separated hN ht'
  have hr := (mem_middlePrimes_iff.mp hdata.2.1).2.2
  have hr' := (mem_middlePrimes_iff.mp hdata'.2.1).2.2
  have hq := (mem_largePrimes_iff.mp hdata.2.2).2.2
  have hq' := (mem_largePrimes_iff.mp hdata'.2.2).2.2
  have hm : k * r * q ∈ oddRawCofactors N :=
    Finset.mem_image.mpr ⟨(k, r, q), ht, rfl⟩
  have hm' : k' * r' * q' ∈ oddRawCofactors N :=
    Finset.mem_image.mpr ⟨(k', r', q'), ht', rfl⟩
  have hdist := shiftedCoefficientGcd_dvd_dist_of_nonempty
    (oddRawCofactors_pos hm) (oddRawCofactors_pos hm')
    (fun p hp ↦ oddOuterPrime_large_of_mem hN hm hp)
    (fun p hp ↦ oddOuterPrime_large_of_mem hN hm' hp) hne
  have hprod : k * r * q ≡ k' * r' * q' [MOD shiftedCoefficientGcd (k * r * q) (k' * r' * q')] := by
    exact mul_modEq_of_dvd_dist hdist rfl
  have hcross := inner_cross_modEq_of_shifted_divisibility hq hq'
    (Nat.not_dvd_of_pos_of_lt (mul_pos hsep.1 hr.pos) hsep.2.2)
    (Nat.not_dvd_of_pos_of_lt (mul_pos hsep'.1 hr'.pos) hsep'.2.2)
    (Nat.gcd_dvd_left (shiftedTotient (k * r * q)) (shiftedTotient (k' * r' * q')))
    (Nat.gcd_dvd_right (shiftedTotient (k * r * q)) (shiftedTotient (k' * r' * q'))) hprod
  have hl : k * r ≤ N ^ 6 := by
    calc
      _ ≤ N * N ^ 5 := Nat.mul_le_mul (oddSmallFactors_le hdata.1) (mem_middlePrimes_iff.mp hdata.2.1).2.1
      _ = _ := by ring
  have hl' : k' * r' ≤ N ^ 6 := by
    calc
      _ ≤ N * N ^ 5 := Nat.mul_le_mul (oddSmallFactors_le hdata'.1) (mem_middlePrimes_iff.mp hdata'.2.1).2.1
      _ = _ := by ring
  have heq : (k * r * Nat.totient (k * r)) * shiftedTotient (k' * r') =
      (k' * r' * Nat.totient (k' * r')) * shiftedTotient (k * r) := by
    have hleft := inner_cross_lt_of_bounds hN hl hl' hlarge
    have hright := inner_cross_lt_of_bounds hN hl' hl hlarge
    change _ % shiftedCoefficientGcd (k * r * q) (k' * r' * q') =
      _ % shiftedCoefficientGcd (k * r * q) (k' * r' * q') at hcross
    rw [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at hcross
    exact hcross
  exact factors_eq_of_inner_ratio_cross_eq hsep.1 hsep'.1 hr hr' hsep.2.1 hsep'.2.1 heq

#print axioms inner_factors_eq_of_large_supported_gcd

end Erdos822
