/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.GILPartBounds
import ErdosProblems.Erdos822.ResidueAboveAnchor

/-! # Summing the large-range gcd weight around one inner-factor anchor -/

namespace Erdos822

open scoped BigOperators Classical

noncomputable def sameInnerSupportedPrimes (N S : ℕ) (C : ℝ) (l q' : ℕ) : Finset ℕ :=
  (largePrimes N).filter fun q ↦ q' < q ∧ l * q ∈ gilCofactors N S C ∧
    (outerCollisionPairs (N ^ 60) (l * q) (l * q')).Nonempty

theorem sameInner_supported_modEq_rough_gcd {N S l q q' : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hm : l * q ∈ gilCofactors N S C) (hm' : l * q' ∈ gilCofactors N S C)
    (hne : (outerCollisionPairs (N ^ 60) (l * q) (l * q')).Nonempty) :
    q ≡ q' [MOD roughPart (shiftedCoefficientGcd (l * q) (l * q')) (b1Cutoff N)] := by
  let g := shiftedCoefficientGcd (l * q) (l * q')
  let d := roughPart g (b1Cutoff N)
  have hmraw := gilCofactors_subset_oddRaw N S C hm
  have hmraw' := gilCofactors_subset_oddRaw N S C hm'
  have hdist := shiftedCoefficientGcd_dvd_dist_of_nonempty
    (oddRawCofactors_pos hmraw) (oddRawCofactors_pos hmraw')
    (fun p hp ↦ oddOuterPrime_large_of_mem hN hmraw hp)
    (fun p hp ↦ oddOuterPrime_large_of_mem hN hmraw' hp) hne
  have hmod : l * q ≡ l * q' [MOD d] :=
    mul_modEq_of_dvd_dist ((roughPart_dvd g (b1Cutoff N)).trans hdist) rfl
  have hcop : Nat.Coprime d l :=
    commonDivisor_coprime_leftFactor_of_largeGcdFree (gilCofactors_largeGcdFree hm)
      (dvd_mul_right l q) (roughPart_dvd g (b1Cutoff N))
      (fun p hp hpdvd ↦ prime_dvd_roughPart_gt hp hpdvd)
  exact Nat.ModEq.cancel_left_of_coprime hcop hmod

theorem sameInner_gcd_weight_le_divisor_sum {N S l q q' : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N)
    (hm : l * q ∈ gilCofactors N S C) (hm' : l * q' ∈ gilCofactors N S C)
    (hne : (outerCollisionPairs (N ^ 60) (l * q) (l * q')).Nonempty) :
    (shiftedCoefficientGcd (l * q) (l * q') : ℝ) / q ≤
      (N : ℝ) * ∑ d ∈ (roughPart (shiftedTotient (l * q')) (b1Cutoff N)).divisors,
        if q ≡ q' [MOD d] then (d : ℝ) / q else 0 := by
  let g := shiftedCoefficientGcd (l * q) (l * q')
  let d := roughPart g (b1Cutoff N)
  have hmpos := oddRawCofactors_pos (gilCofactors_subset_oddRaw N S C hm')
  have hsne : shiftedTotient (l * q') ≠ 0 := by dsimp [shiftedTotient]; omega
  have hgdiv : g ∣ shiftedTotient (l * q') := Nat.gcd_dvd_right _ _
  have hdmem : d ∈ (roughPart (shiftedTotient (l * q')) (b1Cutoff N)).divisors :=
    Nat.mem_divisors.mpr ⟨roughPart_dvd_roughPart_of_dvd hsne hgdiv, roughPart_ne_zero _ _⟩
  have hg : (g : ℝ) ≤ (N : ℝ) * d := by
    exact_mod_cast gilCofactors_divisor_le_mul_rough hN hy hm' hgdiv
  have hmod := sameInner_supported_modEq_rough_gcd hN hm hm' hne
  change q ≡ q' [MOD d] at hmod
  have hterm : (d : ℝ) / q ≤
      ∑ e ∈ (roughPart (shiftedTotient (l * q')) (b1Cutoff N)).divisors,
        if q ≡ q' [MOD e] then (e : ℝ) / q else 0 := by
    have h := Finset.single_le_sum
      (s := (roughPart (shiftedTotient (l * q')) (b1Cutoff N)).divisors)
      (f := fun e ↦ if q ≡ q' [MOD e] then (e : ℝ) / q else 0)
      (fun e he ↦ by split_ifs <;> positivity) hdmem
    simpa only [if_pos hmod] using h
  calc
    _ ≤ (N : ℝ) * d / q := div_le_div_of_nonneg_right hg (by positivity)
    _ = (N : ℝ) * ((d : ℝ) / q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hterm (by positivity)

theorem sum_sameInnerSupportedPrimes_gcd_weight_le {N S l q' : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N) (hl : 0 < l)
    (hm' : l * q' ∈ gilCofactors N S C) :
    (∑ q ∈ sameInnerSupportedPrimes N S C l q',
      (shiftedCoefficientGcd (l * q) (l * q') : ℝ) / (l * q : ℕ)) ≤
        (23 * N * (harmonic N : ℝ) *
          (roughPart (shiftedTotient (l * q')) (b1Cutoff N)).divisors.card) / l := by
  let R := roughPart (shiftedTotient (l * q')) (b1Cutoff N)
  have hfiber (d : ℕ) (hd : d ∈ R.divisors) :
      (∑ q ∈ sameInnerSupportedPrimes N S C l q',
        if q ≡ q' [MOD d] then (d : ℝ) / q else 0) ≤ 23 * (harmonic N : ℝ) := by
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hsub : (sameInnerSupportedPrimes N S C l q').filter (fun q ↦ q ≡ q' [MOD d]) ⊆
        (largePrimes N).filter (fun q ↦ q' < q ∧ q ≡ q' [MOD d]) := by
      intro q hq
      obtain ⟨hq, hmod⟩ := Finset.mem_filter.mp hq
      have hdata := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hdata.1, hdata.2.1, hmod⟩
    have hmass := (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun q : ℕ ↦ (1 : ℝ) / q) (fun q hq hnot ↦ by positivity)).trans
        (sum_inv_largePrimes_above_anchor_modEq_le (by omega) hdpos)
    calc
      _ = (d : ℝ) * ∑ q ∈ (sameInnerSupportedPrimes N S C l q').filter
          (fun q ↦ q ≡ q' [MOD d]), (1 : ℝ) / q := by
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro q hq
        split_ifs <;> ring
      _ ≤ (d : ℝ) * (23 * (harmonic N : ℝ) / d) := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = 23 * (harmonic N : ℝ) := by
        have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
        field_simp
  calc
    _ = (1 : ℝ) / l * ∑ q ∈ sameInnerSupportedPrimes N S C l q',
        (shiftedCoefficientGcd (l * q) (l * q') : ℝ) / q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      push_cast
      ring
    _ ≤ (1 : ℝ) / l * ∑ q ∈ sameInnerSupportedPrimes N S C l q',
        (N : ℝ) * ∑ d ∈ R.divisors, if q ≡ q' [MOD d] then (d : ℝ) / q else 0 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro q hq
      have hdata := (Finset.mem_filter.mp hq).2
      exact sameInner_gcd_weight_le_divisor_sum hN hy hdata.2.1 hm' hdata.2.2
    _ = ((N : ℝ) / l) * ∑ d ∈ R.divisors,
        ∑ q ∈ sameInnerSupportedPrimes N S C l q',
          if q ≡ q' [MOD d] then (d : ℝ) / q else 0 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      ring
    _ ≤ ((N : ℝ) / l) * ∑ _d ∈ R.divisors, 23 * (harmonic N : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfiber) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      dsimp [R]
      ring

#print axioms sum_sameInnerSupportedPrimes_gcd_weight_le

end Erdos822
