/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.MediumPairMass

/-! # Charging medium supported gcds to rough-divisor fibers -/

namespace Erdos822

open scoped BigOperators Classical

noncomputable def mediumRoughDivisors (N m' : ℕ) : Finset ℕ :=
  (roughPart (shiftedTotient m') (b1Cutoff N)).divisors.filter
    (fun d ↦ N ^ 2 < d ∧ d ≤ N ^ 20)

noncomputable def mediumGcdAnchorTerm (N m m' : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
      N ^ 3 < shiftedCoefficientGcd m m' ∧ shiftedCoefficientGcd m m' ≤ N ^ 20 then
    (shiftedCoefficientGcd m m' : ℝ) / m
  else 0

theorem mediumGcdAnchorTerm_le_roughDivisor_sum {N S m m' : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N) (hm' : m' ∈ gilCofactors N S C) :
    mediumGcdAnchorTerm N m m' ≤
      ∑ d ∈ mediumRoughDivisors N m', (N : ℝ) * d *
        if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧ d ∣ shiftedCoefficientGcd m m' then
          (1 : ℝ) / m else 0 := by
  unfold mediumGcdAnchorTerm
  split_ifs with h
  · let g := shiftedCoefficientGcd m m'
    let d := roughPart g (b1Cutoff N)
    have hmpos := oddRawCofactors_pos (gilCofactors_subset_oddRaw N S C hm')
    have hsne : shiftedTotient m' ≠ 0 := by dsimp [shiftedTotient]; omega
    have hgdiv : g ∣ shiftedTotient m' := Nat.gcd_dvd_right _ _
    have hg : g ≤ N * d := gilCofactors_divisor_le_mul_rough hN hy hm' hgdiv
    have hdlo : N ^ 2 < d := by
      by_contra hnot
      have hle : N * d ≤ N ^ 3 := by
        calc
          _ ≤ N * N ^ 2 := Nat.mul_le_mul_left _ (by omega)
          _ = _ := by ring
      exact (not_lt_of_ge (hg.trans hle)) h.2.1
    have hdhi : d ≤ N ^ 20 :=
      (Nat.le_of_dvd (by dsimp [g]; omega) (roughPart_dvd g (b1Cutoff N))).trans h.2.2
    have hdmem : d ∈ mediumRoughDivisors N m' :=
      Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨roughPart_dvd_roughPart_of_dvd hsne hgdiv, roughPart_ne_zero _ _⟩, hdlo, hdhi⟩
    have hcond : (outerCollisionPairs (N ^ 60) m m').Nonempty ∧ d ∣ shiftedCoefficientGcd m m' :=
      ⟨h.1, roughPart_dvd g (b1Cutoff N)⟩
    calc
      _ ≤ (N : ℝ) * d * ((1 : ℝ) / m) := by
        have hgR : (g : ℝ) ≤ (N : ℝ) * d := by exact_mod_cast hg
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hgR (by positivity : (0 : ℝ) ≤ (m : ℝ)⁻¹)
      _ ≤ _ := by
        have hsingle := Finset.single_le_sum
          (s := mediumRoughDivisors N m')
          (f := fun e ↦ (N : ℝ) * e *
            if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧ e ∣ shiftedCoefficientGcd m m' then
              (1 : ℝ) / m else 0)
          (fun e he ↦ by split_ifs <;> positivity) hdmem
        simpa only [if_pos hcond] using hsingle
  · exact Finset.sum_nonneg fun d hd ↦ by split_ifs <;> positivity

theorem sum_mediumGcdAnchorTerm_le {N S m' : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N) (hyN : b1Cutoff N < N ^ 21)
    (hm' : m' ∈ gilCofactors N S C) :
    (∑ m ∈ gilCofactors N S C, mediumGcdAnchorTerm N m m') ≤
      4 * (harmonic N : ℝ) ^ 3 / N *
        (5 : ℝ) ^ (roughPart (shiftedTotient m') (b1Cutoff N)).primeFactors.card := by
  let R := roughPart (shiftedTotient m') (b1Cutoff N)
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj ↦ by positivity
  have hfiber (d : ℕ) (hd : d ∈ mediumRoughDivisors N m') :
      (N : ℝ) * d * (∑ m ∈ gilCofactors N S C,
        if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧ d ∣ shiftedCoefficientGcd m m' then
          (1 : ℝ) / m else 0) ≤
      4 * (harmonic N : ℝ) ^ 3 / N * (4 : ℝ) ^ d.primeFactors.card := by
    have hddata := Finset.mem_filter.mp hd
    have hrough := roughPart_eq_self_of_dvd_roughPart (Nat.mem_divisors.mp hddata.1).1
    have hpair := medium_roughPairMass_mul_le hN hddata.2.1 hddata.2.2 hrough
    have hmass := sum_inv_supported_commonDivisor_le_roughPairMass (h := d)
      hN rfl hyN (gilCofactors_subset_squarefreeLargeGcdFree N S C) hm'
    calc
      _ ≤ (N : ℝ) * d * ((harmonic N : ℝ) * roughQuadraticPairMassBound N (b1Cutoff N) d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hmass.trans (mul_le_mul_of_nonneg_right (sum_inv_oddSmallFactors_le_harmonic N)
          (roughQuadraticPairMassBound_nonneg _ _ _))
      _ = (harmonic N : ℝ) * ((N : ℝ) * d * roughQuadraticPairMassBound N (b1Cutoff N) d) := by ring
      _ ≤ (harmonic N : ℝ) * (4 * (4 : ℝ) ^ d.primeFactors.card * (harmonic N : ℝ) ^ 2 / N) :=
        mul_le_mul_of_nonneg_left hpair hH
      _ = _ := by ring
  have hsum : (∑ d ∈ mediumRoughDivisors N m', (4 : ℝ) ^ d.primeFactors.card) ≤
      (5 : ℝ) ^ R.primeFactors.card := by
    calc
      _ ≤ ∑ d ∈ R.divisors, (4 : ℝ) ^ d.primeFactors.card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun d hd hnot ↦ by positivity)
      _ = _ := by
        exact_mod_cast sum_divisors_four_pow_primeFactorsCard_eq_five_pow
          (gilCofactors_roughDivisor_squarefree hm' (dvd_refl _))
  calc
    _ ≤ ∑ m ∈ gilCofactors N S C, ∑ d ∈ mediumRoughDivisors N m', (N : ℝ) * d *
        if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧ d ∣ shiftedCoefficientGcd m m' then
          (1 : ℝ) / m else 0 :=
      Finset.sum_le_sum fun m hm ↦ mediumGcdAnchorTerm_le_roughDivisor_sum hN hy hm'
    _ = ∑ d ∈ mediumRoughDivisors N m', (N : ℝ) * d *
        (∑ m ∈ gilCofactors N S C,
          if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧ d ∣ shiftedCoefficientGcd m m' then
            (1 : ℝ) / m else 0) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ d ∈ mediumRoughDivisors N m', 4 * (harmonic N : ℝ) ^ 3 / N * (4 : ℝ) ^ d.primeFactors.card :=
      Finset.sum_le_sum hfiber
    _ = (4 * (harmonic N : ℝ) ^ 3 / N) * ∑ d ∈ mediumRoughDivisors N m', (4 : ℝ) ^ d.primeFactors.card :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

#print axioms sum_mediumGcdAnchorTerm_le

end Erdos822
