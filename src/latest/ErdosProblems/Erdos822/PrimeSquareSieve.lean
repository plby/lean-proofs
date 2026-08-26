/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.TotientPrimeTail

/-! # The one-dimensional beta sieve for a prime-square modulus -/

namespace Erdos822

open scoped BigOperators Classical

theorem slopePrimeLoss_prime_sq_self_eq {p z y : ℕ} :
    slopePrimeLoss 0 (p ^ 2) (p ^ 2) z y = slopePrimeLoss 0 p p z y := by
  unfold slopePrimeLoss
  apply Finset.prod_congr rfl
  intro q hq
  have hqp := (Erdos851.mem_sievePrimes.mp hq).2.2
  have heq : q ∣ p ^ 2 ↔ q ∣ p := ⟨hqp.dvd_of_dvd_pow, fun h ↦ h.trans (dvd_pow_self p (by norm_num))⟩
  simp only [heq]

theorem exists_fixed_depth_duplicatePrimeSquareCandidates_bound :
    ∃ S : ℕ, ∃ D : ℝ, 101 ≤ S ∧ 0 < D ∧
      ∀ p q X y : ℕ, p.Prime → q.Prime → y < q → 2 ≤ y →
        ((twoAffinePrimeCandidates (p ^ 2) q (p ^ 2) q X y).card : ℝ) ≤
          (X : ℝ) * (D / Real.log (y : ℝ)) + ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hpair⟩ := exists_twoAffinePrimeCandidates_slopeAware_pair_bound
  obtain ⟨C, hC, hMertens⟩ := exists_oneShift_localEulerProduct_upper
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt (99 * Real.log A / 4)
  let S := max 101 (T + 100)
  have hS : 101 ≤ S := le_max_left _ _
  have hTS : T ≤ S - 100 := by dsimp [S]; omega
  have hlog : Real.log A ≤ 4 * (S - 100 : ℕ) / 99 := by
    have hTSR : (T : ℝ) ≤ (S - 100 : ℕ) := by exact_mod_cast hTS
    linarith only [hT, hTSR]
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let D : ℝ := (1 + eta) * C * Real.log 2 * Real.exp 3
  have hApos : 0 < A := by linarith only [hA]
  have heta : 0 ≤ eta := by dsimp [eta]; positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨S, D, hS, hD, ?_⟩
  intro p q X y hp hq hyq hy
  have hbound := hpair (p ^ 2) (p ^ 2) q q X 2 y S hq hq hyq hyq
    (by norm_num) (by omega) (by omega) hS hlog
  dsimp only at hbound
  have hdet : affineDetNat (p ^ 2) q (p ^ 2) q = 0 := by simp [affineDetNat]
  rw [hdet, localEulerProduct_pairShift_zero_eq_oneShift, slopePrimeLoss_prime_sq_self_eq] at hbound
  have hV := hMertens 2 y (by norm_num) (by omega)
  have hL := slopePrimeLoss_prime_self_le_exp_three (y := y) hp
  have hL0 : 0 ≤ slopePrimeLoss 0 p p 2 y := by
    unfold slopePrimeLoss
    apply Finset.prod_nonneg
    intro r hr
    split_ifs
    · exact inv_nonneg.mpr (Erdos851.pairShift_localFactor_pos
        (Erdos851.mem_sievePrimes.mp hr).2.2 (Erdos851.mem_sievePrimes.mp hr).1).le
    · norm_num
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hprod := mul_le_mul hV hL hL0 (show 0 ≤ C * (Real.log 2 / Real.log (y : ℝ)) by positivity)
  have hscaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hprod (show 0 ≤ 1 + eta by positivity)) (Nat.cast_nonneg (α := ℝ) X)
  refine hbound.trans ?_
  have heq : (X : ℝ) * ((1 + eta) *
      (C * (Real.log 2 / Real.log (y : ℝ)) * Real.exp 3)) = X * (D / Real.log (y : ℝ)) := by
    dsimp [D]
    ring
  rw [← heq]
  simpa [eta, mul_assoc] using add_le_add_right hscaled (((y ^ S : ℕ) : ℝ) ^ 2)

theorem exists_fixed_depth_primeSquareResidueInterval_bound :
    ∃ S : ℕ, ∃ D : ℝ, 101 ≤ S ∧ 0 < D ∧
      ∀ p a L U y : ℕ, p.Prime → 2 ≤ y →
        ((primeResidueInterval (p ^ 2) a L U y).card : ℝ) ≤
          (((U - L) / (p ^ 2) + 1 : ℕ) : ℝ) * (D / Real.log (y : ℝ)) +
            ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨S, D, hS, hD, hdup⟩ := exists_fixed_depth_duplicatePrimeSquareCandidates_bound
  refine ⟨S, D, hS, hD, ?_⟩
  intro p a L U y hp hy
  by_cases hne : (primeResidueInterval (p ^ 2) a L U y).Nonempty
  · let q := (primeResidueInterval (p ^ 2) a L U y).min' hne
    have hq := mem_primeResidueInterval_iff.mp (Finset.min'_mem _ hne)
    have hcard := card_primeResidueInterval_le_duplicateCandidates_of_nonempty_of_pos
      (pow_pos hp.pos 2) hne
    have hcardR : ((primeResidueInterval (p ^ 2) a L U y).card : ℝ) ≤
        (twoAffinePrimeCandidates (p ^ 2) q (p ^ 2) q ((U - L) / (p ^ 2) + 1) y).card := by
      exact_mod_cast hcard
    exact hcardR.trans (hdup p q _ y hp hq.2.2.1 hq.2.2.2.1 hy)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    positivity

theorem exists_fixed_depth_largePrimeSquareResidue_bound :
    ∃ S : ℕ, ∃ D : ℝ, 101 ≤ S ∧ 0 < D ∧
      ∀ N p a y : ℕ, 2 ≤ N → p.Prime → p ^ 2 ≤ N ^ 21 → 2 ≤ y →
        (∑ q ∈ largePrimeResidueClass N (p ^ 2) a y, (1 : ℝ) / q) ≤
          (2 * (D / Real.log (y : ℝ)) / (p : ℝ) ^ 2 +
            ((y ^ S : ℕ) : ℝ) ^ 2 / (N : ℝ) ^ 21) * (harmonic N : ℝ) := by
  obtain ⟨S, D, hS, hD, hbound⟩ := exists_fixed_depth_primeSquareResidueInterval_bound
  refine ⟨S, D, hS, hD, ?_⟩
  intro N p a y hN hp hpN hy
  have hW : 0 ≤ D / Real.log (y : ℝ) :=
    div_nonneg hD.le (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega)))
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 N, ∑ q ∈ largePrimeResidueBlock N (p ^ 2) a y j, (1 : ℝ) / q :=
      sum_inv_largePrimeResidueClass_le_sum_blocks hN
    _ ≤ ∑ j ∈ Finset.Icc 1 N,
        ((((N ^ 21 / (p ^ 2) + 1 : ℕ) : ℝ) * (D / Real.log (y : ℝ)) +
          ((y ^ S : ℕ) : ℝ) ^ 2) / ((j * N ^ 21 + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hwidth : (j + 1) * N ^ 21 - j * N ^ 21 = N ^ 21 := by
        rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]
      have hcard := hbound p a (j * N ^ 21) ((j + 1) * N ^ 21) y hp hy
      rw [hwidth] at hcard
      refine (sum_inv_primeResidueInterval_le_card_div (p ^ 2) a (j * N ^ 21)
        ((j + 1) * N ^ 21) y).trans ?_
      simpa only [Nat.cast_add, Nat.cast_one] using
        div_le_div_of_nonneg_right hcard (show 0 ≤ ((j * N ^ 21 + 1 : ℕ) : ℝ) by positivity)
    _ ≤ _ := by
      simpa only [Nat.cast_pow] using sum_blockKernel_le_harmonic
        (N := N) (L := N ^ 21) (p := p ^ 2)
        (by positivity) (pow_pos hp.pos 2) hpN hW (sq_nonneg ((y ^ S : ℕ) : ℝ))

#print axioms exists_fixed_depth_largePrimeSquareResidue_bound

end Erdos822
