import ErdosProblems.Erdos964.ScalarCoefficientBounds
import ErdosProblems.Erdos964.ScalarAffineS1

/-!
# A logarithmic envelope for the scalar first-sum error

The lcm root multiplicity is bounded by the product of the two divisor
multiplicities. A squarefree divisor mean then sums the coefficient bound.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

theorem three_pow_lcm_primeFactors_le (d e : ℕ) (hd : d ≠ 0) (he : e ≠ 0) :
    (3 : ℝ) ^ (Nat.lcm d e).primeFactors.card ≤
      (3 : ℝ) ^ d.primeFactors.card * (3 : ℝ) ^ e.primeFactors.card := by
  have hsubset : (Nat.lcm d e).primeFactors ⊆ d.primeFactors ∪ e.primeFactors := by
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    rcases hpprime.dvd_lcm.mp (Nat.dvd_of_mem_primeFactors hp) with hpd | hpe
    · exact Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hpprime, hpd, hd⟩)
    · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hpprime, hpe, he⟩)
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num)
    ((Finset.card_le_card hsubset).trans (Finset.card_union_le _ _))

theorem sum_three_pow_squarefree_le (R : ℕ) (D : Finset ℕ)
    (hD : ∀ d ∈ D, d ∈ Finset.Icc 1 R ∧ Squarefree d) :
    (∑ d ∈ D, (3 : ℝ) ^ d.primeFactors.card) ≤
      (R : ℝ) * (1 + Real.log R) ^ 18 := by
  have hsum : (∑ d ∈ D, (3 : ℝ) ^ d.primeFactors.card / Nat.totient d) ≤
      squarefreeTauFirstMean 3 R := by
    calc
      _ = ∑ d ∈ D, if Squarefree d then ((3 ^ ω d : ℕ) : ℝ) / Nat.totient d else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [if_pos (hD d hd).2, Nat.cast_pow, omega_eq_card_primeFactors]
        norm_num
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => (hD d hd).1)
        intro d _ _
        split_ifs <;> positivity
  calc
    _ ≤ ∑ d ∈ D, (R : ℝ) * ((3 : ℝ) ^ d.primeFactors.card / Nat.totient d) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdR := Finset.mem_Icc.mp (hD d hd).1
      have hphi : (0 : ℝ) < Nat.totient d := by
        exact_mod_cast Nat.totient_pos.mpr hdR.1
      have hphiR : (Nat.totient d : ℝ) ≤ R := by
        exact_mod_cast (Nat.totient_le d).trans hdR.2
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hphi).mpr
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) d.primeFactors.card]
    _ = (R : ℝ) * ∑ d ∈ D, (3 : ℝ) ^ d.primeFactors.card / Nat.totient d :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (R : ℝ) * squarefreeTauFirstMean 3 R :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg R)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg R)
      simpa using (squarefreeTauFirstMean_le_one_add_log (k := 3) (Q := R) (by norm_num))

theorem scalar_coefficient_root_mass_le (P R : ℕ) (hP : Squarefree P)
    (w : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hw : ∀ d, |w d| ≤ L)
    (hcut : ∀ d, R ≤ d → w d = 0) :
    (∑ d ∈ P.divisors, (3 : ℝ) ^ d.primeFactors.card * |w d|) ≤
      L * (R : ℝ) * (1 + Real.log R) ^ 18 := by
  classical
  let D := P.divisors.filter (fun d => d < R)
  have hD : ∀ d ∈ D, d ∈ Finset.Icc 1 R ∧ Squarefree d := by
    intro d hd
    obtain ⟨hd, hdR⟩ := Finset.mem_filter.mp hd
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, hdR.le⟩,
      hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)⟩
  have hrestrict : (∑ d ∈ P.divisors, (3 : ℝ) ^ d.primeFactors.card * |w d|) =
      ∑ d ∈ D, (3 : ℝ) ^ d.primeFactors.card * |w d| := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hdR : d < R
    · rw [if_pos hdR]
    · rw [if_neg hdR, hcut d (Nat.le_of_not_gt hdR), abs_zero, mul_zero]
  rw [hrestrict]
  calc
    _ ≤ ∑ d ∈ D, L * (3 : ℝ) ^ d.primeFactors.card := by
      apply Finset.sum_le_sum
      intro d _
      simpa only [mul_comm L] using
        mul_le_mul_of_nonneg_left (hw d) (by positivity : (0 : ℝ) ≤ 3 ^ d.primeFactors.card)
    _ = L * ∑ d ∈ D, (3 : ℝ) ^ d.primeFactors.card := (Finset.mul_sum _ _ _).symm
    _ ≤ L * ((R : ℝ) * (1 + Real.log R) ^ 18) :=
      mul_le_mul_of_nonneg_left (sum_three_pow_squarefree_le R D hD) hL
    _ = _ := by ring

theorem scalar_coefficient_pair_error_le (P R : ℕ) (hP : Squarefree P)
    (w : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hw : ∀ d, |w d| ≤ L)
    (hcut : ∀ d, R ≤ d → w d = 0) :
    (∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
      (3 : ℝ) ^ (Nat.lcm d e).primeFactors.card * |w d * w e|) ≤
      (L * (R : ℝ) * (1 + Real.log R) ^ 18) ^ 2 := by
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        ((3 : ℝ) ^ d.primeFactors.card * |w d|) *
          ((3 : ℝ) ^ e.primeFactors.card * |w e|) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      have hroot := three_pow_lcm_primeFactors_le d e
        (Nat.pos_of_mem_divisors hd).ne' (Nat.pos_of_mem_divisors he).ne'
      have h := mul_le_mul_of_nonneg_right hroot (abs_nonneg (w d * w e))
      rw [abs_mul] at h
      rw [abs_mul]
      convert h using 1
      ring
    _ = (∑ d ∈ P.divisors, (3 : ℝ) ^ d.primeFactors.card * |w d|) ^ 2 := by
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ ≤ _ := pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (abs_nonneg _)))
      (scalar_coefficient_root_mass_le P R hP w L hL hw hcut) 2

theorem normalized_scalarAffineS1_error_le_log (A B : Fin 3 → ℕ) (v N R : ℕ)
    (s : BoundingSieve) (hsM : s.prodPrimes.Coprime (affineNormalizationModulus A B))
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (y : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hy : ∀ u, |y u| ≤ C)
    (hcut : ∀ u, R ≤ u → y u = 0) :
    |(∑ n ∈ Finset.Ico N (2 * N),
        scalarAffineWeight (fun i => A i * affineNormalizationModulus A B)
          (fun i => A i * v + B i) s.prodPrimes (scalarSelbergCoefficient s y) n) -
        (N : ℝ) * ∑ r ∈ s.prodPrimes.divisors, dimensionSelbergWeight 3 r * (y r) ^ 2| ≤
      C ^ 2 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ 684 := by
  apply (normalized_scalarAffineS1_diagonal_error A B v N s hsM hs y).trans
  have h := scalar_coefficient_pair_error_le s.prodPrimes R s.prodPrimes_squarefree
    (scalarSelbergCoefficient s y) (C * (1 + Real.log R) ^ 324) (by positivity)
    (abs_scalarSelbergCoefficient_le_log s hs R y C hC hy hcut)
    (fun d hd => scalarSelbergCoefficient_eq_zero_of_radius s y R d hcut hd)
  have hid : (C * (1 + Real.log R) ^ 324 * (R : ℝ) * (1 + Real.log R) ^ 18) ^ 2 =
      C ^ 2 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ 684 := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    calc
      _ = C ^ 2 * (R : ℝ) ^ 2 *
          ((1 + Real.log R) ^ (324 * 2) * (1 + Real.log R) ^ (18 * 2)) := by
        simp only [mul_assoc, mul_left_comm, mul_comm]
      _ = _ := by rw [← pow_add]
  rwa [hid] at h

end Erdos964
