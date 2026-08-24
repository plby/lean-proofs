import ErdosProblems.Erdos587.LowFrequency

/-!
# Summation over gcd and dyadic blocks

These elementary finite-cover and geometric-mass estimates make the block
assembly cost a harmonic divisor sum, rather than the number of divisors.
-/

open scoped BigOperators

namespace Erdos587

lemma sum_le_sum_family_of_cover {α ι : Type*} [DecidableEq α]
    (S : Finset α) (I : Finset ι) (F : ι → Finset α) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hcover : ∀ x ∈ S, ∃ i ∈ I, x ∈ F i) :
    (∑ x ∈ S, w x) ≤ ∑ i ∈ I, ∑ x ∈ F i, w x := by
  classical
  calc
    _ ≤ ∑ x ∈ S, ∑ i ∈ I, if x ∈ F i then w x else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨i, hi, hxi⟩ := hcover x hx
      have h := Finset.single_le_sum (s := I) (f := fun i => if x ∈ F i then w x else 0)
        (fun i hi => by
          split_ifs
          · exact hw x
          · exact le_rfl) hi
      simpa only [if_pos hxi] using h
    _ = ∑ i ∈ I, ∑ x ∈ S, if x ∈ F i then w x else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · intro x hx hnot
        exact hw x

def dyadicBlockIndices (n : ℕ) : Finset ℕ :=
  if n = 0 then ∅ else Finset.range (n.log2 + 1)

lemma sum_two_pow_add_one (k : ℕ) : (∑ i ∈ Finset.range k, (2 : ℕ) ^ i) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

lemma two_pow_log2_le {n : ℕ} (hn : 0 < n) : 2 ^ n.log2 ≤ n :=
  (Nat.le_log2 hn.ne').mp le_rfl

lemma lt_two_pow_log2_succ {n : ℕ} (hn : 0 < n) : n < 2 ^ (n.log2 + 1) := by
  by_contra hnot
  have h := (Nat.le_log2 hn.ne').mpr (show 2 ^ (n.log2 + 1) ≤ n by omega)
  omega

lemma exists_dyadic_block {r n : ℕ} (hr : 0 < r) (hrn : r ≤ n) :
    ∃ j ∈ dyadicBlockIndices n, 2 ^ j ≤ r ∧ r < 2 * 2 ^ j ∧ 2 ^ j ≤ n := by
  have hn : 0 < n := hr.trans_le hrn
  have hlow := two_pow_log2_le hr
  have hhigh := lt_two_pow_log2_succ hr
  have hlog : r.log2 ≤ n.log2 := (Nat.le_log2 hn.ne').mpr (hlow.trans hrn)
  refine ⟨r.log2, ?_, hlow, ?_, hlow.trans hrn⟩
  · simp only [dyadicBlockIndices, if_neg hn.ne', Finset.mem_range]
    omega
  · simpa only [pow_succ, mul_comm] using hhigh

lemma sum_dyadic_block_lengths_le (n : ℕ) :
    (∑ j ∈ dyadicBlockIndices n, (2 : ℕ) ^ j) ≤ 2 * n := by
  by_cases hn : n = 0
  · simp [hn, dyadicBlockIndices]
  rw [dyadicBlockIndices, if_neg hn]
  have hsum := sum_two_pow_add_one (n.log2 + 1)
  have hpow := two_pow_log2_le (Nat.pos_of_ne_zero hn)
  rw [pow_succ] at hsum
  omega

lemma pow_le_of_mem_dyadicBlockIndices {j n : ℕ} (hj : j ∈ dyadicBlockIndices n) : 2 ^ j ≤ n := by
  by_cases hn : n = 0
  · simp [hn, dyadicBlockIndices] at hj
  rw [dyadicBlockIndices, if_neg hn, Finset.mem_range] at hj
  exact (Nat.le_log2 hn).mp (by omega)

lemma sum_dyadic_block_lengths_real_le (n : ℕ) :
    (∑ j ∈ dyadicBlockIndices n, (2 : ℝ) ^ j) ≤ 2 * n := by
  exact_mod_cast sum_dyadic_block_lengths_le n

lemma sum_divisors_inv_le_one_add_log {u : ℕ} (hu : 0 < u) :
    (∑ d ∈ u.divisors, 1 / (d : ℝ)) ≤ 1 + Real.log u := by
  apply le_trans _ (sum_Icc_inv_natCast_le_one_add_log u)
  simp only [one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      Nat.le_of_dvd hu (Nat.mem_divisors.mp hd).1⟩
  · intro d hd hnot
    positivity

/-- The total dyadic mass over gcd classes has only a logarithmic loss. -/
lemma sum_gcd_dyadic_block_mass_le {u : ℕ} (hu : 0 < u) (M : ℕ) :
    (∑ d ∈ u.divisors, ∑ j ∈ dyadicBlockIndices (M / d), (2 : ℝ) ^ j) ≤
      2 * M * (1 + Real.log u) := by
  calc
    _ ≤ ∑ d ∈ u.divisors, 2 * ((M / d : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun d hd => sum_dyadic_block_lengths_real_le (M / d))
    _ ≤ ∑ d ∈ u.divisors, 2 * (M : ℝ) * (1 / (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdR : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
      have hdiv : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / d := by
        apply (le_div_iff₀ hdR).mpr
        exact_mod_cast Nat.div_mul_le_self M d
      calc
        _ ≤ 2 * ((M : ℝ) / d) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = _ := by ring
    _ = 2 * (M : ℝ) * ∑ d ∈ u.divisors, 1 / (d : ℝ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_divisors_inv_le_one_add_log hu) (by positivity)

/-- Bezout's coefficient gives a canonical integer modular inverse. -/
lemma gcdA_inverse_congruence {a q : ℕ} (h : a.Coprime q) :
    (q : ℤ) ∣ (a : ℤ) * Nat.gcdA a q - 1 := by
  have hb := Nat.gcd_eq_gcd_ab a q
  rw [h.gcd_eq_one, Nat.cast_one] at hb
  refine ⟨-Nat.gcdB a q, ?_⟩
  linarith

end Erdos587
