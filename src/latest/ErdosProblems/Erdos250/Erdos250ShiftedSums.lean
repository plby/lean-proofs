import Mathlib

open scoped BigOperators Topology

namespace ShiftedSums

noncomputable def q : ℝ := 1 / 2

noncomputable def zetaQ1 : ℝ :=
  ∑' m : ℕ, q ^ (m + 1) / (1 - q ^ (m + 1))

noncomputable def zetaQ2sq : ℝ :=
  ∑' m : ℕ, q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2

/-- The convention used by the main Erdős 250 file. -/
noncomputable def zetaQ2 : ℝ :=
  ∑' n : ℕ+, (n : ℝ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))

noncomputable def h1 (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (j - 1), q ^ (m + 1) / (1 - q ^ (m + 1))

noncomputable def h2 (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (j - 1), q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2

lemma q_pos : 0 < q := by norm_num [q]
lemma q_le_one : q ≤ 1 := by norm_num [q]
lemma q_ne_zero : q ≠ 0 := ne_of_gt q_pos

lemma q_pow_succ_le (m : ℕ) : q ^ (m + 1) ≤ q := by
  simpa [pow_succ] using
    mul_le_of_le_one_left (le_of_lt q_pos) (pow_le_one₀ (le_of_lt q_pos) q_le_one)

lemma half_le_one_sub_q_pow_succ (m : ℕ) : (1 / 2 : ℝ) ≤ 1 - q ^ (m + 1) := by
  have := q_pow_succ_le m
  norm_num [q] at this ⊢
  linarith

lemma base1_nonneg (m : ℕ) :
    0 ≤ q ^ (m + 1) / (1 - q ^ (m + 1)) := by
  exact div_nonneg (pow_nonneg (le_of_lt q_pos) _) (by linarith [half_le_one_sub_q_pow_succ m])

lemma base1_le (m : ℕ) :
    q ^ (m + 1) / (1 - q ^ (m + 1)) ≤ 2 * q ^ (m + 1) := by
  have hp : 0 ≤ q ^ (m + 1) := pow_nonneg (le_of_lt q_pos) _
  have hd := half_le_one_sub_q_pow_succ m
  apply (div_le_iff₀ (by linarith : 0 < 1 - q ^ (m + 1))).2
  nlinarith

lemma base2_nonneg (m : ℕ) :
    0 ≤ q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2 := by
  exact div_nonneg (pow_nonneg (le_of_lt q_pos) _) (sq_nonneg _)

lemma base2_le (m : ℕ) :
    q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2 ≤ 4 * q ^ (m + 1) := by
  have hp : 0 ≤ q ^ (m + 1) := pow_nonneg (le_of_lt q_pos) _
  have hd := half_le_one_sub_q_pow_succ m
  have hsq : (1 / 4 : ℝ) ≤ (1 - q ^ (m + 1)) ^ 2 := by nlinarith
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 - q ^ (m + 1)))).2
  nlinarith

lemma summable_base1 :
    Summable (fun m : ℕ => q ^ (m + 1) / (1 - q ^ (m + 1))) := by
  apply Summable.of_nonneg_of_le base1_nonneg base1_le
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
    (summable_geometric_of_norm_lt_one (K := ℝ) (x := q) (by norm_num [q])).mul_left (2 * q)

lemma summable_base2 :
    Summable (fun m : ℕ => q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2) := by
  apply Summable.of_nonneg_of_le base2_nonneg base2_le
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
    (summable_geometric_of_norm_lt_one (K := ℝ) (x := q) (by norm_num [q])).mul_left (4 * q)

lemma tsum_pnat_mul_pow (d : ℕ+) :
    (∑' c : ℕ+, (c : ℝ) * q ^ ((d : ℕ) * (c : ℕ))) =
      q ^ (d : ℕ) / (1 - q ^ (d : ℕ)) ^ 2 := by
  let r : ℝ := q ^ (d : ℕ)
  have hr : ‖r‖ < 1 := by
    dsimp [r]
    simpa [Real.norm_eq_abs, abs_of_pos q_pos] using
      pow_lt_one₀ (le_of_lt q_pos) (by norm_num [q] : q < 1) d.ne_zero
  have hs : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have hpnat := tsum_zero_pnat_eq_tsum_nat hs
  simp only [Nat.cast_zero, zero_mul, zero_add] at hpnat
  calc
    (∑' c : ℕ+, (c : ℝ) * q ^ ((d : ℕ) * (c : ℕ))) =
        ∑' c : ℕ+, (c : ℝ) * r ^ (c : ℕ) := by
          apply tsum_congr
          intro c
          simp [r, pow_mul]
    _ = ∑' n : ℕ, (n : ℝ) * r ^ n := hpnat
    _ = r / (1 - r) ^ 2 := tsum_coe_mul_geometric_of_norm_lt_one hr
    _ = q ^ (d : ℕ) / (1 - q ^ (d : ℕ)) ^ 2 := by rfl

/-- Euler symmetry in the two indices: the square-denominator convention for
`ζ_q(2)` agrees with the convention carrying a factor `n`. -/
lemma zetaQ2sq_eq_zetaQ2 : zetaQ2sq = zetaQ2 := by
  have hq : ‖q‖ < 1 := by norm_num [q]
  calc
    zetaQ2sq = ∑' d : ℕ+, q ^ (d : ℕ) / (1 - q ^ (d : ℕ)) ^ 2 := by
      rw [zetaQ2sq]
      symm
      exact (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => q ^ n / (1 - q ^ n) ^ 2))
    _ = ∑' d : ℕ+, ∑' c : ℕ+,
          (c : ℝ) ^ (1 : ℕ) * q ^ ((d : ℕ) * (c : ℕ)) := by
      apply tsum_congr
      intro d
      simpa using (tsum_pnat_mul_pow d).symm
    _ = ∑' e : ℕ+, (ArithmeticFunction.sigma 1 e : ℝ) * q ^ (e : ℕ) :=
      tsum_prod_pow_eq_tsum_sigma 1 hq
    _ = zetaQ2 := by
      rw [zetaQ2]
      symm
      simpa using tsum_pow_div_one_sub_eq_tsum_sigma hq 1

lemma shifted_one (j : ℕ) (hj : 1 ≤ j) :
    (∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell))) =
      (zetaQ1 - h1 j) / q ^ j := by
  let f : ℕ → ℝ := fun m => q ^ (m + 1) / (1 - q ^ (m + 1))
  have htail := summable_base1.sum_add_tsum_nat_add (j - 1)
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have hpoint : ∀ ell : ℕ,
      f (ell + (j - 1)) = q ^ j * (q ^ ell / (1 - q ^ (j + ell))) := by
    intro ell
    simp only [f]
    rw [show ell + (j - 1) + 1 = ell + j by omega]
    rw [show j + ell = ell + j by omega, pow_add]
    ring
  have hqpow : q ^ j ≠ 0 := pow_ne_zero _ q_ne_zero
  rw [show (∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell))) =
      (∑' ell : ℕ, f (ell + (j - 1))) / q ^ j by
        rw [show (∑' ell : ℕ, f (ell + (j - 1))) =
            q ^ j * ∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell)) by
          simp_rw [hpoint]
          exact tsum_mul_left]
        field_simp]
  have htail' : (∑' i : ℕ, f (i + (j - 1))) = zetaQ1 - h1 j := by
    dsimp [f, zetaQ1, h1]
    linarith
  rw [htail']

lemma shifted_two (j : ℕ) (hj : 1 ≤ j) :
    (∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell)) ^ 2) =
      (zetaQ2sq - h2 j) / q ^ j := by
  let f : ℕ → ℝ := fun m => q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2
  have htail := summable_base2.sum_add_tsum_nat_add (j - 1)
  have hpoint : ∀ ell : ℕ,
      f (ell + (j - 1)) = q ^ j * (q ^ ell / (1 - q ^ (j + ell)) ^ 2) := by
    intro ell
    simp only [f]
    rw [show ell + (j - 1) + 1 = ell + j by omega]
    rw [show j + ell = ell + j by omega, pow_add]
    ring
  have hqpow : q ^ j ≠ 0 := pow_ne_zero _ q_ne_zero
  rw [show (∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell)) ^ 2) =
      (∑' ell : ℕ, f (ell + (j - 1))) / q ^ j by
        rw [show (∑' ell : ℕ, f (ell + (j - 1))) =
            q ^ j * ∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell)) ^ 2 by
          simp_rw [hpoint]
          exact tsum_mul_left]
        field_simp]
  have htail' : (∑' i : ℕ, f (i + (j - 1))) = zetaQ2sq - h2 j := by
    dsimp [f, zetaQ2sq, h2]
    linarith
  rw [htail']

/-- The second shifted identity stated using the main file's convention for
`zetaQ2`. -/
lemma shifted_two_zetaQ2 (j : ℕ) (hj : 1 ≤ j) :
    (∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell)) ^ 2) =
      (zetaQ2 - h2 j) / q ^ j := by
  rw [← zetaQ2sq_eq_zetaQ2]
  exact shifted_two j hj

end ShiftedSums
