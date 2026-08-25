import ErdosProblems.Erdos1197.BMIntRel

namespace Erdos1197

open Chebyshev
open MeasureTheory Set
open scoped Asymptotics BigOperators Chebyshev ENNReal

noncomputable section

lemma bm_prime_mul_mem_window (ν : ℕ) {p y : ℝ}
    (hp : p ∈ Ioo (((23 : ℝ) / 16) * 2 ^ ν) (((3 : ℝ) / 2) * 2 ^ ν))
    (hy : y ∈ I_inf) :
    p * y ∈ Ioo (((8 : ℝ) / 9) * 2 ^ ν) ((2 : ℝ) ^ ν) := by
  rcases hp with ⟨hp_lower, hp_upper⟩
  rcases hy with ⟨hy_lower, hy_upper⟩
  have hy_pos : 0 < y := by linarith
  constructor
  · have hp_times_y : (((23 : ℝ) / 16) * 2 ^ ν) * y < p * y := by
      exact mul_lt_mul_of_pos_right hp_lower hy_pos
    have hlower :
        (((23 : ℝ) / 16) * 2 ^ ν) * ((16 : ℝ) / 25) ≤
          (((23 : ℝ) / 16) * 2 ^ ν) * y := by
      gcongr
    have hnum :
        (((8 : ℝ) / 9) * 2 ^ ν) <
          (((23 : ℝ) / 16) * 2 ^ ν) * ((16 : ℝ) / 25) := by
      have hpow : 0 < (2 : ℝ) ^ ν := by positivity
      nlinarith
    exact lt_trans hnum (lt_of_le_of_lt hlower hp_times_y)
  · have hp_pos : 0 < p := by linarith
    have hy_times_p : p * y ≤ p * ((2 : ℝ) / 3) := by
      gcongr
    have hupper : p * ((2 : ℝ) / 3) < (((3 : ℝ) / 2) * 2 ^ ν) * ((2 : ℝ) / 3) := by
      exact mul_lt_mul_of_pos_right hp_upper (by norm_num)
    have hnum : (((3 : ℝ) / 2) * 2 ^ ν) * ((2 : ℝ) / 3) = (2 : ℝ) ^ ν := by
      ring
    simpa [hnum] using lt_of_le_of_lt hy_times_p hupper

lemma bm_half_grid_not_near_integer (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    ¬ |(m : ℝ) + 1 / (2 : ℝ) ^ k| < 1 / (4 * (2 : ℝ) ^ k) := by
  have hkpow : 0 < (2 : ℝ) ^ k := by positivity
  have hfrac_pos : 0 < 1 / (2 : ℝ) ^ k := by positivity
  have hpow_le : (2 : ℝ) ≤ 2 ^ k := by
    simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk
  have hfrac_le_half : 1 / (2 : ℝ) ^ k ≤ 1 / 2 := by
    simpa [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpow_le)
  have hquarter : 1 / (4 * (2 : ℝ) ^ k) < 1 / (2 : ℝ) ^ k := by
    field_simp [hkpow.ne']
    nlinarith
  intro h
  rcases lt_or_ge m 0 with hm_neg | hm_nonneg
  · have hm_le : (m : ℝ) ≤ -1 := by
      exact_mod_cast (Int.le_sub_one_iff.mpr hm_neg)
    have habs_ge : 1 / (2 : ℝ) ^ k ≤ |(m : ℝ) + 1 / (2 : ℝ) ^ k| := by
      rw [abs_of_nonpos]
      · nlinarith
      · nlinarith
    have hsmall : |(m : ℝ) + 1 / (2 : ℝ) ^ k| < 1 / (2 : ℝ) ^ k := by
      exact lt_trans h hquarter
    exact (not_lt_of_ge habs_ge) hsmall
  · have hm_ge : (0 : ℝ) ≤ m := by exact_mod_cast hm_nonneg
    have habs_ge : 1 / (2 : ℝ) ^ k ≤ |(m : ℝ) + 1 / (2 : ℝ) ^ k| := by
      rw [abs_of_nonneg]
      · have : (1 / (2 : ℝ) ^ k : ℝ) ≤ (m : ℝ) + 1 / (2 : ℝ) ^ k := by
          nlinarith
        exact this
      · positivity
    have hsmall : |(m : ℝ) + 1 / (2 : ℝ) ^ k| < 1 / (2 : ℝ) ^ k := by
      exact lt_trans h hquarter
    exact (not_lt_of_ge habs_ge) hsmall

lemma bm_q_nonzero_of_first_prime_target
    {k : ℕ} (hk : 1 ≤ k) {q : ℤ} {p : ℤ} {a : ℝ}
    (hq :
      |(q : ℝ) * a - (p : ℝ) - 1 / (2 : ℝ) ^ k| <
        1 / (4 * (2 : ℝ) ^ k)) :
    q ≠ 0 := by
  intro hzero
  let s : ℝ := (p : ℝ) + 1 / (2 : ℝ) ^ k
  have hneg : |-s| < 1 / (4 * (2 : ℝ) ^ k) := by
    convert hq using 1
    · simp [s, hzero, sub_eq_add_neg, add_comm]
  have hrew : |s| < 1 / (4 * (2 : ℝ) ^ k) := by
    simpa [abs_neg] using hneg
  exact (bm_half_grid_not_near_integer k hk p) hrew

/-- BM-facing Kronecker wrapper: the common denominator can be chosen nonzero because one
prime-block target is the nonintegral point `1 / 2^k`. -/
lemma bm_common_q_int_nonzero
    {k ν : ℕ} (hk : 1 ≤ k) (p : PrimeIdx k → ℕ)
    (h_intrel :
      ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
        (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
        ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z) :
    ∃ q : ℤ, q ≠ 0 ∧ ∃ m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k) := by
  obtain ⟨q, m, hm⟩ :=
    kronecker_intrel_implies_approx_common_q_int
      (2 ^ k + (2 ^ (ν - 2) + 1)) (bmFlatAlpha p) (bmFlatBeta k ν) h_intrel
      (1 / (4 * (2 : ℝ) ^ k)) (by positivity)
  refine ⟨q, ?_, m, hm⟩
  have hcoord :
      |(q : ℝ) * bmFlatAlpha p
            (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk)) -
          (m (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk)) : ℝ) -
          1 / (2 : ℝ) ^ k| <
        1 / (4 * (2 : ℝ) ^ k) := by
    simpa [bmFlatBeta_primeIdxOne_eq k ν hk] using
      hm (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk))
  exact bm_q_nonzero_of_first_prime_target hk hcoord

lemma int_sign_mul_div_natAbs (q m : ℤ) (hq : q ≠ 0) :
    (((Int.sign q * m : ℤ) : ℝ) / (Int.natAbs q : ℝ)) = (m : ℝ) / (q : ℝ) := by
  rcases lt_trichotomy q 0 with hqneg | rfl | hqpos
  · have hsign : Int.sign q = -1 := Int.sign_eq_neg_one_of_neg hqneg
    have hqabs : (Int.natAbs q : ℝ) = -(q : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg]
      exact_mod_cast hqneg
    have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hqneg.ne
    calc
      (((Int.sign q * m : ℤ) : ℝ) / (Int.natAbs q : ℝ))
          = ((-(m : ℝ)) / (-(q : ℝ))) := by simp [hsign, hqabs]
      _ = (m : ℝ) / (q : ℝ) := by field_simp [hqreal]
  · contradiction
  · have hsign : Int.sign q = 1 := Int.sign_eq_one_of_pos hqpos
    have hqabs : (Int.natAbs q : ℝ) = (q : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos]
      exact_mod_cast hqpos
    simp [hsign, hqabs]

lemma bm_integer_lattice_of_common_q
    {k ν : ℕ} {p : PrimeIdx k → ℕ} {q : ℤ}
    (hq : q ≠ 0)
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k))
    {n : ℕ}
    (hn : (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν))
    (hν : 3 ≤ ν) :
    ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (Int.natAbs q : ℝ)| <
      1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
  obtain ⟨j, rfl⟩ := exists_bmIntVal_eq_of_mem_Ioo ν hν hn
  let idx : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) := Fin.natAdd (2 ^ k) j
  let z : ℤ := Int.sign q * m idx
  refine ⟨z, ?_⟩
  have hcoord :
      |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ)| <
        1 / (4 * (2 : ℝ) ^ k) := by
    simpa [idx, bmFlatAlpha_natAdd, bmFlatBeta_natAdd, sub_eq_add_neg] using hm idx
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hqabs_pos : 0 < |(q : ℝ)| := by
    exact abs_pos.mpr hqreal
  have hscaled :
      |Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ)| <
        (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| := by
    have hmul :
        |(q : ℝ)| *
            |Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |(q : ℝ)| * |Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ)|
            = |(q : ℝ) * (Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ))| := by
                rw [abs_mul]
        _ = |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ)| := by
              congr 1
              field_simp [hq]
        _ < 1 / (4 * (2 : ℝ) ^ k) := by simpa [abs_sub_comm] using hcoord
    exact (lt_div_iff₀ hqabs_pos).2 (by simpa [mul_comm] using hmul)
  have hrewrite :
      ((z : ℝ) / (Int.natAbs q : ℝ)) = (m idx : ℝ) / (q : ℝ) := by
    simpa [z] using int_sign_mul_div_natAbs q (m idx) hq
  rw [hrewrite]
  have hqabs_cast : (Int.natAbs q : ℝ) = |(q : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hqabs_cast_pos : 0 < (Int.natAbs q : ℝ) := by
    rw [hqabs_cast]
    exact hqabs_pos
  have htarget :
      (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| =
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
    rw [← hqabs_cast]
    field_simp [hqabs_cast_pos.ne']
  rw [hqabs_cast]
  convert hscaled using 1
  ring_nf

lemma bm_prime_coordinate_of_common_q
    {k ν : ℕ} {p : PrimeIdx k → ℕ} {q : ℤ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k))
    (i : PrimeIdx k) :
    |(q : ℝ) * Real.logb 2 (p i) - (m (Fin.castAdd (2 ^ (ν - 2) + 1) i) : ℝ) -
        (i : ℝ) / (2 : ℝ) ^ k| <
      1 / (4 * (2 : ℝ) ^ k) := by
  simpa [bmFlatAlpha_castAdd, bmFlatBeta_castAdd] using
    hm (Fin.castAdd (2 ^ (ν - 2) + 1) i)

lemma bm_integer_coordinate_of_common_q
    {k ν : ℕ} {p : PrimeIdx k → ℕ} {q : ℤ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k))
    (j : IntIdx ν) :
    |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (m (Fin.natAdd (2 ^ k) j) : ℝ)| <
      1 / (4 * (2 : ℝ) ^ k) := by
  simpa [bmFlatAlpha_natAdd, bmFlatBeta_natAdd, sub_eq_add_neg] using
    hm (Fin.natAdd (2 ^ k) j)

lemma bm_kronecker_coordinate_data
    {k ν : ℕ} (hk : 1 ≤ k) (p : PrimeIdx k → ℕ)
    (h_intrel :
      ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
        (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
        ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z) :
    ∃ q : ℤ, q ≠ 0 ∧ ∃ m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
      (∀ i : PrimeIdx k,
        |(q : ℝ) * Real.logb 2 (p i) -
            (m (Fin.castAdd (2 ^ (ν - 2) + 1) i) : ℝ) -
            (i : ℝ) / (2 : ℝ) ^ k| <
          1 / (4 * (2 : ℝ) ^ k)) ∧
      (∀ j : IntIdx ν,
        |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) -
            (m (Fin.natAdd (2 ^ k) j) : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k)) := by
  obtain ⟨q, hq, m, hm⟩ := bm_common_q_int_nonzero hk p h_intrel
  refine ⟨q, hq, m, ?_, ?_⟩
  · intro i
    exact bm_prime_coordinate_of_common_q hm i
  · intro j
    exact bm_integer_coordinate_of_common_q hm j



end

end Erdos1197
