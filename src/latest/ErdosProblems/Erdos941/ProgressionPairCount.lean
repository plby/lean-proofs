import ErdosProblems.Erdos941.ProgressionContent

/-! # The arithmetic pair count along each shadowing progression -/

namespace Erdos941

theorem sphereResidueValues_nondegenerate {n q : ℕ} {c e : ℤ}
    (he : e ∈ sphereResidueValues n q c) : e ^ 2 ≠ (n : ℤ) ^ 2 := by
  have heI := Finset.mem_Ioo.mp (Finset.mem_filter.mp he).1
  intro hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h <;> omega

theorem sphereResidueValues_discriminant_bound {n q : ℕ} {c e : ℤ}
    (he : e ∈ sphereResidueValues n q c) :
    ((spherePairDiscriminant n e).natAbs : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
  have heI := Finset.mem_Ioo.mp (Finset.mem_filter.mp he).1
  have hsq : e ^ 2 ≤ (n : ℤ) ^ 2 := by
    have h := mul_nonneg (show 0 ≤ (n : ℤ) - e by omega)
      (show 0 ≤ (n : ℤ) + e by omega)
    nlinarith
  have hZ : ((spherePairDiscriminant n e).natAbs : ℤ) ≤ 4 * (n : ℤ) ^ 2 := by
    rw [Int.natCast_natAbs, spherePairDiscriminant_eq, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr hsq)]
    norm_num
    nlinarith [sq_nonneg e]
  exact_mod_cast hZ

theorem exists_sum_sphere_residue_pairs_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n q : ℕ) (c : ℤ),
      0 < n → 0 < q → q.Coprime n → (c = n ∨ c = -(n : ℤ)) →
      (∑ e ∈ sphereResidueValues n q c, ((spherePairs n e).card : ℝ)) ≤
        K * ((n : ℝ) / q) * (n : ℝ) ^ ε := by
  classical
  let a := ε / 3
  have ha : 0 < a := div_pos hε (by norm_num)
  obtain ⟨C, hC, hpair⟩ := exists_sphere_pair_count_bound ha
  obtain ⟨B, hB, hdiv⟩ := Analytic.exists_card_divisors_le_rpow ha
  refine ⟨8 * C * (4 : ℝ) ^ a * B, by positivity, ?_⟩
  intro n q c hn hq hcop hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpoint (e : ℤ) (he : e ∈ sphereResidueValues n q c) :
      ((spherePairs n e).card : ℝ) ≤ C * pairSquareContent (-(n : ℤ)) (-(2 * e)) *
        (4 * (n : ℝ) ^ 2) ^ a := by
    apply (hpair n e hn.ne' (sphereResidueValues_nondegenerate he)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow (by positivity) (sphereResidueValues_discriminant_bound he) ha.le
  have hsum : (∑ e ∈ sphereResidueValues n q c, ((spherePairs n e).card : ℝ)) ≤
      (C * (4 * (n : ℝ) ^ 2) ^ a) *
        ∑ e ∈ sphereResidueValues n q c, (pairSquareContent (-(n : ℤ)) (-(2 * e)) : ℝ) := by
    calc
      _ ≤ ∑ e ∈ sphereResidueValues n q c,
          C * pairSquareContent (-(n : ℤ)) (-(2 * e)) * (4 * (n : ℝ) ^ 2) ^ a :=
        Finset.sum_le_sum hpoint
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hweighted : (∑ e ∈ sphereResidueValues n q c,
      (pairSquareContent (-(n : ℤ)) (-(2 * e)) : ℝ)) ≤
      (8 * (n : ℝ) / q) * (B * (n : ℝ) ^ a) :=
    (sum_sphere_progression_content_le hn hq hcop hc).trans
      (mul_le_mul_of_nonneg_left (hdiv n hn.ne') (by positivity))
  have hscale : (4 * (n : ℝ) ^ 2) ^ a = (4 : ℝ) ^ a * (n : ℝ) ^ (2 * a) := by
    rw [Real.mul_rpow (by norm_num) (sq_nonneg _), ← Real.rpow_natCast_mul hnR.le 2 a]
    norm_num
  calc
    _ ≤ (C * (4 * (n : ℝ) ^ 2) ^ a) *
        ∑ e ∈ sphereResidueValues n q c, (pairSquareContent (-(n : ℤ)) (-(2 * e)) : ℝ) := hsum
    _ ≤ (C * (4 * (n : ℝ) ^ 2) ^ a) * ((8 * (n : ℝ) / q) * (B * (n : ℝ) ^ a)) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ = (8 * C * (4 : ℝ) ^ a * B) * ((n : ℝ) / q) *
        ((n : ℝ) ^ (2 * a) * (n : ℝ) ^ a) := by rw [hscale]; ring
    _ = (8 * C * (4 : ℝ) ^ a * B) * ((n : ℝ) / q) * (n : ℝ) ^ ε := by
      rw [← Real.rpow_add hnR]
      congr 2
      dsimp [a]
      ring

end Erdos941
