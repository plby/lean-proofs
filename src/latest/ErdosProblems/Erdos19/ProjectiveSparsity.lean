import ErdosProblems.Erdos19.ProjectiveWindowGap

/-! # Projective-rank conflicts are sparse compared with a linear palette -/

namespace Erdos19

theorem projective_degree_quotient_le (n t : ℕ) (ht : 2 ≤ t)
    (hk : 4 ≤ projectiveScale n) :
    (n - 1) / (projectiveScale n - projectiveScale n / t - 1) ≤
      8 * projectiveScale n := by
  let k := projectiveScale n
  let d := k - k / t - 1
  have hdiv : 2 * (k / t) ≤ k :=
    (Nat.mul_le_mul_right _ ht).trans (Nat.mul_div_le k t)
  have hk4 : 4 ≤ k := hk
  have hd : k ≤ 4 * d := by dsimp only [d]; omega
  have hdpos : 0 < d := by omega
  have hupper : n ≤ k * k + k + 1 := le_projectiveScale_sq_add n
  have hn : n ≤ 2 * k ^ 2 := by nlinarith only [hupper, hk4]
  have hprod := Nat.mul_le_mul_left (2 * k) hd
  have hbound : n - 1 ≤ (8 * k) * d := by nlinarith only [hn, hprod, Nat.sub_le n 1]
  have hquot := Nat.mul_div_le (n - 1) d
  apply Nat.le_of_mul_le_mul_left (c := d) _ hdpos
  nlinarith only [hbound, hquot]

theorem eventually_projective_conflicts_sparse (R s : ℕ) (hs : 0 < s)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℕ, 2 ≤ t →
      (R * ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) : ℕ) ≤
        delta * ((n / s : ℕ) : ℝ) := by
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge ((32 : ℝ) * R * s / delta)
  let K := max K₀ (4 * s + 4)
  refine ⟨K * K + K + 2, ?_⟩
  intro n hn t ht
  let k := projectiveScale n
  let D := n / s
  have hK : K ≤ k := projectiveScale_ge_of_large_card K n hn
  have hk₀ : K₀ ≤ k := (le_max_left _ _).trans hK
  have hks : 4 * s + 4 ≤ k := (le_max_right _ _).trans hK
  have hk4 : 4 ≤ k := by omega
  have hn2 : 2 ≤ n := by omega
  have hlow := projectiveScale_pred_sq_add_le (n := n) hn2
  change (k - 1) * (k - 1) + (k - 1) + 2 ≤ n at hlow
  have hkpred : k - 1 + 1 = k := by omega
  have hlow' : k ^ 2 + 2 ≤ n + k := by nlinarith only [hlow, hkpred]
  have hfloor : n < s * (D + 1) := Nat.lt_mul_div_succ n hs
  have hD : k ^ 2 ≤ 4 * s * D := by nlinarith only [hlow', hfloor, hks, hk4]
  have hlarge : (32 : ℝ) * R * s / delta ≤ (k : ℝ) :=
    hK₀.trans (by exact_mod_cast hk₀)
  have hscale : (32 : ℝ) * R * s ≤ delta * k := by
    have h := (div_le_iff₀ hdelta).mp hlarge
    nlinarith only [h]
  have hDreal : (k : ℝ) ^ 2 ≤ 4 * s * D := by exact_mod_cast hD
  have hprod := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg k)
  have hprod' := mul_le_mul_of_nonneg_left hDreal hdelta.le
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
  have hsmall : (R : ℝ) * (8 * k) ≤ delta * D := by
    nlinarith only [hprod, hprod', hsreal]
  have hdegree := projective_degree_quotient_le n t ht hk4
  have hdegree' :
      (R * ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) : ℕ) ≤ R * (8 * k) :=
    Nat.mul_le_mul_left R hdegree
  have hdegreeR :
      ((R * ((n - 1) / (projectiveScale n - projectiveScale n / t - 1)) : ℕ) : ℝ) ≤
        (R : ℝ) * (8 * k) := by exact_mod_cast hdegree'
  exact hdegreeR.trans hsmall

#print axioms eventually_projective_conflicts_sparse

end Erdos19
