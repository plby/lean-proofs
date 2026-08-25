import ErdosProblems.Erdos964.LogPowerAbel

/-!
# Calculus of normalized logarithmic monomials
-/

namespace Erdos964

noncomputable def normalizedLogMonomial (L : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  (Real.log t) ^ j / L ^ j

theorem normalizedLogMonomial_eq (L : ℝ) (j : ℕ) (t : ℝ) :
    normalizedLogMonomial L j t = (Real.log t / L) ^ j := (div_pow _ _ _).symm

theorem normalizedLogMonomial_hasDerivAt (L : ℝ) (j : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (normalizedLogMonomial L j)
      ((j : ℝ) * (Real.log t) ^ (j - 1) / L ^ j / t) t := by
  unfold normalizedLogMonomial
  have h := ((Real.hasDerivAt_log ht.ne').pow j).div_const (L ^ j)
  have hid : (j : ℝ) * (Real.log t) ^ (j - 1) * t⁻¹ / L ^ j =
      (j : ℝ) * (Real.log t) ^ (j - 1) / L ^ j / t := by ring
  rw [hid] at h
  simpa only [Pi.pow_def] using h

theorem normalizedLogMonomial_continuousOn (L : ℝ) (j : ℕ) (Q : ℕ) :
    ContinuousOn (normalizedLogMonomial L j) (Set.Icc (1 : ℝ) Q) :=
  ((continuousOn_id.log (fun _ ht => (zero_lt_one.trans_le ht.1).ne')).pow j).div_const _

theorem normalizedLogMonomial_deriv_continuousOn (L : ℝ) (j : ℕ) (Q : ℕ) :
    ContinuousOn (deriv (normalizedLogMonomial L j)) (Set.Icc (1 : ℝ) Q) := by
  have hformula : ContinuousOn
      (fun t : ℝ => (j : ℝ) * (Real.log t) ^ (j - 1) / L ^ j / t)
      (Set.Icc (1 : ℝ) Q) :=
    ((continuousOn_const.mul ((continuousOn_id.log
      (fun t ht => (zero_lt_one.trans_le ht.1).ne')).pow (j - 1))).div_const _).div
      continuousOn_id (fun t ht => (zero_lt_one.trans_le ht.1).ne')
  exact hformula.congr (fun t ht =>
    (normalizedLogMonomial_hasDerivAt L j t (zero_lt_one.trans_le ht.1)).deriv)

theorem normalizedLogMonomial_bounds (L : ℝ) (hL : 0 < L) (j : ℕ) (t : ℝ)
    (ht : 1 ≤ t) (htL : Real.log t ≤ L) :
    0 ≤ normalizedLogMonomial L j t ∧ normalizedLogMonomial L j t ≤ 1 := by
  rw [normalizedLogMonomial_eq]
  have hratio : 0 ≤ Real.log t / L := div_nonneg (Real.log_nonneg ht) hL.le
  exact ⟨pow_nonneg hratio _, pow_le_one₀ hratio ((div_le_one hL).mpr htL)⟩

theorem normalizedLogMonomial_deriv_nonneg (L : ℝ) (hL : 0 ≤ L) (j : ℕ) (t : ℝ)
    (ht : 1 ≤ t) : 0 ≤ deriv (normalizedLogMonomial L j) t := by
  rw [(normalizedLogMonomial_hasDerivAt L j t (zero_lt_one.trans_le ht)).deriv]
  have hlog := Real.log_nonneg ht
  positivity

end Erdos964
