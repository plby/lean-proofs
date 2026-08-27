import ErdosProblems.Erdos587.HooleyMoments

/-!
# Controlling concentration by integral moments

A unit divisor window is covered by two consecutive windows when its
starting point is moved by at most one. Integrating this covering bound
gives `Delta(n)^q ≤ 2^q M_q(n)` for every positive integer `q`.
-/

open MeasureTheory

namespace Erdos587

lemma deltaDivisors_subset_two_windows (n : ℕ) {u v : ℝ}
    (hvu : v ≤ u) (huv : u ≤ v + 1) :
    deltaDivisors n u ⊆ deltaDivisors n v ∪ deltaDivisors n (v + 1) := by
  classical
  intro d hd
  obtain ⟨hdn, hn, hlow, hupp⟩ := mem_deltaDivisors.mp hd
  by_cases hmid : (d : ℝ) ≤ Real.exp (v + 1)
  · apply Finset.mem_union_left
    exact mem_deltaDivisors.mpr
      ⟨hdn, hn, (Real.exp_le_exp.mpr hvu).trans_lt hlow, hmid⟩
  · apply Finset.mem_union_right
    apply mem_deltaDivisors.mpr
    exact ⟨hdn, hn, lt_of_not_ge hmid,
      hupp.trans (Real.exp_le_exp.mpr (by linarith))⟩

lemma deltaCount_le_two_windows (n : ℕ) {u v : ℝ}
    (hvu : v ≤ u) (huv : u ≤ v + 1) :
    deltaCount n u ≤ deltaCount n v + deltaCount n (v + 1) := by
  unfold deltaCount
  exact_mod_cast (Finset.card_le_card
    (deltaDivisors_subset_two_windows n hvu huv)).trans (Finset.card_union_le _ _)

/-- The finite-moment concentration bound used to pass from moment control
to a weak-type estimate. -/
theorem hooleyDelta_pow_le_two_pow_mul_deltaMoment (n : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (hooleyDelta n : ℝ) ^ q ≤ 2 ^ q * deltaMoment n q := by
  obtain ⟨u, hu⟩ := exists_deltaDivisors_card_eq n
  have hcount : deltaCount n u = (hooleyDelta n : ℝ) := by
    unfold deltaCount
    exact_mod_cast hu
  let S := Set.Icc (u - 1) u
  let F : ℝ → ℝ := S.indicator (fun _ => (hooleyDelta n : ℝ) ^ q)
  let G : ℝ → ℝ := fun v =>
    (2 : ℝ) ^ (q - 1) * (deltaCount n v ^ q + deltaCount n (v + 1) ^ q)
  have hF : Integrable F := by
    apply IntegrableOn.integrable_indicator
    · exact integrableOn_const (by simp [S])
    · exact measurableSet_Icc
  have hi := integrable_deltaCount_pow (n := n) hq
  have hG : Integrable G := (hi.add (hi.comp_add_right 1)).const_mul _
  have hFG : ∀ v, F v ≤ G v := by
    intro v
    by_cases hv : v ∈ S
    · rw [show F v = (hooleyDelta n : ℝ) ^ q from Set.indicator_of_mem hv _]
      have hlocal : (hooleyDelta n : ℝ) ≤ deltaCount n v + deltaCount n (v + 1) := by
        rw [← hcount]
        exact deltaCount_le_two_windows n hv.2 (by linarith [hv.1])
      exact (pow_le_pow_left₀ (by positivity) hlocal q).trans
        (add_pow_le (deltaCount_nonneg n v) (deltaCount_nonneg n (v + 1)) q)
    · rw [show F v = 0 from Set.indicator_of_notMem hv _]
      exact mul_nonneg (by positivity) (add_nonneg
        (pow_nonneg (deltaCount_nonneg n v) q)
        (pow_nonneg (deltaCount_nonneg n (v + 1)) q))
  calc
    (hooleyDelta n : ℝ) ^ q = ∫ v : ℝ, F v := by
      rw [show F = S.indicator (fun _ : ℝ => (hooleyDelta n : ℝ) ^ q) from rfl,
        integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc]
      simp
    _ ≤ ∫ v : ℝ, G v := integral_mono hF hG hFG
    _ = 2 ^ q * deltaMoment n q := by
      change (∫ v : ℝ, (2 : ℝ) ^ (q - 1) *
        (deltaCount n v ^ q + deltaCount n (v + 1) ^ q)) = _
      rw [integral_const_mul, integral_add hi (hi.comp_add_right 1),
        integral_add_right_eq_self (fun v : ℝ => deltaCount n v ^ q) 1]
      change (2 : ℝ) ^ (q - 1) * (deltaMoment n q + deltaMoment n q) = _
      rw [← two_mul, ← mul_assoc, ← pow_succ,
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)]

end Erdos587
