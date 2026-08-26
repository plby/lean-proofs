import ErdosProblems.Erdos747.HeavyCutoffSurvival

open scoped BigOperators

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Explicit optimization of the completion-survival tail -/

lemma exists_bounded_variance_tilt (V b u : ℝ)
    (hV : 0 < V) (hb : 0 < b) (hu : 0 < u) :
    ∃ theta : ℝ, 0 ≤ theta ∧ |theta * b| ≤ 1 / 2 ∧
      theta^2 * V - theta * u ≤ -min (u^2 / (4 * V)) (u / (4 * b)) := by
  by_cases hsmall : u * b ≤ V
  · refine ⟨u / (2 * V), by positivity, ?_, ?_⟩
    · rw [abs_of_nonneg (by positivity)]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (show (0 : ℝ) < 2 * V by positivity)).mpr
      nlinarith
    · have heq : (u / (2 * V))^2 * V - (u / (2 * V)) * u = -(u^2 / (4 * V)) := by
        field_simp
        <;> ring
      rw [heq]
      exact neg_le_neg (min_le_left _ _)
  · refine ⟨1 / (2 * b), by positivity, ?_, ?_⟩
    · rw [abs_of_nonneg (by positivity)]
      have heq : (1 / (2 * b)) * b = (1 / 2 : ℝ) := by field_simp
      exact heq.le
    · have hVle : V ≤ u * b := (lt_of_not_ge hsmall).le
      calc
        (1 / (2 * b))^2 * V - (1 / (2 * b)) * u ≤
            (1 / (2 * b))^2 * (u * b) - (1 / (2 * b)) * u := by gcongr
        _ = -(u / (4 * b)) := by field_simp; ring
        _ ≤ _ := neg_le_neg (min_le_right _ _)

lemma completionThinning_relative_lower_failure_le_optimized
    {n t : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hn : 2 ≤ n) (hZ : Z ∈ allEdges n) (b E u r pHit : ℝ)
    (hH : H.Nonempty) (hs : (H \ completionHeavyEdges H Z b).Nonempty)
    (hb : 0 < b) (hu : 0 < u) (ht0 : 0 < t)
    (hw : 0 < completionWeight H Z)
    (htCard : t ≤ (H \ completionHeavyEdges H Z b).card)
    (hcollision : 2 * t * t ≤ (H \ completionHeavyEdges H Z b).card)
    (hm : ((n - 1 : ℕ) : ℝ) < (H \ completionHeavyEdges H Z b).card)
    (hheavy : ∑ A ∈ completionHeavyEdges H Z b,
      (completionEdgeWeight H Z A : ℝ) ≤ E)
    (hhit : (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card ≤ pHit)
    (hbudget : r * (completionWeight H Z : ℝ) + u ≤
      (completionWeight H Z : ℝ) *
        (1 - ((n - 1 : ℕ) : ℝ) / (H \ completionHeavyEdges H Z b).card)^t) :
    finsetProbability (H.powersetCard t)
        (fun T ↦ (completionWeight (H \ T) Z : ℝ) <
          r * (completionWeight H Z : ℝ)) ≤
      pHit + 2 * Real.exp (-min
        (u^2 / (4 * ((t : ℝ) * ((completionWeight H Z : ℝ) *
          ((n - 1 : ℕ) : ℝ) / (H \ completionHeavyEdges H Z b).card) * b)))
        (u / (4 * b))) := by
  let V := (t : ℝ) * ((completionWeight H Z : ℝ) *
    ((n - 1 : ℕ) : ℝ) / (H \ completionHeavyEdges H Z b).card) * b
  have hV : 0 < V := by
    have hnm : 0 < n - 1 := by omega
    have hspos := Finset.card_pos.mpr hs
    dsimp only [V]
    positivity
  obtain ⟨theta, htheta0, htheta, htail⟩ := exists_bounded_variance_tilt V b u hV hb hu
  have hraw := completionThinning_relative_lower_failure_le_of_heavy_bounds
    H hn hZ b E theta u r pHit hH hs hb htheta0 htheta htCard hcollision hm hheavy hhit hbudget
  apply hraw.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  dsimp only [V] at htail
  nlinarith

end

end Erdos747
