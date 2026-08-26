/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Separation of roots from the proved derivative and repulsion estimates.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.PolynomialDerivatives

namespace Erdos521

theorem polynomial_sub_value_le_of_small_derivative (ε : ℕ → ℝ) (hε : ∀ k, |ε k| ≤ 1)
    (n : ℕ) {x y η ρ : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hxy : |y - x| ≤ ρ)
    (hderiv : |(polynomial ε n).derivative.eval x| ≤ η) :
    |(polynomial ε n).eval y - (polynomial ε n).eval x| ≤ ρ * (η + (n + 1 : ℝ) ^ 3 * ρ) := by
  let s := Set.Icc (-1 : ℝ) 1 ∩ Metric.closedBall x ρ
  have hs : Convex ℝ s := (convex_Icc _ _).inter (convex_closedBall x ρ)
  have hxs : x ∈ s := ⟨hx, by simpa only [Metric.mem_closedBall, dist_self] using hρ⟩
  have hys : y ∈ s := ⟨hy, by simpa only [Metric.mem_closedBall, Real.dist_eq] using hxy⟩
  have hbound (t : ℝ) (ht : t ∈ s) :
      ‖(polynomial ε n).derivative.eval t‖ ≤ η + (n + 1 : ℝ) ^ 3 * ρ := by
    have htx : |t - x| ≤ ρ := by simpa only [Metric.mem_closedBall, Real.dist_eq] using ht.2
    have hlip := polynomial_derivative_lipschitz ε hε n hx ht.1
    have hmul := mul_le_mul_of_nonneg_left htx (by positivity : 0 ≤ (n + 1 : ℝ) ^ 3)
    have htri := norm_add_le
      ((polynomial ε n).derivative.eval t - (polynomial ε n).derivative.eval x)
      ((polynomial ε n).derivative.eval x)
    rw [sub_add_cancel] at htri
    simp only [Real.norm_eq_abs] at htri ⊢
    linarith
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ ↦ ((polynomial ε n).hasDerivAt t).hasDerivWithinAt) hbound hxs hys
  simp only [Real.norm_eq_abs] at h
  have hmul := mul_le_mul_of_nonneg_left hxy
    (by positivity : 0 ≤ η + (n + 1 : ℝ) ^ 3 * ρ)
  exact h.trans (hmul.trans_eq (mul_comm _ _))

theorem root_gap_gt_of_repulsion (ε : ℕ → ℝ) (hε : ∀ k, |ε k| ≤ 1) (n : ℕ)
    {a b δ ρ x y : ℝ} (hI : Set.Icc a b ⊆ Set.Icc (-1 : ℝ) 1) (hρ : 0 ≤ ρ)
    (hscale : (n + 1 : ℝ) ^ 3 * ρ ^ 2 ≤ δ)
    (hrep : ∀ t ∈ Set.Icc a b,
      δ < max |(polynomial ε n).eval t| |(polynomial ε n).derivative.eval t|)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hxy : x < y)
    (hrootx : (polynomial ε n).eval x = 0) (hrooty : (polynomial ε n).eval y = 0) :
    ρ < y - x := by
  by_contra hh
  have hgap : y - x ≤ ρ := le_of_not_gt hh
  obtain ⟨c, hc, hcderiv⟩ := exists_deriv_eq_zero hxy (polynomial ε n).continuous.continuousOn
    (hrootx.trans hrooty.symm)
  rw [Polynomial.deriv] at hcderiv
  have hcI : c ∈ Set.Icc a b := ⟨hx.1.trans hc.1.le, hc.2.le.trans hy.2⟩
  have hcx : |x - c| ≤ ρ := by rw [abs_of_neg (sub_neg.mpr hc.1)]; linarith [hc.2]
  have hdiff := polynomial_sub_value_le_of_small_derivative ε hε n (hI hcI) (hI hx)
    (le_refl (0 : ℝ)) hρ hcx (by simp only [hcderiv, abs_zero, le_refl])
  rw [hrootx, zero_sub, abs_neg, zero_add] at hdiff
  have hbound : |(polynomial ε n).eval c| ≤ δ := by nlinarith
  have h := hrep c hcI
  rw [hcderiv, abs_zero, max_eq_left (abs_nonneg _)] at h
  exact h.not_ge hbound

end Erdos521
