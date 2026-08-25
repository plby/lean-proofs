import Util.Bernays.SpatialCountBounds
import Util.Bernays.DirichletUntwisting
import Util.Bernays.LogarithmicTestFunctions

/-!
# Removing the real Dirichlet twist from compact spatial tests
-/

open Set Filter Topology
open scoped Classical ContDiff

namespace Bernays

theorem spatial_untwist_error_le {a : ℕ → ℂ} {Ψ : ℝ → ℂ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, cumsum (fun n => ‖a n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {b L Q : ℝ} (hb : 0 ≤ b) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hΨ₀ : Ψ 0 = 0) (hΨ : ∀ y : ℝ, ‖Ψ y‖ ≤ Q)
    (hsupp : ∀ y : ℝ, Ψ y ≠ 0 → y ≤ b ∧ |Real.log y| ≤ L)
    {δ : ℝ} (hδ : 0 < δ) :
    ‖(∑' n : ℕ, dirichletTwist a δ n * Ψ ((n : ℝ) / Real.exp (1 / δ))) -
      (Real.exp (-1) : ℂ) * (∑' n : ℕ, a n * Ψ ((n : ℝ) / Real.exp (1 / δ)))‖ /
        (Real.exp (1 / δ) * Real.sqrt δ) ≤
      (Real.exp (-1) * (Real.exp (δ * L) - 1) * Q) * (1 + 2 * C * (b + 2)) := by
  let x := Real.exp (1 / δ)
  let N := ⌈b * x⌉₊ + 1
  let R := Real.exp (-1) * (Real.exp (δ * L) - 1) * Q
  have hx : 0 < x := Real.exp_pos _
  have hx₁ : 1 ≤ x := (Real.one_lt_exp_iff.mpr (by positivity : 0 < 1 / δ)).le
  have hε : 0 ≤ Real.exp (δ * L) - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hδ.le hL))
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hbΨ : ∀ y : ℝ, Ψ y ≠ 0 → y ≤ b := fun y hy => (hsupp y hy).1
  have hsum (c : ℕ → ℂ) : (∑' n : ℕ, c n * Ψ ((n : ℝ) / x)) =
      ∑ n ∈ Finset.range N, c n * Ψ ((n : ℝ) / x) := spatial_sum_eq_finset hx hbΨ
  have hbound : ‖(∑' n : ℕ, dirichletTwist a δ n * Ψ ((n : ℝ) / x)) -
      (Real.exp (-1) : ℂ) * (∑' n : ℕ, a n * Ψ ((n : ℝ) / x))‖ ≤
      R * cumsum (fun n => ‖a n‖) N := by
    rw [hsum, hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    change _ ≤ R * ∑ n ∈ Finset.range N, ‖a n‖
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have hterm : dirichletTwist a δ n * Ψ ((n : ℝ) / x) -
        (Real.exp (-1) : ℂ) * (a n * Ψ ((n : ℝ) / x)) =
        (dirichletTwist a δ n - (Real.exp (-1) : ℂ) * a n) * Ψ ((n : ℝ) / x) := by ring
    rw [hterm, norm_mul]
    by_cases hz : Ψ ((n : ℝ) / x) = 0
    · rw [hz, norm_zero, mul_zero]
      exact mul_nonneg hR (norm_nonneg _)
    · have hn : n ≠ 0 := by intro hn; subst n; simp [hΨ₀] at hz
      have htwist := dirichletTwist_sub_bound a hδ hn (hsupp _ hz).2
      have hmul := mul_le_mul htwist (hΨ ((n : ℝ) / x)) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hε)
      dsimp only [R]
      convert hmul using 1 <;> ring
  have hAN (k : ℕ) : cumsum (fun n => ‖a n‖) k ≤ k := by
    have h := Finset.sum_le_sum (s := Finset.range k) (fun n _ => ha n)
    simpa only [cumsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using h
  have hN := ceil_mul_add_one_le hb hx₁
  have hc := count_scaled_exponential_le hAN hC hcount (show 0 ≤ b + 2 by linarith) hδ hN
  have hdiv := div_le_div_of_nonneg_right hbound (mul_nonneg hx.le (Real.sqrt_nonneg δ))
  rw [mul_div_assoc] at hdiv
  exact hdiv.trans (mul_le_mul_of_nonneg_left hc hR)

theorem compact_positive_test_bounds {Ψ : ℝ → ℂ} (hΨ : Continuous Ψ)
    (hsupp : HasCompactSupport Ψ) (hplus : tsupport Ψ ⊆ Ioi 0) :
    ∃ b L Q : ℝ, 0 ≤ b ∧ 0 ≤ L ∧ 0 ≤ Q ∧ Ψ 0 = 0 ∧ (∀ y : ℝ, ‖Ψ y‖ ≤ Q) ∧
      ∀ y : ℝ, Ψ y ≠ 0 → y ≤ b ∧ |Real.log y| ≤ L := by
  obtain ⟨b, hb⟩ := hsupp.isBounded.exists_norm_le
  obtain ⟨Q, hQ⟩ := hΨ.bounded_above_of_compact_support hsupp
  have hlog : ContinuousOn Real.log (tsupport Ψ) := fun y hy =>
    (Real.continuousAt_log (ne_of_gt (hplus hy))).continuousWithinAt
  obtain ⟨L, hL⟩ := hsupp.exists_bound_of_continuousOn hlog
  refine ⟨max 0 b, max 0 L, max 0 Q, le_max_left _ _, le_max_left _ _, le_max_left _ _, ?_,
    fun y => (hQ y).trans (le_max_right _ _), ?_⟩
  · by_contra hzero
    exact (lt_irrefl (0 : ℝ)) (hplus (subset_closure hzero))
  · intro y hy
    have hys : y ∈ tsupport Ψ := subset_closure hy
    exact ⟨(le_abs_self y).trans ((hb y hys).trans (le_max_right _ _)),
      (hL y hys).trans (le_max_right _ _)⟩

end Bernays
