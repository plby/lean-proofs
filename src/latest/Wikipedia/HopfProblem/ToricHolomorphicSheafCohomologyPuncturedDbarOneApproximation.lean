import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneApproximationSplit
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximationError

/-!
# Genuine finite Laurent-polynomial approximation on disc–annulus regions

The local annular Cauchy splitting gives two actual bidisc functions.
Their finite Cauchy polynomials give a finite Laurent polynomial in the
original second coordinate. It is holomorphic on the whole punctured
product and approximates the original function uniformly on the smaller
closed disc–annulus region.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne

open PeriodTorusLineBundleClassificationPolydiscApproximation
  (exists_entire_polynomial_approximation)

def reciprocal (q : ℂ × ℂ) : ℂ × ℂ := (q.1, q.2⁻¹)

theorem reciprocal_analytic : AnalyticOnNhd ℂ reciprocal domain := by
  intro q hq
  exact analyticAt_fst.prod (analyticAt_snd.inv hq)

theorem reciprocal_mem_closedBidisc {r : ℝ} (hr : 0 < r) {q : ℂ × ℂ}
    (hq : q ∈ annularClosed r) : reciprocal q ∈ closedBall (0 : ℂ) r ×ˢ closedBall 0 r := by
  refine ⟨hq.1, ?_⟩
  have hlo : r⁻¹ ≤ ‖q.2‖ := by
    simpa only [mem_ball, dist_zero_right, not_lt] using hq.2.2
  have hp : 0 < ‖q.2‖ := (inv_pos.mpr hr).trans_le hlo
  change q.2⁻¹ ∈ closedBall (0 : ℂ) r
  rw [mem_closedBall_zero_iff, norm_inv]
  simpa only [inv_inv] using (inv_le_inv₀ hp (inv_pos.mpr hr)).mpr hlo

/-- The approximant is a literal finite sum of nonnegative and negative
coordinate monomials, not a presumed global holomorphic approximation. -/
theorem exists_laurent_polynomial_approximation {f : ℂ × ℂ → ℂ} {r R ε : ℝ}
    (hr : 1 < r) (hrR : r < R) (hε : 0 < ε)
    (hf : AnalyticOnNhd ℂ f (annularOpen R)) :
    ∃ (N M : ℕ) (a b : ℕ → ℕ → ℂ) (P : ℂ × ℂ → ℂ),
      (∀ q, P q =
        (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i j * q.1 ^ i * q.2 ^ j) +
        ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, b i j * q.1 ^ i * (q.2⁻¹) ^ j) ∧
      AnalyticOnNhd ℂ P domain ∧ ∀ q ∈ annularClosed r, ‖P q - f q‖ < ε := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  obtain ⟨B, hrB, hBR⟩ := exists_between hrR
  have hB : 1 < B := hr.trans hrB
  obtain ⟨p, m, hp, hm, heq⟩ := exists_local_annular_splitting hB
    (hf.mono (annularClosed_subset_open (zero_lt_one.trans hB) hBR))
  obtain ⟨S, hrS, hSB⟩ := exists_between hrB
  have hsub : closedBall (0 : ℂ) S ×ˢ closedBall (0 : ℂ) S ⊆
      ball (0 : ℂ) B ×ˢ ball (0 : ℂ) B :=
    Set.prod_mono (closedBall_subset_ball hSB) (closedBall_subset_ball hSB)
  obtain ⟨N, a, P, hPpoly, hP, hPe⟩ := exists_entire_polynomial_approximation
    (r := r) (R := S) (ε := ε / 2) hr0.le hrS (half_pos hε) (hp.mono hsub)
  obtain ⟨M, b, Q, hQpoly, hQ, hQe⟩ := exists_entire_polynomial_approximation
    (r := r) (R := S) (ε := ε / 2) hr0.le hrS (half_pos hε) (hm.mono hsub)
  let F : ℂ × ℂ → ℂ := fun q => P q + Q (reciprocal q)
  refine ⟨N, M, a, b, F, ?_, ?_, ?_⟩
  · intro q
    change P q + Q (reciprocal q) = _
    rw [hPpoly q, hQpoly (reciprocal q)]
    rfl
  · intro q hq
    exact hP.contDiffAt.analyticAt.add
      (hQ.contDiffAt.analyticAt.comp (reciprocal_analytic q hq))
  · intro q hq
    have hqB : q ∈ annularOpen B := annularClosed_subset_open hr0 hrB hq
    have hqp : q ∈ closedBall (0 : ℂ) r ×ˢ closedBall 0 r := ⟨hq.1, hq.2.1⟩
    have hqm := reciprocal_mem_closedBidisc hr0 hq
    change ‖(P q + Q (reciprocal q)) - f q‖ < ε
    rw [← heq q hqB]
    change ‖(P q + Q (reciprocal q)) - (p q + m (reciprocal q))‖ < ε
    rw [show (P q + Q (reciprocal q)) - (p q + m (reciprocal q)) =
      (P q - p q) + (Q (reciprocal q) - m (reciprocal q)) by ring]
    calc
      _ ≤ ‖P q - p q‖ + ‖Q (reciprocal q) - m (reciprocal q)‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hPe q hqp) (hQe (reciprocal q) hqm)
      _ = ε := by ring

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarOne
