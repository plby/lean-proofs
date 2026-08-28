import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOneSplit
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneApproximation

/-!
# Genuine finite Laurent approximation on products of annuli

First-coordinate annular Cauchy splitting gives two disc–annulus
functions. Their proved finite Laurent approximations, in the ordinary
and reciprocal first coordinates, give four literal finite sums of
Laurent monomials on the original product.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne

def reciprocalFirst (q : ℂ × ℂ) : ℂ × ℂ := (q.1⁻¹, q.2)

theorem reciprocalFirst_analytic : AnalyticOnNhd ℂ reciprocalFirst domain := by
  intro q hq
  exact (analyticAt_fst.inv hq.1).prod analyticAt_snd

theorem reciprocalFirst_mem_one_closed {r : ℝ} (hr : 0 < r) {q : ℂ × ℂ}
    (hq : q ∈ annularClosed r) : reciprocalFirst q ∈ PuncturedDbarOne.annularClosed r := by
  refine ⟨?_, hq.2⟩
  have hlo : r⁻¹ ≤ ‖q.1‖ := by
    simpa only [mem_ball, dist_zero_right, not_lt] using hq.1.2
  have hp : 0 < ‖q.1‖ := (inv_pos.mpr hr).trans_le hlo
  change q.1⁻¹ ∈ closedBall (0 : ℂ) r
  rw [mem_closedBall_zero_iff, norm_inv]
  simpa only [inv_inv] using (inv_le_inv₀ hp (inv_pos.mpr hr)).mpr hlo

def finiteLaurentBlock (N M : ℕ) (a b : ℕ → ℕ → ℂ) (q : ℂ × ℂ) : ℂ :=
  (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i j * q.1 ^ i * q.2 ^ j) +
    ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, b i j * q.1 ^ i * (q.2⁻¹) ^ j

/-- Four actual finite Laurent sums, one for each choice of ordinary or
reciprocal first and second coordinates. -/
def IsFiniteLaurentPolynomial (P : ℂ × ℂ → ℂ) : Prop :=
  ∃ (N M K L : ℕ) (a b c d : ℕ → ℕ → ℂ), ∀ q,
    P q = finiteLaurentBlock N M a b q + finiteLaurentBlock K L c d (reciprocalFirst q)

theorem exists_laurent_polynomial_approximation {f : ℂ × ℂ → ℂ} {r R ε : ℝ}
    (hr : 1 < r) (hrR : r < R) (hε : 0 < ε)
    (hf : AnalyticOnNhd ℂ f (annularOpen R)) :
    ∃ P : ℂ × ℂ → ℂ, IsFiniteLaurentPolynomial P ∧ AnalyticOnNhd ℂ P domain ∧
      ∀ q ∈ annularClosed r, ‖P q - f q‖ < ε := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  obtain ⟨B, hrB, hBR⟩ := exists_between hrR
  have hB : 1 < B := hr.trans hrB
  obtain ⟨p, m, hp, hm, heq⟩ := exists_local_first_splitting hB
    (hf.mono (annularClosed_subset_open (zero_lt_one.trans hB) hBR))
  obtain ⟨N, M, a, b, P, hPpoly, hP, hPe⟩ :=
    PuncturedDbarOne.exists_laurent_polynomial_approximation hr hrB (half_pos hε) hp
  obtain ⟨K, L, c, d, Q, hQpoly, hQ, hQe⟩ :=
    PuncturedDbarOne.exists_laurent_polynomial_approximation hr hrB (half_pos hε) hm
  let F : ℂ × ℂ → ℂ := fun q => P q + Q (reciprocalFirst q)
  refine ⟨F, ?_, ?_, ?_⟩
  · refine ⟨N, M, K, L, a, b, c, d, ?_⟩
    intro q
    change P q + Q (reciprocalFirst q) = _
    rw [hPpoly q, hQpoly (reciprocalFirst q)]
    rfl
  · intro q hq
    exact (hP q hq.2).add
      (AnalyticAt.comp (f := reciprocalFirst) (hQ (reciprocalFirst q) hq.2)
        (reciprocalFirst_analytic q hq))
  · intro q hq
    have hqB : q ∈ annularOpen B := annularClosed_subset_open hr0 hrB hq
    have hqp : q ∈ PuncturedDbarOne.annularClosed r := ⟨hq.1.1, hq.2⟩
    have hqm := reciprocalFirst_mem_one_closed hr0 hq
    change ‖(P q + Q (reciprocalFirst q)) - f q‖ < ε
    rw [← heq q hqB]
    change ‖(P q + Q (reciprocalFirst q)) - (p q + m (reciprocalFirst q))‖ < ε
    rw [show (P q + Q (reciprocalFirst q)) - (p q + m (reciprocalFirst q)) =
      (P q - p q) + (Q (reciprocalFirst q) - m (reciprocalFirst q)) by ring]
    calc
      _ ≤ ‖P q - p q‖ + ‖Q (reciprocalFirst q) - m (reciprocalFirst q)‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hPe q hqp) (hQe (reciprocalFirst q) hqm)
      _ = ε := by ring

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne
