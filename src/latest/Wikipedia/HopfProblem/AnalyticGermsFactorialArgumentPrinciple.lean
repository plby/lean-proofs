import Wikipedia.HopfProblem.AnalyticGermsFactorialArgumentPrincipleFactorization
import Wikipedia.HopfProblem.AnalyticGermsFactorialArgumentPrincipleCauchy

/-!
# The weighted argument principle on a closed disc

For every natural number `k`, the normalized contour integral of
`w^k * logDeriv f w` is the sum of the `k`th powers of the actual interior
zeros, with their actual analytic multiplicities. The finite zero set and
nonvanishing analytic factor are constructed from the supplied analytic
function; no factorization or preparation theorem is assumed as input.
-/

noncomputable section

open Set Metric Function Complex
open scoped Topology Real BigOperators

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.ArgumentPrinciple

/-- The normalized polynomially weighted logarithmic-derivative integral. -/
def weightedMoment (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (k : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ * ∮ w in C(c, R), w ^ k * logDeriv f w

private theorem circleIntegral_eq_sum_of_factorization
    {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} {t : Finset ℂ}
    (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hg₀ : ∀ z ∈ closedBall c R, g z ≠ 0) (ht : (t : Set ℂ) ⊆ ball c R)
    (hfg : f = fun z ↦ (∏ a ∈ t, (z - a) ^ analyticOrderNatAt f a) * g z) (k : ℕ) :
    (∮ w in C(c, R), w ^ k * logDeriv f w) =
      (2 * Real.pi * Complex.I) * ∑ a ∈ t, (analyticOrderNatAt f a : ℂ) * a ^ k := by
  have hlog := logDeriv_eq_sum_of_factorization hg hg₀ ht hfg
  have heq : EqOn (fun w ↦ w ^ k * logDeriv f w)
      (fun w ↦ (∑ a ∈ t, w ^ k * ((analyticOrderNatAt f a : ℂ) / (w - a))) +
        w ^ k * logDeriv g w) (sphere c R) := by
    intro w hw
    dsimp only
    rw [hlog hw, mul_add, Finset.mul_sum]
  have hi : ∀ a ∈ t,
      CircleIntegrable (fun w ↦ w ^ k * ((analyticOrderNatAt f a : ℂ) / (w - a))) c R := by
    intro a ha
    exact circleIntegrable_pow_mul_div_sub hR (ht ha) (analyticOrderNatAt f a) k
  rw [circleIntegral.integral_congr hR.le heq,
    circleIntegral.integral_add (.fun_sum _ hi) (circleIntegrable_pow_mul_logDeriv hR hg hg₀ k),
    circleIntegral.integral_fun_sum hi, circleIntegral_pow_mul_logDeriv_eq_zero hR hg hg₀ k,
    add_zero, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a ha ↦
    circleIntegral_pow_mul_div_sub hR (ht ha) (analyticOrderNatAt f a) k

private theorem weightedMoment_eq_sum_of_factorization
    {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} {t : Finset ℂ}
    (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hg₀ : ∀ z ∈ closedBall c R, g z ≠ 0) (ht : (t : Set ℂ) ⊆ ball c R)
    (hfg : f = fun z ↦ (∏ a ∈ t, (z - a) ^ analyticOrderNatAt f a) * g z) (k : ℕ) :
    weightedMoment f c R k = ∑ a ∈ t, (analyticOrderNatAt f a : ℂ) * a ^ k := by
  rw [weightedMoment, circleIntegral_eq_sum_of_factorization hR hg hg₀ ht hfg k]
  simp [← mul_assoc, Real.pi_ne_zero]

/-- Actual finite analytic factorization, together with every weighted
argument-principle identity for the same finite zero set. -/
theorem exists_finset_factorization_weightedMoment {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hf₀ : ∀ z ∈ sphere c R, f z ≠ 0) (hR : 0 < R) :
    ∃ t : Finset ℂ,
      (∀ a, a ∈ t ↔ a ∈ ball c R ∧ f a = 0) ∧
      (∀ a ∈ t, 0 < analyticOrderNatAt f a) ∧
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
        (f = fun z ↦ (∏ a ∈ t, (z - a) ^ analyticOrderNatAt f a) * g z) ∧
        (∀ z ∈ closedBall c R, g z ≠ 0) ∧
        (∀ k : ℕ, weightedMoment f c R k =
          ∑ a ∈ t, (analyticOrderNatAt f a : ℂ) * a ^ k) := by
  obtain ⟨t, ht, hm, g, hg, hfg, hg₀⟩ := exists_finset_factorization hf hf₀ hR
  refine ⟨t, ht, hm, g, hg, hfg, hg₀, ?_⟩
  intro k
  exact weightedMoment_eq_sum_of_factorization hR hg hg₀
    (fun a ha ↦ ((ht a).mp ha).1) hfg k

/-- The actual finite zero set, its positive multiplicities, and all
weighted moment identities, without retaining the analytic unit factor. -/
theorem exists_finset_weightedMoment {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hf₀ : ∀ z ∈ sphere c R, f z ≠ 0) (hR : 0 < R) :
    ∃ t : Finset ℂ,
      (∀ a, a ∈ t ↔ a ∈ ball c R ∧ f a = 0) ∧
      (∀ a ∈ t, 0 < analyticOrderNatAt f a) ∧
      (∀ k : ℕ, weightedMoment f c R k =
        ∑ a ∈ t, (analyticOrderNatAt f a : ℂ) * a ^ k) := by
  obtain ⟨t, ht, hm, g, hg, hfg, hg₀, hmoment⟩ :=
    exists_finset_factorization_weightedMoment hf hf₀ hR
  exact ⟨t, ht, hm, hmoment⟩

/-- Weighted argument principle for any finite set proved to be precisely
the actual interior zeros. Its factorization is generated in the proof. -/
theorem weightedMoment_eq_sum {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {t : Finset ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hf₀ : ∀ z ∈ sphere c R, f z ≠ 0) (hR : 0 < R)
    (ht : ∀ a, a ∈ t ↔ a ∈ ball c R ∧ f a = 0) (k : ℕ) :
    weightedMoment f c R k = ∑ a ∈ t, (analyticOrderNatAt f a : ℂ) * a ^ k := by
  obtain ⟨s, hs, hm, hmoment⟩ := exists_finset_weightedMoment hf hf₀ hR
  have hst : s = t := Finset.ext fun a ↦ (hs a).trans (ht a).symm
  simpa only [hst] using hmoment k

/-- The zeroth weighted moment is the total positive zero multiplicity. -/
theorem weightedMoment_zero_eq_sum {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {t : Finset ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hf₀ : ∀ z ∈ sphere c R, f z ≠ 0) (hR : 0 < R)
    (ht : ∀ a, a ∈ t ↔ a ∈ ball c R ∧ f a = 0) :
    weightedMoment f c R 0 = ((∑ a ∈ t, analyticOrderNatAt f a : ℕ) : ℂ) := by
  rw [weightedMoment_eq_sum hf hf₀ hR ht 0]
  simp

end Wikipedia.HopfProblem.AnalyticGermsFactorial.ArgumentPrinciple
