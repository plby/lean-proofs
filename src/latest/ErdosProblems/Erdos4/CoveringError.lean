import ErdosProblems.Erdos4.ConditionalCovering

/-!
# Explicit error in the conditional covering estimate

The noncoverage bound is the sum of the survival approximation error,
the inverse exposure ratio, and the small-atom collision error. This
form needs no upper bound on the total exposure.
-/

open scoped BigOperators

namespace Erdos4.CoveringError

theorem elementary_ratio_bound {ε r e : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hr : 0 ≤ r) (he : 0 ≤ e) :
    1 - (1 - ε) ^ 2 / (1 + ε + (1 + ε) * r + e) ≤ 3 * ε + 2 * r + e := by
  let D := 1 + ε + (1 + ε) * r + e
  have hD : 1 ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + ε) hr]
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hB : 0 ≤ 3 * ε + 2 * r + e := by positivity
  have hnum : D - (1 - ε) ^ 2 ≤ 3 * ε + 2 * r + e := by
    dsimp [D]
    nlinarith [mul_nonneg (sub_nonneg.mpr hε1) hr]
  have heq : 1 - (1 - ε) ^ 2 / D = (D - (1 - ε) ^ 2) / D := by field_simp
  change 1 - (1 - ε) ^ 2 / D ≤ _
  rw [heq]
  apply (div_le_iff₀ hDpos).mpr
  exact hnum.trans (le_mul_of_one_le_right hB hD)

theorem moment_ratio_bound {k : ℕ} (hk : 1 ≤ k) {σ τ ε α : ℝ}
    (hσ : 0 < σ) (hτ : 0 < τ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α) :
    1 - ((1 - ε) * σ ^ (k - 1) * τ) ^ 2 /
      (((1 + ε) * σ ^ (2 * k - 2)) * τ ^ 2 +
        ((1 + ε) * σ ^ (2 * k - 1) + ((k : ℝ) + (k : ℝ) ^ 2) * α) * τ) ≤
      3 * ε + 2 * σ / τ + (((k : ℝ) + (k : ℝ) ^ 2) * α) / (σ ^ (2 * k - 2) * τ) := by
  have hpow1 : (σ ^ (k - 1)) ^ 2 = σ ^ (2 * k - 2) := by
    rw [← pow_mul]
    congr 1
    omega
  have hpow2 : σ ^ (2 * k - 1) = σ ^ (2 * k - 2) * σ := by
    rw [← pow_succ]
    congr 1
    omega
  let r := σ / τ
  let e := (((k : ℝ) + (k : ℝ) ^ 2) * α) / (σ ^ (2 * k - 2) * τ)
  have hr : 0 ≤ r := (div_pos hσ hτ).le
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hden : 0 < 1 + ε + (1 + ε) * r + e := by positivity
  have heq : ((1 - ε) * σ ^ (k - 1) * τ) ^ 2 /
      (((1 + ε) * σ ^ (2 * k - 2)) * τ ^ 2 +
        ((1 + ε) * σ ^ (2 * k - 1) + ((k : ℝ) + (k : ℝ) ^ 2) * α) * τ) =
        (1 - ε) ^ 2 / (1 + ε + (1 + ε) * r + e) := by
    have hraw : 0 < ((1 + ε) * σ ^ (2 * k - 2)) * τ ^ 2 +
        ((1 + ε) * σ ^ (2 * k - 1) + ((k : ℝ) + (k : ℝ) ^ 2) * α) * τ := by positivity
    rw [mul_pow, mul_pow, hpow1, hpow2]
    dsimp [r, e] at hden ⊢
    field_simp
    <;> ring
  rw [heq]
  exact (elementary_ratio_bound hε0 hε1 hr he).trans_eq (by dsimp [r, e]; ring)

open RandomResidueSieve AffineTuples TupleCollisionMass ConditionalTupleMoments
open TupleSurvivalBounds ConditionalCovering

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

/-- The actual finite conditional noncoverage estimate. -/
theorem mean_miss_le_explicit (hk : 1 ≤ k) (K : ℕ) (sources : Finset ℕ) (Y B : ℕ)
    (μ : ℕ → ℕ → ℝ) (q : ℕ) {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hα : 0 ≤ α)
    (hacc : Accurate ell B (2 * k) ε)
    (hs : ∀ p ∈ sources, p.Prime ∧ K < p ∧ k ≤ p)
    (hpoints : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y,
      ∀ y ∈ tuple (AffineWeights.shift K : Fin k → ℕ) p n, y ≤ B)
    (hμ0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, μ p n ≤ α)
    (hμsum : ∀ p ∈ sources, ∑ n ∈ Finset.Icc 1 Y, μ p n = 1)
    (hτ : 0 < ∑ p : sources, hitMass (AffineWeights.shift K : Fin k → ℕ) p Y (μ p) q) :
    let h : Fin k → ℕ := AffineWeights.shift K
    let τ := ∑ p : sources, hitMass h p Y (μ p) q
    mean ell q (miss ell h sources Y μ q) ≤
      3 * ε + 2 * UnitFourier.unitDensity ell / τ +
        (((k : ℝ) + (k : ℝ) ^ 2) * α) / (UnitFourier.unitDensity ell ^ (2 * k - 2) * τ) := by
  exact (mean_miss_le_three_moments ell K sources Y B μ q hε0 hε1 hα hacc hs hpoints
    hμ0 hμ hμsum hτ).trans (moment_ratio_bound hk (UnitFourier.unitDensity_pos ell) hτ
      hε0 hε1.le hα)

end Erdos4.CoveringError
