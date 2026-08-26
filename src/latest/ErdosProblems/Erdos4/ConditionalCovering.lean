import ErdosProblems.Erdos4.TupleSurvivalBounds
import ErdosProblems.Erdos4.DirectMoments

/-!
# Conditional noncoverage from the proved tuple moments

The finite direct-moment inequality is applied to the actual surviving
tuple masses. The argument permits zero tuple normalizers at individual
random-sieve outcomes. A positive total first moment makes the averaged
denominator positive, allowing the explicit three-moment bounds to be
substituted rigorously.
-/

open scoped BigOperators

namespace Erdos4.ConditionalCovering

open RandomResidueSieve AffineTuples TupleCollisionMass ConditionalTupleMoments
open TupleSurvivalBounds

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem mean_add (q : ℕ) (f g : (∀ l, ZMod (ell l)) → ℝ) :
    mean ell q (fun a => f a + g a) = mean ell q f + mean ell q g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sq_le_mean_square (q : ℕ) (f : (∀ l, ZMod (ell l)) → ℝ) :
    mean ell q f ^ 2 ≤ mean ell q (fun a => f a ^ 2) := by
  have hh := DirectMoments.weighted_sq_sum_le Finset.univ (conditionalWeight ell q) f (fun _ => 1)
    (fun a _ha => conditionalWeight_nonneg ell q a) (fun _ _ => zero_le_one)
    (fun _ _ hzero => by norm_num at hzero)
  simpa only [div_one, mul_one, sum_conditionalWeight, mean] using hh

variable {k : ℕ}

noncomputable def miss (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (q : ℕ) (a : ∀ l, ZMod (ell l)) : ℝ :=
  ∏ p : sources, (1 - hittingMass ell h p Y (μ p) q a / tupleMass ell h p Y (μ p) a)

theorem mean_miss_le (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (q : ℕ)
    (hμ0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n) :
    mean ell q (miss ell h sources Y μ q) ≤
      1 - (mean ell q (fun a => ∑ p : sources, hittingMass ell h p Y (μ p) q a)) ^ 2 /
        mean ell q (fun a => (∑ p : sources, hittingMass ell h p Y (μ p) q a) ^ 2 +
          ∑ p : sources, tupleMass ell h p Y (μ p) a * hittingMass ell h p Y (μ p) q a) := by
  exact DirectMoments.mean_miss_le_moment_ratio Finset.univ (Finset.univ : Finset sources)
    (conditionalWeight ell q) (fun a p => tupleMass ell h p Y (μ p) a)
    (fun a p => hittingMass ell h p Y (μ p) q a)
    (fun a _ha => conditionalWeight_nonneg ell q a) (sum_conditionalWeight ell q)
    (fun a _ha p _hp => tupleMass_nonneg ell h p Y (μ p) (hμ0 p p.property) a)
    (fun a _ha p _hp => hittingMass_nonneg ell h p Y (μ p) q (hμ0 p p.property) a)
    (fun a _ha p _hp => hittingMass_le_tupleMass ell h p Y (μ p) q (hμ0 p p.property) a)

theorem mean_miss_le_of_moments (h : Fin k → ℕ) (sources : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (q : ℕ)
    (hμ0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    {a D : ℝ} (ha : 0 < a)
    (hfirst : a ≤ mean ell q (fun o => ∑ p : sources, hittingMass ell h p Y (μ p) q o))
    (hupper : mean ell q (fun o => (∑ p : sources, hittingMass ell h p Y (μ p) q o) ^ 2) +
      mean ell q (fun o => ∑ p : sources,
        tupleMass ell h p Y (μ p) o * hittingMass ell h p Y (μ p) q o) ≤ D) :
    mean ell q (miss ell h sources Y μ q) ≤ 1 - a ^ 2 / D := by
  let Z := fun o => ∑ p : sources, hittingMass ell h p Y (μ p) q o
  let H := fun o => ∑ p : sources, tupleMass ell h p Y (μ p) o * hittingMass ell h p Y (μ p) q o
  have hH : 0 ≤ mean ell q H := mean_nonneg ell q H (fun o =>
    Finset.sum_nonneg (fun p _hp => mul_nonneg
      (tupleMass_nonneg ell h p Y (μ p) (hμ0 p p.property) o)
      (hittingMass_nonneg ell h p Y (μ p) q (hμ0 p p.property) o)))
  have hZpos : 0 < mean ell q Z := ha.trans_le hfirst
  have hJ := mean_sq_le_mean_square ell q Z
  have hdenpos : 0 < mean ell q (fun o => Z o ^ 2 + H o) := by
    rw [mean_add]
    exact (sq_pos_of_pos hZpos).trans_le (hJ.trans (le_add_of_nonneg_right hH))
  have hdenle : mean ell q (fun o => Z o ^ 2 + H o) ≤ D := by
    rw [mean_add]
    exact hupper
  have hDpos : 0 < D := hdenpos.trans_le hdenle
  have hsq : a ^ 2 ≤ mean ell q Z ^ 2 := (sq_le_sq₀ ha.le hZpos.le).mpr hfirst
  have hratio : a ^ 2 / D ≤ mean ell q Z ^ 2 / mean ell q (fun o => Z o ^ 2 + H o) := by
    calc
      _ ≤ mean ell q Z ^ 2 / D := div_le_div_of_nonneg_right hsq hDpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hdenpos hdenle
  exact (mean_miss_le ell h sources Y μ q hμ0).trans (sub_le_sub_left hratio 1)

/-- Explicit noncoverage bound after inserting all three proved moments. -/
theorem mean_miss_le_three_moments (K : ℕ) (sources : Finset ℕ) (Y B : ℕ)
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
      1 - ((1 - ε) * UnitFourier.unitDensity ell ^ (k - 1) * τ) ^ 2 /
        (((1 + ε) * UnitFourier.unitDensity ell ^ (2 * k - 2)) * τ ^ 2 +
          ((1 + ε) * UnitFourier.unitDensity ell ^ (2 * k - 1) + ((k : ℝ) + (k : ℝ) ^ 2) * α) * τ) := by
  dsimp only
  have hV := UnitFourier.unitDensity_pos ell
  have hmom := three_moments ell K sources Y B μ q hε0 hα hacc hs hpoints hμ0 hμ hμsum
  apply mean_miss_le_of_moments ell (AffineWeights.shift K) sources Y μ q hμ0
    (mul_pos (mul_pos (sub_pos.mpr hε1) (pow_pos hV _)) hτ) hmom.1
  exact (add_le_add hmom.2.1 hmom.2.2).trans_eq (by ring)

end Erdos4.ConditionalCovering
