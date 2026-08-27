import ErdosProblems.Erdos4.FGKMTFullTupleDegreeMoments
import ErdosProblems.Erdos4.FGKMTWeightedNormalizerLoss
import ErdosProblems.Erdos4.FGKMTLawMoments

/-! Concentration of total pinned-target incidence and its retained good-source part. -/

open scoped BigOperators

namespace Erdos4.FGKMT.FiniteLaw

variable {Ω : Type*} [Fintype Ω] (ν : Erdos4.FGKMT.FiniteLaw Ω)

theorem prob_or_le (E F : Ω → Prop) :
    ν.prob (fun o => E o ∨ F o) ≤ ν.prob E + ν.prob F := by
  classical
  rw [prob_eq_mean, prob_eq_mean, prob_eq_mean, ← mean_add]
  apply ν.mean_mono
  intro o
  by_cases he : E o <;> by_cases hf : F o <;> simp [he, hf]

theorem lower_half_tail (Z : Ω → ℝ) {β A : ℝ} (hβ : 0 < β)
    (hA : ν.mean (fun o => (Z o - β) ^ 2) ≤ A) :
    ν.prob (fun o => Z o < β / 2) ≤ 4 * A / β ^ 2 := by
  have hsub : ν.prob (fun o => Z o < β / 2) ≤
      ν.prob (fun o => β / 2 ≤ |Z o - β|) := by
    apply ν.prob_mono
    intro o ho
    have hh := neg_le_abs (Z o - β)
    linarith
  calc
    _ ≤ _ := hsub
    _ ≤ ν.mean (fun o => (Z o - β) ^ 2) / (β / 2) ^ 2 := ν.chebyshev Z β (by positivity)
    _ ≤ A / (β / 2) ^ 2 := div_le_div_of_nonneg_right hA (sq_nonneg _)
    _ = _ := by field_simp; ring

theorem upper_quarter_tail (Z : Ω → ℝ) (hZ : ∀ o, 0 ≤ Z o) {β e : ℝ} (hβ : 0 < β)
    (hmean : ν.mean Z ≤ e * β) :
    ν.prob (fun o => β / 4 < Z o) ≤ 4 * e := by
  calc
    _ ≤ ν.mean Z / (β / 4) := ν.prob_le_of_lower _ Z (by positivity) hZ (fun o ho => ho.le)
    _ ≤ (e * β) / (β / 4) := div_le_div_of_nonneg_right hmean (by positivity)
    _ = _ := by field_simp

theorem retained_degree_lower_tail (Z D : Ω → ℝ) (hD : ∀ o, 0 ≤ D o)
    {β A e : ℝ} (hβ : 0 < β)
    (hvariance : ν.mean (fun o => (Z o - β) ^ 2) ≤ A) (hloss : ν.mean D ≤ e * β) :
    ν.prob (fun o => Z o - D o < β / 4) ≤ 4 * A / β ^ 2 + 4 * e := by
  calc
    _ ≤ ν.prob (fun o => Z o < β / 2 ∨ β / 4 < D o) := by
      apply ν.prob_mono
      intro o ho
      by_contra hh
      push_neg at hh
      linarith
    _ ≤ ν.prob (fun o => Z o < β / 2) + ν.prob (fun o => β / 4 < D o) := ν.prob_or_le _ _
    _ ≤ _ := add_le_add (ν.lower_half_tail Z hβ hvariance) (ν.upper_quarter_tail D hD hβ hloss)

end Erdos4.FGKMT.FiniteLaw

namespace Erdos4.FGKMT

open AffineTuples TupleCollisionMass ConditionalTupleMoments TupleSurvivalBounds

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime] {k : ℕ}

theorem full_tuple_total_variance (h : Fin k → ℕ) (hh : Function.Injective h)
    (sources : Finset ℕ) (Y B : ℕ) (μ : ℕ → ℕ → ℝ) (q : ℕ)
    {ε α : ℝ} (hε : 0 ≤ ε) (hα : 0 ≤ α)
    (hacc : Accurate ell B (3 * k) ε)
    (hs : ∀ p ∈ sources, p.Prime ∧ ∀ i, h i < p)
    (hpoints : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, ∀ t ∈ tuple h p n, t ≤ B)
    (hμ0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, μ p n ≤ α) :
    let σ := UnitFourier.unitDensity ell
    let β := ∑ p : sources, hitMass h p Y (μ p) q
    mean ell q (fun a =>
      ((∑ p : sources, hittingMass ell h p Y (μ p) q a) / σ ^ (k - 1) - β) ^ 2) ≤
        3 * ε * β ^ 2 + (k : ℝ) * α * β / σ ^ (2 * k - 2) := by
  let σ := UnitFourier.unitDensity ell
  let β := ∑ p : sources, hitMass h p Y (μ p) q
  let Z := fun a => ∑ p : sources, hittingMass ell h p Y (μ p) q a
  let ν := conditionalResidueLaw ell q
  have hσ : 0 < σ := UnitFourier.unitDensity_pos ell
  have hβ : 0 ≤ β := Finset.sum_nonneg (fun p _ => hitMass_nonneg h p Y (μ p) q (hμ0 p p.property))
  have hpow : (σ ^ (k - 1)) ^ 2 = σ ^ (2 * k - 2) := by
    rw [← pow_mul]
    congr 1
    omega
  have hmom := full_tuple_total_moment_bounds ell h hh sources Y B μ q hε hα hacc hs hpoints hμ0 hμ
  have hfirst : (1 - ε) * β ≤ ν.mean (fun a => Z a / σ ^ (k - 1)) := by
    rw [FiniteLaw.mean_div_const]
    apply (le_div_iff₀ (pow_pos hσ _)).mpr
    exact (show (1 - ε) * β * σ ^ (k - 1) = (1 - ε) * σ ^ (k - 1) * β by ring).le.trans hmom.1
  have hsecond : ν.mean (fun a => (Z a / σ ^ (k - 1)) ^ 2) ≤
      (1 + ε) * β ^ 2 + (k : ℝ) * α * β / σ ^ (2 * k - 2) := by
    simp only [div_pow, FiniteLaw.mean_div_const, hpow]
    calc
      _ ≤ ((1 + ε) * σ ^ (2 * k - 2) * β ^ 2 + (k : ℝ) * α * β) / σ ^ (2 * k - 2) :=
        div_le_div_of_nonneg_right hmom.2 (pow_nonneg hσ.le _)
      _ = _ := by field_simp
  change ν.mean (fun a => (Z a / σ ^ (k - 1) - β) ^ 2) ≤ _
  rw [FiniteLaw.mean_sq_sub]
  have hhfirst := mul_le_mul_of_nonneg_left hfirst hβ
  nlinarith

end Erdos4.FGKMT
