import ErdosProblems.Erdos4.FGKMTInitialDegreeConcentration
import ErdosProblems.Erdos4.FGKMTFullTupleNormalizerLoss

/-! The finite conditional lower-tail bound after discarding bad full-tuple normalizers. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical AffineTuples TupleCollisionMass ConditionalTupleMoments TupleSurvivalBounds

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime] {k : ℕ}

theorem full_tuple_discarded_total_mean (hk : 1 ≤ k)
    (h : Fin k → ℕ) (hh : Function.Injective h)
    (sources : Finset ℕ) (Y B : ℕ) (μ : ℕ → ℕ → ℝ) (q : ℕ)
    {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (hacc : Accurate ell B (3 * k) ε)
    (hs : ∀ p ∈ sources, 0 < p)
    (hpoints : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, ∀ t ∈ tuple h p n, t ≤ B)
    (hμ0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hμsum : ∀ p ∈ sources, ∑ n ∈ Finset.Icc 1 Y, μ p n = 1)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, μ p n ≤ α) :
    let σ := UnitFourier.unitDensity ell
    mean ell q (fun a => ∑ p : sources,
      if (1 / 2 : ℝ) < |tupleMass ell h p Y (μ p) a / σ ^ k - 1| then
        hittingMass ell h p Y (μ p) q a / σ ^ (k - 1) else 0) ≤
      (16 * ε + 20 * ((k : ℝ) ^ 2 * α / σ ^ (3 * k - 1))) *
        ∑ p : sources, hitMass h p Y (μ p) q := by
  dsimp only
  rw [mean_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  exact full_tuple_bad_normalizer_loss ell hk h hh (hs p p.property) Y B (μ p) q
    hε0 hε1 hα hacc (hpoints p p.property) (hμ0 p p.property)
    (hμsum p p.property) (hμ p p.property)

theorem full_tuple_retained_lower_tail (hk : 1 ≤ k)
    (h : Fin k → ℕ) (hh : Function.Injective h)
    (sources : Finset ℕ) (Y B : ℕ) (μ : ℕ → ℕ → ℝ) (q : ℕ)
    {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (hacc : Accurate ell B (3 * k) ε)
    (hs : ∀ p ∈ sources, p.Prime ∧ ∀ i, h i < p)
    (hpoints : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, ∀ t ∈ tuple h p n, t ≤ B)
    (hμ0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hμsum : ∀ p ∈ sources, ∑ n ∈ Finset.Icc 1 Y, μ p n = 1)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, μ p n ≤ α)
    (hβ : 0 < ∑ p : sources, hitMass h p Y (μ p) q) :
    let σ := UnitFourier.unitDensity ell
    let β := ∑ p : sources, hitMass h p Y (μ p) q
    (conditionalResidueLaw ell q).prob (fun a =>
      (∑ p : sources, hittingMass ell h p Y (μ p) q a) / σ ^ (k - 1) -
        (∑ p : sources,
          if (1 / 2 : ℝ) < |tupleMass ell h p Y (μ p) a / σ ^ k - 1| then
            hittingMass ell h p Y (μ p) q a / σ ^ (k - 1) else 0) < β / 4) ≤
      76 * ε + 4 * (k : ℝ) * α / (σ ^ (2 * k - 2) * β) +
        80 * (k : ℝ) ^ 2 * α / σ ^ (3 * k - 1) := by
  let σ := UnitFourier.unitDensity ell
  let β := ∑ p : sources, hitMass h p Y (μ p) q
  let Z := fun a => (∑ p : sources, hittingMass ell h p Y (μ p) q a) / σ ^ (k - 1)
  let D := fun a => ∑ p : sources,
    if (1 / 2 : ℝ) < |tupleMass ell h p Y (μ p) a / σ ^ k - 1| then
      hittingMass ell h p Y (μ p) q a / σ ^ (k - 1) else 0
  have hσ : 0 < σ := UnitFourier.unitDensity_pos ell
  have hD : ∀ a, 0 ≤ D a := by
    intro a
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact div_nonneg (hittingMass_nonneg ell h p Y (μ p) q (hμ0 p p.property) a)
        (pow_nonneg hσ.le _)
    · exact le_refl 0
  have hv := full_tuple_total_variance ell h hh sources Y B μ q hε0 hα
    hacc hs hpoints hμ0 hμ
  have hd := full_tuple_discarded_total_mean ell hk h hh sources Y B μ q
    hε0 hε1 hα hacc (fun p hp => (hs p hp).1.pos) hpoints hμ0 hμsum hμ
  have ht := (conditionalResidueLaw ell q).retained_degree_lower_tail Z D hD hβ hv hd
  change (conditionalResidueLaw ell q).prob (fun a => Z a - D a < β / 4) ≤ _
  calc
    _ ≤ 4 * (3 * ε * β ^ 2 + (k : ℝ) * α * β / σ ^ (2 * k - 2)) / β ^ 2 +
        4 * (16 * ε + 20 * ((k : ℝ) ^ 2 * α / σ ^ (3 * k - 1))) := ht
    _ = _ := by
      change _ = 76 * ε + 4 * (k : ℝ) * α / (σ ^ (2 * k - 2) * β) +
        80 * (k : ℝ) ^ 2 * α / σ ^ (3 * k - 1)
      have hβ' : β ≠ 0 := hβ.ne'
      field_simp [hσ.ne', hβ']
      <;> ring

end Erdos4.FGKMT
