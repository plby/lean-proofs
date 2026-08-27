import ErdosProblems.Erdos4.FGKMTFullTupleMomentBounds
import ErdosProblems.Erdos4.FGKMTWeightedNormalizerLoss

/-! The actual weighted loss from discarding full-tuple normalizers outside [1/2,3/2]. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical AffineTuples TupleCollisionMass ConditionalTupleMoments TupleSurvivalBounds

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime] {k : ℕ}

theorem sieve_unitDensity_le_one : UnitFourier.unitDensity ell ≤ 1 := by
  unfold UnitFourier.unitDensity
  apply Finset.prod_le_one
  · intro l _
    have hl : (1 : ℝ) ≤ ell l := by exact_mod_cast (Fact.out : (ell l).Prime).one_le
    exact div_nonneg (sub_nonneg.mpr hl) (Nat.cast_nonneg _)
  · intro l _
    have hl : (0 : ℝ) < ell l := by exact_mod_cast (Fact.out : (ell l).Prime).pos
    apply (div_le_one hl).mpr
    linarith

theorem full_tuple_normalizer_deviation (hk : 1 ≤ k)
    (h : Fin k → ℕ) (hh : Function.Injective h) {p : ℕ} (hp : 0 < p)
    (Y B : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (hacc : Accurate ell B (3 * k) ε)
    (hpoints : ∀ n ∈ Finset.Icc 1 Y, ∀ t ∈ tuple h p n, t ≤ B)
    (hμ0 : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n)
    (hμsum : ∑ n ∈ Finset.Icc 1 Y, μ n = 1)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α) :
    let σ := UnitFourier.unitDensity ell
    mean ell q (fun a => (tupleMass ell h p Y μ a / σ ^ k - 1) ^ 2 *
      (hittingMass ell h p Y μ q a / σ ^ (k - 1))) ≤
        (4 * ε + 5 * ((k : ℝ) ^ 2 * α / σ ^ (3 * k - 1))) * hitMass h p Y μ q := by
  let σ := UnitFourier.unitDensity ell
  let β := hitMass h p Y μ q
  let δ := (k : ℝ) ^ 2 * α / σ ^ (3 * k - 1)
  have hσ : 0 < σ := UnitFourier.unitDensity_pos ell
  have hσ1 : σ ≤ 1 := sieve_unitDensity_le_one ell
  have hβ : 0 ≤ β := hitMass_nonneg h p Y μ q hμ0
  have hkα : 0 ≤ (k : ℝ) ^ 2 * α := mul_nonneg (sq_nonneg _) hα
  have hpow : σ ^ (3 * k - 1) ≤ 1 := by
    simpa using pow_le_pow_left₀ hσ.le hσ1 (3 * k - 1)
  have hδ : (k : ℝ) ^ 2 * α ≤ δ := by
    apply (le_div_iff₀ (pow_pos hσ _)).mpr
    exact mul_le_of_le_one_right hkα hpow
  have hδeq : δ * σ ^ (3 * k - 1) = (k : ℝ) ^ 2 * α :=
    div_mul_cancel₀ _ (pow_pos hσ _).ne'
  have hst : σ ^ k * σ ^ (k - 1) = σ ^ (2 * k - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hs2t : (σ ^ k) ^ 2 * σ ^ (k - 1) = σ ^ (3 * k - 1) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hmom := full_tuple_mixed_moment_bounds ell h hh hp Y B μ q hε0 hε1 hα
    hacc hpoints hμ0 hμsum hμ
  change _ ≤ (4 * ε + 5 * δ) * β
  apply (conditionalResidueLaw ell q).normalized_weighted_deviation
    (tupleMass ell h p Y μ) (hittingMass ell h p Y μ q)
    (pow_pos hσ k) (pow_pos hσ (k - 1))
  · exact hmom.1
  · rw [hst]
    have hcoef : 1 - ε - δ ≤ (1 - ε) * (1 - (k : ℝ) ^ 2 * α) := by
      nlinarith [mul_nonneg hε0 hkα]
    calc
      _ ≤ ((1 - ε) * (1 - (k : ℝ) ^ 2 * α)) * σ ^ (2 * k - 1) * β :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hσ.le _)) hβ
      _ = ((1 - ε) * σ ^ (2 * k - 1) * (1 - (k : ℝ) ^ 2 * α)) * β := by ring
      _ ≤ _ := hmom.2.1
  · rw [hs2t]
    have heq : (1 + ε + 3 * δ) * σ ^ (3 * k - 1) =
        (1 + ε) * σ ^ (3 * k - 1) + 3 * (k : ℝ) ^ 2 * α := by
      nlinarith [hδeq]
    rw [heq]
    exact hmom.2.2

theorem full_tuple_bad_normalizer_loss (hk : 1 ≤ k)
    (h : Fin k → ℕ) (hh : Function.Injective h) {p : ℕ} (hp : 0 < p)
    (Y B : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (hacc : Accurate ell B (3 * k) ε)
    (hpoints : ∀ n ∈ Finset.Icc 1 Y, ∀ t ∈ tuple h p n, t ≤ B)
    (hμ0 : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n)
    (hμsum : ∑ n ∈ Finset.Icc 1 Y, μ n = 1)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α) :
    let σ := UnitFourier.unitDensity ell
    mean ell q (fun a => if (1 / 2 : ℝ) < |tupleMass ell h p Y μ a / σ ^ k - 1| then
      hittingMass ell h p Y μ q a / σ ^ (k - 1) else 0) ≤
        (16 * ε + 20 * ((k : ℝ) ^ 2 * α / σ ^ (3 * k - 1))) * hitMass h p Y μ q := by
  let σ := UnitFourier.unitDensity ell
  have hσ : 0 < σ := UnitFourier.unitDensity_pos ell
  have hhbound := (conditionalResidueLaw ell q).bad_normalizer_weighted_loss
    (fun a => tupleMass ell h p Y μ a / σ ^ k)
    (fun a => hittingMass ell h p Y μ q a / σ ^ (k - 1))
    (fun a => div_nonneg (hittingMass_nonneg ell h p Y μ q hμ0 a) (pow_nonneg hσ.le _))
    (full_tuple_normalizer_deviation ell hk h hh hp Y B μ q hε0 hε1 hα hacc hpoints hμ0 hμsum hμ)
  exact hhbound.trans_eq (by ring)

end Erdos4.FGKMT
