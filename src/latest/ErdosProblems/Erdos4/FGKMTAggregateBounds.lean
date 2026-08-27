import ErdosProblems.Erdos4.FGKMTDegreeMoments
import ErdosProblems.Erdos4.FGKMTSelectionBounds

/-! Aggregate source-hit and normalization-error estimates. -/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

theorem aggregate_meeting_prob_le (μ : I → FiniteLaw (Finset V)) (T : Finset V) :
    (∑ i, (μ i).prob (fun e => ¬Disjoint T e)) ≤ ∑ v ∈ T, vertexDegree μ v := by
  calc
    _ ≤ ∑ i, ∑ v ∈ T, (μ i).prob (fun e => v ∈ e) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hh := (μ i).prob_exists_finset_le T (fun v e => v ∈ e)
      have heq : (μ i).prob (fun e => ¬Disjoint T e) =
          (μ i).prob (fun e => ∃ v ∈ T, v ∈ e) := by
        apply le_antisymm
        · exact (μ i).prob_mono (fun e he => Finset.not_disjoint_iff.mp he)
        · exact (μ i).prob_mono (fun e he => Finset.not_disjoint_iff.mpr he)
      rw [heq]
      exact hh
    _ = _ := Finset.sum_comm

theorem aggregate_meeting_prob_le_card (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    {D : ℝ} (hD0 : 0 ≤ D) (hp0 : ∀ v, 0 < p v) (hp1 : ∀ v, p v ≤ 1)
    (hD : ∀ v, vertexDegree μ v / p v ≤ D) (T : Finset V) :
    (∑ i, (μ i).prob (fun e => ¬Disjoint T e)) ≤ (T.card : ℝ) * D := by
  calc
    _ ≤ ∑ v ∈ T, vertexDegree μ v := aggregate_meeting_prob_le μ T
    _ ≤ ∑ _v ∈ T, D := by
      apply Finset.sum_le_sum
      intro v _hv
      have hh := (div_le_iff₀ (hp0 v)).mp (hD v)
      exact hh.trans (mul_le_of_le_one_right hD0 (hp1 v))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

noncomputable def normalizationError (r : ℕ) (κ δ ε t : ℝ) : ℝ :=
  2 * t + (3 * ε + (1 + ε) * (r : ℝ) * δ / κ ^ r) / t ^ 2

theorem normalizationError_nonneg (r : ℕ) {κ δ ε t : ℝ}
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    0 ≤ normalizationError r κ δ ε t := by
  unfold normalizationError
  positivity

theorem aggregate_normalization_error (ν : FiniteLaw (Finset V))
    (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    {r : ℕ} {κ δ ε t D : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) (hD0 : 0 ≤ D)
    (hp : ∀ v, κ ≤ p v) (hp1 : ∀ v, p v ≤ 1)
    (hsize : ∀ i e, 0 < (μ i).weight e → e.card ≤ r)
    (hsparse : ∀ i v, (μ i).prob (fun e => v ∈ e) ≤ δ)
    (hD : ∀ v, vertexDegree μ v / p v ≤ D)
    (hacc : SurvivalAccurate ν p (2 * r) ε) (T : Finset V) :
    ν.mean (fun W => ∑ i,
      |(selectLaw (μ i) p (fun v => hκ0.trans_le (hp v)) t W).prob (fun e => ¬Disjoint T e) -
        eventNumerator (μ i) p W (fun e => ¬Disjoint T e)|) ≤
      normalizationError r κ δ ε t * (T.card : ℝ) * D / κ ^ r := by
  have hK := normalizationError_nonneg r hκ0 hδ hε ht0.le
  rw [FiniteLaw.mean_finset_sum]
  calc
    _ ≤ ∑ i, normalizationError r κ δ ε t *
        ((μ i).prob (fun e => ¬Disjoint T e) / κ ^ r) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mean_selection_event_error ν (μ i) p hκ0 hκ1 ht0 ht1 hδ hε hp
        (hsize i) (hsparse i) hacc (fun e => ¬Disjoint T e) (by simp)
    _ = normalizationError r κ δ ε t *
        (∑ i, (μ i).prob (fun e => ¬Disjoint T e)) / κ ^ r := by
      rw [← Finset.mul_sum, ← Finset.sum_div]
      ring
    _ ≤ normalizationError r κ δ ε t * ((T.card : ℝ) * D) / κ ^ r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (aggregate_meeting_prob_le_card μ p hD0 (fun v => hκ0.trans_le (hp v)) hp1 hD T) hK)
        (pow_pos hκ0 r).le
    _ = _ := by ring

end Erdos4.FGKMT
