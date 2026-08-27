import ErdosProblems.Erdos4.FGKMTRoundError

/-! Uniform bounds on selected hit probabilities and their squares. -/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

theorem selection_event_le (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {κ t : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (ht : t ≤ 1 / 2)
    (hp : ∀ v, κ ≤ p v) (hsize : ∀ e, 0 < μ.weight e → e.card ≤ r)
    (W : Finset V) (E : Finset V → Prop) (hE : ¬E ∅) :
    (selectLaw μ p (fun v => hκ0.trans_le (hp v)) t W).prob E ≤ 2 * μ.prob E / κ ^ r := by
  classical
  have hp0 : ∀ v, 0 < p v := fun v => hκ0.trans_le (hp v)
  rw [selectLaw_event μ p hp0 (by linarith : t < 1) W E hE]
  by_cases hgood : |normalizer μ p W - 1| ≤ t
  · rw [if_pos hgood]
    have hlow : (1 / 2 : ℝ) ≤ normalizer μ p W := by
      have hh := (abs_le.mp hgood).1
      linarith
    calc
      _ ≤ eventNumerator μ p W E / (1 / 2) := div_le_div_of_nonneg_left
        (eventNumerator_nonneg μ p hp0 W E) (by norm_num) hlow
      _ ≤ (μ.prob E / κ ^ r) / (1 / 2) := div_le_div_of_nonneg_right
        (eventNumerator_le μ p hκ0 hκ1 hp hsize W E) (by norm_num)
      _ = _ := by ring
  · rw [if_neg hgood]
    exact div_nonneg (mul_nonneg (by norm_num) (μ.prob_nonneg E)) (pow_pos hκ0 r).le

theorem selection_meeting_le (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    {κ t σ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (ht : t ≤ 1 / 2)
    (hp : ∀ v, κ ≤ p v) (hsize : ∀ e, 0 < μ.weight e → e.card ≤ r)
    (hsparse : ∀ v, μ.prob (fun e => v ∈ e) ≤ σ) (W T : Finset V) :
    (selectLaw μ p (fun v => hκ0.trans_le (hp v)) t W).prob (fun e => ¬Disjoint T e) ≤
      2 * (T.card : ℝ) * σ / κ ^ r := by
  have hh := selection_event_le μ p hκ0 hκ1 ht hp hsize W
    (fun e => ¬Disjoint T e) (by simp)
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left (meeting_prob_le μ T hsparse) (by norm_num : (0 : ℝ) ≤ 2)
  exact (div_le_div_of_nonneg_right hm (pow_pos hκ0 r).le).trans_eq (by ring)

theorem selection_meeting_sq_sum (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    {κ t δ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (ht : t ≤ 1 / 2)
    (hp : ∀ v, κ ≤ p v) (hsize : ∀ i e, 0 < (μ i).weight e → e.card ≤ r)
    (σ : I → ℝ) (hsparse : ∀ i v, (μ i).prob (fun e => v ∈ e) ≤ σ i)
    (hsq : (∑ i, σ i ^ 2) ≤ δ ^ 2) (W T : Finset V) :
    (∑ i, (selectLaw (μ i) p (fun v => hκ0.trans_le (hp v)) t W).prob
        (fun e => ¬Disjoint T e) ^ 2) ≤ 4 * (T.card : ℝ) ^ 2 * δ ^ 2 / κ ^ (2 * r) := by
  calc
    _ ≤ ∑ i, (2 * (T.card : ℝ) * σ i / κ ^ r) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact pow_le_pow_left₀ ((selectLaw (μ i) p _ t W).prob_nonneg _)
        (selection_meeting_le (μ i) p hκ0 hκ1 ht hp (hsize i) (hsparse i) W T) 2
    _ = (4 * (T.card : ℝ) ^ 2 / κ ^ (2 * r)) * ∑ i, σ i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      have hpow : κ ^ (2 * r) = (κ ^ r) ^ 2 := by rw [Nat.mul_comm 2 r, pow_mul]
      rw [hpow]
      ring
    _ ≤ (4 * (T.card : ℝ) ^ 2 / κ ^ (2 * r)) * δ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

end Erdos4.FGKMT
