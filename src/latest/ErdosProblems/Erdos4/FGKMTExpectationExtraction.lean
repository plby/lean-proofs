import ErdosProblems.Erdos4.FGKMTProcessSupport

/-! From a survivor law to a deterministic legal covering. -/

open scoped BigOperators

namespace Erdos4.FGKMT.FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem exists_support_le_mean (ν : FiniteLaw Ω) (f : Ω → ℝ) :
    ∃ o, 0 < ν.weight o ∧ f o ≤ ν.mean f := by
  have htotalpos : 0 < ∑ o, ν.weight o := by rw [ν.total]; norm_num
  obtain ⟨o₀, ho₀, hpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun o _ho => ν.nonneg o)).mp htotalpos
  by_contra hnone
  have hstrict : ∀ o, 0 < ν.weight o → ν.mean f < f o := by
    intro o ho
    exact lt_of_not_ge (fun hle => hnone ⟨o, ho, hle⟩)
  have hpoint (o : Ω) : ν.weight o * ν.mean f ≤ ν.weight o * f o := by
    by_cases hz : ν.weight o = 0
    · simp [hz]
    · have hp : 0 < ν.weight o := lt_of_le_of_ne (ν.nonneg o) (Ne.symm hz)
      exact mul_le_mul_of_nonneg_left (hstrict o hp).le hp.le
  have hh := Finset.sum_lt_sum (fun o _ho => hpoint o)
    ⟨o₀, ho₀, mul_lt_mul_of_pos_left (hstrict o₀ hpos) hpos⟩
  change ν.mean (fun _ => ν.mean f) < ν.mean f at hh
  rw [ν.mean_const] at hh
  exact (lt_irrefl _) hh

end Erdos4.FGKMT.FiniteLaw

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem survivor_mean_card (ν : FiniteLaw (Finset V)) :
    ν.mean (fun W => (W.card : ℝ)) = ∑ v, survival ν {v} := by
  have hcard (W : Finset V) : (W.card : ℝ) = ∑ v : V, if v ∈ W then (1 : ℝ) else 0 := by
    simp
  calc
    _ = ν.mean (fun W => ∑ v : V, if v ∈ W then (1 : ℝ) else 0) := ν.mean_congr hcard
    _ = ∑ v, ν.mean (fun W => if v ∈ W then (1 : ℝ) else 0) := ν.mean_finset_sum _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _hv
      unfold survival
      rw [FiniteLaw.prob_eq_mean]
      apply ν.mean_congr
      intro W
      simp only [Finset.singleton_subset_iff]

theorem survivor_mean_card_le (ν : FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) {A : ℕ} {ε : ℝ} (hA : 1 ≤ A)
    (hacc : SurvivalAccurate ν p A ε) :
    ν.mean (fun W => (W.card : ℝ)) ≤ (1 + ε) * ∑ v, p v := by
  rw [survivor_mean_card, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _hv
  have hh := (abs_le.mp (hacc {v} (by simpa using hA))).2
  have heq : setProduct p {v} = p v := by simp [setProduct]
  rw [heq] at hh
  apply (div_le_iff₀ (hp v)).mp
  linarith

theorem exists_legal_cover (μ : ℕ → I → FiniteLaw (Finset V)) (t : ℕ → ℝ)
    {m A : ℕ} {ε : ℝ} (hA : 1 ≤ A)
    (hacc : SurvivalAccurate (survivorProcess μ t m) (modelSequence μ m) A ε) :
    ∃ choice : ℕ → I → Finset V,
      (∀ j < m, ∀ i, choice j i = ∅ ∨ 0 < (μ j i).weight (choice j i)) ∧
      ((Finset.univ \ coveredThrough choice m).card : ℝ) ≤
        (1 + ε) * ∑ v, modelSequence μ m v := by
  obtain ⟨W, hW, hcard⟩ := (survivorProcess μ t m).exists_support_le_mean
    (fun W => (W.card : ℝ))
  obtain ⟨choice, heq, hlegal⟩ := survivorProcess_legal μ t m W hW
  refine ⟨choice, hlegal, ?_⟩
  rw [← heq]
  exact hcard.trans (survivor_mean_card_le (survivorProcess μ t m) (modelSequence μ m)
    (modelSequence_pos μ m) hA hacc)

end Erdos4.FGKMT
