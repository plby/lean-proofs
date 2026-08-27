import Arxiv.Arxiv2411_18291.SharpTypicalityBounds
import Arxiv.Arxiv2411_18291.LocalTypicality

/-! # Corrected Lemma 5.3 at its printed local threshold in every positive rank

The density range, typicality error and local threshold are unchanged.
Only the paper's refuted probability convention is corrected to failure
below `exp(-n^(1/10))`. Rank one is deterministic; all higher ranks also
have simultaneous relative density control at the same threshold.
-/

open MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem typical_failure_stretched_exp_full_local_threshold {r h n : ℕ}
    (hr : 1 ≤ r) (hh : 1 ≤ h) (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
      {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)} <
      Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  obtain ⟨_, hhalf, hδ, hroot⟩ := sharp_local_typicality_size hr hh hn
  have hnr : r + 1 ≤ n := hhalf.trans (Nat.div_le_self n 2)
  have hb := typical_failure_probability_separate (V := Fin n) p
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by linarith only [hδ]) hh
    (by simpa only [Fintype.card_fin] using hnr)
    (by simpa only [Fintype.card_fin] using hroot)
  simp only [Fintype.card_fin] at hb
  exact hb.trans_lt (separate_typicality_failure_bound_local hr hh hn p hp)

theorem typical_density_whp_full_local_threshold {r h n : ℕ}
    (hr : 1 ≤ r) (hh : 1 ≤ h) (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) <
      (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
        {ω | |density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
          IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h} := by
  have hm : MeasurableSet {ω : BernoulliSubset.Sample (Block (Fin n) (r + 1)) |
      |density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h} := (Set.toFinite _).measurableSet
  have he := measureReal_compl (μ := BernoulliSubset.probability (Block (Fin n) (r + 1)) p) hm
  simp only [probReal_univ, Set.compl_ofPred] at he
  have hf := typical_failure_stretched_exp_full_local_threshold hr hh hn p hp
  rw [he] at hf
  linarith only [hf]

/-- The standalone source lemma in every positive edge rank. -/
theorem typical_paper_whp_corrected_local_all_ranks {r h n : ℕ}
    (hh : 1 ≤ h) (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) <
      (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
        {ω | IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h} := by
  by_cases hr : r = 0
  · subst r
    rw [rankOne_typical_probability (Real.rpow_nonneg (Nat.cast_nonneg n) _) p]
    linarith only [Real.exp_pos (-((n : ℝ) ^ (1 / 10 : ℝ)))]
  · exact (typical_density_whp_full_local_threshold (by omega) hh hn p hp).trans_le
      (measureReal_mono (by intro ω hω; exact hω.2))

theorem exists_typicalGraph_density_full_local_threshold {r h n : ℕ}
    (hr : 1 ≤ r) (hh : 1 ≤ h) (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    ∃ G : Hypergraph (Fin n) (r + 1),
      |density G - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical G ((n : ℝ) ^ (-(1 / 10 : ℝ))) h := by
  have hf := typical_density_whp_full_local_threshold hr hh hn p hp
  have hnNat := (sharp_local_typicality_size hr hh hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hexp : Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.rpow_pos_of_pos hn0 _))
  have hpos : 0 < (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
      {ω | |density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h} := by
    linarith only [hf, hexp]
  obtain ⟨ω, hω⟩ := nonempty_of_measureReal_ne_zero hpos.ne'
  exact ⟨sampleGraph ω, hω⟩

end Arxiv2411_18291
