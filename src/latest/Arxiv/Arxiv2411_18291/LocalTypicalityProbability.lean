import Arxiv.Arxiv2411_18291.LinearTypicalityDensity
import Arxiv.Arxiv2411_18291.LocalTypicalityNumerics

/-! # Random typicality at the source's local size threshold

For edge rank at least two and rank times neighborhood size at least fifteen,
the threshold in Lemma 5.3 suffices. The failure rate is the corrected
`exp(-n^(1/10))`; the already refuted printed exponential rate is not used.
-/

open MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem typical_failure_probability_linear_scales {r h n : ℕ}
    (hn : 1 ≤ n) (hh : 1 ≤ h) (hnr : r + 1 ≤ n) (hsize : 2 * (h * r) ≤ n)
    (hroot : (4 * (h + 1) * (h * r) : ℝ) ≤ (n : ℝ) ^ (9 / 10 : ℝ))
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
      {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)} ≤
      2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
        Real.exp (-((n : ℝ) ^ (3 / 10 : ℝ) / (192 * (h + 1 : ℝ) ^ 2))) := by
  let δ := (n : ℝ) ^ (-(1 / 10 : ℝ))
  let c := δ / (4 * (h + 1 : ℝ))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ : 0 ≤ δ := Real.rpow_nonneg hn0.le _
  have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hden : 0 < 4 * (h + 1 : ℝ) := by positivity
  have hc : 0 ≤ c := div_nonneg hδ hden.le
  have hcδ : c ≤ δ := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hδ, mul_nonneg hδ (Nat.cast_nonneg h)]
  have hc1 : c ≤ 1 := hcδ.trans hδ1
  have hsmall : c * h ≤ 1 / 4 := by
    dsimp only [c]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have hm := mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg h)
    linarith only [hm]
  have hcn : c * n = (n : ℝ) ^ (9 / 10 : ℝ) / (4 * (h + 1 : ℝ)) := by
    dsimp only [c, δ]
    rw [div_mul_eq_mul_div, ← Real.rpow_add_one hn0.ne']
    norm_num
  have hroot' : (h * r : ℝ) ≤ c * n := by
    rw [hcn, le_div_iff₀ hden]
    nlinarith only [hroot]
  have hnormal : (4 + 4 * h : ℝ) * c = δ := by
    dsimp only [c]
    field_simp
    ring
  have hb := typical_failure_probability_linear (V := Fin n) p hc
    (by simpa only [Fintype.card_fin] using hnr)
    (by simpa only [Fintype.card_fin] using hroot') hsmall
  simp only [Fintype.card_fin, hnormal] at hb
  have hsub : {ω : BernoulliSubset.Sample (Block (Fin n) (r + 1)) |
      ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ δ * p ∧
        IsTypical (sampleGraph ω) δ h)} ⊆
      {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ c * p ∧
        IsTypical (sampleGraph ω) δ h)} := by
    intro ω hω hgood
    exact hω ⟨hgood.1.trans (mul_le_mul_of_nonneg_right hcδ p.property.1), hgood.2⟩
  have hph : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (p : ℝ) ^ h := by
    have hm := pow_le_pow_left₀ (Real.rpow_nonneg hn0.le _) hp h
    rw [← Real.rpow_mul_natCast hn0.le] at hm
    have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
    have heq : -(1 / (2 * h : ℝ)) * h = -(1 / 2 : ℝ) := by field_simp
    rwa [heq] at hm
  have hpower : (n : ℝ) ^ (3 / 10 : ℝ) =
      n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * δ ^ 2 := by
    dsimp only [δ]
    rw [← Real.rpow_mul_natCast hn0.le,
      show (3 / 10 : ℝ) = (1 + -(1 / 2)) + (-(1 / 10)) * 2 by norm_num,
      Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one]
    norm_num
  have hscale : (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * c ^ 2 / 12 =
      (n : ℝ) ^ (3 / 10 : ℝ) / (192 * (h + 1 : ℝ) ^ 2) := by
    rw [hpower]
    dsimp only [c]
    field_simp
    ring
  have hexp : Real.exp (-((n : ℝ) * (p : ℝ) ^ h * c ^ 2 / 12)) ≤
      Real.exp (-((n : ℝ) ^ (3 / 10 : ℝ) / (192 * (h + 1 : ℝ) ^ 2))) := by
    apply Real.exp_le_exp.mpr
    rw [← hscale]
    have hm := mul_le_mul_of_nonneg_left hph (show 0 ≤ (n : ℝ) * c ^ 2 / 12 by positivity)
    nlinarith only [hm]
  calc
    _ ≤ typicalFailureBound n r h p c := (measureReal_mono hsub).trans hb
    _ ≤ 2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
        Real.exp (-((n : ℝ) * (p : ℝ) ^ h * c ^ 2 / 12)) :=
      typicalFailureBound_le n r h hn hh p.property.1 p.property.2 hc hc1 hsize
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

theorem typical_failure_stretched_exp_local_threshold {r h n : ℕ}
    (hr : 1 ≤ r) (hh : 1 ≤ h) (hk : 15 ≤ (r + 1) * h)
    (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
      {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)} <
      Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  obtain ⟨hn1, hnr, hsize, hroot, _⟩ := local_typicality_numerics hr hh hk hn
  exact (typical_failure_probability_linear_scales hn1 hh hnr hsize hroot p hp).trans_lt
    (local_typicality_tail hr hh hk hn)

theorem typical_paper_whp_corrected_local_threshold {r h n : ℕ}
    (hr : 1 ≤ r) (hh : 1 ≤ h) (hk : 15 ≤ (r + 1) * h)
    (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n)
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
  have hf := typical_failure_stretched_exp_local_threshold hr hh hk hn p hp
  rw [he] at hf
  linarith only [hf]

theorem exists_typicalGraph_local_threshold {r h n : ℕ}
    (hr : 1 ≤ r) (hh : 1 ≤ h) (hk : 15 ≤ (r + 1) * h)
    (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    ∃ G : Hypergraph (Fin n) (r + 1),
      |density G - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical G ((n : ℝ) ^ (-(1 / 10 : ℝ))) h := by
  have hf := typical_paper_whp_corrected_local_threshold hr hh hk hn p hp
  have hnNat : 1 ≤ n := (local_typicality_numerics hr hh hk hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hexp : Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.rpow_pos_of_pos hn0 _))
  have hpos : 0 < (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
      {ω | |density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h} := by
    linarith only [hf, hexp]
  obtain ⟨ω, hω⟩ := nonempty_of_measureReal_ne_zero hpos.ne'
  exact ⟨sampleGraph ω, hω⟩

end Arxiv2411_18291
