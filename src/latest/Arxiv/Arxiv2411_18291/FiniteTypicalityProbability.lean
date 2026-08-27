import Arxiv.Arxiv2411_18291.FiniteTypicalityThreshold
import Arxiv.Arxiv2411_18291.AsymptoticTypicality

/-! # Corrected random typicality with an explicit finite threshold

The density lower bound and typicality error are those of Lemma 5.3.
The failure rate is the corrected `exp(-n^(1/10))`, not the false printed rate.
All numerical conditions are discharged at `correctedTypicalityThreshold`.
-/

open MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem typical_failure_probability_paper_scales_explicit {r h n : ℕ}
    (hn : correctedTypicalityThreshold r h ≤ n) (hh : 1 ≤ h)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
      {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)} ≤
      2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
        Real.exp (-((n : ℝ) ^ (1 / 4 : ℝ) / 12)) := by
  let c := (n : ℝ) ^ (-(1 / 8 : ℝ))
  have hnNat : 1 ≤ n := (correctedTypicalityThreshold_pos r h).trans_le hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  obtain ⟨hC, hlarge⟩ := corrected_typicality_growth hn
  have hpowN : (n : ℝ) ^ (1 / 40 : ℝ) ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1
      (by norm_num : (1 / 40 : ℝ) ≤ 1)
  have hsizeReal : (2 * (h * r) : ℝ) ≤ n := by
    have hh := hlarge.trans_le hpowN
    nlinarith only [hh, (Nat.cast_nonneg h : (0 : ℝ) ≤ h),
      (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hsize : 2 * (h * r) ≤ n := by exact_mod_cast hsizeReal
  have hrh : r ≤ h * r := by simpa using Nat.mul_le_mul_right r hh
  have hnr : r + 1 ≤ n := by omega
  have hroot : (h * r : ℝ) ≤ c * n := by
    have hh : (h * r : ℝ) ≤ (n : ℝ) ^ (1 / 40 : ℝ) := by
      nlinarith only [hlarge, (Nat.cast_nonneg h : (0 : ℝ) ≤ h),
        (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1
      (by norm_num : (1 / 40 : ℝ) ≤ 7 / 8)
    have heq : (n : ℝ) ^ (7 / 8 : ℝ) = c * n := by
      rw [show (7 / 8 : ℝ) = -(1 / 8) + 1 by norm_num, Real.rpow_add hn0, Real.rpow_one]
    exact hh.trans (heq ▸ hpow)
  have hc : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hc1 : c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hnormal : (4 + 2 * h * 2 ^ h : ℝ) * c ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 40 : ℝ) * c := mul_le_mul_of_nonneg_right hC hc
      _ = _ := by dsimp only [c]; rw [← Real.rpow_add hn0]; norm_num
  have herror1 : (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hsmall : c * h * 2 ^ h ≤ 1 / 2 := by nlinarith only [hnormal, herror1, hc]
  have hb := typical_failure_probability (V := Fin n) (r := r) (h := h) p hc hc1
    (by simpa only [Fintype.card_fin] using hnr)
    (by simpa only [Fintype.card_fin] using hroot) hsmall
  simp only [Fintype.card_fin] at hb
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have heq : (1 / (2 * h : ℝ)) * h = 1 / 2 := by field_simp
  have hexp : 1 - (1 / (2 * h : ℝ)) * h - 2 * (1 / 8 : ℝ) = 1 / 4 := by
    rw [heq]
    norm_num
  have hbound := typicalFailureBound_power_le n r h hnNat hh hsize
    (by norm_num : (0 : ℝ) ≤ 1 / 8) p hp
  rw [hexp] at hbound
  have hcerror : c ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hsub : {ω : BernoulliSubset.Sample (Block (Fin n) (r + 1)) |
      ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)} ⊆
      {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ c * p ∧
        IsTypical (sampleGraph ω) ((4 + 2 * h * 2 ^ h) * c) h)} := by
    intro ω hω hgood
    exact hω ⟨hgood.1.trans (mul_le_mul_of_nonneg_right hcerror p.property.1),
      hgood.2.mono hnormal le_rfl⟩
  exact (measureReal_mono hsub).trans (hb.trans hbound)

theorem typical_failure_stretched_exp_explicit {r h n : ℕ}
    (hn : correctedTypicalityThreshold r h ≤ n) (hh : 1 ≤ h)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
      {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)} <
      Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) :=
  (typical_failure_probability_paper_scales_explicit hn hh p hp).trans_lt
    (corrected_typicality_tail hn)

/-- Corrected Lemma 5.3, with all size and probability conditions explicit. -/
theorem typical_paper_whp_corrected_explicit {r h n : ℕ}
    (hn : correctedTypicalityThreshold r h ≤ n) (hh : 1 ≤ h)
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
  have hf := typical_failure_stretched_exp_explicit hn hh p hp
  rw [he] at hf
  linarith only [hf]

theorem exists_typicalGraph_corrected_explicit {r h n : ℕ}
    (hn : correctedTypicalityThreshold r h ≤ n) (hh : 1 ≤ h)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    ∃ G : Hypergraph (Fin n) (r + 1),
      |density G - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical G ((n : ℝ) ^ (-(1 / 10 : ℝ))) h := by
  have hf := typical_failure_stretched_exp_explicit hn hh p hp
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (correctedTypicalityThreshold_pos r h).trans_le hn
  have hexp : Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.rpow_pos_of_pos hn0 _))
  by_contra hnone
  have hbad : {ω : BernoulliSubset.Sample (Block (Fin n) (r + 1)) |
      ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)} = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro ω hω
    exact hnone ⟨sampleGraph ω, hω⟩
  rw [hbad, probReal_univ] at hf
  exact (lt_irrefl (1 : ℝ)) (hf.trans hexp)

theorem typical_paper_whp_corrected_paper_threshold {q r n h : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) <
      (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
        {ω | |density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
          IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h} :=
  typical_paper_whp_corrected_explicit
    ((correctedTypicalityThreshold_le_paperThreshold hqr hh hH).trans hn) hh p hp

theorem exists_typicalGraph_paper_density_threshold {q r n h : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hh : 1 ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    ∃ G : Hypergraph (Fin n) (r + 1),
      |density G - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical G ((n : ℝ) ^ (-(1 / 10 : ℝ))) h :=
  exists_typicalGraph_corrected_explicit
    ((correctedTypicalityThreshold_le_paperThreshold hqr hh hH).trans hn) hh p hp

end Arxiv2411_18291
