import ErdosProblems.Erdos4.TiltedCompositeErrorBudget
import ErdosProblems.Erdos4.TiltedColorParameters

/-! The expected composite remainder is smaller than any fixed multiple of `x / log x`. -/

namespace Erdos4.Tilted

open Filter

theorem eventually_composite_degree_exp :
    ∀ᶠ x : ℕ in atTop,
      Real.exp (-((compositeColors x).card : ℝ) / (8 * (17 * (x : ℝ)) * compositeSurvivalBound x)) ≤
        1 / Real.log (x : ℝ) ^ (3 : ℕ) := by
  filter_upwards [eventually_color_supply, eventually_compositeSurvivalBound,
    eventually_outerScale_bounds, log_two_tendsto.eventually (eventually_ge_atTop (408 / Real.log 2)),
    eventually_ge_atTop 1] with x hm hQ hb hl hx
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let Q := compositeSurvivalBound x
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr hx
  have hL : 0 < L := by have hh := hb.1; change 16 ≤ L at hh; linarith
  have hlpos : 0 < l := by have hh := hb.2.1; change 1 ≤ l at hh; linarith
  have hQpos : 0 < Q := compositeSurvivalBound_pos hx
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hdegree : Real.log 2 * l ^ 2 / 136 ≤
      ((compositeColors x).card : ℝ) / (8 * (17 * (x : ℝ)) * Q) := by
    calc
      _ = (Real.log 2 * (x : ℝ) / L) / (8 * (17 * (x : ℝ)) * (1 / (L * l ^ 2))) := by field_simp; ring
      _ ≤ ((compositeColors x).card : ℝ) / (8 * (17 * (x : ℝ)) * (1 / (L * l ^ 2))) :=
        div_le_div_of_nonneg_right hm.2.1 (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left hQ (by positivity))
  have h3 : 3 * l ≤ Real.log 2 * l ^ 2 / 136 := by
    have hh := (div_le_iff₀ hlog2).mp hl
    change 408 ≤ l * Real.log 2 at hh
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 136)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hh hlpos.le]
  calc
    _ ≤ Real.exp (-(3 * l)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith
    _ = 1 / L ^ (3 : ℕ) := by
      have hlog : Real.log (L ^ (3 : ℕ)) = 3 * l := by
        simp only [Real.log_pow, Nat.cast_ofNat, l]
      rw [← hlog, Real.exp_neg, Real.exp_log (pow_pos hL 3), one_div]

theorem composite_cover_numeric_budget {x L l C Q K m : ℝ}
    (hx : 0 < x) (hL : 1 ≤ L) (hl : 1 ≤ l) (_hC0 : 0 ≤ C) (hC : C ≤ x * L)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ 1 / (L * l ^ 2)) (hK0 : 0 ≤ K) (hK : K ≤ L)
    (hexp : Real.exp (-m / (8 * (17 * x) * Q)) ≤ 1 / L ^ (3 : ℕ)) :
    C * Q * (4 * (1 / L ^ (30 : ℕ)) + Real.exp (-m / (8 * (17 * x) * Q))) +
      8 * Q * K * (17 * x) * (1 / L ^ (30 : ℕ)) ≤ 141 * x / L ^ (3 : ℕ) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hQ' : Q ≤ 1 / L := by
    apply hQ.trans
    apply one_div_le_one_div_of_le hLpos
    exact (mul_one L).symm.trans_le
      (mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ l ^ 2) hLpos.le)
  have hCQ : C * Q ≤ x := by
    calc
      _ ≤ (x * L) * (1 / L) := mul_le_mul hC hQ' hQ0 (by positivity)
      _ = _ := by field_simp
  have hQK : Q * K ≤ 1 := by
    calc
      _ ≤ (1 / L) * L := mul_le_mul hQ' hK hK0 (by positivity)
      _ = _ := by field_simp
  have htail : 1 / L ^ (30 : ℕ) ≤ 1 / L ^ (3 : ℕ) :=
    one_div_le_one_div_of_le (pow_pos hLpos 3) (pow_le_pow_right₀ hL (by norm_num))
  have hterm : 4 * (1 / L ^ (30 : ℕ)) + Real.exp (-m / (8 * (17 * x) * Q)) ≤ 5 / L ^ (3 : ℕ) := by
    calc
      _ ≤ 4 * (1 / L ^ (3 : ℕ)) + 1 / L ^ (3 : ℕ) :=
        add_le_add (mul_le_mul_of_nonneg_left htail (by norm_num)) hexp
      _ = _ := by ring
  have hfirst := mul_le_mul hCQ hterm
    (by positivity : 0 ≤ 4 * (1 / L ^ (30 : ℕ)) + Real.exp (-m / (8 * (17 * x) * Q))) hx.le
  have hsecond : 8 * Q * K * (17 * x) * (1 / L ^ (30 : ℕ)) ≤ 136 * x / L ^ (3 : ℕ) := by
    calc
      _ = 136 * x * (Q * K) * (1 / L ^ (30 : ℕ)) := by ring
      _ ≤ 136 * x * 1 * (1 / L ^ (3 : ℕ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hQK (by positivity)) htail (by positivity) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ x * (5 / L ^ (3 : ℕ)) + 136 * x / L ^ (3 : ℕ) := add_le_add hfirst hsecond
    _ = _ := by ring

theorem eventually_composite_cover_numeric_budget {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      ((compositeTargets c x).card : ℝ) * compositeSurvivalBound x *
          (4 * (1 / Real.log (x : ℝ) ^ (30 : ℕ)) +
            Real.exp (-((compositeColors x).card : ℝ) /
              (8 * (17 * (x : ℝ)) * compositeSurvivalBound x))) +
        8 * compositeSurvivalBound x * blockSize x (compositeTargets c x) * (17 * (x : ℝ)) *
          (1 / Real.log (x : ℝ) ^ (30 : ℕ)) ≤ ε * (x : ℝ) / Real.log (x : ℝ) := by
  filter_upwards [eventually_composite_degree_exp, eventually_compositeSurvivalBound,
    eventually_gapTarget_bounds hc, eventually_blockSize_le_log hc, eventually_outerScale_bounds,
    log_tendsto.eventually (eventually_ge_atTop (141 / ε)), eventually_ge_atTop 1]
    with x he hQ hY hK hb hLε hx
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr hx
  have hL1 : 1 ≤ Real.log (x : ℝ) := by linarith [hb.1]
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hL1
  have hC : ((compositeTargets c x).card : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) := by
    have hs : compositeTargets c x ⊆ Finset.Icc 1 (gapTarget c x) := by
      intro n hn
      have hh := compositeTargets_properties hn
      exact Finset.mem_Icc.mpr ⟨by omega, hh.2.1⟩
    have hh := Finset.card_le_card hs
    simp only [Nat.card_Icc] at hh
    exact (Nat.cast_le.mpr (show (compositeTargets c x).card ≤ gapTarget c x by omega)).trans hY.2.2.2.2.2.2.2.1
  have hmain := composite_cover_numeric_budget hxpos hL1 hb.2.1 (Nat.cast_nonneg _) hC
    (compositeSurvivalBound_nonneg x) hQ (Nat.cast_nonneg _) hK he
  have hcoeff : 141 ≤ ε * Real.log (x : ℝ) ^ (2 : ℕ) := by
    have hh := (div_le_iff₀ hε).mp hLε
    have hpow : Real.log (x : ℝ) ≤ Real.log (x : ℝ) ^ (2 : ℕ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hpow hε.le]
  apply hmain.trans
  calc
    _ ≤ (ε * Real.log (x : ℝ) ^ (2 : ℕ)) * (x : ℝ) / Real.log (x : ℝ) ^ (3 : ℕ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hxpos.le) (by positivity)
    _ = _ := by field_simp

end Erdos4.Tilted
