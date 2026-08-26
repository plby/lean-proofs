import ErdosProblems.Erdos747.OptimizedSurvival
import ErdosProblems.Erdos747.ResidualPresentBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Density-normalized finite completion survival -/

lemma exp_neg_eight_mul_le_one_sub_pow (t : ℕ) (T L x : ℝ)
    (hL : 8 ≤ L) (hT : 0 ≤ T) (hx0 : 0 ≤ x) (hx : x ≤ 4 / L)
    (ht : (t : ℝ) ≤ T * L) :
    Real.exp (-8 * T) ≤ (1 - x)^t := by
  have hL0 : 0 < L := by linarith only [hL]
  have hxHalf : x ≤ 1 / 2 := by
    have h := (div_le_iff₀ hL0).mpr (show (4 : ℝ) ≤ 1 / 2 * L by linarith only [hL])
    exact hx.trans h
  have hx1 : x < 1 := by linarith only [hxHalf]
  have hlog : -2 * x ≤ Real.log (1 - x) := by
    apply le_trans _ (neg_div_one_sub_le_log_one_sub hx1)
    apply (le_div_iff₀ (sub_pos.mpr hx1)).mpr
    nlinarith only [mul_nonneg hx0 (sub_nonneg.mpr hxHalf)]
  have htx : (t : ℝ) * x ≤ 4 * T := by
    calc
      _ ≤ (T * L) * (4 / L) := mul_le_mul ht hx hx0 (mul_nonneg hT hL0.le)
      _ = _ := by field_simp <;> ring
  have hlogt := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg t)
  calc
    _ ≤ Real.exp ((t : ℝ) * Real.log (1 - x)) :=
      Real.exp_le_exp.mpr (by nlinarith only [htx, hlogt])
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (sub_pos.mpr hx1)]

lemma normalized_survival_exponents_le (T v w r b V : ℝ)
    (hT : 0 < T) (hv : 0 < v) (hw : 0 < w) (hr : 0 < r)
    (hb : 0 < b) (hV : 0 < V) (hbupper : b ≤ 4 * v * w)
    (hVupper : V ≤ 16 * T * v * w^2) :
    min (r^2 / (64 * T * v)) (r / (16 * v)) ≤
      min ((r * w)^2 / (4 * V)) ((r * w) / (4 * b)) := by
  apply min_le_min
  · calc
      _ = (r * w)^2 / (4 * (16 * T * v * w^2)) := by field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith only [hVupper])
  · calc
      _ = (r * w) / (4 * (4 * v * w)) := by field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith only [hbupper])

lemma card_nonheavy_ge_half_of_residual_presentSpread
    {n : ℕ} (H : Finset (Edge n)) {Z : Edge n} (hZ : Z ∈ allEdges n)
    (delta eta h : ℝ) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hh : 1 + delta ≤ h) (hhmass : 2 * (delta + eta) ≤ h)
    (hw : 0 < matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ))
    (hspread : PresentWeightSpread (reindexGraphAway H Z hZ) delta eta) :
    (H.card : ℝ) / 2 ≤
      (H \ completionHeavyEdges H Z
        (h * matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ))).card := by
  let A := completionHeavyEdges H Z
    (h * matchingWeightTarget (n - 1) (reindexGraphAway H Z hZ))
  have hh0 : 0 < h := by linarith only [hdelta, hh]
  have hc := completionHeavyEdges_card_mul_le_of_residual_presentSpread H hZ delta eta h
    hdelta hh hw hspread
  have hj : ((reindexGraphAway H Z hZ).card : ℝ) ≤ H.card := by
    exact_mod_cast card_reindexGraphAway_le_card H hZ
  have hbound : (A.card : ℝ) * h ≤ (delta + eta) * H.card :=
    hc.trans (mul_le_mul_of_nonneg_left hj (by positivity))
  have hhalf : (A.card : ℝ) ≤ (H.card : ℝ) / 2 := by
    apply (mul_le_mul_iff_right₀ hh0).mp
    have hs := mul_le_mul_of_nonneg_right hhmass (Nat.cast_nonneg H.card)
    nlinarith only [hbound, hs]
  have hsub : A ⊆ H := Finset.filter_subset _ _
  have hcard : (H \ A).card + A.card = H.card := Finset.card_sdiff_add_card_eq_card hsub
  have hcardR : ((H \ A).card : ℝ) + A.card = H.card := by exact_mod_cast hcard
  change (H.card : ℝ) / 2 ≤ (H \ A).card
  linarith only [hhalf, hcardR]

end

end Erdos747
