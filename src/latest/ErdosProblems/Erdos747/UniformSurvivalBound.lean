import ErdosProblems.Erdos747.NormalizedSurvivalBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

def coarseSurvivalFraction (T : ℝ) : ℝ := Real.exp (-8 * T) / 2

lemma coarseSurvivalFraction_pos (T : ℝ) : 0 < coarseSurvivalFraction T := by
  unfold coarseSurvivalFraction
  positivity

/-- A fixed logarithmic thinning has a graph-independent lower-survival
bound, once the residual present-weight error is small. -/
lemma completionThinning_relative_lower_failure_le_normalized
    {n t : ℕ} (H : Finset (Edge n)) {Z : Edge n}
    (hn : 2 ≤ n) (hZ : Z ∈ allEdges n) (delta eta h T L : ℝ)
    (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hh : 1 + delta ≤ h) (hhmass : 2 * (delta + eta) ≤ h)
    (hL : 8 ≤ L) (hT : 0 < T) (ht0 : 0 < t) (ht : (t : ℝ) ≤ T * L)
    (hcollision : 4 * t * t ≤ H.card)
    (hw : 0 < completionWeight H Z)
    (hmean : L / 2 ≤ ((reindexGraphAway H Z hZ).card : ℝ) / ((n - 1 : ℕ) : ℝ))
    (hspread : PresentWeightSpread (reindexGraphAway H Z hZ) delta eta) :
    finsetProbability (H.powersetCard t)
        (fun U ↦ (completionWeight (H \ U) Z : ℝ) <
          coarseSurvivalFraction T * (completionWeight H Z : ℝ)) ≤
      T * L * (delta + eta) / h + 2 * Real.exp (-min
        ((coarseSurvivalFraction T)^2 / (64 * T * (h / L)))
        (coarseSurvivalFraction T / (16 * (h / L)))) := by
  let J := reindexGraphAway H Z hZ
  let w : ℝ := completionWeight H Z
  let b := h * matchingWeightTarget (n - 1) J
  let s := H \ completionHeavyEdges H Z b
  let k : ℝ := (n - 1 : ℕ)
  let r := coarseSurvivalFraction T
  let v := h / L
  have hk : 0 < k := by dsimp only [k]; exact_mod_cast (show 0 < n - 1 by omega)
  have hL0 : 0 < L := by linarith only [hL]
  have hh0 : 0 < h := by linarith only [hdelta, hh]
  have hwR : 0 < w := by dsimp only [w]; exact_mod_cast hw
  have hv : 0 < v := div_pos hh0 hL0
  have hr : 0 < r := coarseSurvivalFraction_pos T
  have hJ0 : (0 : ℝ) < J.card := by
    have hp : 0 < (J.card : ℝ) / k := (half_pos hL0).trans_le hmean
    exact (div_pos_iff.mp hp).elim (fun h ↦ h.1) (fun h ↦ False.elim (not_lt_of_ge hk.le h.2))
  have hJH : (J.card : ℝ) ≤ H.card := by exact_mod_cast card_reindexGraphAway_le_card H hZ
  have hH0 : (0 : ℝ) < H.card := hJ0.trans_le hJH
  have hH : H.Nonempty := Finset.card_pos.mp (by exact_mod_cast hH0)
  have htarget : matchingWeightTarget (n - 1) J = w * k / J.card := by
    dsimp only [matchingWeightTarget, J, w, k]
    rw [card_perfectMatchings_reindexGraphAway (by omega : 0 < n)]
  have htarget0 : 0 < matchingWeightTarget (n - 1) J := by rw [htarget]; positivity
  have hb : 0 < b := mul_pos hh0 htarget0
  have hpool : (H.card : ℝ) / 2 ≤ s.card :=
    card_nonheavy_ge_half_of_residual_presentSpread H hZ delta eta h hdelta heta hh hhmass
      htarget0 hspread
  have hs0 : (0 : ℝ) < s.card := (half_pos hH0).trans_le hpool
  have hs : s.Nonempty := Finset.card_pos.mp (by exact_mod_cast hs0)
  have hmean' : L * k ≤ 2 * J.card := by
    have h := (le_div_iff₀ hk).mp hmean
    nlinarith only [h]
  have hJratio : k / J.card ≤ 2 / L := by
    apply (div_le_div_iff₀ hJ0 hL0).mpr
    nlinarith only [hmean']
  have hratio : k / s.card ≤ 4 / L := by
    apply (div_le_div_iff₀ hs0 hL0).mpr
    nlinarith only [hmean', hJH, hpool]
  have hhalfRatio : k / s.card ≤ 1 / 2 := by
    apply hratio.trans
    apply (div_le_iff₀ hL0).mpr
    linarith only [hL]
  have hm : k < s.card := by
    have h := (div_le_iff₀ hs0).mp hhalfRatio
    linarith only [h, hk]
  have hcollision' : 2 * t * t ≤ s.card := by
    have hc : (4 : ℝ) * t * t ≤ H.card := by exact_mod_cast hcollision
    have hsR : (2 : ℝ) * t * t ≤ s.card := by linarith only [hc, hpool]
    exact_mod_cast hsR
  have htCard : t ≤ s.card := by
    have hsq : t ≤ t * t := Nat.le_mul_of_pos_left t ht0
    nlinarith only [hsq, hcollision']
  have hheavy := completionHeavyEdges_mass_le_of_residual_presentSpread
    H (by omega) hZ delta eta h hdelta hh hspread
  have hhit : (t : ℝ) * ((completionHeavyEdges H Z b).card : ℝ) / H.card ≤
      T * L * (delta + eta) / h := by
    apply (completionHeavyEdges_hit_bound_of_residual_presentSpread H hZ t delta eta h
      hH hdelta heta hh htarget0 hspread).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right ht (by positivity)) hh0.le
  have hsurvive : 2 * r ≤ (1 - k / s.card)^t := by
    have hp := exp_neg_eight_mul_le_one_sub_pow t T L (k / s.card) hL hT.le
      (by positivity) hratio ht
    simpa only [r, coarseSurvivalFraction, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hp
  have hbudget : r * w + r * w ≤ w * (1 - k / s.card)^t := by
    nlinarith only [mul_le_mul_of_nonneg_left hsurvive hwR.le]
  have hbupper : b ≤ 4 * v * w := by
    calc
      _ = h * w * (k / J.card) := by dsimp only [b]; rw [htarget]; ring
      _ ≤ h * w * (2 / L) := mul_le_mul_of_nonneg_left hJratio (by positivity)
      _ ≤ 4 * v * w := by
        dsimp only [v]
        have hp : 0 ≤ h * w / L := by positivity
        calc
          _ = 2 * (h * w / L) := by ring
          _ ≤ 4 * (h * w / L) := by linarith only [hp]
          _ = _ := by ring
  let V := (t : ℝ) * (w * k / s.card) * b
  have hV : 0 < V := by dsimp only [V]; positivity
  have htx : (t : ℝ) * (k / s.card) ≤ 4 * T := by
    calc
      _ ≤ (T * L) * (4 / L) := mul_le_mul ht hratio (by positivity) (by positivity)
      _ = _ := by field_simp <;> ring
  have hVupper : V ≤ 16 * T * v * w^2 := by
    calc
      _ = ((t : ℝ) * (k / s.card)) * (w * b) := by dsimp only [V]; ring
      _ ≤ (4 * T) * (w * (4 * v * w)) :=
        mul_le_mul htx (mul_le_mul_of_nonneg_left hbupper hwR.le) (by positivity) (by positivity)
      _ = _ := by ring
  have hraw := completionThinning_relative_lower_failure_le_optimized H hn hZ b
    ((delta + eta) * k * w) (r * w) r (T * L * (delta + eta) / h)
    hH hs hb (mul_pos hr hwR) ht0 hw htCard hcollision' hm hheavy hhit hbudget
  apply hraw.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (normalized_survival_exponents_le T v w r b V
    hT hv hwR hr hb hV hbupper hVupper)

end

end Erdos747
