import ErdosProblems.Erdos747.UniformDeletionBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## A vanishing count-error budget after removing one triple -/

def residualCountError (n : ℕ) (C c : ℝ) : ℝ :=
  (C * n + 3 - 2 * Real.log c) / ((n - 1 : ℕ) : ℝ)

lemma residualCountError_nonneg (n : ℕ) (C c : ℝ)
    (hC : 0 ≤ C) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ residualCountError n C c := by
  have hlog : Real.log c ≤ 0 := Real.log_nonpos hc0.le hc1
  unfold residualCountError
  apply div_nonneg _ (by positivity)
  have hCn : 0 ≤ C * n := by positivity
  linarith

lemma residualCountError_tendsto_zero (C : ℕ → ℝ) (c : ℝ)
    (hC : Tendsto C atTop (𝓝 0)) :
    Tendsto (fun n ↦ residualCountError n (C n) c) atTop (𝓝 0) := by
  have hpred : Tendsto (fun n : ℕ ↦ n - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b + 1)] with n hn
    omega
  have hcast : Tendsto (fun n : ℕ ↦ ((n - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpred
  have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n - 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hlast : Tendsto (fun n : ℕ ↦ (3 - 2 * Real.log c) / ((n - 1 : ℕ) : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hcast
  have hratio : Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / ((n - 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  have hlim := (hC.mul hratio).add hlast
  norm_num only [zero_mul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  change C n * ((1 : ℝ) + 1 / ((n - 1 : ℕ) : ℝ)) +
    (3 - 2 * Real.log c) / ((n - 1 : ℕ) : ℝ) = residualCountError n (C n) c
  unfold residualCountError
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  field_simp [(sub_pos.mpr hnR).ne']
  ring

lemma pred_mul_log_ratio_le_one (n : ℕ) (hn : 2 ≤ n) :
    ((n - 1 : ℕ) : ℝ) * Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ 1 := by
  have hk : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hnR hk)
  have h := mul_le_mul_of_nonneg_left hlog hk.le
  have heq : ((n - 1 : ℕ) : ℝ) * ((n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have hpred : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    field_simp [hpred.ne']
    ring
  exact h.trans_eq heq

/-- The degree normalization cancels the edge-density term in the
residual count loss.  Only a constant divided by `n-1` remains. -/
lemma residualCountError_budget (n M j : ℕ) (C c : ℝ)
    (hn : 2 ≤ n) (hM : 0 < M) (hj : 0 < j) (hjM : j ≤ M) (hc : 0 < c) :
    ((n - 1 : ℕ) : ℝ) * Real.log ((j : ℝ) / ((n - 1 : ℕ) : ℝ)) -
        2 * ((n - 1 : ℕ) : ℝ) - residualCountError n C c * ((n - 1 : ℕ) : ℝ) ≤
      (n : ℝ) * Real.log ((M : ℝ) / n) - 2 * n - C * n +
        Real.log (c^2 * (n : ℝ) / M) := by
  have hk : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hmono : Real.log ((j : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤
      Real.log ((M : ℝ) / ((n - 1 : ℕ) : ℝ)) :=
    Real.log_le_log (div_pos hjR hk)
      (div_le_div_of_nonneg_right (by exact_mod_cast hjM) hk.le)
  have hsplit : Real.log ((M : ℝ) / ((n - 1 : ℕ) : ℝ)) =
      Real.log ((M : ℝ) / n) + Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
    rw [Real.log_div hMR.ne' hk.ne', Real.log_div hMR.ne' hnR.ne',
      Real.log_div hnR.ne' hk.ne']
    ring
  have hcompare : ((n - 1 : ℕ) : ℝ) * Real.log ((j : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤
      ((n - 1 : ℕ) : ℝ) * Real.log ((M : ℝ) / n) + 1 := by
    calc
      _ ≤ ((n - 1 : ℕ) : ℝ) * Real.log ((M : ℝ) / ((n - 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hmono hk.le
      _ = ((n - 1 : ℕ) : ℝ) * Real.log ((M : ℝ) / n) +
          ((n - 1 : ℕ) : ℝ) * Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
        rw [hsplit, mul_add]
      _ ≤ _ := add_le_add le_rfl (pred_mul_log_ratio_le_one n hn)
  have hlogc : Real.log (c^2 * (n : ℝ) / M) = 2 * Real.log c - Real.log ((M : ℝ) / n) := by
    rw [Real.log_div (mul_ne_zero (pow_ne_zero 2 hc.ne') hnR.ne') hMR.ne',
      Real.log_mul (pow_ne_zero 2 hc.ne') hnR.ne', Real.log_pow,
      Real.log_div hMR.ne' hnR.ne']
    norm_num
    ring
  have herror : residualCountError n C c * ((n - 1 : ℕ) : ℝ) = C * n + 3 - 2 * Real.log c :=
    div_mul_cancel₀ _ hk.ne'
  rw [herror, hlogc]
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hcompare ⊢
  nlinarith

lemma kahnCountLower_reindexGraphAway_explicit_error
    {n M : ℕ} {H : Finset (Edge n)} {Z : Edge n} {C c : ℝ}
    (hn : 2 ≤ n) (hM : 0 < M) (hH : H ∈ sample n M)
    (hZ : Z ∈ allEdges n) (hc : 0 < c)
    (hPhi : (perfectMatchings n H).card ≠ 0) (hcount : KahnCountLower H C)
    (hweight : c^2 * matchingWeightTarget n H ≤ completionWeight H Z) :
    KahnCountLower (reindexGraphAway H Z hZ) (residualCountError n C c) := by
  have hHcard := (mem_sample.mp hH).2
  have hpm := hasPerfectMatching_reindexGraphAway_of_weightLower
    hn (by simpa only [hHcard] using hM) hZ hPhi hc hweight
  have hJpos : 0 < (reindexGraphAway H Z hZ).card := by
    obtain ⟨F, hFsub, hFcard, hFmatch⟩ := hpm
    have hcard := Finset.card_le_card hFsub
    omega
  have hJM : (reindexGraphAway H Z hZ).card ≤ M := by
    rw [card_reindexGraphAway]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hHcard
  exact kahnCountLower_reindexGraphAway_of_weightLower hn hM hH hZ hc hPhi hcount hweight
    (residualCountError_budget n M (reindexGraphAway H Z hZ).card C c hn hM hJpos hJM hc)

end

end Erdos747
