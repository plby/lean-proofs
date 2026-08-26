import ErdosProblems.Erdos747.EntropyParameterBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Uniform numerical budgets for the stopped deletion process -/

def deletionDeviationScale (n : ℕ) : ℝ :=
  (n : ℝ) / Real.sqrt (Real.log ((3 * n : ℕ) : ℝ))

def deletionCountError (n : ℕ) (C : ℝ) : ℝ :=
  (Real.log ((3 * n : ℕ) : ℝ) / 2 + 1) / n +
    1 / Real.sqrt (Real.log ((3 * n : ℕ) : ℝ)) +
      2 * C^2 / Real.log ((3 * n : ℕ) : ℝ)

lemma log_vertexCount_tendsto_atTop :
    Tendsto (fun n : ℕ ↦ Real.log ((3 * n : ℕ) : ℝ)) atTop atTop := by
  apply Real.tendsto_log_atTop.comp
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)

lemma deletionCountError_nonneg (n : ℕ) (C : ℝ) (hn : 1 ≤ n) :
    0 ≤ deletionCountError n C := by
  have hlog : 0 ≤ Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * n by omega))
  unfold deletionCountError
  positivity

lemma deletionCountError_tendsto_zero (C : ℝ) :
    Tendsto (fun n ↦ deletionCountError n C) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hfirst := (tendsto_log_three_mul_div.div_const 2).add hinv
  have hsqrt : Tendsto (fun n : ℕ ↦
      1 / Real.sqrt (Real.log ((3 * n : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp log_vertexCount_tendsto_atTop)
  have hlast : Tendsto (fun n : ℕ ↦
      2 * C^2 / Real.log ((3 * n : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_vertexCount_tendsto_atTop
  have hlim := (hfirst.add hsqrt).add hlast
  norm_num only [zero_div, add_zero] at hlim
  refine hlim.congr (fun n ↦ ?_)
  unfold deletionCountError
  ring

lemma deletionGamma_le_inv_log
    (ε : ℝ) (hε : 0 ≤ ε) (n M i : ℕ) (hn : 1 ≤ n)
    (hMlower : upperEdgeCount ε n ≤ M) (hMK : M ≤ (allEdges n).card)
    (hi : i ≤ (allEdges n).card - M) :
    deletionGamma n (allEdges n) i ≤ 1 / Real.log ((3 * n : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * n by omega))
  have hmean : Real.log ((3 * n : ℕ) : ℝ) ≤ (M : ℝ) / n :=
    (upperEdgeCount_mean_ge ε hε n (by omega)).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hMlower) hnR.le)
  have hML : Real.log ((3 * n : ℕ) : ℝ) * n ≤ (M : ℝ) := (le_div_iff₀ hnR).mp hmean
  have hMpos : (0 : ℝ) < M := (mul_pos hlog hnR).trans_le hML
  have hremaining : (M : ℝ) ≤ ((allEdges n).card - i : ℕ) := by
    exact_mod_cast (show M ≤ (allEdges n).card - i by omega)
  unfold deletionGamma
  calc
    _ ≤ (n : ℝ) / M := div_le_div_of_nonneg_left hnR.le hMpos hremaining
    _ ≤ 1 / Real.log ((3 * n : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hMpos hlog).mpr
      nlinarith

lemma deletionVarianceBudget_le_log
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (n M t : ℕ) (hn : 1 ≤ n)
    (hMlower : upperEdgeCount ε n ≤ M) (hMK : M ≤ (allEdges n).card)
    (ht : t ≤ (allEdges n).card - M) :
    deletionVarianceBudget n (allEdges n) C t ≤
      C * n / Real.log ((3 * n : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * n by omega))
  let m := (allEdges n).card - t
  have hmm : M ≤ m := by dsimp only [m]; omega
  have hmK : m ≤ (allEdges n).card := Nat.sub_le _ _
  have hmean : Real.log ((3 * n : ℕ) : ℝ) ≤ (m : ℝ) / n :=
    (upperEdgeCount_mean_ge ε hε n (by omega)).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hMlower.trans hmm) hnR.le)
  have hmL : Real.log ((3 * n : ℕ) : ℝ) * n ≤ (m : ℝ) := (le_div_iff₀ hnR).mp hmean
  have hmpos : 0 < m := by exact_mod_cast (mul_pos hlog hnR).trans_le hmL
  have htime : (allEdges n).card - m = t := by dsimp only [m]; omega
  have hraw := deletionVarianceBudget_le n (allEdges n) C m hC hmpos hmK
  rw [htime] at hraw
  calc
    _ ≤ C * (n : ℝ)^2 / m := hraw
    _ ≤ C * (n : ℝ)^2 / (Real.log ((3 * n : ℕ) : ℝ) * n) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hlog hnR) hmL
    _ = _ := by field_simp

lemma sharp_initial_normalization_le (n M : ℕ) (hn : 1 ≤ n) (hM : 0 < M) :
    (n : ℝ) * Real.log ((M : ℝ) / n) ≤
      2 * n * Real.log (n : ℝ) + n * Real.log ((9 : ℝ) / 2) -
        n * Real.log (((allEdges n).card : ℝ) / M) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hK : (0 : ℝ) < (allEdges n).card := by
    rw [card_allEdges]
    exact_mod_cast Nat.choose_pos (show 3 ≤ 3 * n by omega)
  have hKbound : ((allEdges n).card : ℝ) ≤ (9 / 2 : ℝ) * n^3 := by
    rw [card_allEdges]
    have h := Nat.choose_le_pow_div (α := ℝ) 3 (3 * n)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.factorial_succ, Nat.factorial_zero] at h
    nlinarith
  have hlogK := Real.log_le_log hK hKbound
  rw [Real.log_mul (by norm_num) (pow_ne_zero 3 hnR.ne'), Real.log_pow] at hlogK
  have hscaled := mul_le_mul_of_nonneg_left hlogK hnR.le
  rw [Real.log_div hMR.ne' hnR.ne', Real.log_div hK.ne' hMR.ne']
  norm_num only [Nat.cast_ofNat] at hscaled
  nlinarith

lemma deletionCountError_budget
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (n M t : ℕ) (hn : 1 ≤ n)
    (hMlower : upperEdgeCount ε n ≤ M) (hMK : M ≤ (allEdges n).card)
    (ht : t ≤ (allEdges n).card - M) :
    (n : ℝ) * Real.log ((((allEdges n).card - t : ℕ) : ℝ) / n) - 2 * n -
        deletionCountError n C * n ≤
      2 * n * Real.log (n : ℝ) + n * Real.log ((9 : ℝ) / 2) - 2 * n -
        Real.log (n : ℝ) / 2 - 1 -
        (deletionDeviationScale n +
          n * Real.log (((allEdges n).card : ℝ) / ((allEdges n).card - t : ℕ))) -
        (C * deletionVarianceBudget n (allEdges n) C t) / (1 - (1 / 2 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * n by omega))
  have hmean := upperEdgeCount_mean_ge ε hε n (by omega)
  have hupperPos : 0 < upperEdgeCount ε n := by
    have h := (le_div_iff₀ hnR).mp hmean
    exact_mod_cast (mul_pos hlog hnR).trans_le h
  have hm : 0 < (allEdges n).card - t := by omega
  have hinit := sharp_initial_normalization_le n ((allEdges n).card - t) hn hm
  have hV := deletionVarianceBudget_le_log ε C hε hC n M t hn hMlower hMK ht
  have hquad : (C * deletionVarianceBudget n (allEdges n) C t) / (1 - (1 / 2 : ℝ)) ≤
      2 * C^2 * n / Real.log ((3 * n : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hV (show 0 ≤ 2 * C by positivity)
    calc
      _ = 2 * C * deletionVarianceBudget n (allEdges n) C t := by ring
      _ ≤ 2 * C * (C * n / Real.log ((3 * n : ℕ) : ℝ)) := h
      _ = _ := by ring
  have hlogn : Real.log (n : ℝ) ≤ Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_le_log hnR (by exact_mod_cast (show n ≤ 3 * n by omega))
  have herror : deletionCountError n C * n =
      Real.log ((3 * n : ℕ) : ℝ) / 2 + 1 + deletionDeviationScale n +
        2 * C^2 * n / Real.log ((3 * n : ℕ) : ℝ) := by
    unfold deletionCountError deletionDeviationScale
    field_simp
  nlinarith

lemma eventually_stoppedCenteredSum_probability_le
    (ε C : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, t ≤ (allEdges n).card - upperEdgeCount ε n →
      finsetProbability (Finset.univ : Finset (DeletionHistory (allEdges n) t))
        (fun e ↦ deletionDeviationScale n < stoppedCenteredSum C t e) ≤
          Real.exp (-12 * Real.log ((3 * n : ℕ) : ℝ)) := by
  have hsmall := (tendsto_order.1 tendsto_sq_log_three_mul_div).2 (1 / 48)
    (by norm_num : (0 : ℝ) < 1 / 48)
  have hroot := Real.tendsto_sqrt_atTop.comp log_vertexCount_tendsto_atTop
  filter_upwards [eventually_upperEdgeCount_collision_condition ε hε0 hε1,
    log_vertexCount_tendsto_atTop.eventually_ge_atTop (1 + 2 * C),
    hroot.eventually_ge_atTop (2 * C), hsmall, eventually_ge_atTop 1]
    with n hcollision hlogbig hsqrtbig hsmall hn
  intro t ht
  let L := Real.log ((3 * n : ℕ) : ℝ)
  let s := Real.sqrt L
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hs : 0 < s := Real.sqrt_pos.mpr hL
  have hs2 : s^2 = L := Real.sq_sqrt hL.le
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hL1
  have hsL : s ≤ L := by nlinarith
  have hM : upperEdgeCount ε n ≤ (allEdges n).card := by
    by_cases hz : upperEdgeCount ε n = 0
    · simp [hz]
    · have hp : 0 < upperEdgeCount ε n := Nat.pos_of_ne_zero hz
      nlinarith
  have hClog : C / L ≤ 1 / 2 := by
    apply (div_le_iff₀ hL).mpr
    dsimp only [L]
    linarith
  have htilt : ∀ i < t,
      |(1 : ℝ) * (C * deletionGamma n (allEdges n) i)| ≤ 1 / 2 := by
    intro i hi
    have hgamma := deletionGamma_le_inv_log ε hε0 n (upperEdgeCount ε n) i
      hn le_rfl hM (by omega)
    have hnonneg : 0 ≤ C * deletionGamma n (allEdges n) i := by
      unfold deletionGamma
      positivity
    rw [one_mul, abs_of_nonneg hnonneg]
    calc
      _ ≤ C * (1 / L) := mul_le_mul_of_nonneg_left hgamma hC.le
      _ = C / L := by ring
      _ ≤ _ := hClog
  have hV := deletionVarianceBudget_le_log ε C hε0 hC.le n (upperEdgeCount ε n) t
    hn le_rfl hM ht
  have hVhalf : deletionVarianceBudget n (allEdges n) C t ≤ deletionDeviationScale n / 2 := by
    calc
      _ ≤ C * n / L := hV
      _ ≤ (s / 2) * n / L := by
        gcongr
        change 2 * C ≤ s at hsqrtbig
        linarith
      _ = deletionDeviationScale n / 2 := by
        change (s / 2) * n / L = ((n : ℝ) / s) / 2
        rw [← hs2]
        field_simp
  have hsmallN : 48 * L^2 < (n : ℝ) := by
    have h := (div_lt_iff₀ hnR).mp hsmall
    dsimp only [L]
    nlinarith
  have huLarge : 12 * L ≤ deletionDeviationScale n / 2 := by
    have hprod := mul_le_mul_of_nonneg_left hsL hL.le
    have hscale : 12 * L * (2 * s) ≤ (n : ℝ) := by nlinarith
    have h := (le_div_iff₀ (show 0 < 2 * s by positivity)).mpr hscale
    calc
      _ ≤ (n : ℝ) / (2 * s) := h
      _ = deletionDeviationScale n / 2 := by change _ = ((n : ℝ) / s) / 2; ring
  have harg : deletionVarianceBudget n (allEdges n) C t - deletionDeviationScale n ≤ -12 * L := by
    linarith
  have hraw := stoppedCenteredSum_gt_probability_le (H := allEdges n)
    C 1 (deletionDeviationScale n) (by omega) hC t (by omega) (by norm_num) htilt
  simp only [one_pow, one_mul] at hraw
  exact hraw.trans (Real.exp_le_exp.mpr harg)

end

end Erdos747
