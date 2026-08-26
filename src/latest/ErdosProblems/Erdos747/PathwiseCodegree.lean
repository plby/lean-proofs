import ErdosProblems.Erdos747.PathwiseRegularityTails

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## A uniformly negligible relative codegree cap -/

def codegreeRelativeTolerance (n : ℕ) : ℝ :=
  (Real.sqrt (Real.log (n : ℝ)))⁻¹

def relativeCodegreeCap (n M : ℕ) (delta : ℝ) : ℕ :=
  ⌈delta * ((M : ℝ) / n)⌉₊

def CodegreeCapFailure (n cap : ℕ) (H : Finset (Edge n)) : Prop :=
  ∃ u v : Vertex n, u ≠ v ∧ cap < vertexCodegree H u v

lemma codegreeRelativeTolerance_nonneg (n : ℕ) :
    0 ≤ codegreeRelativeTolerance n := by
  unfold codegreeRelativeTolerance
  positivity

lemma codegreeRelativeTolerance_tendsto_zero :
    Tendsto codegreeRelativeTolerance atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

lemma codegreeRelativeTolerance_mul_log_tendsto_atTop :
    Tendsto (fun n ↦ codegreeRelativeTolerance n * Real.log (n : ℝ)) atTop atTop := by
  have hlim := Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hs : Real.sqrt (Real.log (n : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  dsimp only [Function.comp_def, codegreeRelativeTolerance]
  field_simp [hs]
  nlinarith [Real.sq_sqrt hlog.le]

lemma codegreeCapFailure_probability_le
    (n M cap : ℕ) (theta : ℝ) (hn : 0 < n)
    (hM : M ≤ (allEdges n).card) (htheta : 0 ≤ theta) :
    finsetProbability (sample n M) (CodegreeCapFailure n cap) ≤
      ((3 * n : ℝ)^2) * (((allEdges n).card + 1 : ℝ) *
        Real.exp ((M : ℝ) * (2 / ((n : ℝ) * (3 * n - 1))) *
          (Real.exp theta - 1) - theta * (cap + 1))) := by
  calc
    _ = finsetProbability (sample n M)
        (fun H ↦ H ∈ allDensityCodegreeCapFailureSet n M cap) := by
      apply finsetProbability_congr_event
      intro H hH
      rw [mem_allDensityCodegreeCapFailureSet_iff]
      simp only [hH, true_and, CodegreeCapFailure]
    _ ≤ _ := allDensityCodegreeCapFailureSet_probability_le n M cap theta hn hM htheta

/-- Choosing the exponential tilt `log n` makes its positive term at
most the vertex-degree mean, at every edge density. -/
lemma codegree_chernoff_positive_term_le_mean (n M : ℕ) (hn : 1 ≤ n) :
    (M : ℝ) * (2 / ((n : ℝ) * (3 * n - 1))) *
      (Real.exp (Real.log (n : ℝ)) - 1) ≤ (M : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (3 * n - 1 : ℝ) := by linarith
  rw [Real.exp_log hnR]
  have hratio : (2 * ((n : ℝ) - 1)) / (3 * n - 1) ≤ 1 := by
    apply (div_le_one hd).mpr
    linarith
  calc
    _ = ((M : ℝ) / n) * (2 * ((n : ℝ) - 1) / (3 * n - 1)) := by
      field_simp
    _ ≤ ((M : ℝ) / n) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := mul_one _

lemma relativeCodegreeCap_failure_probability_le_uniform
    (ε delta kappa : ℝ) (hε : 0 ≤ ε) (hkappa : 0 ≤ kappa)
    (n M : ℕ) (hn : 1 ≤ n)
    (hMlower : upperEdgeCount ε n ≤ M) (hM : M ≤ (allEdges n).card)
    (hdelta : kappa + 1 ≤ delta * Real.log (n : ℝ)) :
    finsetProbability (sample n M)
        (CodegreeCapFailure n (relativeCodegreeCap n M delta)) ≤
      ((3 * n : ℝ)^2) * (((allEdges n).card + 1 : ℝ) *
        Real.exp (-kappa * Real.log ((3 * n : ℕ) : ℝ))) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hmean : Real.log ((3 * n : ℕ) : ℝ) ≤ (M : ℝ) / n :=
    (upperEdgeCount_mean_ge ε hε n (by omega)).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hMlower) (by positivity))
  have hcap : delta * ((M : ℝ) / n) ≤ (relativeCodegreeCap n M delta : ℝ) :=
    Nat.le_ceil _
  have hpositive := codegree_chernoff_positive_term_le_mean n M hn
  have hcaplog := mul_le_mul_of_nonneg_left hcap hlog
  have hdeltaMean := mul_le_mul_of_nonneg_right hdelta
    (show 0 ≤ (M : ℝ) / n by positivity)
  have hmeanK := mul_le_mul_of_nonneg_left hmean hkappa
  have harg : (M : ℝ) * (2 / ((n : ℝ) * (3 * n - 1))) *
      (Real.exp (Real.log (n : ℝ)) - 1) -
        Real.log (n : ℝ) * (relativeCodegreeCap n M delta + 1) ≤
          -kappa * Real.log ((3 * n : ℕ) : ℝ) := by
    nlinarith
  calc
    _ ≤ ((3 * n : ℝ)^2) * (((allEdges n).card + 1 : ℝ) *
        Real.exp ((M : ℝ) * (2 / ((n : ℝ) * (3 * n - 1))) *
          (Real.exp (Real.log (n : ℝ)) - 1) -
            Real.log (n : ℝ) * (relativeCodegreeCap n M delta + 1))) :=
      codegreeCapFailure_probability_le n M (relativeCodegreeCap n M delta)
        (Real.log (n : ℝ)) (by omega) hM hlog
    _ ≤ _ := by gcongr

lemma upper_codegree_path_failure_probability_tendsto_zero
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Tendsto (fun n : ℕ ↦
      finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n)
          ((allEdges n).card - upperEdgeCount ε n)))
        (LayerPathFailure (allEdges n) (upperEdgeCount ε n)
          (fun M ↦ CodegreeCapFailure n
            (relativeCodegreeCap n M (codegreeRelativeTolerance n))))) atTop (𝓝 0) := by
  have hlim := allEdges_polynomial_exp_log_tendsto_zero 2 2 12 (by norm_num)
  apply squeeze_zero' (Eventually.of_forall fun n ↦ finsetProbability_nonneg _ _) _ hlim
  filter_upwards [eventually_upperEdgeCount_collision_condition ε hε0 hε1,
    codegreeRelativeTolerance_mul_log_tendsto_atTop.eventually_ge_atTop 13,
    eventually_ge_atTop 1] with n hcollision hdelta hn
  have hM : upperEdgeCount ε n ≤ (allEdges n).card := by
    by_cases hzero : upperEdgeCount ε n = 0
    · simp [hzero]
    · have hpos : 0 < upperEdgeCount ε n := Nat.pos_of_ne_zero hzero
      nlinarith
  calc
    _ ≤ ((allEdges n).card + 1 : ℝ) *
        (((3 * n : ℝ)^2) * (((allEdges n).card + 1 : ℝ) *
          Real.exp (-12 * Real.log ((3 * n : ℕ) : ℝ)))) :=
      layerPath_failure_probability_le_card_mul n (upperEdgeCount ε n)
        (fun M ↦ CodegreeCapFailure n
          (relativeCodegreeCap n M (codegreeRelativeTolerance n))) _ hM (by positivity)
        (fun m hml hm ↦ relativeCodegreeCap_failure_probability_le_uniform
          ε (codegreeRelativeTolerance n) 12 hε0 (by norm_num) n m hn hml hm
          (by simpa only [show (12 : ℝ) + 1 = 13 by norm_num] using hdelta))
    _ = _ := by ring

lemma relativeCodegreeCap_ratio_le (n M : ℕ) (delta : ℝ)
    (hn : 0 < n) (hM : 0 < M) (hdelta : 0 ≤ delta) :
    (relativeCodegreeCap n M delta : ℝ) / ((M : ℝ) / n) ≤
      delta + 1 / ((M : ℝ) / n) := by
  have hmean : 0 < (M : ℝ) / n := by positivity
  have hceil : (relativeCodegreeCap n M delta : ℝ) ≤
      delta * ((M : ℝ) / n) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  apply (div_le_iff₀ hmean).mpr
  calc
    _ ≤ _ := hceil
    _ = _ := by field_simp

/-- A single error envelope controls the codegree/degree ratio throughout
all supercritical layers. -/
def codegreeRelativeError (n : ℕ) : ℝ :=
  codegreeRelativeTolerance n + 1 / Real.log ((3 * n : ℕ) : ℝ)

lemma codegreeRelativeError_tendsto_zero :
    Tendsto codegreeRelativeError atTop (𝓝 0) := by
  have hthree : Tendsto (fun n : ℕ ↦ ((3 * n : ℕ) : ℝ)) atTop atTop := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hthree)
  change Tendsto (fun n ↦ codegreeRelativeTolerance n +
    1 / Real.log ((3 * n : ℕ) : ℝ)) atTop (𝓝 0)
  simpa only [one_div, add_zero, Function.comp_def] using
    codegreeRelativeTolerance_tendsto_zero.add hinv

lemma relativeCodegreeCap_ratio_le_error
    (ε : ℝ) (hε : 0 ≤ ε) (n M : ℕ) (hn : 1 ≤ n)
    (hM : upperEdgeCount ε n ≤ M) :
    (relativeCodegreeCap n M (codegreeRelativeTolerance n) : ℝ) / ((M : ℝ) / n) ≤
      codegreeRelativeError n := by
  have hlog : 0 < Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * n by omega))
  have hmean : Real.log ((3 * n : ℕ) : ℝ) ≤ (M : ℝ) / n :=
    (upperEdgeCount_mean_ge ε hε n (by omega)).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hM) (by positivity))
  have hM0 : 0 < M := by
    by_contra hbad
    have hz : M = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_div] at hmean
    linarith
  exact (relativeCodegreeCap_ratio_le n M (codegreeRelativeTolerance n)
    (by omega) hM0 (codegreeRelativeTolerance_nonneg n)).trans
    (add_le_add le_rfl (one_div_le_one_div_of_le hlog hmean))

lemma eventually_relativeCodegreeCap_ratio_le
    (ε eta : ℝ) (hε : 0 ≤ ε) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ, upperEdgeCount ε n ≤ M →
      (relativeCodegreeCap n M (codegreeRelativeTolerance n) : ℝ) /
          ((M : ℝ) / n) ≤ eta := by
  have hsmall := (tendsto_order.1 codegreeRelativeError_tendsto_zero).2 eta heta
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hsmall hn
  intro M hM
  exact (relativeCodegreeCap_ratio_le_error ε hε n M hn hM).trans hsmall.le

end

end Erdos747
