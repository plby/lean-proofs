import ErdosProblems.Erdos747.PathwiseMinimumDegree

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Summable regularity errors along every deletion layer -/

/-- Occurrence of a graph property at any recursive prefix, indexed by
the number of edges remaining at that prefix. -/
def LayerPathFailure {n : ℕ} (H : Finset (Edge n)) (M : ℕ)
    (P : ℕ → Finset (Edge n) → Prop) :
    DeletionHistory H (H.card - M) → Prop :=
  SomeDeletionPrefix (fun t e ↦ P (H.card - t) (historyState e t le_rfl))
    (H.card - M)

lemma layerPath_failure_probability_le_sum
    (n M : ℕ) (P : ℕ → Finset (Edge n) → Prop) :
    finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n) ((allEdges n).card - M)))
        (LayerPathFailure (allEdges n) M P) ≤
      ∑ t ∈ Finset.range ((allEdges n).card - M + 1),
        finsetProbability (sample n ((allEdges n).card - t))
          (P ((allEdges n).card - t)) := by
  calc
    _ ≤ ∑ t ∈ Finset.range ((allEdges n).card - M + 1),
        finsetProbability (Finset.univ : Finset (DeletionHistory (allEdges n) t))
          (fun e ↦ P ((allEdges n).card - t) (historyState e t le_rfl)) :=
      finsetProbability_someDeletionPrefix_le_sum (allEdges n)
        (fun t e ↦ P ((allEdges n).card - t) (historyState e t le_rfl))
        ((allEdges n).card - M) (Nat.sub_le _ _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      have htK : t ≤ (allEdges n).card := by
        have ht' := Finset.mem_range.mp ht
        omega
      exact historyState_probability_eq_sample_at_time htK (P ((allEdges n).card - t))

lemma layerPath_failure_probability_le_card_mul
    (n M : ℕ) (P : ℕ → Finset (Edge n) → Prop) (b : ℝ)
    (hM : M ≤ (allEdges n).card) (hb : 0 ≤ b)
    (hpoint : ∀ m, M ≤ m → m ≤ (allEdges n).card →
      finsetProbability (sample n m) (P m) ≤ b) :
    finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n) ((allEdges n).card - M)))
        (LayerPathFailure (allEdges n) M P) ≤
      ((allEdges n).card + 1 : ℝ) * b := by
  calc
    _ ≤ ∑ t ∈ Finset.range ((allEdges n).card - M + 1),
        finsetProbability (sample n ((allEdges n).card - t))
          (P ((allEdges n).card - t)) :=
      layerPath_failure_probability_le_sum n M P
    _ ≤ ∑ _t ∈ Finset.range ((allEdges n).card - M + 1), b := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_range.mp ht
      exact hpoint _ (by omega) (Nat.sub_le _ _)
    _ = (((allEdges n).card - M + 1 : ℕ) : ℝ) * b := by simp
    _ ≤ ((allEdges n).card + 1 : ℝ) * b := by
      apply mul_le_mul_of_nonneg_right _ hb
      exact_mod_cast (show (allEdges n).card - M + 1 ≤ (allEdges n).card + 1 by omega)

/-- A fixed polynomial in the vertex count is absorbed by a strictly
larger logarithmic exponential exponent. -/
lemma vertexPow_exp_log_tendsto_zero (p : ℕ) (kappa : ℝ)
    (hkappa : (p : ℝ) < kappa) :
    Tendsto (fun n : ℕ ↦ (3 * n : ℝ)^p *
      Real.exp (-kappa * Real.log ((3 * n : ℕ) : ℝ))) atTop (𝓝 0) := by
  have hthree : Tendsto (fun n : ℕ ↦ ((3 * n : ℕ) : ℝ)) atTop atTop := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hlog := Real.tendsto_log_atTop.comp hthree
  have hscaled := hlog.const_mul_atTop (sub_pos.mpr hkappa)
  have hlim := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hx : (0 : ℝ) < ((3 * n : ℕ) : ℝ) := by positivity
  dsimp only [Function.comp_def]
  rw [show -((kappa - p) * Real.log ((3 * n : ℕ) : ℝ)) =
      (p : ℝ) * Real.log ((3 * n : ℕ) : ℝ) +
        (-kappa * Real.log ((3 * n : ℕ) : ℝ)) by ring,
    Real.exp_add, ← Real.log_pow, Real.exp_log (pow_pos hx p)]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]

lemma allEdges_card_add_one_le (n : ℕ) (hn : 1 ≤ n) :
    ((allEdges n).card + 1 : ℝ) ≤ 2 * (3 * n : ℝ)^3 := by
  have hK : ((allEdges n).card : ℝ) ≤ (3 * n : ℝ)^3 := by
    rw [card_allEdges]
    exact_mod_cast Nat.choose_le_pow (3 * n) 3
  have hx1 : (1 : ℝ) ≤ 3 * n := by exact_mod_cast (show 1 ≤ 3 * n by omega)
  have hp := one_le_pow₀ hx1 (n := 3)
  linarith

/-- This form includes polynomial losses from conditioning on the sample
size and from union-bounding every deletion time. -/
lemma allEdges_polynomial_exp_log_tendsto_zero
    (p q : ℕ) (kappa : ℝ) (hkappa : ((p + 3 * q : ℕ) : ℝ) < kappa) :
    Tendsto (fun n : ℕ ↦ (3 * n : ℝ)^p *
      ((allEdges n).card + 1 : ℝ)^q *
        Real.exp (-kappa * Real.log ((3 * n : ℕ) : ℝ))) atTop (𝓝 0) := by
  have hlim := (vertexPow_exp_log_tendsto_zero (p + 3 * q) kappa hkappa).const_mul
    ((2 : ℝ)^q)
  norm_num only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  calc
    _ ≤ (3 * n : ℝ)^p * (2 * (3 * n : ℝ)^3)^q *
        Real.exp (-kappa * Real.log ((3 * n : ℕ) : ℝ)) := by
      gcongr
      exact allEdges_card_add_one_le n hn
    _ = _ := by
      rw [mul_pow (2 : ℝ) ((3 * n : ℝ)^3) q, ← pow_mul, pow_add]
      ring

lemma upperEdgeCount_mean_ge (ε : ℝ) (hε : 0 ≤ ε)
    (n : ℕ) (hn : 0 < n) :
    Real.log ((3 * n : ℕ) : ℝ) ≤ (upperEdgeCount ε n : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ hnR).2
  have hscale := shamirScale_le_upperEdgeCount ε hε n
  simpa only [shamirScale, Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hscale

lemma thirtyTwo_degree_chernoff_coefficient_le :
    (32 : ℝ) - 1 - 32 * Real.log 32 ≤ -12 := by
  have h := sq_div_le_mul_log_sub_add_one (x := (32 : ℝ)) (by norm_num)
  norm_num at h ⊢
  linarith

lemma degreeUpperFailure_probability_le_allDensity
    (n M : ℕ) (B : ℝ) (hn : 0 < n)
    (hM : M ≤ (allEdges n).card) (hB : 1 ≤ B) :
    finsetProbability (sample n M) (DegreeUpperFailure n M B) ≤
      (3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) * (B - 1 - B * Real.log B))) := by
  calc
    _ = finsetProbability (sample n M)
        (fun H ↦ H ∈ allDensityDegreeUpperFailureSet n M B) := by
      apply finsetProbability_congr_event
      intro H hH
      rw [mem_allDensityDegreeUpperFailureSet_iff]
      simp only [hH, true_and, DegreeUpperFailure]
    _ ≤ _ := allDensityDegreeUpperFailureSet_probability_le n M B hn hM hB

lemma degreeUpperFailure_probability_le_uniform
    (ε : ℝ) (hε : 0 ≤ ε) (n M : ℕ) (hn : 1 ≤ n)
    (hMlower : upperEdgeCount ε n ≤ M) (hM : M ≤ (allEdges n).card) :
    finsetProbability (sample n M) (DegreeUpperFailure n M 32) ≤
      (3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
        Real.exp (-12 * Real.log ((3 * n : ℕ) : ℝ))) := by
  have hmean : Real.log ((3 * n : ℕ) : ℝ) ≤ (M : ℝ) / n :=
    (upperEdgeCount_mean_ge ε hε n (by omega)).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hMlower) (by positivity))
  have harg : ((M : ℝ) / n) * (32 - 1 - 32 * Real.log 32) ≤
      -12 * Real.log ((3 * n : ℕ) : ℝ) := by
    have hfirst := mul_le_mul_of_nonneg_left thirtyTwo_degree_chernoff_coefficient_le
      (show 0 ≤ (M : ℝ) / n by positivity)
    nlinarith
  calc
    _ ≤ (3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) * (32 - 1 - 32 * Real.log 32))) :=
      degreeUpperFailure_probability_le_allDensity n M 32 (by omega) hM (by norm_num)
    _ ≤ _ := by gcongr

lemma upper_maxDegree_path_failure_probability_tendsto_zero
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Tendsto (fun n : ℕ ↦
      finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n)
          ((allEdges n).card - upperEdgeCount ε n)))
        (LayerPathFailure (allEdges n) (upperEdgeCount ε n)
          (fun M ↦ DegreeUpperFailure n M 32))) atTop (𝓝 0) := by
  have hlim := allEdges_polynomial_exp_log_tendsto_zero 1 2 12 (by norm_num)
  apply squeeze_zero' (Eventually.of_forall fun n ↦ finsetProbability_nonneg _ _) _ hlim
  filter_upwards [eventually_upperEdgeCount_collision_condition ε hε0 hε1,
    eventually_ge_atTop 1] with n hcollision hn
  have hM : upperEdgeCount ε n ≤ (allEdges n).card := by
    by_cases hzero : upperEdgeCount ε n = 0
    · simp [hzero]
    · have hpos : 0 < upperEdgeCount ε n := Nat.pos_of_ne_zero hzero
      nlinarith
  calc
    _ ≤ ((allEdges n).card + 1 : ℝ) *
        ((3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
          Real.exp (-12 * Real.log ((3 * n : ℕ) : ℝ)))) :=
      layerPath_failure_probability_le_card_mul n (upperEdgeCount ε n)
        (fun M ↦ DegreeUpperFailure n M 32) _ hM (by positivity)
        (fun m hml hm ↦ degreeUpperFailure_probability_le_uniform ε hε0 n m hn hml hm)
    _ = _ := by ring

end

end Erdos747
