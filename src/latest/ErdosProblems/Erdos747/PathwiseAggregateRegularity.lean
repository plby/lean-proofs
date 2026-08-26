import ErdosProblems.Erdos747.PathwiseCodegree

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Aggregate degree regularity along the whole deletion path -/

def aggregateDegreeTolerance (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (codegreeRelativeTolerance n))

lemma aggregateDegreeTolerance_nonneg (n : ℕ) :
    0 ≤ aggregateDegreeTolerance n := Real.sqrt_nonneg _

lemma aggregateDegreeTolerance_fourth (n : ℕ) :
    (aggregateDegreeTolerance n)^4 = codegreeRelativeTolerance n := by
  dsimp only [aggregateDegreeTolerance]
  calc
    _ = (Real.sqrt (Real.sqrt (codegreeRelativeTolerance n))^2)^2 := by ring
    _ = _ := by
      rw [Real.sq_sqrt (Real.sqrt_nonneg _),
        Real.sq_sqrt (codegreeRelativeTolerance_nonneg n)]

lemma aggregateDegreeTolerance_tendsto_zero :
    Tendsto aggregateDegreeTolerance atTop (𝓝 0) := by
  change Tendsto (fun n ↦ Real.sqrt (Real.sqrt (codegreeRelativeTolerance n)))
    atTop (𝓝 0)
  simpa only [Real.sqrt_zero] using codegreeRelativeTolerance_tendsto_zero.sqrt.sqrt

def AggregateDegreeFailure (n M : ℕ) (q : ℝ) (H : Finset (Edge n)) : Prop :=
  q * (3 * n : ℝ) < (degreeRelativeBadVertices n M q H).card

lemma eventually_log_three_mul_le_nat :
    ∀ᶠ n : ℕ in atTop, Real.log ((3 * n : ℕ) : ℝ) ≤ n := by
  have hsmall := (tendsto_order.1 tendsto_log_three_mul_div).2 1
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hsmall hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ((div_lt_one hnR).mp hsmall).le

lemma aggregateDegreeFailure_probability_le_uniform
    (ε q kappa : ℝ) (hε : 0 ≤ ε) (hkappa : 0 ≤ kappa)
    (n M : ℕ) (hn : 1 ≤ n) (hM0 : 0 < M)
    (hMlower : upperEdgeCount ε n ≤ M) (hM : M ≤ (allEdges n).card)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hbudget : 64 * (3 * Real.log 2 + kappa) ≤ q^4 * Real.log (n : ℝ))
    (hlog : Real.log ((3 * n : ℕ) : ℝ) ≤ n) :
    finsetProbability (sample n M) (AggregateDegreeFailure n M q) ≤
      8 * (((allEdges n).card + 1 : ℝ) *
        Real.exp (-kappa * Real.log ((3 * n : ℕ) : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogs : Real.log (n : ℝ) ≤ Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_le_log hnR (by exact_mod_cast (show n ≤ 3 * n by omega))
  have hmean : Real.log (n : ℝ) ≤ (M : ℝ) / n :=
    hlogs.trans ((upperEdgeCount_mean_ge ε hε n (by omega)).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hMlower) (by positivity)))
  have hMreal : Real.log (n : ℝ) * n ≤ (M : ℝ) := (le_div_iff₀ hnR).mp hmean
  have hbudgetN := mul_le_mul_of_nonneg_right hbudget hnR.le
  have hMbudget := mul_le_mul_of_nonneg_left hMreal (show 0 ≤ q^4 by positivity)
  have hklog := mul_le_mul_of_nonneg_left hlog hkappa
  have harg : (3 * n : ℝ) * Real.log 2 - q^2 * q^2 * (M : ℝ) / 64 ≤
      -kappa * Real.log ((3 * n : ℕ) : ℝ) := by
    nlinarith
  have hpow : (2 : ℝ)^(3 * n) = Real.exp ((3 * n : ℝ) * Real.log 2) := by
    simpa only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] using
      (Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2) (3 * n))).symm
  have hexp : (2 : ℝ)^(3 * n) * Real.exp (-(q^2 * q^2 * (M : ℝ) / 64)) ≤
      Real.exp (-kappa * Real.log ((3 * n : ℕ) : ℝ)) := by
    rw [hpow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  calc
    _ ≤ (2 : ℝ)^(3 * n) *
        (8 * (((allEdges n).card + 1 : ℝ) *
          Real.exp (-(q^2 * q^2 * (M : ℝ) / 64)))) :=
      degreeRelativeBadVertices_large_probability_le_allDensity
        n M q q (by omega) hM0 hM hq0 hq1 hq0
    _ = (8 * ((allEdges n).card + 1 : ℝ)) *
        ((2 : ℝ)^(3 * n) * Real.exp (-(q^2 * q^2 * (M : ℝ) / 64))) := by ring
    _ ≤ (8 * ((allEdges n).card + 1 : ℝ)) *
        Real.exp (-kappa * Real.log ((3 * n : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

lemma upper_aggregateDegree_path_failure_probability_tendsto_zero
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Tendsto (fun n : ℕ ↦
      finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n)
          ((allEdges n).card - upperEdgeCount ε n)))
        (LayerPathFailure (allEdges n) (upperEdgeCount ε n)
          (fun M ↦ AggregateDegreeFailure n M (aggregateDegreeTolerance n))))
      atTop (𝓝 0) := by
  have hlim := (allEdges_polynomial_exp_log_tendsto_zero 0 2 12 (by norm_num)).const_mul 8
  norm_num only [mul_zero] at hlim
  have hqsmall := (tendsto_order.1 aggregateDegreeTolerance_tendsto_zero).2 1
    (by norm_num : (0 : ℝ) < 1)
  apply squeeze_zero' (Eventually.of_forall fun n ↦ finsetProbability_nonneg _ _) _ hlim
  filter_upwards [eventually_upperEdgeCount_collision_condition ε hε0 hε1,
    codegreeRelativeTolerance_mul_log_tendsto_atTop.eventually_ge_atTop
      (64 * (3 * Real.log 2 + 12)), hqsmall, eventually_log_three_mul_le_nat,
    eventually_ge_atTop 1] with n hcollision hbudget hqsmall hlog hn
  have hM0 : 0 < upperEdgeCount ε n := by
    have hlogpos : 0 < Real.log ((3 * n : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < 3 * n by omega))
    have hmean := upperEdgeCount_mean_ge ε hε0 n (by omega)
    by_contra hbad
    have hz : upperEdgeCount ε n = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_div] at hmean
    linarith
  have hM : upperEdgeCount ε n ≤ (allEdges n).card := by nlinarith
  calc
    _ ≤ ((allEdges n).card + 1 : ℝ) *
        (8 * (((allEdges n).card + 1 : ℝ) *
          Real.exp (-12 * Real.log ((3 * n : ℕ) : ℝ)))) :=
      layerPath_failure_probability_le_card_mul n (upperEdgeCount ε n)
        (fun M ↦ AggregateDegreeFailure n M (aggregateDegreeTolerance n)) _
        hM (by positivity) (by
          intro m hml hm
          apply aggregateDegreeFailure_probability_le_uniform
            ε (aggregateDegreeTolerance n) 12 hε0 (by norm_num) n m hn
            (hM0.trans_le hml) hml hm (aggregateDegreeTolerance_nonneg n)
            hqsmall.le _ hlog
          simpa only [aggregateDegreeTolerance_fourth] using hbudget)
    _ = _ := by ring

/-- A failed aggregate layer certificate must fail one of its four
elementary random-regularity clauses. -/
lemma aggregateLayerRegular_compl_implies_four_failures
    (n M cap : ℕ) (a B q : ℝ) (H : Finset (Edge n))
    (hfail : ¬ AggregateLayerRegular n M cap a B q q B H) :
    DegreeLowerFailure n M a H ∨ DegreeUpperFailure n M B H ∨
      CodegreeCapFailure n cap H ∨ AggregateDegreeFailure n M q H := by
  by_contra hnone
  simp only [not_or] at hnone
  have hlow : ∀ v : Vertex n, a * ((M : ℝ) / n) < vertexDegree H v := by
    intro v
    by_contra hv
    exact hnone.1 ⟨v, le_of_not_gt hv⟩
  have hupp : ∀ v : Vertex n, (vertexDegree H v : ℝ) < B * ((M : ℝ) / n) := by
    intro v
    by_contra hv
    exact hnone.2.1 ⟨v, le_of_not_gt hv⟩
  have hcap : ∀ u v : Vertex n, u ≠ v → vertexCodegree H u v ≤ cap := by
    intro u v huv
    by_contra hbad
    exact hnone.2.2.1 ⟨u, v, huv, lt_of_not_ge hbad⟩
  have hagg : ((degreeRelativeBadVertices n M q H).card : ℝ) ≤ q * (3 * n : ℝ) :=
    le_of_not_gt hnone.2.2.2
  exact hfail ⟨hlow, hupp, hcap, hagg, fun v ↦ (hupp v).le⟩

lemma layerPath_failure_or_probability_le
    {n : ℕ} (H : Finset (Edge n)) (M : ℕ)
    (P Q : ℕ → Finset (Edge n) → Prop) :
    finsetProbability
        (Finset.univ : Finset (DeletionHistory H (H.card - M)))
        (LayerPathFailure H M (fun m G ↦ P m G ∨ Q m G)) ≤
      finsetProbability (Finset.univ : Finset (DeletionHistory H (H.card - M)))
        (LayerPathFailure H M P) +
      finsetProbability (Finset.univ : Finset (DeletionHistory H (H.card - M)))
        (LayerPathFailure H M Q) := by
  calc
    _ = finsetProbability
        (Finset.univ : Finset (DeletionHistory H (H.card - M)))
        (fun e ↦ LayerPathFailure H M P e ∨ LayerPathFailure H M Q e) := by
      apply finsetProbability_congr_event
      intro e he
      exact someDeletionPrefix_or
        (fun t e ↦ P (H.card - t) (historyState e t le_rfl))
        (fun t e ↦ Q (H.card - t) (historyState e t le_rfl)) (H.card - M) e
    _ ≤ _ := finsetProbability_or_le_add _ _ _

lemma layerPath_failure_probability_mono
    {n : ℕ} (H : Finset (Edge n)) (M : ℕ)
    (P Q : ℕ → Finset (Edge n) → Prop)
    (hPQ : ∀ m G, P m G → Q m G) :
    finsetProbability
        (Finset.univ : Finset (DeletionHistory H (H.card - M)))
        (LayerPathFailure H M P) ≤
      finsetProbability (Finset.univ : Finset (DeletionHistory H (H.card - M)))
        (LayerPathFailure H M Q) := by
  apply finsetProbability_mono_event
  intro e he hbad
  exact someDeletionPrefix_mono
    (fun t z hz ↦ hPQ (H.card - t) (historyState z t le_rfl) hz) _ e hbad

/-- The explicit regularity certificate for the final asymptotic
assembly.  The two tolerances vanish and the relative codegree cap is
uniformly negligible above the terminal layer. -/
def StandardAggregateLayerRegular (n M : ℕ) (a : ℝ) (H : Finset (Edge n)) : Prop :=
  AggregateLayerRegular n M (relativeCodegreeCap n M (codegreeRelativeTolerance n))
    a 32 (aggregateDegreeTolerance n) (aggregateDegreeTolerance n) 32 H

lemma standardAggregateLayer_path_failure_probability_le
    (n M : ℕ) (a : ℝ) :
    finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n) ((allEdges n).card - M)))
        (LayerPathFailure (allEdges n) M (fun m H ↦ ¬ StandardAggregateLayerRegular n m a H)) ≤
      finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n) ((allEdges n).card - M)))
          (DegreeLowerPathFailure (allEdges n) M a) +
        (finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n) ((allEdges n).card - M)))
          (LayerPathFailure (allEdges n) M (fun m ↦ DegreeUpperFailure n m 32)) +
        (finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n) ((allEdges n).card - M)))
          (LayerPathFailure (allEdges n) M (fun m ↦ CodegreeCapFailure n
            (relativeCodegreeCap n m (codegreeRelativeTolerance n)))) +
        finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n) ((allEdges n).card - M)))
          (LayerPathFailure (allEdges n) M
            (fun m ↦ AggregateDegreeFailure n m (aggregateDegreeTolerance n))))) := by
  let P₀ := fun m ↦ DegreeLowerFailure n m a
  let P₁ := fun m ↦ DegreeUpperFailure n m 32
  let P₂ := fun m ↦ CodegreeCapFailure n
    (relativeCodegreeCap n m (codegreeRelativeTolerance n))
  let P₃ := fun m ↦ AggregateDegreeFailure n m (aggregateDegreeTolerance n)
  let prob := fun P ↦ finsetProbability
    (Finset.univ : Finset (DeletionHistory (allEdges n) ((allEdges n).card - M)))
    (LayerPathFailure (allEdges n) M P)
  change prob (fun m H ↦ ¬ StandardAggregateLayerRegular n m a H) ≤
    prob P₀ + (prob P₁ + (prob P₂ + prob P₃))
  calc
    _ ≤ prob (fun m H ↦ P₀ m H ∨ P₁ m H ∨ P₂ m H ∨ P₃ m H) := by
      apply layerPath_failure_probability_mono
      intro m H hfail
      exact aggregateLayerRegular_compl_implies_four_failures n m
        (relativeCodegreeCap n m (codegreeRelativeTolerance n)) a 32
        (aggregateDegreeTolerance n) H hfail
    _ ≤ prob P₀ + prob (fun m H ↦ P₁ m H ∨ P₂ m H ∨ P₃ m H) :=
      layerPath_failure_or_probability_le (allEdges n) M P₀ _
    _ ≤ prob P₀ + (prob P₁ + prob (fun m H ↦ P₂ m H ∨ P₃ m H)) :=
      add_le_add le_rfl (layerPath_failure_or_probability_le (allEdges n) M P₁ _)
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl
      (layerPath_failure_or_probability_le (allEdges n) M P₂ P₃))

lemma upper_standardAggregateLayer_path_failure_probability_tendsto_zero
    (ε a : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hexp : 1 < (1 + ε) * (1 - a + a * Real.log a)) :
    Tendsto (fun n : ℕ ↦
      finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n)
          ((allEdges n).card - upperEdgeCount ε n)))
        (LayerPathFailure (allEdges n) (upperEdgeCount ε n)
          (fun M H ↦ ¬ StandardAggregateLayerRegular n M (a / 2) H))) atTop (𝓝 0) := by
  have hlim := (upper_minDegree_path_failure_probability_tendsto_zero
    ε a hε0 hε1 ha0 ha1 hexp).add
      ((upper_maxDegree_path_failure_probability_tendsto_zero ε hε0 hε1).add
        ((upper_codegree_path_failure_probability_tendsto_zero ε hε0 hε1).add
          (upper_aggregateDegree_path_failure_probability_tendsto_zero ε hε0 hε1)))
  norm_num only [add_zero] at hlim
  exact squeeze_zero (fun n ↦ finsetProbability_nonneg _ _)
    (fun n ↦ standardAggregateLayer_path_failure_probability_le n (upperEdgeCount ε n) (a / 2))
    hlim

lemma exists_upper_standardAggregateLayer_path_factor_tendsto_zero
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      Tendsto (fun n : ℕ ↦
        finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n)
            ((allEdges n).card - upperEdgeCount ε n)))
          (LayerPathFailure (allEdges n) (upperEdgeCount ε n)
            (fun M H ↦ ¬ StandardAggregateLayerRegular n M a H))) atTop (𝓝 0) := by
  obtain ⟨a, ha0, ha1, hexp⟩ := exists_lower_degree_factor ε hε0
  exact ⟨a / 2, by positivity, by linarith,
    upper_standardAggregateLayer_path_failure_probability_tendsto_zero
      ε a hε0.le hε1 ha0 ha1 hexp⟩

end

end Erdos747
