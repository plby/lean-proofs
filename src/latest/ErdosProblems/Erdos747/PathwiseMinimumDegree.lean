import ErdosProblems.Erdos747.DyadicCheckpoints
import ErdosProblems.Erdos747.AllDensityAggregateBase
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Minimum-degree failure along the whole deletion path -/

def DegreeLowerPathFailure {n : ℕ} (H : Finset (Edge n)) (M : ℕ) (a : ℝ) :
    DeletionHistory H (H.card - M) → Prop :=
  SomeDeletionPrefix (fun t e ↦ DegreeLowerFailure n (H.card - t) a
    (historyState e t le_rfl)) (H.card - M)

lemma degreeLowerPath_failure_probability_le_dyadic_sum
    {n : ℕ} (H : Finset (Edge n)) (M : ℕ) (a : ℝ)
    (hM0 : 0 < M) (hM : M ≤ H.card) (ha : 0 ≤ a) :
    finsetProbability (Finset.univ : Finset (DeletionHistory H (H.card - M)))
        (DegreeLowerPathFailure H M (a / 2)) ≤
      ∑ t ∈ dyadicCheckpointSet H.card M,
        finsetProbability (Finset.univ : Finset (DeletionHistory H t))
          (fun e ↦ DegreeLowerFailure n (H.card - t) a
            (historyState e t le_rfl)) := by
  let I := dyadicCheckpointSet H.card M
  let proj : (i : ↥I) → DeletionHistory H (H.card - M) → DeletionHistory H i.1 :=
    fun i e ↦ deletionHistoryAt e i.1 (dyadicCheckpoint_le_terminal i.2)
  let P : (i : ↥I) → DeletionHistory H i.1 → Prop :=
    fun i e ↦ DegreeLowerFailure n (H.card - i.1) a
      (historyState e i.1 le_rfl)
  have hbound := finsetProbability_le_checkpoint_sum
    (Finset.univ : Finset (DeletionHistory H (H.card - M)))
    (Finset.univ : Finset ↥I) (fun i ↦ DeletionHistory H i.1)
    proj P (DegreeLowerPathFailure H M (a / 2))
    (by
      intro e he hbad
      obtain ⟨t, ht, hfail⟩ :=
        someDegreeLowerFailure_implies_dyadicCheckpoint H a hM0 hM ha e hbad
      exact ⟨⟨t, ht⟩, Finset.mem_univ _, hfail⟩)
    (by
      intro i hi
      exact (finsetProbability_deletionHistoryAt H (H.card - M) i.1
        (dyadicCheckpoint_le_terminal i.2) (Nat.sub_le _ _) (P i)).le)
  exact hbound.trans_eq
    (Finset.sum_subtype I (fun _ ↦ Iff.rfl)
      (fun t ↦ finsetProbability (Finset.univ : Finset (DeletionHistory H t))
        (fun e ↦ DegreeLowerFailure n (H.card - t) a
          (historyState e t le_rfl)))).symm

lemma degreeLowerPath_failure_probability_le_fixed_layer_sum
    (n M : ℕ) (a : ℝ) (hM0 : 0 < M)
    (hM : M ≤ (allEdges n).card) (ha : 0 ≤ a) :
    finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n) ((allEdges n).card - M)))
        (DegreeLowerPathFailure (allEdges n) M (a / 2)) ≤
      ∑ t ∈ dyadicCheckpointSet (allEdges n).card M,
        finsetProbability (sample n ((allEdges n).card - t))
          (DegreeLowerFailure n ((allEdges n).card - t) a) := by
  calc
    _ ≤ ∑ t ∈ dyadicCheckpointSet (allEdges n).card M,
        finsetProbability (Finset.univ : Finset (DeletionHistory (allEdges n) t))
          (fun e ↦ DegreeLowerFailure n ((allEdges n).card - t) a
            (historyState e t le_rfl)) :=
      degreeLowerPath_failure_probability_le_dyadic_sum (allEdges n) M a hM0 hM ha
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      have htK : t ≤ (allEdges n).card :=
        (dyadicCheckpoint_le_terminal ht).trans (Nat.sub_le _ _)
      exact historyState_probability_eq_sample_at_time htK
        (DegreeLowerFailure n ((allEdges n).card - t) a)

lemma degreeLowerPath_failure_probability_le_log_mul
    (n M : ℕ) (a p : ℝ) (hM0 : 0 < M)
    (hM : M ≤ (allEdges n).card) (ha : 0 ≤ a) (hp : 0 ≤ p)
    (hpoint : ∀ t ∈ dyadicCheckpointSet (allEdges n).card M,
      finsetProbability (sample n ((allEdges n).card - t))
        (DegreeLowerFailure n ((allEdges n).card - t) a) ≤ p) :
    finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n) ((allEdges n).card - M)))
        (DegreeLowerPathFailure (allEdges n) M (a / 2)) ≤
      ((Nat.log 2 (allEdges n).card + 1 : ℕ) : ℝ) * p := by
  calc
    _ ≤ ∑ t ∈ dyadicCheckpointSet (allEdges n).card M,
        finsetProbability (sample n ((allEdges n).card - t))
          (DegreeLowerFailure n ((allEdges n).card - t) a) :=
      degreeLowerPath_failure_probability_le_fixed_layer_sum n M a hM0 hM ha
    _ ≤ ∑ _t ∈ dyadicCheckpointSet (allEdges n).card M, p :=
      Finset.sum_le_sum hpoint
    _ = ((dyadicCheckpointSet (allEdges n).card M).card : ℝ) * p := by simp
    _ ≤ ((Nat.log 2 (allEdges n).card + 1 : ℕ) : ℝ) * p := by
      apply mul_le_mul_of_nonneg_right _ hp
      exact_mod_cast card_dyadicCheckpointSet_le (allEdges n).card M

lemma degreeLowerFailure_probability_le_allDensity
    (n M : ℕ) (a : ℝ) (hn : 0 < n)
    (hM : M ≤ (allEdges n).card) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    finsetProbability (sample n M) (DegreeLowerFailure n M a) ≤
      (3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) * (a - 1 - a * Real.log a))) := by
  calc
    finsetProbability (sample n M) (DegreeLowerFailure n M a) =
        finsetProbability (sample n M)
          (fun H ↦ H ∈ allDensityDegreeLowerFailureSet n M a) := by
      apply finsetProbability_congr_event
      intro H hH
      rw [mem_allDensityDegreeLowerFailureSet_iff]
      simp only [hH, true_and, DegreeLowerFailure]
    _ ≤ _ := allDensityDegreeLowerFailureSet_probability_le n M a hn hM ha0 ha1

/-- Above eight times the terminal layer, the stronger exponential decay
absorbs the polynomial conditioning cost of the all-density bound.  Below
that point, the collision estimate gives the sharp sparse bound. -/
lemma degreeLowerFailure_probability_le_uniform
    (n M₀ M : ℕ) (a kappa : ℝ)
    (hn : 1 ≤ n) (hMlower : M₀ ≤ M) (hM : M ≤ (allEdges n).card)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hkappa : 1 ≤ kappa)
    (hcoefficient : a - 1 - a * Real.log a ≤ 0)
    (hbase : ((M₀ : ℝ) / n) * (a - 1 - a * Real.log a) ≤
      -kappa * Real.log ((3 * n : ℕ) : ℝ))
    (hcollision : 2 * (8 * M₀) * (8 * M₀) ≤ (allEdges n).card) :
    finsetProbability (sample n M) (DegreeLowerFailure n M a) ≤
      (3 * n : ℝ) * (2 * Real.exp (-kappa * Real.log ((3 * n : ℕ) : ℝ))) := by
  have hn0 : 0 < n := by omega
  by_cases hsparse : M ≤ 8 * M₀
  · have hcollM : 2 * M * M ≤ (allEdges n).card := by
      calc
        2 * M * M ≤ 2 * (8 * M₀) * (8 * M₀) := by gcongr
        _ ≤ _ := hcollision
    have hMr : (M₀ : ℝ) ≤ M := by exact_mod_cast hMlower
    have hmean := div_le_div_of_nonneg_right hMr (Nat.cast_nonneg (α := ℝ) n)
    have hexponent := (mul_le_mul_of_nonpos_right hmean hcoefficient).trans hbase
    calc
      _ = finsetProbability (sample n M)
          (fun H ↦ ∃ v : Vertex n, (vertexDegree H v : ℝ) ≤ a * ((M : ℝ) / n)) := by
        apply finsetProbability_congr_event
        intro H hH
        rfl
      _ ≤ (3 * n : ℝ) * (2 * Real.exp
          (((M : ℝ) / n) * (a - 1 - a * Real.log a))) :=
        sampled_exists_degree_lower_factor_sample_le n M a hn0 ha0 ha1 hcollM
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num))
        (by positivity)
  · let x : ℝ := ((3 * n : ℕ) : ℝ)
    have hx : 0 < x := by dsimp only [x]; positivity
    have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast (show 1 ≤ 3 * n by omega)
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hMscale : (8 : ℝ) * M₀ ≤ M := by
      exact_mod_cast (show 8 * M₀ ≤ M by omega)
    have hmean := div_le_div_of_nonneg_right hMscale (Nat.cast_nonneg (α := ℝ) n)
    have hfirst := mul_le_mul_of_nonpos_right hmean hcoefficient
    have hbase8 := mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 8)
    have harg : ((M : ℝ) / n) * (a - 1 - a * Real.log a) ≤
        -kappa * Real.log x - 3 * Real.log x := by
      have hreshape : ((8 : ℝ) * M₀ / n) * (a - 1 - a * Real.log a) =
          8 * (((M₀ : ℝ) / n) * (a - 1 - a * Real.log a)) := by ring
      rw [hreshape] at hfirst
      have hnonneg := mul_nonneg (show 0 ≤ 7 * kappa - 3 by linarith) hlog
      dsimp only [x] at hlog hnonneg ⊢
      nlinarith
    have hK : ((allEdges n).card : ℝ) ≤ x^3 := by
      rw [card_allEdges]
      dsimp only [x]
      exact_mod_cast Nat.choose_le_pow (3 * n) 3
    have hx3 : 1 ≤ x^3 := one_le_pow₀ hx1
    have hKplus : ((allEdges n).card + 1 : ℝ) ≤ 2 * x^3 := by linarith
    have hexp3 : Real.exp (3 * Real.log x) = x^3 := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using Real.exp_log (pow_pos hx 3)
    have hfactor : ((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) * (a - 1 - a * Real.log a)) ≤
          2 * Real.exp (-kappa * Real.log x) := by
      calc
        _ ≤ (2 * x^3) * Real.exp (-kappa * Real.log x - 3 * Real.log x) := by
          gcongr
        _ = 2 * (Real.exp (3 * Real.log x) *
            Real.exp (-kappa * Real.log x - 3 * Real.log x)) := by
          rw [hexp3]
          ring
        _ = 2 * Real.exp (-kappa * Real.log x) := by
          rw [← Real.exp_add]
          congr 1
          congr 1
          ring
    exact (degreeLowerFailure_probability_le_allDensity
      n M a hn0 hM ha0 ha1).trans
      (mul_le_mul_of_nonneg_left hfactor (by positivity))

/-- The logarithmic number of checkpoints is bounded by the logarithm of
the vertex count, with an explicit constant independent of the layer. -/
lemma log_card_allEdges_add_one_le (n : ℕ) (hn : 1 ≤ n) :
    ((Nat.log 2 (allEdges n).card + 1 : ℕ) : ℝ) ≤
      3 * Real.log ((3 * n : ℕ) : ℝ) / Real.log 2 + 1 := by
  have hKpos : (0 : ℝ) < (allEdges n).card := by
    rw [card_allEdges]
    exact_mod_cast Nat.choose_pos (show 3 ≤ 3 * n by omega)
  have hK : ((allEdges n).card : ℝ) ≤ (((3 * n : ℕ) : ℝ)) ^ 3 := by
    rw [card_allEdges]
    exact_mod_cast Nat.choose_le_pow (3 * n) 3
  have hlog := Real.log_le_log hKpos hK
  rw [Real.log_pow] at hlog
  have hdiv := div_le_div_of_nonneg_right hlog
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have hnat := Real.natLog_le_logb (allEdges n).card 2
  rw [Real.logb] at hnat
  have hbound := hnat.trans hdiv
  norm_num only [Nat.cast_ofNat] at hbound
  norm_num only [Nat.cast_add, Nat.cast_one]
  linarith

/-- Even after the logarithmic checkpoint union, a vertex tail with
exponent strictly greater than one remains negligible. -/
lemma checkpoint_vertexUnion_exp_log_tendsto_zero
    (kappa : ℝ) (hkappa : 1 < kappa) :
    Tendsto (fun n : ℕ ↦
      ((Nat.log 2 (allEdges n).card + 1 : ℕ) : ℝ) *
        ((3 * n : ℝ) * (2 * Real.exp
          (-kappa * Real.log ((3 * n : ℕ) : ℝ))))) atTop (𝓝 0) := by
  let L : ℕ → ℝ := fun n ↦ Real.log ((3 * n : ℕ) : ℝ)
  let c : ℝ := kappa - 1
  have hc : 0 < c := sub_pos.mpr hkappa
  have hthree : Tendsto (fun n : ℕ ↦ ((3 * n : ℕ) : ℝ)) atTop atTop := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp hthree
  have hscaled : Tendsto (fun n ↦ c * L n) atTop atTop := hL.const_mul_atTop hc
  have hdecay : Tendsto (fun n ↦ Real.exp (-(c * L n))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled
  have hweighted : Tendsto
      (fun n ↦ (c * L n) * Real.exp (-(c * L n))) atTop (𝓝 0) := by
    simpa only [pow_one, Function.comp_def] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscaled
  have hbound : Tendsto (fun n ↦
      (3 * L n / Real.log 2 + 1) *
        ((3 * n : ℝ) * (2 * Real.exp (-kappa * L n)))) atTop (𝓝 0) := by
    have hlim := ((hweighted.const_mul (3 / (c * Real.log 2))).add hdecay).const_mul 2
    norm_num only [mul_zero, zero_add] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hx : (0 : ℝ) < ((3 * n : ℕ) : ℝ) := by positivity
    have hidentity : Real.exp (-(c * L n)) =
        (3 * n : ℝ) * Real.exp (-kappa * L n) := by
      rw [show -(c * L n) = L n + (-kappa * L n) by dsimp only [c]; ring,
        Real.exp_add]
      dsimp only [L]
      rw [Real.exp_log hx]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    rw [hidentity]
    field_simp [hc.ne', Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)]
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) _ hbound
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact mul_le_mul_of_nonneg_right (log_card_allEdges_add_one_le n hn) (by positivity)

/-- The sparse coupling remains available on every layer up to eight
times the terminal supercritical size. -/
lemma eventually_eight_upperEdgeCount_collision_condition (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      2 * (8 * upperEdgeCount ε n) * (8 * upperEdgeCount ε n) ≤
        (allEdges n).card := by
  have hratio := (upper_collision_ratio_tendsto_zero ε hε0 hε1).const_mul 64
  norm_num only [mul_zero] at hratio
  have hsmall := (tendsto_order.1 hratio).2 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hsmall hn
  have hKpos : (0 : ℝ) < ((3 * n).choose 3 : ℕ) := by
    exact_mod_cast Nat.choose_pos (show 3 ≤ 3 * n by omega)
  have hreal : (2 : ℝ) * (8 * (upperEdgeCount ε n : ℝ)) *
      (8 * (upperEdgeCount ε n : ℝ)) < ((3 * n).choose 3 : ℝ) := by
    rw [← mul_div_assoc] at hsmall
    have h := (div_lt_one hKpos).mp hsmall
    nlinarith
  rw [card_allEdges]
  exact_mod_cast hreal.le

/-- Minimum degree stays above a positive fixed multiple of its current
mean throughout the deletion trajectory to the supercritical layer. -/
lemma upper_minDegree_path_failure_probability_tendsto_zero
    (ε a : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hexp : 1 < (1 + ε) * (1 - a + a * Real.log a)) :
    Tendsto (fun n : ℕ ↦
      finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n)
          ((allEdges n).card - upperEdgeCount ε n)))
        (DegreeLowerPathFailure (allEdges n) (upperEdgeCount ε n) (a / 2)))
      atTop (𝓝 0) := by
  let kappa : ℝ := (1 + ε) * (1 - a + a * Real.log a)
  have hkappa : 1 < kappa := hexp
  have hgap : 0 < 1 - a + a * Real.log a := by
    have hone : 0 < 1 + ε := by linarith
    nlinarith [hexp]
  have hcoef : a - 1 - a * Real.log a ≤ 0 := by linarith
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦ finsetProbability_nonneg _ _) _
    (checkpoint_vertexUnion_exp_log_tendsto_zero kappa hkappa)
  filter_upwards [eventually_eight_upperEdgeCount_collision_condition ε hε0 hε1,
    eventually_ge_atTop 1] with n hcollision hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log ((3 * n : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * n by omega))
  have hscale := upperScale_le_upperEdgeCount ε (by linarith) n
  have hM0 : 0 < upperEdgeCount ε n := by
    have hs : (0 : ℝ) < (1 + ε) * shamirScale n := by
      dsimp only [shamirScale]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hlogpos ⊢
      exact mul_pos (by linarith) (mul_pos hnR hlogpos)
    exact_mod_cast (hs.trans_le hscale)
  have hM : upperEdgeCount ε n ≤ (allEdges n).card := by
    have hM1 : 1 ≤ upperEdgeCount ε n := hM0
    nlinarith
  have hmean : (1 + ε) * Real.log ((3 * n : ℕ) : ℝ) ≤
      (upperEdgeCount ε n : ℝ) / n := by
    apply (le_div_iff₀ hnR).2
    calc
      _ = (1 + ε) * shamirScale n := by
        dsimp only [shamirScale]
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ ≤ _ := hscale
  have hbase : ((upperEdgeCount ε n : ℝ) / n) *
      (a - 1 - a * Real.log a) ≤
        -kappa * Real.log ((3 * n : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonpos_right hmean hcoef
    dsimp only [kappa]
    nlinarith
  apply degreeLowerPath_failure_probability_le_log_mul n (upperEdgeCount ε n) a
    _ hM0 hM ha0.le (by positivity)
  intro t ht
  have htM := dyadicCheckpoint_le_terminal ht
  exact degreeLowerFailure_probability_le_uniform
    n (upperEdgeCount ε n) ((allEdges n).card - t) a kappa
    hn (by omega) (Nat.sub_le _ _) ha0 ha1 hkappa.le hcoef hbase hcollision

/-- The minimum-degree part of pathwise regularity, with a single
positive factor valid along the entire path. -/
lemma exists_upper_minDegree_path_factor_tendsto_zero
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      Tendsto (fun n : ℕ ↦
        finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n)
            ((allEdges n).card - upperEdgeCount ε n)))
          (DegreeLowerPathFailure (allEdges n) (upperEdgeCount ε n) a))
        atTop (𝓝 0) := by
  obtain ⟨a, ha0, ha1, hexp⟩ := exists_lower_degree_factor ε hε0
  refine ⟨a / 2, by positivity, by linarith, ?_⟩
  exact upper_minDegree_path_failure_probability_tendsto_zero
    ε a hε0.le hε1 ha0 ha1 hexp

end

end Erdos747
