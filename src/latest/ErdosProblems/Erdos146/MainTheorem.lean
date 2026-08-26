/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 146. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/146#post-8253
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos146.HammingHostAndExclusion

set_option linter.mathlibStandardSet false

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos146

attribute [local instance] Classical.propDecidable

section MainTheorem

noncomputable def manuscriptHammingRadius (dimension : ℕ) : ℕ :=
  ⌊tau * (dimension : ℝ)⌋₊

theorem manuscriptHammingRadius_le (dimension : ℕ) :
    (manuscriptHammingRadius dimension : ℝ) ≤
      tau * (dimension : ℝ) := by
  unfold manuscriptHammingRadius
  exact Nat.floor_le
    (mul_nonneg tau_pos.le (Nat.cast_nonneg dimension))

theorem manuscriptHammingRadius_le_dimension (dimension : ℕ) :
    manuscriptHammingRadius dimension ≤ dimension := by
  have hradius := manuscriptHammingRadius_le dimension
  have hdimension : 0 ≤ (dimension : ℝ) := Nat.cast_nonneg dimension
  have htau := tau_lt_one_half
  have hreal :
      (manuscriptHammingRadius dimension : ℝ) ≤ (dimension : ℝ) := by
    nlinarith
  exact_mod_cast hreal

theorem manuscriptHammingRadius_ratio_tendsto :
    Tendsto
      (fun dimension : ℕ =>
        (manuscriptHammingRadius dimension : ℝ) / (dimension : ℝ))
      atTop (𝓝 tau) := by
  unfold manuscriptHammingRadius
  exact
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) tau_pos.le).comp
      tendsto_natCast_atTop_atTop

theorem manuscriptHammingRadius_binEntropy_tendsto :
    Tendsto
      (fun dimension : ℕ =>
        Real.binEntropy
          ((manuscriptHammingRadius dimension : ℝ) / (dimension : ℝ)))
      atTop (𝓝 (Real.binEntropy tau)) := by
  exact Real.binEntropy_continuous.continuousAt.tendsto.comp
    manuscriptHammingRadius_ratio_tendsto

theorem manuscriptHammingBall_card_entropy_lower
    (dimension : ℕ) (word : HammingWord dimension) :
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((manuscriptHammingRadius dimension : ℝ) /
              (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      ((hammingBall dimension
        (manuscriptHammingRadius dimension) word).card : ℝ) := by
  calc
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((manuscriptHammingRadius dimension : ℝ) /
              (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      (dimension.choose (manuscriptHammingRadius dimension) : ℝ) :=
        exp_binary_entropy_div_le_choose dimension
          (manuscriptHammingRadius dimension)
          (manuscriptHammingRadius_le_dimension dimension)
    _ ≤ ((hammingBall dimension
        (manuscriptHammingRadius dimension) word).card : ℝ) := by
      exact_mod_cast hammingBall_card_ge_boundary_binomial
        dimension (manuscriptHammingRadius dimension) word

theorem eventually_manuscriptHammingRadius_binEntropy_ge
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.binEntropy tau - loss ≤
        Real.binEntropy
          ((manuscriptHammingRadius dimension : ℝ) /
            (dimension : ℝ)) := by
  have hneighborhood :
      Set.Ioi (Real.binEntropy tau - loss) ∈
        𝓝 (Real.binEntropy tau) :=
    Ioi_mem_nhds (by linarith)
  filter_upwards
    [manuscriptHammingRadius_binEntropy_tendsto hneighborhood]
    with dimension hdimension
  exact (show Real.binEntropy tau - loss <
    Real.binEntropy
      ((manuscriptHammingRadius dimension : ℝ) /
        (dimension : ℝ)) from hdimension).le

noncomputable def sampledHammingEdgeEntropyRate : ℝ :=
  (1 - 2 * midpointBeta) * Real.log 2 + Real.binEntropy tau

theorem sampledHammingEdgeEntropyRate_pos :
    0 < sampledHammingEdgeEntropyRate := by
  have hwindow := midpointBeta_lt_upper_unconditional
  unfold entropyUpperEndpoint at hwindow
  have hbeta := midpointBeta_lt_one
  have hbits : 0 < 1 - 2 * midpointBeta + binaryEntropy tau := by
    nlinarith
  have hentropy :
      Real.binEntropy tau = binaryEntropy tau * Real.log 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  unfold sampledHammingEdgeEntropyRate
  rw [hentropy]
  nlinarith [mul_pos hbits log_two_pos]

theorem eventually_manuscriptExpectedRetainedEdge_entropy_lower
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.exp
          ((dimension : ℝ) *
            (sampledHammingEdgeEntropyRate - loss)) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) := by
  filter_upwards
    [eventually_manuscriptHammingRadius_binEntropy_ge loss hloss]
    with dimension hentropy
  have hdegree :
      Real.exp
          ((dimension : ℝ) *
            Real.binEntropy
              ((manuscriptHammingRadius dimension : ℝ) /
                (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        ((∑ distance ∈
          Finset.range (manuscriptHammingRadius dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
    have hball := manuscriptHammingBall_card_entropy_lower dimension
      (fun _ : Fin dimension => false)
    rw [hammingBall_card] at hball
    exact hball
  calc
    Real.exp
        ((dimension : ℝ) *
          (sampledHammingEdgeEntropyRate - loss)) /
        ((dimension + 1 : ℕ) : ℝ) =
      (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp
          ((dimension : ℝ) * (Real.binEntropy tau - loss)) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        rw [hammingRetentionProbability_sq_mul_wordCount_eq_exp,
          ← mul_div_assoc, ← Real.exp_add]
        congr 1
        unfold sampledHammingEdgeEntropyRate
        ring_nf
    _ ≤ (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp
          ((dimension : ℝ) *
            Real.binEntropy
              ((manuscriptHammingRadius dimension : ℝ) /
                (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        gcongr
    _ ≤ (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        ((∑ distance ∈
          Finset.range (manuscriptHammingRadius dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
        gcongr
    _ = hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) := by
      rw [hammingExpectedRetainedEdgeCount_eq]

theorem manuscriptExpectedRetainedEdgeCount_tendsto_atTop :
    Tendsto
      (fun dimension : ℕ =>
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension))
      atTop atTop := by
  have hrate := sampledHammingEdgeEntropyRate_pos
  have hloss : 0 < sampledHammingEdgeEntropyRate / 2 := by
    positivity
  have hlower := eventually_manuscriptExpectedRetainedEdge_entropy_lower
    (sampledHammingEdgeEntropyRate / 2) hloss
  have hgrowth := exp_mul_div_nat_succ_tendsto_atTop
    (sampledHammingEdgeEntropyRate / 2) hloss
  have hhalf :
      sampledHammingEdgeEntropyRate -
          sampledHammingEdgeEntropyRate / 2 =
        sampledHammingEdgeEntropyRate / 2 := by
    ring
  apply tendsto_atTop_mono' atTop _ hgrowth
  filter_upwards [hlower] with dimension hdimension
  simpa only [hhalf, mul_comm] using hdimension

theorem manuscriptExpectedRetainedEdgeCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    manuscriptExpectedRetainedEdgeCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

noncomputable def manuscriptSamplingFailureBound
    (depth dimension : ℕ) : ℝ :=
  (((2 * depth : ℕ) : ℝ)) *
      Real.exp (-(dimension : ℝ) * Real.log 2) +
    4 / hammingExpectedRetainedVertexCount dimension +
    (4 / hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) +
      8 / (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)))

theorem manuscriptSamplingFailureBound_tendsto_zero
    (depth : ℕ) :
    Tendsto
      (manuscriptSamplingFailureBound depth)
      atTop (𝓝 0) := by
  have hexclusion := pairLayerExclusionProbability_tendsto_zero depth
  have hvertices :=
    hammingExpectedRetainedVertexCount_inv_tendsto_zero.const_mul 4
  have hedges :=
    manuscriptExpectedRetainedEdgeCount_inv_tendsto_zero.const_mul 4
  have hwords :=
    hammingRetentionProbability_mul_wordCount_inv_tendsto_zero.const_mul 8
  have htotal := (hexclusion.add hvertices).add (hedges.add hwords)
  have htotal_zero :
      Tendsto
        (fun dimension : ℕ =>
          (((2 * depth : ℕ) : ℝ)) *
              Real.exp (-(dimension : ℝ) * Real.log 2) +
            4 * (1 / hammingExpectedRetainedVertexCount dimension) +
            (4 * (1 / hammingExpectedRetainedEdgeCount dimension
                (manuscriptHammingRadius dimension)) +
              8 * (1 / (hammingRetentionProbability dimension *
                ((2 ^ dimension : ℕ) : ℝ)))))
        atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using htotal
  apply htotal_zero.congr'
  filter_upwards [] with dimension
  unfold manuscriptSamplingFailureBound
  push_cast
  simp only [div_eq_mul_inv]
  ring

noncomputable def manuscriptSamplingFailureEvent
    {depth : ℕ}
    (layerSizes : Fin depth → ℕ)
    (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  (badPairLayersRetentionEvent layerSizes dimension ∪
    {retained : Set (Bool × HammingWord dimension) |
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained}) ∪
    {retained : Set (Bool × HammingWord dimension) |
      hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained <
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2}

theorem manuscriptSamplingFailureEvent_real_le
    {depth dimension : ℕ}
    (layerSizes : Fin depth → ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, 4 ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        3 * logTwo
          (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1) :
    (hammingRetentionMeasure dimension).real
      (manuscriptSamplingFailureEvent layerSizes dimension) ≤
        manuscriptSamplingFailureBound depth dimension := by
  let vertexFailure : Set (Set (Bool × HammingWord dimension)) :=
    {retained : Set (Bool × HammingWord dimension) |
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained}
  let edgeFailure : Set (Set (Bool × HammingWord dimension)) :=
    {retained : Set (Bool × HammingWord dimension) |
      hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained <
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2}
  change
    (hammingRetentionMeasure dimension).real
      ((badPairLayersRetentionEvent layerSizes dimension ∪
        vertexFailure) ∪ edgeFailure) ≤
        manuscriptSamplingFailureBound depth dimension
  calc
    (hammingRetentionMeasure dimension).real
      ((badPairLayersRetentionEvent layerSizes dimension ∪
        vertexFailure) ∪ edgeFailure) ≤
      ((hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) +
       (hammingRetentionMeasure dimension).real vertexFailure) +
        (hammingRetentionMeasure dimension).real edgeFailure := by
      calc
        (hammingRetentionMeasure dimension).real
          ((badPairLayersRetentionEvent layerSizes dimension ∪
            vertexFailure) ∪ edgeFailure) ≤
          (hammingRetentionMeasure dimension).real
            (badPairLayersRetentionEvent layerSizes dimension ∪
              vertexFailure) +
            (hammingRetentionMeasure dimension).real edgeFailure :=
              MeasureTheory.measureReal_union_le _ _
        _ ≤ ((hammingRetentionMeasure dimension).real
              (badPairLayersRetentionEvent layerSizes dimension) +
            (hammingRetentionMeasure dimension).real vertexFailure) +
            (hammingRetentionMeasure dimension).real edgeFailure := by
              gcongr
              exact MeasureTheory.measureReal_union_le _ _
    _ ≤ ((((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2) +
        4 / hammingExpectedRetainedVertexCount dimension) +
        (4 / hammingExpectedRetainedEdgeCount dimension
            (manuscriptHammingRadius dimension) +
          8 / (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ))) := by
      gcongr
      · exact badPairLayersRetentionEvent_real_le
          layerSizes hdimension hparents hbase
      · exact hammingRetainedVertexCount_upper_tail_probability_le dimension
      · exact hammingRetainedEdgeCount_lower_tail_probability_le
          dimension (manuscriptHammingRadius dimension)
    _ = manuscriptSamplingFailureBound depth dimension := by
      rfl

theorem pairGraphOverFin_free_of_manuscript_exclusion
    {baseSize depth dimension : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension
        (manuscriptHammingRadius dimension) retained) := by
  exact pairGraphOverFin_free_of_layer_exclusion
    hbase hdimension hdepth
    (manuscriptHammingRadius_le dimension)
    retained hexclusion herror

theorem eventually_exists_pairGraph_free_dense_retainedHost :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        ∃ retained : Set (Bool × HammingWord dimension),
          (pairGraphOverFin baseSize depth).Free
              (retainedHammingHost dimension
                (manuscriptHammingRadius dimension) retained) ∧
          hammingRetainedVertexCount dimension retained <
            3 * hammingRetentionProbability dimension *
              ((2 ^ dimension : ℕ) : ℝ) ∧
          hammingExpectedRetainedEdgeCount dimension
              (manuscriptHammingRadius dimension) / 2 ≤
            hammingRetainedEdgeCount dimension
              (manuscriptHammingRadius dimension) retained := by
  obtain ⟨baseSize, depth, hbase, hdepth, hdepth_window, hlayers⟩ :=
    exists_actualPairLayer_exclusion_parameters
  let layerSizes : Fin depth → ℕ := fun layer =>
    Fintype.card (PairLayer baseSize layer.val)
  have hparents : ∀ layer, 4 ≤ layerSizes layer :=
    fun layer => (hlayers layer).1
  have hfirst_moment :
      ∀ layer,
        (layerSizes layer : ℝ) +
          3 * logTwo
            (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
            entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1 :=
    fun layer => (hlayers layer).2.2
  have hsmall :
      ∀ᶠ dimension : ℕ in Filter.atTop,
        manuscriptSamplingFailureBound depth dimension < 1 :=
    (tendsto_order.1
      (manuscriptSamplingFailureBound_tendsto_zero depth)).2
        1 (by norm_num)
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards [hsmall, Filter.eventually_gt_atTop 0] with dimension
    hbound hdimension
  obtain ⟨retained, houtside⟩ :=
    exists_hammingRetention_outside_event dimension
      (manuscriptSamplingFailureEvent layerSizes dimension)
      ((manuscriptSamplingFailureEvent_real_le layerSizes
        hdimension hparents hfirst_moment).trans_lt hbound)
  have hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (layerSizes layer) dimension side
              (midpointBeta - entropySlack) := by
    intro side layer hbad
    exact houtside (Or.inl (Or.inl (Set.mem_iUnion.mpr
      ⟨side, Set.mem_iUnion.mpr ⟨layer, hbad⟩⟩)))
  have hvertices :
      hammingRetainedVertexCount dimension retained <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) :=
    lt_of_not_ge fun hlarge => houtside (Or.inl (Or.inr hlarge))
  have hedges :
      hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 ≤
        hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained :=
    le_of_not_gt fun hlow => houtside (Or.inr hlow)
  exact ⟨retained,
    pairGraphOverFin_free_of_manuscript_exclusion
      hbase hdimension hdepth_window retained hexclusion
      (fun layer => (hlayers layer).2.1),
    hvertices, hedges⟩

theorem baseSize_le_pairVertex_card
    (baseSize depth : ℕ) :
    baseSize ≤ Fintype.card (PairVertex baseSize depth) := by
  calc
    baseSize = Fintype.card (PairLayer baseSize 0) :=
      (pairLayer_card_zero baseSize).symm
    _ ≤ Fintype.card (PairVertex baseSize depth) :=
      Fintype.card_le_of_embedding
        (pairLayerEmbedding baseSize depth 0 (by omega))

theorem pairGraphOverFin_forall_exists_adj
    (baseSize depth : ℕ)
    (hbase : 4 ≤ baseSize)
    (hdepth : 0 < depth) :
    ∀ vertex : Fin (Fintype.card (PairVertex baseSize depth)),
      ∃ neighbor,
        (pairGraphOverFin baseSize depth).Adj vertex neighbor := by
  have hcard : 2 ≤ Fintype.card (PairVertex baseSize depth) := by
    have hcard_base := baseSize_le_pairVertex_card baseSize depth
    omega
  let : Nontrivial (Fin (Fintype.card (PairVertex baseSize depth))) :=
    Fin.nontrivial_iff_two_le.mpr hcard
  intro vertex
  exact
    (pairGraphOverFin_connected baseSize depth (by omega) hdepth).preconnected
      |>.exists_adj_of_nontrivial vertex

noncomputable def manuscriptVertexCount (dimension : ℕ) : ℕ :=
  ⌈3 * hammingRetentionProbability dimension *
    ((2 ^ dimension : ℕ) : ℝ)⌉₊

open Classical in
theorem retainedVertex_card_le_manuscriptVertexCount
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension))
    (hvertices :
      hammingRetainedVertexCount dimension retained <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) :
    Fintype.card retained ≤ manuscriptVertexCount dimension := by
  have hreal :
      (Fintype.card retained : ℝ) ≤
        (manuscriptVertexCount dimension : ℝ) := by
    calc
      (Fintype.card retained : ℝ) =
          hammingRetainedVertexCount dimension retained :=
        (hammingRetainedVertexCount_eq_card dimension retained).symm
      _ ≤ 3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) := hvertices.le
      _ ≤ (⌈3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) :=
        Nat.le_ceil _
      _ = (manuscriptVertexCount dimension : ℝ) := rfl
  exact_mod_cast hreal

open Classical in
theorem eventually_expectedRetainedEdge_le_extremalNumber :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        hammingExpectedRetainedEdgeCount dimension
            (manuscriptHammingRadius dimension) / 2 ≤
          (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension)
            (pairGraphOverFin baseSize depth) : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hhosts⟩ :=
    eventually_exists_pairGraph_free_dense_retainedHost
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards [hhosts] with dimension hhost
  obtain ⟨retained, hfree, hvertices, hedges⟩ := hhost
  have hcard :=
    retainedVertex_card_le_manuscriptVertexCount
      dimension retained hvertices
  have hembedding :
      Nonempty (retained ↪ Fin (manuscriptVertexCount dimension)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using hcard
  obtain ⟨embedding⟩ := hembedding
  let paddedHost : SimpleGraph (Fin (manuscriptVertexCount dimension)) :=
    (retainedHammingHost dimension
      (manuscriptHammingRadius dimension) retained).map embedding
  have hpadded_free :
      (pairGraphOverFin baseSize depth).Free paddedHost := by
    exact Erdos146.free_map_of_no_isolated
      (pairGraphOverFin baseSize depth)
      (pairGraphOverFin_forall_exists_adj baseSize depth hbase hdepth)
      embedding hfree
  have hpadded_edges :
      paddedHost.edgeFinset.card ≤
        SimpleGraph.extremalNumber
          (manuscriptVertexCount dimension)
          (pairGraphOverFin baseSize depth) := by
    simpa using
      (SimpleGraph.card_edgeFinset_le_extremalNumber hpadded_free)
  calc
    hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) / 2 ≤
      hammingRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) retained := hedges
    _ = ((retainedHammingHost dimension
        (manuscriptHammingRadius dimension) retained).edgeFinset.card : ℝ) :=
      hammingRetainedEdgeCount_eq_edgeFinset_card
        dimension (manuscriptHammingRadius dimension) retained
    _ = (paddedHost.edgeFinset.card : ℝ) := by
      congr 1
      exact (SimpleGraph.card_edgeFinset_map embedding
        (retainedHammingHost dimension
          (manuscriptHammingRadius dimension) retained)).symm
    _ ≤ (SimpleGraph.extremalNumber
        (manuscriptVertexCount dimension)
        (pairGraphOverFin baseSize depth) : ℝ) := by
      exact_mod_cast hpadded_edges

noncomputable def manuscriptExtremalPower : ℝ :=
  (3 : ℝ) / 2 + exponentGain

theorem manuscriptExtremalPower_pos :
    0 < manuscriptExtremalPower := by
  unfold manuscriptExtremalPower
  linarith [exponentGain_pos]

noncomputable def manuscriptEntropyGap : ℝ :=
  certifiedWindowWidth * Real.log 2 / 16

theorem manuscriptEntropyGap_pos : 0 < manuscriptEntropyGap := by
  unfold manuscriptEntropyGap
  positivity [certifiedWindowWidth_pos, log_two_pos]

theorem sampledHammingEdgeEntropyRate_eq_manuscriptExtremalPower :
    sampledHammingEdgeEntropyRate =
      (1 - midpointBeta) * manuscriptExtremalPower * Real.log 2 +
        2 * manuscriptEntropyGap := by
  have hmidpoint :
      entropyUpperEndpoint - midpointBeta =
        certifiedWindowWidth / 2 := by
    have hwindow := entropyWindow_eq_certifiedWindowWidth
    unfold midpointBeta
    linarith
  have hupper :
      binaryEntropy tau = (entropyUpperEndpoint + 1) / 2 := by
    unfold entropyUpperEndpoint
    ring
  have hgain :
      (1 - midpointBeta) * exponentGain =
        certifiedWindowWidth / 8 := by
    have hnonzero : 1 - midpointBeta ≠ 0 :=
      (sub_pos.mpr midpointBeta_lt_one).ne'
    unfold exponentGain
    field_simp [hnonzero]
  have hbits :
      1 - 2 * midpointBeta + binaryEntropy tau =
        (1 - midpointBeta) *
            ((3 : ℝ) / 2 + exponentGain) +
          certifiedWindowWidth / 8 := by
    nlinarith [hmidpoint, hupper, hgain]
  have hentropy :
      Real.binEntropy tau = binaryEntropy tau * Real.log 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  calc
    sampledHammingEdgeEntropyRate =
        (1 - 2 * midpointBeta + binaryEntropy tau) *
          Real.log 2 := by
      unfold sampledHammingEdgeEntropyRate
      rw [hentropy]
      ring
    _ = ((1 - midpointBeta) *
          ((3 : ℝ) / 2 + exponentGain) +
          certifiedWindowWidth / 8) * Real.log 2 := by
      rw [hbits]
    _ = (1 - midpointBeta) *
          manuscriptExtremalPower * Real.log 2 +
        2 * manuscriptEntropyGap := by
      unfold manuscriptExtremalPower manuscriptEntropyGap
      ring

theorem manuscriptVertexCount_le_four_wordMean
    (dimension : ℕ)
    (hmean :
      1 ≤ hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)) :
    (manuscriptVertexCount dimension : ℝ) ≤
      4 * (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)) := by
  have hargument :
      0 ≤ 3 * hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by
    positivity [hammingRetentionProbability_pos dimension]
  have hceiling :
      (manuscriptVertexCount dimension : ℝ) <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) + 1 := by
    unfold manuscriptVertexCount
    exact Nat.ceil_lt_add_one hargument
  nlinarith

theorem eventually_manuscriptVertexCount_le_four_wordMean :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      (manuscriptVertexCount dimension : ℝ) ≤
        4 * (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  have hlarge := Filter.tendsto_atTop.1
    hammingRetentionProbability_mul_wordCount_tendsto_atTop (1 : ℝ)
  filter_upwards [hlarge] with dimension hdimension
  exact manuscriptVertexCount_le_four_wordMean dimension hdimension

theorem eventually_manuscriptEntropyGap_dominates_power_constant :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      2 * (4 : ℝ) ^ manuscriptExtremalPower ≤
        Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ) := by
  exact Filter.tendsto_atTop.1
    (exp_mul_div_nat_succ_tendsto_atTop
      manuscriptEntropyGap manuscriptEntropyGap_pos)
    (2 * (4 : ℝ) ^ manuscriptExtremalPower)

theorem eventually_manuscriptVertexCount_power_le_expectedRetainedEdge :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      (manuscriptVertexCount dimension : ℝ) ^
          manuscriptExtremalPower ≤
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 := by
  have hlower :=
    eventually_manuscriptExpectedRetainedEdge_entropy_lower
      manuscriptEntropyGap manuscriptEntropyGap_pos
  have hvertex :=
    eventually_manuscriptVertexCount_le_four_wordMean
  have hconstant :=
    eventually_manuscriptEntropyGap_dominates_power_constant
  filter_upwards [hlower, hvertex, hconstant] with dimension
    hedge_lower hvertex_bound hconstant_bound
  have hconstant_half :
      (4 : ℝ) ^ manuscriptExtremalPower ≤
        (Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
    linarith
  have hexponent :
      ((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower +
          manuscriptEntropyGap * (dimension : ℝ) =
        (dimension : ℝ) *
          (sampledHammingEdgeEntropyRate - manuscriptEntropyGap) := by
    rw [sampledHammingEdgeEntropyRate_eq_manuscriptExtremalPower]
    ring
  calc
    (manuscriptVertexCount dimension : ℝ) ^
        manuscriptExtremalPower ≤
      (4 * (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ))) ^
          manuscriptExtremalPower := by
        apply Real.rpow_le_rpow
        · positivity
        · exact hvertex_bound
        · exact manuscriptExtremalPower_pos.le
    _ = (4 : ℝ) ^ manuscriptExtremalPower *
        Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower) := by
      rw [hammingRetentionProbability_mul_wordCount_eq_exp,
        Real.mul_rpow (by norm_num) (Real.exp_pos _).le,
        ← Real.exp_mul]
    _ ≤ Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower) *
        ((Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2) := by
      calc
        (4 : ℝ) ^ manuscriptExtremalPower *
            Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) =
          Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) *
            (4 : ℝ) ^ manuscriptExtremalPower := by ring
        _ ≤ Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) *
            ((Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
              ((dimension + 1 : ℕ) : ℝ)) / 2) :=
          mul_le_mul_of_nonneg_left hconstant_half
            (Real.exp_pos _).le
    _ = (Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
              manuscriptExtremalPower +
            manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
      rw [Real.exp_add]
      ring
    _ = (Real.exp
          ((dimension : ℝ) *
            (sampledHammingEdgeEntropyRate - manuscriptEntropyGap)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
      rw [hexponent]
    _ ≤ hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 := by
      gcongr

theorem eventually_manuscriptVertexCount_power_le_extremalNumber :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        (manuscriptVertexCount dimension : ℝ) ^
            manuscriptExtremalPower ≤
          (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension)
            (pairGraphOverFin baseSize depth) : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hextremal⟩ :=
    eventually_expectedRetainedEdge_le_extremalNumber
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards
    [eventually_manuscriptVertexCount_power_le_expectedRetainedEdge,
      hextremal] with dimension hpower hbound
  exact hpower.trans hbound

theorem manuscriptVertexCount_tendsto_atTop :
    Filter.Tendsto manuscriptVertexCount Filter.atTop Filter.atTop := by
  have hscaled :
      Filter.Tendsto
        (fun dimension : ℕ =>
          3 * (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    hammingRetentionProbability_mul_wordCount_tendsto_atTop.const_mul_atTop
      (by norm_num)
  have hceiling := tendsto_nat_ceil_atTop.comp hscaled
  apply hceiling.congr'
  filter_upwards [] with dimension
  change
    ⌈3 * (hammingRetentionProbability dimension *
      ((2 ^ dimension : ℕ) : ℝ))⌉₊ =
      manuscriptVertexCount dimension
  unfold manuscriptVertexCount
  congr 1
  ring

theorem manuscriptVertexCount_succ_le_two_mul
    (dimension : ℕ) :
    manuscriptVertexCount (dimension + 1) ≤
      2 * manuscriptVertexCount dimension := by
  have hfactor :
      Real.exp ((1 - midpointBeta) * Real.log 2) ≤ (2 : ℝ) := by
    calc
      Real.exp ((1 - midpointBeta) * Real.log 2) ≤
          Real.exp (Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_pos midpointBeta_pos log_two_pos]
      _ = 2 := Real.exp_log (by norm_num)
  have hrecurrence :
      hammingRetentionProbability (dimension + 1) *
          ((2 ^ (dimension + 1) : ℕ) : ℝ) =
        Real.exp ((1 - midpointBeta) * Real.log 2) *
          (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)) := by
    rw [hammingRetentionProbability_mul_wordCount_eq_exp,
      hammingRetentionProbability_mul_wordCount_eq_exp,
      ← Real.exp_add]
    congr 1
    push_cast
    ring
  unfold manuscriptVertexCount
  apply Nat.ceil_le.mpr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    3 * hammingRetentionProbability (dimension + 1) *
        ((2 ^ (dimension + 1) : ℕ) : ℝ) =
      Real.exp ((1 - midpointBeta) * Real.log 2) *
        (3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        rw [show
          3 * hammingRetentionProbability (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ) =
            3 * (hammingRetentionProbability (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ)) by ring,
          hrecurrence]
        ring
    _ ≤ 2 * (3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hfactor (by
          positivity [hammingRetentionProbability_pos dimension])
    _ ≤ 2 *
          (⌈3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) := by
        gcongr
        exact Nat.le_ceil _

theorem exists_manuscriptVertexCount_bracket
    (minimum n : ℕ)
    (hminimum : manuscriptVertexCount minimum ≤ n) :
    ∃ dimension : ℕ,
      minimum ≤ dimension ∧
      manuscriptVertexCount dimension ≤ n ∧
      n < manuscriptVertexCount (dimension + 1) := by
  have hlarge :
      ∀ᶠ dimension : ℕ in Filter.atTop,
        n < manuscriptVertexCount dimension := by
    have hevent := Filter.tendsto_atTop.1
      manuscriptVertexCount_tendsto_atTop (n + 1)
    filter_upwards [hevent] with dimension hdimension
    omega
  obtain ⟨dimension, hdimension, hafter⟩ :=
    (hlarge.and (Filter.eventually_ge_atTop minimum)).exists
  have hexists :
      ∃ offset : ℕ,
        n < manuscriptVertexCount (minimum + offset) := by
    refine ⟨dimension - minimum, ?_⟩
    rw [Nat.add_sub_of_le hafter]
    exact hdimension
  let offset : ℕ := Nat.find hexists
  have hnext :
      n < manuscriptVertexCount (minimum + offset) :=
    Nat.find_spec hexists
  have hoffset : 0 < offset := by
    by_contra hnot
    have hzero : offset = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hzero] at hnext
    omega
  refine ⟨minimum + (offset - 1), by omega, ?_, ?_⟩
  · have hbefore :
        ¬ n < manuscriptVertexCount (minimum + (offset - 1)) := by
      exact Nat.find_min hexists (by omega)
    exact Nat.le_of_not_gt hbefore
  · rw [show minimum + (offset - 1) + 1 = minimum + offset by omega]
    exact hnext

open Classical in
theorem twoDegenerateExtremalCounterexample :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsTwoDegenerate H ∧
      (∀ coloring : H.Coloring (Fin 2), ∀ side : Fin 2,
        2 < (Finset.univ.filter
          (fun vertex : Fin q => coloring vertex = side)).sup
          (fun vertex => H.degree vertex)) ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  classical
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hsubsequence⟩ :=
    eventually_manuscriptVertexCount_power_le_extremalNumber
  have hwidth : certifiedWindowWidth < 1 := by
    rw [← entropyWindow_eq_certifiedWindowWidth]
    linarith [entropyLowerEndpoint_pos, entropyUpperEndpoint_lt_one]
  have hproduct :
      0 ≤ (depth : ℝ) * (1 - certifiedWindowWidth) :=
    mul_nonneg (Nat.cast_nonneg depth) (sub_nonneg.mpr hwidth.le)
  have hdepth_real : (2 : ℝ) < (depth : ℝ) := by
    nlinarith
  have hdepth_nat : 2 < depth := by
    exact_mod_cast hdepth_real
  have hdepth_two : 2 ≤ depth := by
    omega
  let forbidden :
      SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) :=
    pairGraphOverFin baseSize depth
  have hnoisolated :
      ∀ vertex : Fin (Fintype.card (PairVertex baseSize depth)),
        ∃ neighbor, forbidden.Adj vertex neighbor := by
    exact pairGraphOverFin_forall_exists_adj
      baseSize depth hbase hdepth
  refine ⟨Fintype.card (PairVertex baseSize depth), forbidden,
    pairGraphOverFin_connected baseSize depth (by omega) hdepth,
    pairGraphOverFin_isBipartite baseSize depth,
    pairGraphOverFin_isTwoDegenerate baseSize depth,
    ?_,
    1 / (2 : ℝ) ^ manuscriptExtremalPower,
    exponentGain, ?_, exponentGain_pos, ?_⟩
  · simpa only [forbidden] using
      pairGraphOverFin_bipartition_maximum_degree_gt_two
        baseSize depth hbase hdepth_two
  · exact one_div_pos.mpr
      (Real.rpow_pos_of_pos (by norm_num) manuscriptExtremalPower)
  · obtain ⟨minimum, hminimum⟩ :=
      Filter.eventually_atTop.1 hsubsequence
    apply Filter.eventually_atTop.2
    refine ⟨manuscriptVertexCount minimum, ?_⟩
    intro n hn
    obtain ⟨dimension, hdimension, hbelow, habove⟩ :=
      exists_manuscriptVertexCount_bracket minimum n hn
    have hdouble :=
      manuscriptVertexCount_succ_le_two_mul dimension
    have hn_bound :
        n ≤ 2 * manuscriptVertexCount dimension := by
      omega
    have hn_real :
        (n : ℝ) ≤
          2 * (manuscriptVertexCount dimension : ℝ) := by
      exact_mod_cast hn_bound
    have hsubseq := hminimum dimension hdimension
    have hmonotone :
        SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension) forbidden ≤
          SimpleGraph.extremalNumber n forbidden :=
      Erdos146.extremalNumber_monotone_of_no_isolated
        forbidden hnoisolated hbelow
    change
      (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (n : ℝ) ^ manuscriptExtremalPower ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ)
    calc
      (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (n : ℝ) ^ manuscriptExtremalPower ≤
        (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (2 * (manuscriptVertexCount dimension : ℝ)) ^
            manuscriptExtremalPower := by
          apply mul_le_mul_of_nonneg_left
          · exact Real.rpow_le_rpow
              (Nat.cast_nonneg n) hn_real
              manuscriptExtremalPower_pos.le
          · positivity
      _ = (manuscriptVertexCount dimension : ℝ) ^
            manuscriptExtremalPower := by
          rw [Real.mul_rpow (by norm_num)
            (Nat.cast_nonneg (manuscriptVertexCount dimension))]
          have htwo :
              (2 : ℝ) ^ manuscriptExtremalPower ≠ 0 :=
            (Real.rpow_pos_of_pos (by norm_num)
              manuscriptExtremalPower).ne'
          field_simp [htwo]
      _ ≤ (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension) forbidden : ℝ) :=
          hsubseq
      _ ≤ (SimpleGraph.extremalNumber n forbidden : ℝ) := by
          exact_mod_cast hmonotone

end MainTheorem

end Erdos146
