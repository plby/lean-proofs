/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 146. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/146#post-8253
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos146.HammingProfiles

set_option linter.mathlibStandardSet false

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos146

section SamplingAndHammingBalls

noncomputable def hammingRetentionProbability (dimension : ℕ) : ℝ :=
  Real.exp (-(midpointBeta * (dimension : ℝ) * Real.log 2))

theorem hammingRetentionProbability_pos (dimension : ℕ) :
    0 < hammingRetentionProbability dimension := by
  unfold hammingRetentionProbability
  exact Real.exp_pos _

theorem hammingRetentionProbability_le_one (dimension : ℕ) :
    hammingRetentionProbability dimension ≤ 1 := by
  unfold hammingRetentionProbability
  apply Real.exp_le_one_iff.mpr
  have hproduct :
      0 ≤ midpointBeta * (dimension : ℝ) * Real.log 2 :=
    mul_nonneg
      (mul_nonneg midpointBeta_pos.le (Nat.cast_nonneg dimension))
      log_two_pos.le
  linarith

theorem hammingRetentionProbability_mul_wordCount_eq_exp
    (dimension : ℕ) :
    hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) := by
  have hwords :
      ((2 ^ dimension : ℕ) : ℝ) =
        Real.exp ((dimension : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_cast
  unfold hammingRetentionProbability
  rw [hwords, ← Real.exp_add]
  congr 1
  ring

theorem hammingRetentionProbability_sq_mul_wordCount_eq_exp
    (dimension : ℕ) :
    hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - 2 * midpointBeta) * (dimension : ℝ) * Real.log 2) := by
  have hwords :
      ((2 ^ dimension : ℕ) : ℝ) =
        Real.exp ((dimension : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_cast
  unfold hammingRetentionProbability
  rw [hwords, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem hammingRetentionProbability_mul_wordCount_tendsto_atTop :
    Tendsto
      (fun dimension : ℕ =>
        hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ))
      atTop atTop := by
  have hrate : 0 < (1 - midpointBeta) * Real.log 2 :=
    mul_pos (sub_pos.mpr midpointBeta_lt_one) log_two_pos
  have hlinear :
      Tendsto
        (fun dimension : ℕ =>
          ((1 - midpointBeta) * Real.log 2) * (dimension : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hrate
  have hexponential := Real.tendsto_exp_atTop.comp hlinear
  apply hexponential.congr'
  filter_upwards [] with dimension
  simp only [Function.comp_apply]
  rw [hammingRetentionProbability_mul_wordCount_eq_exp]
  congr 1
  ring

theorem hammingRetentionProbability_mul_wordCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    hammingRetentionProbability_mul_wordCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

theorem exp_mul_div_nat_succ_tendsto_atTop
    (rate : ℝ) (hrate : 0 < rate) :
    Tendsto
      (fun dimension : ℕ =>
        Real.exp (rate * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ))
      atTop atTop := by
  have hquotient :
      Tendsto
        (fun dimension : ℕ =>
          Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ))
        atTop atTop := by
    have htendsto :=
      (tendsto_exp_mul_div_rpow_atTop 1 rate hrate).comp
        tendsto_natCast_atTop_atTop
    refine htendsto.congr' ?_
    filter_upwards [] with dimension
    simp [Function.comp_apply]
  have hhalf :
      Tendsto
        (fun dimension : ℕ =>
          (1 / 2 : ℝ) *
            (Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ)))
        atTop atTop :=
    hquotient.const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono' atTop _ hhalf
  filter_upwards [Filter.eventually_ge_atTop 1] with dimension hdimension
  have hpositive : 0 < (dimension : ℝ) := by
    exact_mod_cast (show 0 < dimension by omega)
  have hdimension_real : (1 : ℝ) ≤ (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    (1 / 2 : ℝ) *
        (Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ)) =
      Real.exp (rate * (dimension : ℝ)) /
        (2 * (dimension : ℝ)) := by
        ring
    _ ≤ Real.exp (rate * (dimension : ℝ)) /
        ((dimension + 1 : ℕ) : ℝ) := by
      gcongr
      push_cast
      nlinarith

noncomputable def hammingRetentionParameter (dimension : ℕ) : unitInterval :=
  ⟨hammingRetentionProbability dimension,
    hammingRetentionProbability_pos dimension |>.le,
    hammingRetentionProbability_le_one dimension⟩

noncomputable def hammingRetentionMeasure (dimension : ℕ) :
    MeasureTheory.Measure (Set (Bool × HammingWord dimension)) :=
  ProbabilityTheory.setBernoulli Set.univ
    (hammingRetentionParameter dimension)

theorem hammingRetentionMeasure_isProbability (dimension : ℕ) :
    MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) := by
  unfold hammingRetentionMeasure
  infer_instance

theorem hammingRetentionMeasure_integrable
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.Integrable observable
      (hammingRetentionMeasure dimension) := by
  let : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  exact MeasureTheory.Integrable.of_finite

theorem hammingRetentionMeasure_memLp_two
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.MemLp observable 2
      (hammingRetentionMeasure dimension) := by
  apply (MeasureTheory.memLp_two_iff_integrable_sq
    (hammingRetentionMeasure_integrable dimension observable).aestronglyMeasurable).mpr
  exact hammingRetentionMeasure_integrable dimension
    (fun retained => observable retained ^ 2)

theorem hammingRetentionMeasure_integral_eq_sum
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    (∫ retained,
      observable retained ∂hammingRetentionMeasure dimension) =
      ∑ retained : Set (Bool × HammingWord dimension),
        (hammingRetentionMeasure dimension).real {retained} *
          observable retained := by
  classical
  simpa [smul_eq_mul] using
    (MeasureTheory.integral_fintype
      (hammingRetentionMeasure_integrable dimension observable))

open Classical in
theorem hammingRetentionMeasure_real_event_eq_sum
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension))) :
    (hammingRetentionMeasure dimension).real event =
      ∑ retained : Set (Bool × HammingWord dimension),
        if retained ∈ event then
          (hammingRetentionMeasure dimension).real {retained}
        else 0 := by
  classical
  let : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  let support : Finset (Set (Bool × HammingWord dimension)) :=
    Finset.univ.filter (fun retained => retained ∈ event)
  have hsupport :
      (support : Set (Set (Bool × HammingWord dimension))) = event := by
    ext retained
    simp [support]
  calc
    (hammingRetentionMeasure dimension).real event =
        (hammingRetentionMeasure dimension).real support := by
      rw [hsupport]
    _ = ∑ retained ∈ support,
        (hammingRetentionMeasure dimension).real {retained} := by
      exact (MeasureTheory.sum_measureReal_singleton support).symm
    _ = ∑ retained : Set (Bool × HammingWord dimension),
        if retained ∈ event then
          (hammingRetentionMeasure dimension).real {retained}
        else 0 := by
      rw [← Finset.sum_filter]

open Classical in
theorem hammingRetentionMeasure_integral_event_indicator
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension))) :
    (∫ retained,
      (if retained ∈ event then (1 : ℝ) else 0)
        ∂hammingRetentionMeasure dimension) =
      (hammingRetentionMeasure dimension).real event := by
  rw [hammingRetentionMeasure_integral_eq_sum,
    hammingRetentionMeasure_real_event_eq_sum]
  apply Finset.sum_congr rfl
  intro retained _
  split_ifs <;> simp

theorem hammingRetentionMeasure_real_deviation_le
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |observable retained -
            (∫ candidate,
              observable candidate ∂hammingRetentionMeasure dimension)|} ≤
      ProbabilityTheory.variance observable
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := by
  let : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hchebyshev :=
    ProbabilityTheory.meas_ge_le_variance_div_sq
      (hammingRetentionMeasure_memLp_two dimension observable)
      hthreshold
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hchebyshev
  have hnonnegative :
      0 ≤ ProbabilityTheory.variance observable
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := by
    exact div_nonneg
      (ProbabilityTheory.variance_nonneg observable
        (hammingRetentionMeasure dimension))
      (sq_nonneg threshold)
  simpa [MeasureTheory.Measure.real, ENNReal.toReal_ofReal hnonnegative]
    using hreal

theorem hammingRetentionMeasure_real_contains_finset
    (dimension : ℕ)
    (required : Finset (Bool × HammingWord dimension)) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} =
      hammingRetentionProbability dimension ^ required.card := by
  classical
  have hpreimage :
      (fun membership : (Bool × HammingWord dimension) → Prop =>
        {vertex | membership vertex}) ⁻¹'
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained} =
        Set.pi (required : Set (Bool × HammingWord dimension))
          (fun _ => ({True} : Set Prop)) := by
    ext membership
    simp
  have hmeasure :
      hammingRetentionMeasure dimension
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained} =
        (↑(unitInterval.toNNReal
          (hammingRetentionParameter dimension)) : ENNReal) ^
            required.card := by
    unfold hammingRetentionMeasure
    rw [ProbabilityTheory.setBernoulli_apply']
    rw [hpreimage]
    rw [MeasureTheory.Measure.infinitePi_pi]
    · simp
    · intro vertex _
      measurability
  change
    ENNReal.toReal
        (hammingRetentionMeasure dimension
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained}) = _
  rw [hmeasure, ENNReal.toReal_pow]
  simp [hammingRetentionParameter]

theorem hammingRetentionMeasure_real_contains_pair
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension)
    (hdistinct : first ≠ second) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      hammingRetentionProbability dimension ^ 2 := by
  classical
  simpa [hdistinct] using
    hammingRetentionMeasure_real_contains_finset dimension {first, second}

theorem hammingRetentionMeasure_real_contains_vertex
    (dimension : ℕ)
    (vertex : Bool × HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained} =
      hammingRetentionProbability dimension := by
  classical
  simpa using
    hammingRetentionMeasure_real_contains_finset dimension {vertex}

theorem hammingRetentionMeasure_real_contains_edgePair
    (dimension : ℕ)
    (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      hammingRetentionProbability dimension ^
        (2 +
          (if firstLeft = secondLeft then 0 else 1) +
          (if firstRight = secondRight then 0 else 1)) := by
  classical
  let required : Finset (Bool × HammingWord dimension) :=
    {(false, firstLeft), (true, firstRight),
      (false, secondLeft), (true, secondRight)}
  have hevent :
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} := by
    ext retained
    simp [required, and_left_comm]
  rw [hevent, hammingRetentionMeasure_real_contains_finset]
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight
  · subst secondLeft
    subst secondRight
    simp [required]
  · subst secondLeft
    simp [required, hright]
  · subst secondRight
    simp [required, hleft]
  · simp [required, hleft, hright]

theorem hammingRetentionMeasure_real_contains_edgePair_le
    (dimension : ℕ)
    (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} ≤
      hammingRetentionProbability dimension ^ 4 +
        (if firstLeft = secondLeft then
          hammingRetentionProbability dimension ^ 3 else 0) +
        (if firstRight = secondRight then
          hammingRetentionProbability dimension ^ 3 else 0) +
        (if firstLeft = secondLeft ∧ firstRight = secondRight then
          hammingRetentionProbability dimension ^ 2 else 0) := by
  rw [hammingRetentionMeasure_real_contains_edgePair]
  have hnonnegative := (hammingRetentionProbability_pos dimension).le
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight <;>
    simp only [hleft, hright, ↓reduceIte, add_zero, Nat.reduceAdd,
      and_self, and_false, and_true, le_add_iff_nonneg_left, ge_iff_le,
      Std.le_refl] <;>
    positivity

noncomputable def hammingExpectedRetainedVertexCount
    (dimension : ℕ) : ℝ :=
  ∑ vertex : Bool × HammingWord dimension,
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained}

theorem hammingExpectedRetainedVertexCount_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexCount dimension =
      2 * hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by
  unfold hammingExpectedRetainedVertexCount
  simp_rw [hammingRetentionMeasure_real_contains_vertex]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [HammingWord]
  ring

theorem hammingExpectedRetainedVertexCount_pos
    (dimension : ℕ) :
    0 < hammingExpectedRetainedVertexCount dimension := by
  rw [hammingExpectedRetainedVertexCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  positivity

theorem hammingExpectedRetainedVertexCount_tendsto_atTop :
    Tendsto hammingExpectedRetainedVertexCount atTop atTop := by
  have hgrowth :=
    hammingRetentionProbability_mul_wordCount_tendsto_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)
  apply hgrowth.congr'
  filter_upwards [] with dimension
  rw [hammingExpectedRetainedVertexCount_eq]
  ring

theorem hammingExpectedRetainedVertexCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / hammingExpectedRetainedVertexCount dimension)
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    hammingExpectedRetainedVertexCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

theorem hammingRetentionMeasure_real_vertexPair
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      if first = second then
        hammingRetentionProbability dimension
      else hammingRetentionProbability dimension ^ 2 := by
  classical
  by_cases hequal : first = second
  · subst second
    have hevent :
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ first ∈ retained} =
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained} := by
      ext retained
      simp
    rw [hevent, hammingRetentionMeasure_real_contains_vertex]
    simp
  · rw [hammingRetentionMeasure_real_contains_pair
      dimension first second hequal]
    simp [hequal]

noncomputable def hammingExpectedRetainedVertexSquare
    (dimension : ℕ) : ℝ :=
  ∑ first : Bool × HammingWord dimension,
    ∑ second : Bool × HammingWord dimension,
      (hammingRetentionMeasure dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ second ∈ retained}

theorem hammingExpectedRetainedVertexSquare_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension =
      (((2 * 2 ^ dimension : ℕ) : ℝ) ^ 2) *
        hammingRetentionProbability dimension ^ 2 +
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        (hammingRetentionProbability dimension -
          hammingRetentionProbability dimension ^ 2) := by
  classical
  have hpoint
      (first second : Bool × HammingWord dimension) :
      (if first = second then
        hammingRetentionProbability dimension
      else hammingRetentionProbability dimension ^ 2) =
        hammingRetentionProbability dimension ^ 2 +
          (if first = second then
            hammingRetentionProbability dimension -
              hammingRetentionProbability dimension ^ 2
           else 0) := by
    by_cases hequal : first = second <;>
      simp [hequal]
  unfold hammingExpectedRetainedVertexSquare
  simp_rw [hammingRetentionMeasure_real_vertexPair,
    hpoint, Finset.sum_add_distrib]
  simp [HammingWord, nsmul_eq_mul]
  ring

theorem hammingExpectedRetainedVertexVariance_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 =
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        hammingRetentionProbability dimension *
        (1 - hammingRetentionProbability dimension) := by
  rw [hammingExpectedRetainedVertexSquare_eq,
    hammingExpectedRetainedVertexCount_eq]
  push_cast
  ring

theorem hammingExpectedRetainedVertexVariance_le_mean
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 ≤
      hammingExpectedRetainedVertexCount dimension := by
  rw [hammingExpectedRetainedVertexVariance_eq,
    hammingExpectedRetainedVertexCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  have hupper := hammingRetentionProbability_le_one dimension
  have hfactor :
      0 ≤ (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        hammingRetentionProbability dimension := by
    positivity
  have hle : 1 - hammingRetentionProbability dimension ≤ 1 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hle hfactor
  push_cast at hscaled ⊢
  nlinarith

noncomputable def hammingRetainedVertexCount
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : ℝ := by
  classical
  exact ∑ vertex : Bool × HammingWord dimension,
    if vertex ∈ retained then 1 else 0

open Classical in
theorem hammingRetainedVertexCount_eq_card
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedVertexCount dimension retained =
      (Fintype.card retained : ℝ) := by
  classical
  simp [hammingRetainedVertexCount, Fintype.card_subtype]

theorem hammingRetainedVertexCount_integral_eq
    (dimension : ℕ) :
    (∫ retained,
      hammingRetainedVertexCount dimension retained
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexCount dimension := by
  classical
  unfold hammingRetainedVertexCount hammingExpectedRetainedVertexCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun vertex _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if vertex ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro vertex _
  exact hammingRetentionMeasure_integral_event_indicator dimension
    {retained : Set (Bool × HammingWord dimension) | vertex ∈ retained}

open Classical in
theorem hammingRetainedVertexCount_sq
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedVertexCount dimension retained ^ 2 =
      ∑ first : Bool × HammingWord dimension,
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0 := by
  classical
  unfold hammingRetainedVertexCount
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  by_cases hfirst : first ∈ retained <;>
    by_cases hsecond : second ∈ retained <;>
    simp [hfirst, hsecond]

theorem hammingRetainedVertexCount_sq_integral_eq
    (dimension : ℕ) :
    (∫ retained,
      hammingRetainedVertexCount dimension retained ^ 2
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexSquare dimension := by
  classical
  simp_rw [hammingRetainedVertexCount_sq]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun first _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  unfold hammingExpectedRetainedVertexSquare
  apply Finset.sum_congr rfl
  intro first _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun second _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro second _
  rw [hammingRetentionMeasure_integral_eq_sum,
    hammingRetentionMeasure_real_event_eq_sum]
  apply Finset.sum_congr rfl
  intro retained _
  by_cases hretained : first ∈ retained ∧ second ∈ retained <;>
    simp [hretained]

theorem hammingRetainedVertexCount_variance_eq
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedVertexCount dimension)
        (hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 := by
  let : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  rw [ProbabilityTheory.variance_eq_sub
    (hammingRetentionMeasure_memLp_two dimension
      (hammingRetainedVertexCount dimension))]
  change
    (∫ retained,
      hammingRetainedVertexCount dimension retained ^ 2
        ∂hammingRetentionMeasure dimension) -
      (∫ retained,
        hammingRetainedVertexCount dimension retained
          ∂hammingRetentionMeasure dimension) ^ 2 =
      hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2
  rw [hammingRetainedVertexCount_sq_integral_eq,
    hammingRetainedVertexCount_integral_eq]

theorem hammingRetainedVertexCount_variance_le
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedVertexCount dimension)
        (hammingRetentionMeasure dimension) ≤
      hammingExpectedRetainedVertexCount dimension := by
  rw [hammingRetainedVertexCount_variance_eq]
  exact hammingExpectedRetainedVertexVariance_le_mean dimension

theorem hammingRetainedVertexCount_deviation_probability_le
    (dimension : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} ≤
      hammingExpectedRetainedVertexCount dimension / threshold ^ 2 := by
  have hchebyshev := hammingRetentionMeasure_real_deviation_le
    dimension (hammingRetainedVertexCount dimension)
    threshold hthreshold
  rw [hammingRetainedVertexCount_integral_eq] at hchebyshev
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} ≤
      ProbabilityTheory.variance
          (hammingRetainedVertexCount dimension)
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := hchebyshev
    _ ≤ hammingExpectedRetainedVertexCount dimension /
        threshold ^ 2 := by
      gcongr
      exact hammingRetainedVertexCount_variance_le dimension

theorem hammingRetainedVertexCount_upper_tail_probability_le
    (dimension : ℕ) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ≤
      4 / hammingExpectedRetainedVertexCount dimension := by
  let : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hmean := hammingExpectedRetainedVertexCount_pos dimension
  have hthreshold :
      0 < hammingExpectedRetainedVertexCount dimension / 2 := by
    positivity
  have hchebyshev := hammingRetainedVertexCount_deviation_probability_le
    dimension (hammingExpectedRetainedVertexCount dimension / 2)
    hthreshold
  have hsubset :
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ⊆
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedVertexCount dimension / 2 ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} := by
    intro retained hretained
    change
      hammingExpectedRetainedVertexCount dimension / 2 ≤
        |hammingRetainedVertexCount dimension retained -
          hammingExpectedRetainedVertexCount dimension|
    have habsolute := le_abs_self
      (hammingRetainedVertexCount dimension retained -
        hammingExpectedRetainedVertexCount dimension)
    rw [hammingExpectedRetainedVertexCount_eq] at habsolute ⊢
    change
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained at hretained
    nlinarith
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ≤
      (hammingRetentionMeasure dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          hammingExpectedRetainedVertexCount dimension / 2 ≤
            |hammingRetainedVertexCount dimension retained -
              hammingExpectedRetainedVertexCount dimension|} :=
        MeasureTheory.measureReal_mono hsubset
    _ ≤ hammingExpectedRetainedVertexCount dimension /
        (hammingExpectedRetainedVertexCount dimension / 2) ^ 2 :=
      hchebyshev
    _ = 4 / hammingExpectedRetainedVertexCount dimension := by
      field_simp [hmean.ne']
      ring

noncomputable def pairChildVertexFinset
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    Finset (Bool × HammingWord dimension) := by
  classical
  exact (Finset.univ : Finset (PairLayer parentCount 1)).image
    (fun pair => (side, children pair))

theorem pairChildVertexFinset_card
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (pairChildVertexFinset side children).card = parentCount.choose 2 := by
  classical
  unfold pairChildVertexFinset
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
      pairLayer_card_zero]
  · intro first second hequal
    exact hinjective (congrArg Prod.snd hequal)

def pairChildRetentionEvent
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    Set (Set (Bool × HammingWord dimension)) :=
  {retained | ∀ pair, (side, children pair) ∈ retained}

theorem hammingRetentionMeasure_real_pairChildren
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (hammingRetentionMeasure dimension).real
        (pairChildRetentionEvent side children) =
      hammingRetentionProbability dimension ^ (parentCount.choose 2) := by
  classical
  have hevent :
      pairChildRetentionEvent side children =
        {retained : Set (Bool × HammingWord dimension) |
          ∀ vertex ∈ pairChildVertexFinset side children,
            vertex ∈ retained} := by
    ext retained
    simp [pairChildRetentionEvent, pairChildVertexFinset]
  rw [hevent, hammingRetentionMeasure_real_contains_finset,
    pairChildVertexFinset_card side children hinjective]

noncomputable def badPairChildRetentionEvent
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) := by
  classical
  exact
    ⋃ children ∈
        (badPairChildArrays parents threshold).filter Function.Injective,
      pairChildRetentionEvent side children

theorem badPairChildRetentionEvent_real_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) :
    (hammingRetentionMeasure dimension).real
        (badPairChildRetentionEvent parents side threshold) ≤
      ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
  classical
  let distinctBad :
      Finset (PairLayer parentCount 1 → HammingWord dimension) :=
    (badPairChildArrays parents threshold).filter Function.Injective
  have hprobability_nonneg :
      0 ≤ hammingRetentionProbability dimension ^
        (parentCount.choose 2) :=
    pow_nonneg (hammingRetentionProbability_pos dimension).le _
  have hcard :
      (distinctBad.card : ℝ) ≤
        ((badPairChildArrays parents threshold).card : ℝ) := by
    dsimp [distinctBad]
    exact_mod_cast
      Finset.card_filter_le
        (badPairChildArrays parents threshold) Function.Injective
  calc
    (hammingRetentionMeasure dimension).real
        (badPairChildRetentionEvent parents side threshold) =
      (hammingRetentionMeasure dimension).real
        (⋃ children ∈ distinctBad,
          pairChildRetentionEvent side children) := by
        rfl
    _ ≤ ∑ children ∈ distinctBad,
          (hammingRetentionMeasure dimension).real
            (pairChildRetentionEvent side children) :=
        MeasureTheory.measureReal_biUnion_finset_le
          distinctBad (pairChildRetentionEvent side)
    _ = ∑ _children ∈ distinctBad,
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
        apply Finset.sum_congr rfl
        intro children hchildren
        have hinjective : Function.Injective children := by
          have hmembership :
              children ∈
                (badPairChildArrays parents threshold).filter
                  Function.Injective := by
            simpa only [distinctBad] using hchildren
          exact (Finset.mem_filter.mp hmembership).2
        exact hammingRetentionMeasure_real_pairChildren
          side children hinjective
    _ = (distinctBad.card : ℝ) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
        simp [nsmul_eq_mul]
    _ ≤ ((badPairChildArrays parents threshold).card : ℝ) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) :=
        mul_le_mul_of_nonneg_right hcard hprobability_nonneg
    _ ≤
      ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) :=
        mul_le_mul_of_nonneg_right
          (badPairChildArrays_card_le hparents hdimension parents threshold)
          hprobability_nonneg

theorem hammingParentTuple_card (parentCount dimension : ℕ) :
    Fintype.card (Fin parentCount → HammingWord dimension) =
      2 ^ (dimension * parentCount) := by
  simp [HammingWord, ← pow_mul]

noncomputable def badPairLayerRetentionEvent
    (parentCount dimension : ℕ)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ parents : Fin parentCount → HammingWord dimension,
    badPairChildRetentionEvent parents side threshold

theorem badPairLayerRetentionEvent_real_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (side : Bool)
    (threshold : ℝ) :
    (hammingRetentionMeasure dimension).real
        (badPairLayerRetentionEvent parentCount dimension side threshold) ≤
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
  classical
  let bound : ℝ :=
    ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (dimension : ℝ) * threshold)) *
        hammingRetentionProbability dimension ^
          (parentCount.choose 2)
  calc
    (hammingRetentionMeasure dimension).real
        (badPairLayerRetentionEvent parentCount dimension side threshold) =
      (hammingRetentionMeasure dimension).real
        (⋃ parents : Fin parentCount → HammingWord dimension,
          badPairChildRetentionEvent parents side threshold) := by
        rfl
    _ ≤ ∑ parents : Fin parentCount → HammingWord dimension,
          (hammingRetentionMeasure dimension).real
            (badPairChildRetentionEvent parents side threshold) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun parents => badPairChildRetentionEvent parents side threshold)
    _ ≤ ∑ _parents : Fin parentCount → HammingWord dimension, bound := by
      apply Finset.sum_le_sum
      intro parents _
      exact badPairChildRetentionEvent_real_le
        hparents hdimension parents side threshold
    _ =
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        hammingParentTuple_card]
      dsimp [bound]
      ring

theorem badPairLayerRetentionBound_eq_exp
    (parentCount dimension : ℕ) :
    ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (dimension : ℝ) * (midpointBeta - entropySlack))) *
        hammingRetentionProbability dimension ^
          (parentCount.choose 2)) =
      Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (parentCount.choose 2 : ℝ))) := by
  have hparent :
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
        Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
    calc
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
          (2 : ℝ) ^ (dimension * parentCount) := by
            norm_cast
      _ = Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hprofile :
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) =
        Real.exp
          (((3 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 2 + 1 : ℕ) : ℝ)) := by
    calc
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) =
          (((parentCount.choose 2 + 1 : ℕ) : ℝ)) ^
            (3 * dimension) := by
              norm_cast
      _ = Real.exp
          (((3 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 2 + 1 : ℕ) : ℝ)) := by
              rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hretention :
      hammingRetentionProbability dimension ^
          (parentCount.choose 2) =
        Real.exp
          ((parentCount.choose 2 : ℝ) *
            (-(midpointBeta * (dimension : ℝ) * Real.log 2))) := by
    unfold hammingRetentionProbability
    rw [Real.exp_nat_mul]
  rw [hparent, hprofile, hretention,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply congrArg Real.exp
  unfold logTwo
  push_cast
  field_simp [log_two_pos.ne']
  ring

theorem badPairLayerRetentionEvent_real_lt_exp_neg
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (hbase :
      (parentCount : ℝ) +
        3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * (parentCount.choose 2 : ℝ) < -1)
    (side : Bool) :
    (hammingRetentionMeasure dimension).real
      (badPairLayerRetentionEvent parentCount dimension side
        (midpointBeta - entropySlack)) <
      Real.exp (-(dimension : ℝ) * Real.log 2) := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    (hammingRetentionMeasure dimension).real
      (badPairLayerRetentionEvent parentCount dimension side
        (midpointBeta - entropySlack)) ≤
      ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * (midpointBeta - entropySlack))) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2)) :=
        badPairLayerRetentionEvent_real_le
          (by omega) hdimension side (midpointBeta - entropySlack)
    _ = Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (parentCount.choose 2 : ℝ))) :=
        badPairLayerRetentionBound_eq_exp parentCount dimension
    _ < Real.exp (-(dimension : ℝ) * Real.log 2) := by
      apply Real.exp_lt_exp.mpr
      have hscaled := mul_lt_mul_of_pos_left hbase
        (mul_pos hdimension_real log_two_pos)
      nlinarith

noncomputable def badPairLayersRetentionEvent
    {depth : ℕ}
    (layerSizes : Fin depth → ℕ)
    (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ side : Bool, ⋃ layer : Fin depth,
    badPairLayerRetentionEvent (layerSizes layer) dimension side
      (midpointBeta - entropySlack)

theorem badPairLayersRetentionEvent_real_le
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
        (badPairLayersRetentionEvent layerSizes dimension) ≤
      (((2 * depth : ℕ) : ℝ)) *
        Real.exp (-(dimension : ℝ) * Real.log 2) := by
  classical
  let bound : ℝ := Real.exp (-(dimension : ℝ) * Real.log 2)
  calc
    (hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) =
      (hammingRetentionMeasure dimension).real
        (⋃ side : Bool, ⋃ layer : Fin depth,
          badPairLayerRetentionEvent (layerSizes layer) dimension side
            (midpointBeta - entropySlack)) := by
        rfl
    _ ≤ ∑ side : Bool,
        (hammingRetentionMeasure dimension).real
          (⋃ layer : Fin depth,
            badPairLayerRetentionEvent (layerSizes layer) dimension side
              (midpointBeta - entropySlack)) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun side =>
            ⋃ layer : Fin depth,
              badPairLayerRetentionEvent (layerSizes layer) dimension side
                (midpointBeta - entropySlack))
    _ ≤ ∑ side : Bool, ∑ layer : Fin depth,
          (hammingRetentionMeasure dimension).real
            (badPairLayerRetentionEvent
              (layerSizes layer) dimension side
                (midpointBeta - entropySlack)) := by
        apply Finset.sum_le_sum
        intro side _
        exact MeasureTheory.measureReal_iUnion_fintype_le
          (fun layer =>
            badPairLayerRetentionEvent
              (layerSizes layer) dimension side
                (midpointBeta - entropySlack))
    _ ≤ ∑ _side : Bool, ∑ _layer : Fin depth, bound := by
        apply Finset.sum_le_sum
        intro side _
        apply Finset.sum_le_sum
        intro layer _
        exact (badPairLayerRetentionEvent_real_lt_exp_neg
          (hparents layer) hdimension (hbase layer) side).le
    _ = (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2) := by
        simp [bound, nsmul_eq_mul]
        ring

theorem exp_neg_dimension_log_two (dimension : ℕ) :
    Real.exp (-(dimension : ℝ) * Real.log 2) =
      ((1 / 2 : ℝ) ^ dimension) := by
  calc
    Real.exp (-(dimension : ℝ) * Real.log 2) =
        Real.exp (-((dimension : ℝ) * Real.log 2)) := by
          congr 1
          ring
    _ = (Real.exp ((dimension : ℝ) * Real.log 2))⁻¹ :=
      Real.exp_neg _
    _ = ((2 : ℝ) ^ dimension)⁻¹ := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ = ((1 / 2 : ℝ) ^ dimension) := by
      rw [← inv_pow]
      norm_num

theorem pairLayerExclusionProbability_tendsto_zero (depth : ℕ) :
    Filter.Tendsto
      (fun dimension : ℕ =>
        (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2))
      Filter.atTop (nhds 0) := by
  have hgeometric :
      Filter.Tendsto
        (fun dimension : ℕ => (1 / 2 : ℝ) ^ dimension)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simp_rw [exp_neg_dimension_log_two]
  simpa only [mul_zero] using
    hgeometric.const_mul (((2 * depth : ℕ) : ℝ))

theorem exists_hammingRetention_outside_event
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension)))
    (hsmall : (hammingRetentionMeasure dimension).real event < 1) :
    ∃ retained : Set (Bool × HammingWord dimension), retained ∉ event := by
  let : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  by_contra hnone
  push Not at hnone
  have hevent : event = Set.univ := Set.eq_univ_of_forall hnone
  rw [hevent] at hsmall
  simp at hsmall

theorem exists_actualPairLayer_exclusion_parameters :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ layer : Fin depth,
        let layerSize :=
          Fintype.card (PairLayer baseSize layer.val)
        4 ≤ layerSize ∧
        empiricalEntropyError layerSize < entropySlack ∧
        (layerSize : ℝ) +
          3 * logTwo ((layerSize.choose 2 + 1 : ℕ) : ℝ) -
            entropySlack * (layerSize.choose 2 : ℝ) < -1 := by
  obtain ⟨baseSize, hbase, hbase_conditions⟩ :=
    exists_entropy_exclusion_base
  obtain ⟨depth, hdepth, hdepth_window⟩ :=
    exists_entropy_exclusion_depth
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  intro layer
  dsimp
  have hsize :
      baseSize ≤ Fintype.card (PairLayer baseSize layer.val) :=
    pairLayer_card_ge_base baseSize layer.val hbase
  obtain ⟨herror, hfirst_moment⟩ :=
    hbase_conditions
      (Fintype.card (PairLayer baseSize layer.val)) hsize
  exact ⟨hbase.trans hsize, herror, hfirst_moment⟩

noncomputable def hammingDifferenceSet {dimension : ℕ}
    (u v : HammingWord dimension) : Finset (Fin dimension) := by
  classical
  exact Finset.univ.filter (fun coordinate => u coordinate ≠ v coordinate)

noncomputable def hammingFlip {dimension : ℕ}
    (u : HammingWord dimension) (coordinates : Finset (Fin dimension)) :
    HammingWord dimension := by
  classical
  exact fun coordinate =>
    if coordinate ∈ coordinates then !(u coordinate) else u coordinate

theorem hammingDifferenceSet_flip {dimension : ℕ}
    (u : HammingWord dimension) (coordinates : Finset (Fin dimension)) :
    hammingDifferenceSet u (hammingFlip u coordinates) = coordinates := by
  classical
  ext coordinate
  by_cases hcoordinate : coordinate ∈ coordinates
  · simp [hammingDifferenceSet, hammingFlip, hcoordinate]
  · simp [hammingDifferenceSet, hammingFlip, hcoordinate]

theorem hammingFlip_differenceSet {dimension : ℕ}
    (u v : HammingWord dimension) :
    hammingFlip u (hammingDifferenceSet u v) = v := by
  classical
  funext coordinate
  cases hu : u coordinate <;> cases hv : v coordinate <;>
    simp [hammingFlip, hammingDifferenceSet, hu, hv]

noncomputable def hammingBall (dimension radius : ℕ)
    (u : HammingWord dimension) : Finset (HammingWord dimension) := by
  classical
  exact Finset.univ.filter (fun v => hammingDist u v ≤ radius)

noncomputable def boundedDifferenceSets (dimension radius : ℕ) :
    Finset (Finset (Fin dimension)) := by
  classical
  exact ((Finset.univ : Finset (Fin dimension)).powerset).filter
    (fun coordinates => coordinates.card ≤ radius)

noncomputable def hammingBallEquiv (dimension radius : ℕ)
    (u : HammingWord dimension) :
    ↥(hammingBall dimension radius u) ≃
      ↥(boundedDifferenceSets dimension radius) := by
  classical
  refine
    { toFun := fun v => ⟨hammingDifferenceSet u v.val, ?_⟩
      invFun := fun coordinates =>
        ⟨hammingFlip u coordinates.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hball : hammingDist u v.val ≤ radius := by
      have hmembership : v.val ∈
          (Finset.univ.filter
            (fun w : HammingWord dimension => hammingDist u w ≤ radius)) := by
        simpa only [hammingBall] using v.property
      exact (Finset.mem_filter.mp hmembership).2
    simp only [boundedDifferenceSets, Finset.mem_filter,
      Finset.mem_powerset]
    refine ⟨Finset.subset_univ _, ?_⟩
    simpa [hammingDist, hammingDifferenceSet] using hball
  · have hcoordinates : coordinates.val.card ≤ radius := by
      have hmembership : coordinates.val ∈
          (((Finset.univ : Finset (Fin dimension)).powerset).filter
            (fun S => S.card ≤ radius)) := by
        simpa only [boundedDifferenceSets] using coordinates.property
      exact (Finset.mem_filter.mp hmembership).2
    simp only [hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
    change (hammingDifferenceSet u
      (hammingFlip u coordinates.val)).card ≤ radius
    simpa [hammingDifferenceSet_flip] using hcoordinates
  · intro v
    apply Subtype.ext
    exact hammingFlip_differenceSet u v.val
  · intro coordinates
    apply Subtype.ext
    exact hammingDifferenceSet_flip u coordinates.val

theorem boundedDifferenceSets_card (dimension radius : ℕ) :
    (boundedDifferenceSets dimension radius).card =
      ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
  classical
  have hmaps :
      ((boundedDifferenceSets dimension radius :
        Finset (Finset (Fin dimension))) : Set (Finset (Fin dimension))).MapsTo
        Finset.card (Finset.range (radius + 1)) := by
    intro S hS
    have hmembership : S ∈
        (((Finset.univ : Finset (Fin dimension)).powerset).filter
          (fun coordinates => coordinates.card ≤ radius)) := by
      exact Finset.mem_coe.mp hS
    have hcard := (Finset.mem_filter.mp hmembership).2
    exact Finset.mem_range.mpr (by omega)
  calc
    (boundedDifferenceSets dimension radius).card =
        ∑ d ∈ Finset.range (radius + 1),
          ((boundedDifferenceSets dimension radius).filter
            (fun coordinates => coordinates.card = d)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdle : d ≤ radius := by
        have := Finset.mem_range.mp hd
        omega
      have hfiber :
          (boundedDifferenceSets dimension radius).filter
            (fun coordinates => coordinates.card = d) =
          (Finset.univ : Finset (Fin dimension)).powersetCard d := by
        ext coordinates
        simp only [boundedDifferenceSets, Finset.mem_filter,
          Finset.mem_powerset, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨hsubset, _⟩, hcard⟩
          exact ⟨hsubset, hcard⟩
        · rintro ⟨hsubset, hcard⟩
          exact ⟨⟨hsubset, by omega⟩, hcard⟩
      rw [hfiber, Finset.card_powersetCard]
      simp

theorem hammingBall_card (dimension radius : ℕ)
    (u : HammingWord dimension) :
    (hammingBall dimension radius u).card =
      ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
  calc
    (hammingBall dimension radius u).card =
        Fintype.card ↥(hammingBall dimension radius u) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card ↥(boundedDifferenceSets dimension radius) :=
      Fintype.card_congr (hammingBallEquiv dimension radius u)
    _ = (boundedDifferenceSets dimension radius).card :=
      Fintype.card_coe _
    _ = ∑ d ∈ Finset.range (radius + 1), dimension.choose d :=
      boundedDifferenceSets_card dimension radius

end SamplingAndHammingBalls

end Erdos146
