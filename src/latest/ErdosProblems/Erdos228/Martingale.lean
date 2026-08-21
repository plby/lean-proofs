import Mathlib.Probability.Moments.SubGaussian

/-!
# Conditional-Gaussian finite walks for Erdős Problem 228

The edge-walk argument used in the Lovett--Meka partial-colouring theorem is a
finite stopped Gaussian walk.  After conditioning on the past, the projection
of its next increment onto any fixed constraint vector is a centred Gaussian;
its variance is bounded by a deterministic variance budget.  This file turns
exactly that input into the one- and two-sided tail estimates used by the
partial-colouring argument.

Mathlib already proves the hard analytic step: a sum of adapted conditionally
sub-Gaussian increments is sub-Gaussian.  The definitions below provide the
missing adapter from the conditional Gaussian MGF identity (with a possibly
random conditional variance) to Mathlib's conditional sub-Gaussian API.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace Erdos228.Martingale

/-! ## Exact conditional Gaussian MGF data -/

/-- `X` has, conditionally on `m`, the MGF of a centred Gaussian whose
conditional variance is `variance`.  Allowing the variance to depend on the
past is essential for a stopped Gaussian walk: after a coordinate or
constraint freezes, its conditional variance can drop to zero.

This is the precise fragment of conditional Gaussianity needed for
concentration.  It is stated using the same conditional-expectation kernel as
`HasCondSubgaussianMGF`, so no regular-conditional-distribution conversion is
needed downstream. -/
structure HasConditionalGaussianMGF
    {Omega : Type*} (m : MeasurableSpace Omega)
    {mOmega : MeasurableSpace Omega} (hm : m ≤ mOmega)
    [StandardBorelSpace Omega]
    (X : Omega → ℝ) (variance : Omega → ℝ≥0)
    (mu : Measure Omega := by volume_tac) [IsFiniteMeasure mu] : Prop where
  integrable_exp_mul :
    ∀ t : ℝ, Integrable (fun omega ↦ exp (t * X omega)) mu
  mgf_eq :
    ∀ᵐ omega ∂(mu.trim hm), ∀ t : ℝ,
      mgf X (condExpKernel mu m omega) t =
        exp (variance omega * t ^ 2 / 2)

namespace HasConditionalGaussianMGF

/-- A conditional centred-Gaussian MGF with almost-sure variance bounded by
`c` is conditionally sub-Gaussian with parameter `c`. -/
theorem hasCondSubgaussianMGF
    {Omega : Type*} {m mOmega : MeasurableSpace Omega} {hm : m ≤ mOmega}
    [StandardBorelSpace Omega]
    {X : Omega → ℝ} {variance : Omega → ℝ≥0}
    {mu : Measure Omega} [IsFiniteMeasure mu] {c : ℝ≥0}
    (hX : HasConditionalGaussianMGF m hm X variance (mu := mu))
    (hvariance : ∀ᵐ omega ∂(mu.trim hm), variance omega ≤ c) :
    HasCondSubgaussianMGF m hm X c (μ := mu) := by
  rw [HasCondSubgaussianMGF]
  constructor
  · rw [condExpKernel_comp_trim]
    exact hX.integrable_exp_mul
  · filter_upwards [hX.mgf_eq, hvariance] with omega hmgf hvar t
    rw [hmgf]
    gcongr

end HasConditionalGaussianMGF

/-! ## Finite sums -/

/-- The sum of the first `n` increments of a real-valued finite walk. -/
def partialSum {Omega : Type*} (increment : ℕ → Omega → ℝ)
    (n : ℕ) (omega : Omega) : ℝ :=
  ∑ i ∈ Finset.range n, increment i omega

@[simp]
theorem partialSum_zero {Omega : Type*} (increment : ℕ → Omega → ℝ) :
    partialSum increment 0 = 0 := by
  funext omega
  simp [partialSum]

theorem partialSum_succ {Omega : Type*} (increment : ℕ → Omega → ℝ) (n : ℕ) :
    partialSum increment (n + 1) =
      fun omega ↦ partialSum increment n omega + increment n omega := by
  funext omega
  simpa [partialSum] using Finset.sum_range_succ (fun i ↦ increment i omega) n

/-- An adapted finite walk whose later increments are conditionally centred
Gaussian is sub-Gaussian.  The zeroth increment is kept as a separate
sub-Gaussian input because it is not conditioned on an earlier filtration.

This theorem directly accommodates a stopped edge-walk: take `variance i` to
be the conditional variance after applying all freezes decided by time
`i - 1`, and prove `variance i ≤ varianceBound i` almost surely. -/
theorem partialSum_hasSubgaussianMGF_of_conditionalGaussian
    {Omega : Type*} {mOmega : MeasurableSpace Omega} [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsZeroOrProbabilityMeasure mu]
    {increment : ℕ → Omega → ℝ} {variance : ℕ → Omega → ℝ≥0}
    {varianceBound : ℕ → ℝ≥0} {filtration : Filtration ℕ mOmega}
    (hAdapted : StronglyAdapted filtration increment)
    (hzero : HasSubgaussianMGF (increment 0) (varianceBound 0) mu)
    (n : ℕ)
    (hGaussian : ∀ i < n - 1,
      HasConditionalGaussianMGF (filtration i) (filtration.le i)
        (increment (i + 1)) (variance (i + 1)) (mu := mu))
    (hVariance : ∀ i < n - 1,
      ∀ᵐ omega ∂(mu.trim (filtration.le i)),
        variance (i + 1) omega ≤ varianceBound (i + 1)) :
    HasSubgaussianMGF (partialSum increment n)
      (∑ i ∈ Finset.range n, varianceBound i) mu := by
  apply HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF hAdapted hzero n
  intro i hi
  exact (hGaussian i hi).hasCondSubgaussianMGF (hVariance i hi)

/-! ## Tail bounds -/

/-- A reusable two-sided Chernoff estimate. -/
theorem measureReal_abs_ge_le_of_hasSubgaussianMGF
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {X : Omega → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c mu)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    mu.real {omega | epsilon ≤ |X omega|} ≤
      2 * exp (-epsilon ^ 2 / (2 * c)) := by
  have hset : {omega | epsilon ≤ |X omega|} =
      {omega | epsilon ≤ X omega} ∪ {omega | epsilon ≤ -X omega} := by
    ext omega
    simp only [mem_ofPred_eq, mem_union]
    constructor
    · intro h
      by_cases hnonneg : 0 ≤ X omega
      · exact Or.inl (by simpa [abs_of_nonneg hnonneg] using h)
      · exact Or.inr (by simpa [abs_of_nonpos (le_of_not_ge hnonneg)] using h)
    · rintro (h | h)
      · exact h.trans (le_abs_self (X omega))
      · exact h.trans (neg_le_abs (X omega))
  rw [hset]
  calc
    mu.real ({omega | epsilon ≤ X omega} ∪ {omega | epsilon ≤ -X omega}) ≤
        mu.real {omega | epsilon ≤ X omega} +
          mu.real {omega | epsilon ≤ -X omega} := measureReal_union_le _ _
    _ ≤ exp (-epsilon ^ 2 / (2 * c)) + exp (-epsilon ^ 2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hepsilon) (hX.neg.measure_ge_le hepsilon)
    _ = 2 * exp (-epsilon ^ 2 / (2 * c)) := by ring

/-- Two-sided concentration for the terminal value of an adapted,
conditionally Gaussian finite walk. -/
theorem conditionalGaussian_partialSum_abs_tail
    {Omega : Type*} {mOmega : MeasurableSpace Omega} [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsZeroOrProbabilityMeasure mu]
    {increment : ℕ → Omega → ℝ} {variance : ℕ → Omega → ℝ≥0}
    {varianceBound : ℕ → ℝ≥0} {filtration : Filtration ℕ mOmega}
    (hAdapted : StronglyAdapted filtration increment)
    (hzero : HasSubgaussianMGF (increment 0) (varianceBound 0) mu)
    (n : ℕ)
    (hGaussian : ∀ i < n - 1,
      HasConditionalGaussianMGF (filtration i) (filtration.le i)
        (increment (i + 1)) (variance (i + 1)) (mu := mu))
    (hVariance : ∀ i < n - 1,
      ∀ᵐ omega ∂(mu.trim (filtration.le i)),
        variance (i + 1) omega ≤ varianceBound (i + 1))
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    mu.real {omega | epsilon ≤ |partialSum increment n omega|} ≤
      2 * exp (-epsilon ^ 2 /
        (2 * ∑ i ∈ Finset.range n, varianceBound i)) := by
  exact measureReal_abs_ge_le_of_hasSubgaussianMGF
    (partialSum_hasSubgaussianMGF_of_conditionalGaussian hAdapted hzero n
      hGaussian hVariance) hepsilon

/-! ## Simultaneous control of finitely many constraints -/

/-- A union bound for finitely many (not necessarily independent)
sub-Gaussian constraint variables.  In the partial-colouring application the
index type is the finite family of constraint vectors. -/
theorem measureReal_exists_abs_ge_le_of_hasSubgaussianMGF
    {Omega J : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    (s : Finset J) {X : J → Omega → ℝ} {c : J → ℝ≥0}
    {epsilon : J → ℝ}
    (hX : ∀ j ∈ s, HasSubgaussianMGF (X j) (c j) mu)
    (hepsilon : ∀ j ∈ s, 0 ≤ epsilon j) :
    mu.real {omega | ∃ j ∈ s, epsilon j ≤ |X j omega|} ≤
      ∑ j ∈ s, 2 * exp (-(epsilon j) ^ 2 / (2 * c j)) := by
  classical
  have hset : {omega | ∃ j ∈ s, epsilon j ≤ |X j omega|} =
      ⋃ j ∈ s, {omega | epsilon j ≤ |X j omega|} := by
    ext omega
    simp
  rw [hset]
  refine (measureReal_biUnion_finset_le s
    (fun j ↦ {omega | epsilon j ≤ |X j omega|})).trans ?_
  exact Finset.sum_le_sum fun j hj ↦
    measureReal_abs_ge_le_of_hasSubgaussianMGF (hX j hj) (hepsilon j hj)

end Erdos228.Martingale
