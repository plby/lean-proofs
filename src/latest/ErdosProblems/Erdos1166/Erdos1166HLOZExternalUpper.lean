import ErdosProblems.Erdos1166.Erdos1166HLOZDecomposition
import ErdosProblems.Erdos1166.Erdos1166HLOZExternalPairPath
import ErdosProblems.Erdos1166.Erdos1166HLOZGreen
import ErdosProblems.Erdos1166.Erdos1166HLOZUrn

namespace Erdos1166.HLOZExternalUpper

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open HLOZDecomposition
open HLOZFoundation

/-!
This file fixes the numerical form of the external-local-time upper event
used in HLOZ Proposition 4.4 and records both the genuine external-chain
event and a separate original-time decomposition on the canonical increment
space.

The elementary decomposition below is unconditional.  It deliberately does
not identify `paperExternalLocalTime s n x`, which is
`\widetilde \xi(x,N_n)`, with the source's external-time statistic
`\widetilde \xi(x,n)`.
-/

/-- The concrete preliminary exponent `κ₁ = 17/50`. -/
noncomputable def kappaOne : ℝ := 17 / 50

/-- The correction exponent in the external-local-time threshold. -/
noncomputable def beta : ℝ := 3 - 4 * kappaOne

/-- The exponent left in the exponential error after division by one log. -/
noncomputable def rateExponent : ℝ := 2 - 4 * kappaOne

theorem beta_eq : beta = (41 : ℝ) / 25 := by
  norm_num [beta, kappaOne]

theorem rateExponent_eq : rateExponent = (16 : ℝ) / 25 := by
  norm_num [rateExponent, kappaOne]

theorem beta_sub_one_eq_rateExponent : beta - 1 = rateExponent := by
  norm_num [beta, rateExponent, kappaOne]

theorem beta_between_one_and_two : 1 < beta ∧ beta < 2 := by
  norm_num [beta_eq]

theorem rateExponent_between_zero_and_one :
    0 < rateExponent ∧ rateExponent < 1 := by
  norm_num [rateExponent_eq]

/-! ### A finite Kac/mgf conversion -/

private theorem finite_geometric_sum_le_inv_one_sub
    (x : ℝ) (N : ℕ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (∑ r ∈ Finset.range (N + 1), x ^ r) ≤ (1 - x)⁻¹ := by
  rw [geom_sum_eq (ne_of_lt hx1)]
  have hden : 0 < 1 - x := sub_pos.mpr hx1
  have heq : (x ^ (N + 1) - 1) / (x - 1) =
      (1 - x ^ (N + 1)) / (1 - x) := by
    have hxm1 : x - 1 ≠ 0 := by linarith
    field_simp [hxm1, ne_of_gt hden]
    ring
  rw [heq]
  apply (div_le_iff₀ hden).2
  rw [inv_mul_cancel₀ (ne_of_gt hden)]
  have hpow : 0 ≤ x ^ (N + 1) := pow_nonneg hx0 _
  rw [pow_succ] at hpow
  ring_nf
  linarith

/-- Finite binomial-moment form of the Kac exponential-moment argument.

For a bounded integer-valued local time `L`, bounds
`E[choose (L,r)] ≤ G^r` imply the near-geometric tail below.  This formulation
avoids an infinite power-series interchange and is the analytic bridge used
after the external-chain collision/Green estimates are supplied. -/
theorem measureReal_ge_le_of_binomial_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : Ω → ℕ) (hL : Measurable L) (N : ℕ)
    (hLN : ∀ ω, L ω ≤ N) (G u : ℝ)
    (hG0 : 0 ≤ G) (hu0 : 0 ≤ u) (huG : u * G < 1)
    (hmoment : ∀ r ≤ N,
      ∫ ω, ((L ω).choose r : ℝ) ∂μ ≤ G ^ r)
    (m : ℕ) :
    μ.real {ω | m ≤ L ω} ≤
      1 / ((1 + u) ^ m * (1 - u * G)) := by
  let chooseMoment (r : ℕ) : Ω → ℝ :=
    fun ω ↦ ((L ω).choose r : ℝ)
  have hchooseMeas (r : ℕ) : Measurable (chooseMoment r) := by
    exact (measurable_of_countable fun k : ℕ ↦ (k.choose r : ℝ)).comp hL
  have hchooseInt (r : ℕ) : Integrable (chooseMoment r) μ := by
    apply Integrable.of_bound (hchooseMeas r).aestronglyMeasurable
      ((N.choose r : ℕ) : ℝ)
    filter_upwards with ω
    rw [Real.norm_of_nonneg (by positivity)]
    change (((L ω).choose r : ℕ) : ℝ) ≤ ((N.choose r : ℕ) : ℝ)
    exact_mod_cast Nat.choose_le_choose r (hLN ω)
  let mgf : Ω → ℝ := fun ω ↦ (1 + u) ^ L ω
  have hbase : 1 ≤ 1 + u := by linarith
  have hmgfMeas : Measurable mgf := by
    exact (measurable_of_countable fun k : ℕ ↦ (1 + u) ^ k).comp hL
  have hmgfInt : Integrable mgf μ := by
    apply Integrable.of_bound hmgfMeas.aestronglyMeasurable ((1 + u) ^ N)
    filter_upwards with ω
    rw [Real.norm_of_nonneg (pow_nonneg (by linarith) _)]
    exact pow_le_pow_right₀ hbase (hLN ω)
  have hbinomial (ω : Ω) :
      mgf ω = ∑ r ∈ Finset.range (N + 1),
        u ^ r * chooseMoment r ω := by
    rw [show mgf ω = (u + 1) ^ L ω by simp [mgf, add_comm], add_pow]
    rw [Finset.sum_subset (Finset.range_mono
      (Nat.add_le_add_right (hLN ω) 1))]
    · apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_range] at hr
      simp [chooseMoment, Nat.sub_eq, mul_assoc, mul_comm, mul_left_comm]
    · intro r hrN hrL
      have hrLt : L ω < r := by
        simp only [Finset.mem_range, not_lt] at hrL
        exact lt_of_lt_of_le (Nat.lt_succ_self _) hrL
      simp [chooseMoment, Nat.choose_eq_zero_of_lt hrLt]
  have hmgfIntegral :
      ∫ ω, mgf ω ∂μ =
        ∑ r ∈ Finset.range (N + 1),
          u ^ r * ∫ ω, chooseMoment r ω ∂μ := by
    simp_rw [hbinomial]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro r _hr
      rw [integral_const_mul]
    · intro r _hr
      exact (hchooseInt r).const_mul (u ^ r)
  have hmgfBound : ∫ ω, mgf ω ∂μ ≤ (1 - u * G)⁻¹ := by
    rw [hmgfIntegral]
    calc
      ∑ r ∈ Finset.range (N + 1),
          u ^ r * ∫ ω, chooseMoment r ω ∂μ ≤
          ∑ r ∈ Finset.range (N + 1), u ^ r * G ^ r := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left
          (hmoment r (Nat.le_of_lt_succ (Finset.mem_range.mp hr)))
          (pow_nonneg hu0 r)
      _ = ∑ r ∈ Finset.range (N + 1), (u * G) ^ r := by
        apply Finset.sum_congr rfl
        intro r _hr
        rw [mul_pow]
      _ ≤ (1 - u * G)⁻¹ :=
        finite_geometric_sum_le_inv_one_sub (u * G) N
          (mul_nonneg hu0 hG0) huG
  have hpowPos : 0 < (1 + u) ^ m := pow_pos (by linarith) _
  have hsubset : {ω | m ≤ L ω} ⊆ {ω | (1 + u) ^ m ≤ mgf ω} := by
    intro ω hω
    exact pow_le_pow_right₀ hbase hω
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω ↦ pow_nonneg (by linarith) (L ω))
    hmgfInt ((1 + u) ^ m)
  have hmul :
      (1 + u) ^ m * μ.real {ω | m ≤ L ω} ≤ (1 - u * G)⁻¹ := by
    calc
      (1 + u) ^ m * μ.real {ω | m ≤ L ω} ≤
          (1 + u) ^ m * μ.real {ω | (1 + u) ^ m ≤ mgf ω} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hpowPos.le
      _ ≤ ∫ ω, mgf ω ∂μ := hmarkov
      _ ≤ (1 - u * G)⁻¹ := hmgfBound
  rw [one_div, mul_inv_rev]
  change μ.real {ω | m ≤ L ω} ≤ (1 - u * G)⁻¹ / (1 + u) ^ m
  exact (le_div_iff₀ hpowPos).2 (by simpa [mul_comm] using hmul)

/-- The real threshold in HLOZ Lemma 2.5(2), specialized to `κ₁=17/50`. -/
noncomputable def externalThreshold (n : ℕ) : ℝ :=
  15 / (16 * Real.pi) * Real.log (n : ℝ) ^ 2 -
    2 * Real.log (n : ℝ) ^ beta

/-- The desired safe probability majorant.  Multiplication by `n` gives the
`exp (8 (log n)^(2-4κ₁))` expectation bound used in Proposition 4.4. -/
noncomputable def externalRate (n : ℕ) : ℝ :=
  Real.exp (8 * Real.log (n : ℝ) ^ rateExponent) / (n : ℝ)

/-! ### The genuine external-chain event -/

/-- Number of retained two-increment labels needed to reconstruct the
external path through external time `n`. -/
def externalLabelCount (n : ℕ) : ℕ := (n + 1) / 2

theorem external_time_fits_labelCount (n : ℕ) :
    n + 1 ≤ 2 * externalLabelCount n + 1 := by
  simp only [externalLabelCount]
  omega

/-- Local time at the origin through external time `n`, reconstructed from a
long-enough list of successive non-distinguished pair labels.  Taking the
first `n+1` vertices handles even and odd external times uniformly. -/
def externalOriginLocalTimeFromLabels
    (n : ℕ) (labels : List IncrementPair) : ℕ :=
  ((externalPathFromLabels labels).take (n + 1)).count (0, 0)

theorem externalPathPrefix_length {n : ℕ} {labels : List IncrementPair}
    (hlen : labels.length = externalLabelCount n) :
    ((externalPathFromLabels labels).take (n + 1)).length = n + 1 := by
  rw [List.length_take, externalPathFromLabels_length, hlen]
  exact Nat.min_eq_left (external_time_fits_labelCount n)

/-- A canonical-increment-space formulation of the high local-time event for
the *external chain at external time `n`*.  Each member of the union fixes the
first `externalLabelCount n` non-distinguished pair labels.  This is distinct
from `paperExternalLocalTime (simpleRandomWalk ω) n 0`, whose index is the
original walk time and whose external index is the random clock `N_n`.

The union omits only paths on which the requested finite terminal-label prefix
does not exist.  Proving that those exceptional paths are null, and packaging
the resulting infinite external chain, is one of the missing bridge lemmas. -/
noncomputable def externalChainUpperBad (n : ℕ) : Set (ℕ → Direction) :=
  ⋃ labels : List IncrementPair,
    if labels.length = externalLabelCount n ∧
        (∀ p ∈ labels, p ≠ distinguishedIncrementPair) ∧
        externalThreshold n ≤ (externalOriginLocalTimeFromLabels n labels : ℝ)
    then firstPairTerminalLabelsEqFrom 0 labels
    else ∅

theorem measurableSet_externalChainUpperBad (n : ℕ) :
    MeasurableSet (externalChainUpperBad n) := by
  rw [externalChainUpperBad]
  apply MeasurableSet.iUnion
  intro labels
  split_ifs
  · exact iidTail_le 0 _
      (measurableSet_firstPairTerminalLabelsEqFrom_iidTail 0 labels)
  · exact MeasurableSet.empty

/-- The analogous canonical cylinder event that the reconstructed external
chain is at the origin at external time `n`. -/
noncomputable def externalChainReturnAt (n : ℕ) : Set (ℕ → Direction) :=
  ⋃ labels : List IncrementPair,
    if labels.length = externalLabelCount n ∧
        (∀ p ∈ labels, p ≠ distinguishedIncrementPair) ∧
        (externalPathFromLabels labels).getD n (0, 0) = (0, 0)
    then firstPairTerminalLabelsEqFrom 0 labels
    else ∅

theorem measurableSet_externalChainReturnAt (n : ℕ) :
    MeasurableSet (externalChainReturnAt n) := by
  rw [externalChainReturnAt]
  apply MeasurableSet.iUnion
  intro labels
  split_ifs
  · exact iidTail_le 0 _
      (measurableSet_firstPairTerminalLabelsEqFrom_iidTail 0 labels)
  · exact MeasurableSet.empty

/-- Return probability of the finite-cylinder external chain. -/
noncomputable def externalReturnProb (n : ℕ) : ℝ :=
  incrementLaw.real (externalChainReturnAt n)

/-- Its finite Green function at the origin. -/
noncomputable def externalFiniteGreen (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), externalReturnProb j

/-- The sharp return estimate still needed from the external chain.  Its
coefficient `15/(16π)` is what produces the leading threshold in (2.19).
The current planar return estimates concern `simpleRandomWalk`, not this
terminal-label chain. -/
def HasExternalSharpGreenUpper : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    externalFiniteGreen n ≤
      15 / (16 * Real.pi) * Real.log (n : ℝ) + C

/-- The exact probability input corresponding to HLOZ Lemma 2.5(2), (2.19),
at `κ₁=17/50`, now indexed by genuine external-chain time. -/
def HasExternalChainUpperDeviation : Prop :=
  ∀ᶠ n : ℕ in atTop,
    incrementLaw.real (externalChainUpperBad n) ≤ externalRate n

/-- The expectation normalization used in Proposition 4.4 follows from the
genuine external-chain probability input with exactly the constant `8`. -/
theorem externalChain_expectedCount_le_exp_of_rate
    {n : ℕ} (hn : 1 ≤ n)
    (hprob : incrementLaw.real (externalChainUpperBad n) ≤ externalRate n) :
    (n : ℝ) * incrementLaw.real (externalChainUpperBad n) ≤
      Real.exp (8 * Real.log (n : ℝ) ^ rateExponent) := by
  calc
    (n : ℝ) * incrementLaw.real (externalChainUpperBad n) ≤
        (n : ℝ) * externalRate n :=
      mul_le_mul_of_nonneg_left hprob (by positivity)
    _ = Real.exp (8 * Real.log (n : ℝ) ^ rateExponent) := by
      rw [externalRate]
      field_simp

theorem eventually_externalChain_expectedCount_le_exp
    (hdev : HasExternalChainUpperDeviation) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * incrementLaw.real (externalChainUpperBad n) ≤
        Real.exp (8 * Real.log (n : ℝ) ^ rateExponent) := by
  filter_upwards [Filter.eventually_ge_atTop 1, hdev] with n hn hprob
  exact externalChain_expectedCount_le_exp_of_rate hn hprob

/-! ### A different, original-time event -/

/-- The literal canonical-increment event corresponding to
`\widetilde ξ(0,N_n)` at original time `n`.  It is useful for the pathwise
decomposition below, but is not the event in HLOZ (2.19). -/
def originalTimeExternalUpperBad (n : ℕ) : Set (ℕ → Direction) :=
  {ω | externalThreshold n ≤
    (paperExternalLocalTime (simpleRandomWalk ω) n (0, 0) : ℝ)}

theorem measurable_externalLocalTime_comp (n : ℕ) :
    Measurable (fun ω : ℕ → Direction ↦
      paperExternalLocalTime (simpleRandomWalk ω) n (0, 0)) := by
  have hpath : Measurable (fun s : ℕ → Site ↦
      paperExternalLocalTime s n (0, 0)) :=
    (measurable_paperExternalLocalTime_lookahead n (0, 0)).mono
      (canonicalFiltration.le (n + 1)) le_rfl
  exact hpath.comp measurable_simpleRandomWalk

theorem measurableSet_originalTimeExternalUpperBad (n : ℕ) :
    MeasurableSet (originalTimeExternalUpperBad n) := by
  exact measurableSet_le measurable_const
    ((measurable_of_countable fun k : ℕ ↦ (k : ℝ)).comp
      (measurable_externalLocalTime_comp n))

/-- A weaker original-time probability statement.  This is deliberately not
named or used as HLOZ (2.19). -/
def HasOriginalTimeExternalUpperDeviation : Prop :=
  ∀ᶠ n : ℕ in atTop,
    incrementLaw.real (originalTimeExternalUpperBad n) ≤ externalRate n

/-- A natural-threshold version convenient for the exact decomposition
`ξ = \widetilde ξ + ξ^L`. -/
def externalNatHigh (n a : ℕ) : Set (ℕ → Direction) :=
  {ω | a ≤ paperExternalLocalTime (simpleRandomWalk ω) n (0, 0)}

/-- Upper event for the ordinary local time at the origin. -/
def ordinaryNatHigh (n a : ℕ) : Set (ℕ → Direction) :=
  {ω | a ≤ localTime (simpleRandomWalk ω) n (0, 0)}

/-- Lower-deviation event for the deleted lazy contribution. -/
def lazyNatLow (n b : ℕ) : Set (ℕ → Direction) :=
  {ω | paperLazyLocalTime (simpleRandomWalk ω) n (0, 0) < b}

/-- Exact pathwise split: if the external contribution is at least `a`, then
either the total local time is at least `a+b`, or the lazy contribution is
smaller than `b`. -/
theorem externalNatHigh_subset_ordinary_union_lazyLow (n a b : ℕ) :
    externalNatHigh n a ⊆ ordinaryNatHigh n (a + b) ∪ lazyNatLow n b := by
  intro ω hω
  change a ≤ paperExternalLocalTime (simpleRandomWalk ω) n (0, 0) at hω
  by_cases hlazy : b ≤ paperLazyLocalTime (simpleRandomWalk ω) n (0, 0)
  · apply Set.mem_union_left
    have hdecomp := localTime_eq_paperExternal_add_paperLazy
      (simpleRandomWalk ω) n (0, 0)
    change a + b ≤ localTime (simpleRandomWalk ω) n (0, 0)
    omega
  · apply Set.mem_union_right
    change paperLazyLocalTime (simpleRandomWalk ω) n (0, 0) < b
    omega

/-- Probability form of the exact split.  This is the point at which the
ordinary fixed-site upper deviation and the conditional negative-binomial
lower deviation have to be supplied. -/
theorem externalNatHigh_measureReal_le (n a b : ℕ) :
    incrementLaw.real (externalNatHigh n a) ≤
      incrementLaw.real (ordinaryNatHigh n (a + b)) +
        incrementLaw.real (lazyNatLow n b) := by
  exact (measureReal_mono
      (externalNatHigh_subset_ordinary_union_lazyLow n a b)).trans
    (measureReal_union_le _ _)

/-- Once the source probability estimate is available, the expectation
normalization in Proposition 4.4 is immediate and has exactly constant `8`. -/
theorem expectedCount_le_exp_of_externalRate
    {n : ℕ} (hn : 1 ≤ n)
    (hprob : incrementLaw.real (originalTimeExternalUpperBad n) ≤ externalRate n) :
    (n : ℝ) * incrementLaw.real (originalTimeExternalUpperBad n) ≤
      Real.exp (8 * Real.log (n : ℝ) ^ rateExponent) := by
  calc
    (n : ℝ) * incrementLaw.real (originalTimeExternalUpperBad n) ≤
        (n : ℝ) * externalRate n :=
      mul_le_mul_of_nonneg_left hprob (by positivity)
    _ = Real.exp (8 * Real.log (n : ℝ) ^ rateExponent) := by
      rw [externalRate]
      field_simp

/-- Eventual expectation consequence of the exact probability interface. -/
theorem eventually_expectedCount_le_exp
    (hdev : HasOriginalTimeExternalUpperDeviation) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * incrementLaw.real (originalTimeExternalUpperBad n) ≤
        Real.exp (8 * Real.log (n : ℝ) ^ rateExponent) := by
  filter_upwards [Filter.eventually_ge_atTop 1, hdev] with n hn hprob
  exact expectedCount_le_exp_of_externalRate hn hprob

end Erdos1166.HLOZExternalUpper
