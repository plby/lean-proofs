import ErdosProblems.Erdos746.BinomialLayers
import ErdosProblems.Erdos746.EdgeTail
import ErdosProblems.Erdos746.ErrorLimits
import ErdosProblems.Erdos746.LimitAssembly

/-!
# Threshold-level probability assembly for Erdős 746

This file isolates the deterministic probability algebra at the end of the
proof.  The first exposure is a binomial graph at density
`(1 + ρ / 2) log n / n`, transferred to the exact uniform layer
`baseEdgeThreshold ρ n`.  The second exposure contributes the explicit
adaptive-sprinkling error from equation (12) of the mathematical writeup.

The only input left abstract in the last two theorems is the finite
sprinkling comparison itself: an upper bound of the threshold failure by the
base-expansion failure plus the displayed sprinkling error.  All passage from
that finite comparison to the required limit is proved here.
-/

open Filter
open scoped Topology

namespace Erdos746

noncomputable section

/-- A positive margin bounded both by `ε` and by one. -/
def auxiliaryMargin (ε : ℝ) : ℝ := min ε 1

theorem auxiliaryMargin_pos {ε : ℝ} (hε : 0 < ε) :
    0 < auxiliaryMargin ε := by
  exact lt_min hε zero_lt_one

theorem auxiliaryMargin_le (ε : ℝ) : auxiliaryMargin ε ≤ ε :=
  min_le_left _ _

theorem auxiliaryMargin_le_one (ε : ℝ) : auxiliaryMargin ε ≤ 1 :=
  min_le_right _ _

/-- The increasing base event used before sprinkling. -/
def IsQuarterTwoExpander (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  G.IsTwoExpanderUpTo (n / 4)

/-- Failure of quarter-two-expansion on the exact base edge layer. -/
def baseBadProbability (ρ : ℝ) (n : ℕ) : ℝ :=
  graphPropertyFailure n (baseEdgeThreshold ρ n) (IsQuarterTwoExpander n)

/-- Failure of quarter-two-expansion in the auxiliary binomial graph. -/
def binomialBaseBadProbability (ρ : ℝ) (n : ℕ) : ℝ :=
  binomialGraphPropertyFailure n (clippedEdgeProbability (ρ / 2) n)
    (IsQuarterTwoExpander n)

/-- Failure of Hamiltonicity on the rounded target layer. -/
def thresholdFailureProbability (ε : ℝ) (n : ℕ) : ℝ :=
  1 - hamiltonianProbability n (edgeThreshold ε n)

/-- The explicit error from the adaptive second exposure. -/
def thresholdSprinklingError (ρ : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((n : ℝ) - 1 -
    ((1 - Real.exp (-1)) * ρ / 48) *
      (n : ℝ) * Real.log (n : ℝ))

/-- The finite-horizon error delivered directly by the adaptive sprinkling
argument, before replacing the horizon by its asymptotic lower bound. -/
def adaptiveSprinklingError (ε ρ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (((n - 1 : ℕ) : ℝ) -
    (1 / 16 : ℝ) * (sprinklingLength ε ρ n : ℝ) *
      (1 - Real.exp (-1)))

/-- The complete threshold majorant after Bernoulli-to-uniform transfer. -/
def thresholdFailureMajorant (ρ : ℝ) (n : ℕ) : ℝ :=
  2 * binomialBaseBadProbability ρ n + thresholdSprinklingError ρ n

theorem isQuarterTwoExpander_mono {n : ℕ}
    {G H : SimpleGraph (Fin n)} (hGH : G ≤ H)
    (hG : IsQuarterTwoExpander n G) : IsQuarterTwoExpander n H :=
  isTwoExpanderUpTo_mono hGH hG

theorem baseEdgeThreshold_eq_baseEdgeCount_half (ρ : ℝ) (n : ℕ) :
    baseEdgeThreshold ρ n = baseEdgeCount (ρ / 2) n := by
  rw [baseEdgeCount_eq_baseEdgeThreshold]
  congr 1
  ring

theorem edgeThreshold_eq_baseEdgeThreshold_two (ε : ℝ) (n : ℕ) :
    edgeThreshold ε n = baseEdgeThreshold (2 * ε) n := by
  unfold edgeThreshold baseEdgeThreshold
  congr 1
  ring

theorem baseBadProbability_nonneg (ρ : ℝ) (n : ℕ) :
    0 ≤ baseBadProbability ρ n :=
  uniformProbability_nonneg _

theorem baseBadProbability_eq_one_sub_twoExpanderProbability
    {ρ : ℝ} {n : ℕ} (hbase : baseEdgeThreshold ρ n ≤ edgeCount n) :
    baseBadProbability ρ n =
      1 - twoExpanderProbability n (baseEdgeThreshold ρ n) (n / 4) := by
  unfold baseBadProbability IsQuarterTwoExpander twoExpanderProbability
  exact graphPropertyFailure_eq_one_sub _ hbase

theorem thresholdFailureProbability_nonneg (ε : ℝ) (n : ℕ) :
    0 ≤ thresholdFailureProbability ε n := by
  unfold thresholdFailureProbability
  linarith [hamiltonianProbability_le_one n (edgeThreshold ε n)]

theorem thresholdFailureProbability_eq_graphPropertyFailure
    {ε : ℝ} {n : ℕ} (htarget : edgeThreshold ε n ≤ edgeCount n) :
    thresholdFailureProbability ε n =
      graphPropertyFailure n (edgeThreshold ε n)
        (fun G : SimpleGraph (Fin n) ↦ G.IsHamiltonian) := by
  unfold thresholdFailureProbability graphPropertyFailure
  rw [graphPropertyFailure_eq_one_sub _ htarget]
  rfl

theorem thresholdSprinklingError_nonneg (ρ : ℝ) (n : ℕ) :
    0 ≤ thresholdSprinklingError ρ n := by
  exact Real.exp_nonneg _

theorem eventually_baseEdgeThreshold_le_target
    {ε ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρε : ρ ≤ ε) :
    ∀ᶠ n : ℕ in atTop, baseEdgeThreshold ρ n ≤ edgeThreshold ε n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply Nat.ceil_le_ceil
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hcoeff : 1 / 2 + ρ / 2 ≤ 1 / 2 + ε := by
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)) hlog

/-- The rounded threshold gap contains the promised sprinkling horizon. -/
theorem eventually_sprinklingLength_lower
    {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ ≤ ε) :
    ∀ᶠ n : ℕ in atTop,
      ρ / 3 * (n : ℝ) * Real.log (n : ℝ) ≤
        (sprinklingLength ε ρ n : ℝ) := by
  simpa [sprinklingLength, edgeThreshold, baseEdgeThreshold] using
    eventually_threshold_ceil_gap hρ hρε

/-- The raw adaptive Chernoff exponent is eventually bounded by the single
sprinkling error used in the final probability estimate. -/
theorem eventually_adaptive_exp_le_thresholdSprinklingError
    {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ ≤ ε) :
    ∀ᶠ n : ℕ in atTop,
      adaptiveSprinklingError ε ρ n ≤ thresholdSprinklingError ρ n := by
  filter_upwards [eventually_sprinklingLength_lower hρ hρε,
    eventually_ge_atTop 1] with n hgap hn
  unfold adaptiveSprinklingError thresholdSprinklingError
  apply Real.exp_le_exp.mpr
  have hexp : 0 < 1 - Real.exp (-1) := by
    have : Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
    simpa using this
  have hcast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hmul := mul_le_mul_of_nonneg_left hgap
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16) hexp.le)
  rw [hcast]
  nlinarith [hmul]

/-- The exact base threshold is eventually a valid layer of the complete
graph. -/
theorem eventually_baseEdgeThreshold_le_edgeCount (ρ : ℝ) :
    ∀ᶠ n : ℕ in atTop, baseEdgeThreshold ρ n ≤ edgeCount n := by
  let c : ℝ := 1 / 2 + ρ / 2
  have hsmall : Tendsto
      (fun n : ℕ ↦ c * (Real.log (n : ℝ) / (n : ℝ)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul tendsto_log_div_nat
  have hevent := hsmall.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hevent, eventually_ge_atTop 2] with n hnsmall hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hreal :
      (1 / 2 + ρ / 2) * (n : ℝ) * Real.log (n : ℝ) ≤
        (edgeCount n : ℝ) := by
    have hnsmall' :
        c * Real.log (n : ℝ) / (n : ℝ) < 1 / 4 := by
      simpa [div_eq_mul_inv, mul_assoc] using hnsmall
    rw [div_lt_iff₀ hnpos] at hnsmall'
    have hscaled := mul_le_mul_of_nonneg_right hnsmall'.le hnpos.le
    have hchoose : (edgeCount n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      simp [edgeCount, Nat.cast_choose_two]
    rw [hchoose]
    dsimp [c] at hscaled
    nlinarith [show (2 : ℝ) ≤ n by exact_mod_cast hn]
  exact Nat.ceil_le.mpr hreal

theorem eventually_edgeThreshold_le_edgeCount (ε : ℝ) :
    ∀ᶠ n : ℕ in atTop, edgeThreshold ε n ≤ edgeCount n := by
  simpa [edgeThreshold_eq_baseEdgeThreshold_two] using
    eventually_baseEdgeThreshold_le_edgeCount (2 * ε)

/-- The Bernoulli edge-count upper tail transfers base failure to the exact
uniform layer with loss at most a factor of two. -/
theorem baseBadProbability_le_two_mul_binomialBaseBadProbability
    {ρ : ℝ} {n : ℕ}
    (hbase : baseEdgeThreshold ρ n ≤ edgeCount n)
    (htail : edgeCountUpperTail (ρ / 2) n ≤ (1 : ℝ) / 2) :
    baseBadProbability ρ n ≤ 2 * binomialBaseBadProbability ρ n := by
  unfold baseBadProbability binomialBaseBadProbability
  apply graphPropertyFailure_le_two_mul_binomialFailure
    (IsQuarterTwoExpander n)
    (fun _G _H hGH hG ↦ isQuarterTwoExpander_mono hGH hG)
    (clippedEdgeProbability (ρ / 2) n)
    (clippedEdgeProbability_nonneg (ρ / 2) n)
    (clippedEdgeProbability_le_one (ρ / 2) n) hbase
  simpa [edgeCountUpperTail, edgeCount,
    baseEdgeThreshold_eq_baseEdgeCount_half] using htail

/-- Eventually-valid form of the base transfer. -/
theorem eventually_baseBadProbability_le_two_mul_binomial
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ n : ℕ in atTop,
      baseBadProbability ρ n ≤ 2 * binomialBaseBadProbability ρ n := by
  have htail := eventually_edgeCountUpperTail_le_half (half_pos hρ)
  filter_upwards [eventually_baseEdgeThreshold_le_edgeCount ρ, htail]
    with n hbase hnTail
  exact baseBadProbability_le_two_mul_binomialBaseBadProbability hbase hnTail

/-- Assemble the raw finite sprinkling estimate with all of its eventual
side conditions and replace its horizon-dependent exponential by
`thresholdSprinklingError`.

The functional argument is the exact interface supplied by the finite
sprinkling module; this theorem contains no probabilistic assumption beyond
that already-proved pointwise bound. -/
theorem eventually_thresholdFailure_le_base_add_sprinklingError
    {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ ≤ ε)
    (hfinite : ∀ n : ℕ, 8 ≤ n →
      baseEdgeThreshold ρ n ≤ edgeThreshold ε n →
      edgeThreshold ε n ≤ edgeCount n →
      thresholdFailureProbability ε n ≤
        baseBadProbability ρ n + adaptiveSprinklingError ε ρ n) :
    ∀ᶠ n : ℕ in atTop,
      thresholdFailureProbability ε n ≤
        baseBadProbability ρ n + thresholdSprinklingError ρ n := by
  filter_upwards [eventually_ge_atTop 8,
    eventually_baseEdgeThreshold_le_target hρ.le hρε,
    eventually_edgeThreshold_le_edgeCount ε,
    eventually_adaptive_exp_le_thresholdSprinklingError hρ hρε]
      with n hn hnBaseTarget hnTargetCount hnError
  exact (hfinite n hn hnBaseTarget hnTargetCount).trans
    (add_le_add le_rfl hnError)

/-- Combining a finite sprinkling comparison with the edge-tail transfer
gives the complete explicit threshold majorant. -/
theorem thresholdFailureProbability_le_majorant
    {ε ρ : ℝ} {n : ℕ}
    (hbase : baseEdgeThreshold ρ n ≤ edgeCount n)
    (htail : edgeCountUpperTail (ρ / 2) n ≤ (1 : ℝ) / 2)
    (hsprinkle : thresholdFailureProbability ε n ≤
      baseBadProbability ρ n + thresholdSprinklingError ρ n) :
    thresholdFailureProbability ε n ≤ thresholdFailureMajorant ρ n := by
  have hbaseTransfer :=
    baseBadProbability_le_two_mul_binomialBaseBadProbability hbase htail
  unfold thresholdFailureMajorant
  linarith

theorem tendsto_thresholdSprinklingError_zero
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (thresholdSprinklingError ρ) atTop (nhds 0) := by
  change Tendsto (fun n : ℕ ↦ Real.exp ((n : ℝ) - 1 -
    ((1 - Real.exp (-1)) * ρ / 48) *
      (n : ℝ) * Real.log (n : ℝ))) atTop (nhds 0)
  exact tendsto_sprinkling_error_zero hρ

/-- If the binomial first-exposure failure vanishes, then so does the full
explicit majorant. -/
theorem tendsto_thresholdFailureMajorant_zero
    {ρ : ℝ} (hρ : 0 < ρ)
    (hbase : Tendsto (binomialBaseBadProbability ρ) atTop (nhds 0)) :
    Tendsto (thresholdFailureMajorant ρ) atTop (nhds 0) := by
  have htwo : Tendsto (fun n ↦ 2 * binomialBaseBadProbability ρ n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hbase
  change Tendsto (fun n ↦
    2 * binomialBaseBadProbability ρ n + thresholdSprinklingError ρ n)
      atTop (nhds 0)
  simpa only [add_zero] using
    htwo.add (tendsto_thresholdSprinklingError_zero hρ)

/-- Limit closure from the two genuine probabilistic inputs: vanishing
binomial base failure and the finite sprinkling comparison. -/
theorem tendsto_thresholdHamiltonianProbability_one
    {ε ρ : ℝ} (hρ : 0 < ρ)
    (hbase : Tendsto (binomialBaseBadProbability ρ) atTop (nhds 0))
    (hsprinkle : ∀ᶠ n : ℕ in atTop,
      thresholdFailureProbability ε n ≤
        baseBadProbability ρ n + thresholdSprinklingError ρ n) :
    Tendsto (fun n ↦ hamiltonianProbability n (edgeThreshold ε n))
      atTop (nhds 1) := by
  have htail := eventually_edgeCountUpperTail_le_half (half_pos hρ)
  have hmajorant : ∀ᶠ n : ℕ in atTop,
      thresholdFailureProbability ε n ≤ thresholdFailureMajorant ρ n := by
    filter_upwards [eventually_baseEdgeThreshold_le_edgeCount ρ,
      htail, hsprinkle] with n hnBase hnTail hnSprinkle
    exact thresholdFailureProbability_le_majorant hnBase hnTail hnSprinkle
  have hfailure : Tendsto (thresholdFailureProbability ε) atTop (nhds 0) := by
    apply squeeze_zero'
      (Eventually.of_forall (thresholdFailureProbability_nonneg ε)) hmajorant
    exact tendsto_thresholdFailureMajorant_zero hρ hbase
  have hsuccess :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) - thresholdFailureProbability ε n)
        atTop (nhds ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub hfailure
  simpa [thresholdFailureProbability] using hsuccess

/-- Final statement closure once the preceding threshold theorem has been
established for every positive `ε`. -/
theorem erdos746Statement_of_binomial_and_sprinkling
    (hthreshold : ∀ ε : ℝ, 0 < ε →
      ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (binomialBaseBadProbability ρ) atTop (nhds 0) ∧
        ∀ᶠ n : ℕ in atTop,
          thresholdFailureProbability ε n ≤
            baseBadProbability ρ n + thresholdSprinklingError ρ n) :
    Erdos746Statement := by
  apply erdos746Statement_of_threshold
  intro ε hε
  obtain ⟨ρ, hρ, hbase, hsprinkle⟩ := hthreshold ε hε
  exact tendsto_thresholdHamiltonianProbability_one hρ hbase hsprinkle

/-- Convenient specialization using the canonical margin `min ε 1`. -/
theorem erdos746Statement_of_auxiliaryMargin
    (hbase : ∀ ε : ℝ, 0 < ε →
      Tendsto (binomialBaseBadProbability (auxiliaryMargin ε))
        atTop (nhds 0))
    (hsprinkle : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        thresholdFailureProbability ε n ≤
          baseBadProbability (auxiliaryMargin ε) n +
            thresholdSprinklingError (auxiliaryMargin ε) n) :
    Erdos746Statement := by
  apply erdos746Statement_of_binomial_and_sprinkling
  intro ε hε
  exact ⟨auxiliaryMargin ε, auxiliaryMargin_pos hε,
    hbase ε hε, hsprinkle ε hε⟩

/-- Final assembly at the exact finite interface exposed by the expansion
and sprinkling modules.  The canonical margin simultaneously supplies
positivity and the inequality `ρ ≤ ε`. -/
theorem erdos746Statement_of_auxiliaryMargin_finite
    (hbase : ∀ ε : ℝ, 0 < ε →
      Tendsto (binomialBaseBadProbability (auxiliaryMargin ε))
        atTop (nhds 0))
    (hfinite : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 8 ≤ n →
      baseEdgeThreshold (auxiliaryMargin ε) n ≤ edgeThreshold ε n →
      edgeThreshold ε n ≤ edgeCount n →
      thresholdFailureProbability ε n ≤
        baseBadProbability (auxiliaryMargin ε) n +
          adaptiveSprinklingError ε (auxiliaryMargin ε) n) :
    Erdos746Statement := by
  apply erdos746Statement_of_auxiliaryMargin hbase
  intro ε hε
  exact eventually_thresholdFailure_le_base_add_sprinklingError
    (auxiliaryMargin_pos hε) (auxiliaryMargin_le ε) (hfinite ε hε)

end

end Erdos746
