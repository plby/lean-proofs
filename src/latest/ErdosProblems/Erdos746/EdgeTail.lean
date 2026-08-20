import ErdosProblems.Erdos746.BinomialBounds
import ErdosProblems.Erdos746.Asymptotics
import ErdosProblems.Erdos746.Parameters

/-!
# The edge-count tail in the Bernoulli model

For `δ > 0` we use the Bernoulli edge density
`(1 + δ) log n / n`, clipped to the unit interval.  The expected number of
edges is below the base layer
`ceil ((1/2 + δ) n log n)` by a fixed positive multiple of `n log n`.
The finite Chernoff bound from `BinomialBounds` therefore gives an
exponentially small upper tail.
-/

open Filter
open scoped Topology unitInterval

namespace Erdos746

noncomputable section

/-- The unclipped edge density used in the auxiliary Bernoulli graph. -/
def rawEdgeProbability (δ : ℝ) (n : ℕ) : ℝ :=
  (1 + δ) * Real.log (n : ℝ) / (n : ℝ)

/-- The edge density, clipped to the unit interval. -/
def edgeProbability (δ : ℝ) (n : ℕ) : unitInterval :=
  Set.projIcc (0 : ℝ) 1 zero_le_one (rawEdgeProbability δ n)

/-- The real value of the clipped edge density. -/
def clippedEdgeProbability (δ : ℝ) (n : ℕ) : ℝ :=
  (edgeProbability δ n : ℝ)

theorem clippedEdgeProbability_mem (δ : ℝ) (n : ℕ) :
    clippedEdgeProbability δ n ∈ Set.Icc (0 : ℝ) 1 :=
  (edgeProbability δ n).property

theorem clippedEdgeProbability_nonneg (δ : ℝ) (n : ℕ) :
    0 ≤ clippedEdgeProbability δ n :=
  (clippedEdgeProbability_mem δ n).1

theorem clippedEdgeProbability_le_one (δ : ℝ) (n : ℕ) :
    clippedEdgeProbability δ n ≤ 1 :=
  (clippedEdgeProbability_mem δ n).2

/-- The exact integer base layer `ceil ((1/2 + δ) n log n)`. -/
def baseEdgeCount (δ : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil ((1 / 2 + δ) * (n : ℝ) * Real.log (n : ℝ))

theorem baseEdgeCount_eq_baseEdgeThreshold (δ : ℝ) (n : ℕ) :
    baseEdgeCount δ n = baseEdgeThreshold (2 * δ) n := by
  congr 1
  ring

/-- The fixed exponential tilt used in the upper-tail estimate. -/
def edgeTailTilt (δ : ℝ) : ℝ :=
  min 1 (δ / (2 * (1 + δ)))

/-- The positive coefficient in the final `exp (-b n log n)` bound. -/
def edgeTailRate (δ : ℝ) : ℝ :=
  edgeTailTilt δ * δ / 4

theorem edgeTailTilt_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < edgeTailTilt δ := by
  unfold edgeTailTilt
  exact lt_min zero_lt_one (div_pos hδ (by positivity))

theorem edgeTailTilt_le_one (δ : ℝ) : edgeTailTilt δ ≤ 1 := by
  exact min_le_left _ _

theorem edgeTailTilt_le_ratio (δ : ℝ) :
    edgeTailTilt δ ≤ δ / (2 * (1 + δ)) := by
  exact min_le_right _ _

theorem edgeTailRate_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < edgeTailRate δ := by
  unfold edgeTailRate
  exact div_pos (mul_pos (edgeTailTilt_pos hδ) hδ) (by norm_num)

/-- Eventually the clipping is inactive. -/
theorem eventually_clippedEdgeProbability_eq_raw {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      clippedEdgeProbability δ n = rawEdgeProbability δ n := by
  have hlim : Tendsto (rawEdgeProbability δ) atTop (nhds 0) := by
    change Tendsto
      (fun n : ℕ ↦ (1 + δ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0)
    simpa [div_eq_mul_inv, mul_assoc] using
      (tendsto_const_nhds.mul tendsto_log_div_nat :
        Tendsto (fun n : ℕ ↦ (1 + δ) *
          (Real.log (n : ℝ) / (n : ℝ))) atTop (nhds ((1 + δ) * 0)))
  have hupper : ∀ᶠ n : ℕ in atTop, rawEdgeProbability δ n < 1 :=
    hlim.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hupper, eventually_ge_atTop 1] with n hnupper hn
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hnonneg : 0 ≤ rawEdgeProbability δ n := by
    unfold rawEdgeProbability
    positivity
  unfold clippedEdgeProbability edgeProbability
  rw [Set.projIcc_of_mem]
  exact ⟨hnonneg, hnupper.le⟩

/-- The finite binomial mass of having more than the base number of edges. -/
def edgeCountUpperTail (δ : ℝ) (n : ℕ) : ℝ :=
  binomialUpperTail (n.choose 2) (baseEdgeCount δ n + 1)
    (clippedEdgeProbability δ n)

theorem edgeCountUpperTail_nonneg (δ : ℝ) (n : ℕ) :
    0 ≤ edgeCountUpperTail δ n := by
  unfold edgeCountUpperTail binomialUpperTail
  exact Finset.sum_nonneg fun i _ ↦
    binomialTerm_nonneg (clippedEdgeProbability_nonneg δ n)
      (clippedEdgeProbability_le_one δ n)

/-- A quadratic upper estimate for the exponential increment on `[0,1]`. -/
private theorem exp_sub_one_le_add_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t - 1 ≤ t + t ^ 2 := by
  have habs : |t| ≤ 1 := by simpa [abs_of_nonneg ht0]
  have hrem := Real.abs_exp_sub_one_sub_id_le habs
  have hle : Real.exp t - 1 - t ≤ |Real.exp t - 1 - t| :=
    le_abs_self _
  linarith

/-- Explicit Chernoff majorant for the edge-count overflow.  The two
side conditions are precisely the eventual facts needed to remove the
clipping and to make `log n` nonnegative. -/
theorem edgeCountUpperTail_le_exp {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : 1 ≤ n)
    (hclip : clippedEdgeProbability δ n = rawEdgeProbability δ n) :
    edgeCountUpperTail δ n ≤
      Real.exp (-edgeTailRate δ * (n : ℝ) * Real.log (n : ℝ)) := by
  let t := edgeTailTilt δ
  have ht0 : 0 ≤ t := (edgeTailTilt_pos hδ).le
  have ht1 : t ≤ 1 := edgeTailTilt_le_one δ
  have htratio : t ≤ δ / (2 * (1 + δ)) := edgeTailTilt_le_ratio δ
  have hδone : 0 < 1 + δ := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hp0 : 0 ≤ clippedEdgeProbability δ n :=
    clippedEdgeProbability_nonneg δ n
  have hp1 : clippedEdgeProbability δ n ≤ 1 :=
    clippedEdgeProbability_le_one δ n
  have hchern := edgeCountUpperTail_chernoff
    n (baseEdgeCount δ n + 1) hp0 hp1 ht0
  have hexp : Real.exp t - 1 ≤ t + t ^ 2 :=
    exp_sub_one_le_add_sq ht0 ht1
  have hK :
      (1 / 2 + δ) * (n : ℝ) * Real.log (n : ℝ) ≤
        (baseEdgeCount δ n + 1 : ℕ) := by
    have := Nat.le_ceil
      ((1 / 2 + δ) * (n : ℝ) * Real.log (n : ℝ))
    exact this.trans (by exact_mod_cast Nat.le_add_right (baseEdgeCount δ n) 1)
  have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpred : (n - 1 : ℝ) ≤ n := by
      exact_mod_cast Nat.sub_le n 1
    nlinarith
  have hmean :
      (n.choose 2 : ℝ) * clippedEdgeProbability δ n ≤
        (1 + δ) / 2 * (n : ℝ) * Real.log (n : ℝ) := by
    rw [hclip]
    unfold rawEdgeProbability
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      (n.choose 2 : ℝ) * ((1 + δ) * Real.log (n : ℝ) / (n : ℝ)) ≤
          ((n : ℝ) ^ 2 / 2) *
            ((1 + δ) * Real.log (n : ℝ) / (n : ℝ)) := by
        gcongr
      _ = (1 + δ) / 2 * (n : ℝ) * Real.log (n : ℝ) := by
        field_simp
  have htgap : (1 + δ) * t ≤ δ / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have := mul_le_mul_of_nonneg_left htratio hδone.le
    field_simp [hδone.ne'] at this
    nlinarith
  have hprod0 : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := mul_nonneg (Nat.cast_nonneg n) hlog
  have hinc0 : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp ht0)
  have hmeanTerm :
      (n.choose 2 : ℝ) * clippedEdgeProbability δ n * (Real.exp t - 1) ≤
        ((1 + δ) / 2 * (n : ℝ) * Real.log (n : ℝ)) * (t + t ^ 2) := by
    exact (mul_le_mul hmean hexp hinc0
      (by positivity : 0 ≤ (1 + δ) / 2 * (n : ℝ) * Real.log (n : ℝ)))
  have hexponent :
      -(t * (baseEdgeCount δ n + 1 : ℕ)) +
          (n.choose 2 : ℝ) * clippedEdgeProbability δ n * (Real.exp t - 1) ≤
        -(edgeTailRate δ) * (n : ℝ) * Real.log (n : ℝ) := by
    have hnegK :
        -(t * (baseEdgeCount δ n + 1 : ℕ)) ≤
          -(t * ((1 / 2 + δ) * (n : ℝ) * Real.log (n : ℝ))) := by
      gcongr
    rw [show edgeTailRate δ = t * δ / 4 by rfl]
    have hsqgap : (1 + δ) * t ^ 2 ≤ t * δ / 2 := by
      have hmul := mul_le_mul_of_nonneg_right htgap ht0
      nlinarith
    have hcoeff :
        -(t * (1 / 2 + δ)) + (1 + δ) / 2 * (t + t ^ 2) ≤
          -(t * δ / 4) := by
      nlinarith
    have hcoeff_mul := mul_le_mul_of_nonneg_right hcoeff hprod0
    calc
      -(t * (baseEdgeCount δ n + 1 : ℕ)) +
          (n.choose 2 : ℝ) * clippedEdgeProbability δ n * (Real.exp t - 1) ≤
          -(t * ((1 / 2 + δ) * (n : ℝ) * Real.log (n : ℝ))) +
            ((1 + δ) / 2 * (n : ℝ) * Real.log (n : ℝ)) *
              (t + t ^ 2) := add_le_add hnegK hmeanTerm
      _ = (-(t * (1 / 2 + δ)) +
            (1 + δ) / 2 * (t + t ^ 2)) *
              ((n : ℝ) * Real.log (n : ℝ)) := by ring
      _ ≤ (-(t * δ / 4)) * ((n : ℝ) * Real.log (n : ℝ)) := hcoeff_mul
      _ = -(t * δ / 4) * (n : ℝ) * Real.log (n : ℝ) := by ring
  unfold edgeCountUpperTail at *
  exact hchern.trans (Real.exp_le_exp.mpr hexponent)

/-- The binomial edge-count overflow probability tends to zero. -/
theorem tendsto_edgeCountUpperTail_zero {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (edgeCountUpperTail δ) atTop (nhds 0) := by
  have hclip := eventually_clippedEdgeProbability_eq_raw hδ
  have hupper : ∀ᶠ n : ℕ in atTop,
      edgeCountUpperTail δ n ≤
        Real.exp (-edgeTailRate δ * (n : ℝ) * Real.log (n : ℝ)) := by
    filter_upwards [hclip, eventually_ge_atTop 1] with n hnclip hn
    exact edgeCountUpperTail_le_exp hδ hn hnclip
  apply squeeze_zero' (Eventually.of_forall (edgeCountUpperTail_nonneg δ)) hupper
  exact tendsto_exp_neg_mul_nat_log (edgeTailRate_pos hδ)

/-- In particular, the exceptional edge-count event eventually has mass at
most one half. -/
theorem eventually_edgeCountUpperTail_le_half {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, edgeCountUpperTail δ n ≤ 1 / 2 := by
  exact (tendsto_edgeCountUpperTail_zero hδ).eventually
    (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))

end

end Erdos746
