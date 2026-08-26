import ErdosProblems.Erdos520.HarperTiltedVaryingBarrier

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Removing the moderate-coordinate cutoff

The local Gaussian comparison is deliberately restricted to a growing
coordinate box.  This file proves that the omitted part is harmless under
the tilted cube law.  The exact second moment of a centered block is its
block variance, while the scheduled box radius is of order `sqrt (2^j)`.
Chebyshev and a finite union therefore give a total complement probability
bounded by `64 * (1 / 2)^start`, independently of the path length.
-/

/-- A centered prime-block sum is the uncentered linear block minus its
exact tilted mean. -/
theorem harperCenteredLinearPrimeBlockSum_eq_sub_mean
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (t u : ℝ) (eta : HarperPrimeCube y) :
    harperCenteredLinearPrimeBlockSum y S t u eta =
      harperLinearBlockSum y S u eta -
        harperLinearBlockMean y S t u := by
  unfold harperCenteredLinearPrimeBlockSum
    harperCenteredLinearPrimeIncrement harperLinearBlockSum
    harperLinearBlockMean harperLinearPrimeMean
  rw [Finset.sum_sub_distrib]

/-- Exact centered second moment of an arbitrary finite prime block under
the tilted cube law. -/
theorem integral_harperCenteredLinearPrimeBlockSum_sq
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    (∫ eta, harperCenteredLinearPrimeBlockSum y S t u eta ^ 2
        ∂harperTiltedCubeLaw y t) =
      harperLinearBlockVariance y S t u := by
  simpa only [harperCenteredLinearPrimeBlockSum_eq_sub_mean] using!
    integral_harperLinearBlockSum_sub_mean_sq y S t u

/-- Chebyshev in the exact form needed for a centered block. -/
theorem harperTiltedCubeLaw_real_abs_centeredBlockSum_gt_le
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u R : ℝ)
    (hR : 0 < R) :
    (harperTiltedCubeLaw y t).real
        {eta | R < |harperCenteredLinearPrimeBlockSum y S t u eta|} ≤
      harperLinearBlockVariance y S t u / R ^ 2 := by
  let X : HarperPrimeCube y → ℝ :=
    harperCenteredLinearPrimeBlockSum y S t u
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := harperTiltedCubeLaw y t)
    (ae_of_all _ fun eta ↦ sq_nonneg (X eta))
    (Integrable.of_finite : Integrable (fun eta ↦ X eta ^ 2)
      (harperTiltedCubeLaw y t)) (R ^ 2)
  have hsubset : {eta | R < |X eta|} ⊆ {eta | R ^ 2 ≤ X eta ^ 2} := by
    intro eta heta
    change R ^ 2 ≤ X eta ^ 2
    rw [← sq_abs (X eta)]
    exact le_of_lt ((sq_lt_sq₀ hR.le (abs_nonneg (X eta))).2 heta)
  have hmul :
      R ^ 2 * (harperTiltedCubeLaw y t).real {eta | R < |X eta|} ≤
        harperLinearBlockVariance y S t u := by
    calc
      R ^ 2 * (harperTiltedCubeLaw y t).real {eta | R < |X eta|} ≤
          R ^ 2 * (harperTiltedCubeLaw y t).real
            {eta | R ^ 2 ≤ X eta ^ 2} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) (sq_nonneg R)
      _ ≤ ∫ eta, X eta ^ 2 ∂harperTiltedCubeLaw y t := hmarkov
      _ = harperLinearBlockVariance y S t u := by
        exact integral_harperCenteredLinearPrimeBlockSum_sq y S t u
  exact (le_div_iff₀ (sq_pos_of_pos hR)).2 (by
    simpa only [mul_comm] using! hmul)

/-! ## Scheduled radius arithmetic -/

/-- From the eighth scheduled scale onward, half of the nominal
quarter-square-root radius remains after the fixed displacement margin. -/
theorem one_eighth_sqrt_two_pow_le_harperScheduledModerateRadius
    {start n : ℕ} (i : Fin n) (hj : 8 ≤ start + (i : ℕ)) :
    (1 / 8 : ℝ) *
        Real.sqrt (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ)) ≤
      harperScheduledModerateRadius start n i := by
  let j := start + (i : ℕ)
  have hpowNat : 2 ^ 8 ≤ 2 ^ j :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hj
  have hpowReal : (256 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  have hsqrt : (16 : ℝ) ≤ Real.sqrt (((2 ^ j : ℕ) : ℝ)) := by
    have := Real.sqrt_le_sqrt hpowReal
    norm_num at this ⊢
    exact this
  unfold harperScheduledModerateRadius harperScheduledModerateThreshold
  dsimp [j] at hsqrt ⊢
  linarith

theorem harperScheduledModerateRadius_pos_of_eight_le
    {start n : ℕ} (i : Fin n) (hj : 8 ≤ start + (i : ℕ)) :
    0 < harperScheduledModerateRadius start n i := by
  have hlower :=
    one_eighth_sqrt_two_pow_le_harperScheduledModerateRadius i hj
  have hsqrtPos :
      0 < Real.sqrt (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ)) := by
    positivity
  have hbasePos :
      0 < (1 / 8 : ℝ) *
        Real.sqrt (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ)) := by
    exact mul_pos (by norm_num) hsqrtPos
  exact hbasePos.trans_le hlower

/-- Squared radius form used in Chebyshev. -/
theorem one_sixtyFourth_two_pow_le_harperScheduledModerateRadius_sq
    {start n : ℕ} (i : Fin n) (hj : 8 ≤ start + (i : ℕ)) :
    (1 / 64 : ℝ) * (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ)) ≤
      harperScheduledModerateRadius start n i ^ 2 := by
  have hlower :=
    one_eighth_sqrt_two_pow_le_harperScheduledModerateRadius i hj
  have hnonneg :
      0 ≤ (1 / 8 : ℝ) *
        Real.sqrt (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ)) := by
    positivity
  have hsquare := pow_le_pow_left₀ hnonneg hlower 2
  have hsqrtSq :
      Real.sqrt (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ)) ^ 2 =
        (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ)) := by
    exact Real.sq_sqrt (by positivity)
  nlinarith

/-! ## One coordinate and the full box complement -/

/-- A scheduled block with variance at most `1/2` leaves the moderate box
with probability at most `32 * 2^{-j}`. -/
theorem harperTiltedCubeLaw_real_abs_scheduledCenteredBlockSum_gt_radius_le
    {y start n : ℕ} (t : ℝ) (u : Fin n → ℝ) (i : Fin n)
    (hj : 8 ≤ start + (i : ℕ))
    (hvar :
      harperLinearBlockVariance y
          (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) ≤
        (1 / 2 : ℝ)) :
    (harperTiltedCubeLaw y t).real
        {eta |
          harperScheduledModerateRadius start n i <
            |harperScheduledCenteredBlockVectorVarying
              y start n t u eta i|} ≤
      32 * (1 / 2 : ℝ) ^ (start + (i : ℕ)) := by
  let j := start + (i : ℕ)
  let R := harperScheduledModerateRadius start n i
  have hR : 0 < R :=
    harperScheduledModerateRadius_pos_of_eight_le i hj
  have hR2 : (1 / 64 : ℝ) * (((2 ^ j : ℕ) : ℝ)) ≤ R ^ 2 := by
    simpa only [j, R] using!
      one_sixtyFourth_two_pow_le_harperScheduledModerateRadius_sq i hj
  have htwoPowPos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have htail := harperTiltedCubeLaw_real_abs_centeredBlockSum_gt_le
    y (harperScheduledPrimeBlock y j) t (u i) R hR
  have hratio :
      harperLinearBlockVariance y
          (harperScheduledPrimeBlock y j) t (u i) / R ^ 2 ≤
        32 / (((2 ^ j : ℕ) : ℝ)) := by
    have hbasePos :
        0 < (1 / 64 : ℝ) * (((2 ^ j : ℕ) : ℝ)) := by positivity
    calc
      harperLinearBlockVariance y
            (harperScheduledPrimeBlock y j) t (u i) / R ^ 2 ≤
          (1 / 2 : ℝ) / R ^ 2 :=
        div_le_div_of_nonneg_right hvar (sq_nonneg R)
      _ ≤ (1 / 2 : ℝ) /
          ((1 / 64 : ℝ) * (((2 ^ j : ℕ) : ℝ))) :=
        div_le_div_of_nonneg_left (by norm_num) hbasePos hR2
      _ = 32 / (((2 ^ j : ℕ) : ℝ)) := by
        field_simp [ne_of_gt htwoPowPos] <;> norm_num
  calc
    (harperTiltedCubeLaw y t).real
        {eta |
          harperScheduledModerateRadius start n i <
            |harperScheduledCenteredBlockVectorVarying
              y start n t u eta i|} ≤
        harperLinearBlockVariance y
            (harperScheduledPrimeBlock y j) t (u i) / R ^ 2 := by
      simpa only [harperScheduledCenteredBlockVectorVarying, j, R] using! htail
    _ ≤ 32 / (((2 ^ j : ℕ) : ℝ)) := hratio
    _ = 32 * (1 / 2 : ℝ) ^ j := by
      rw [div_eq_mul_inv]
      norm_num [Nat.cast_pow]
      rw [← inv_pow]
      norm_num
    _ = 32 * (1 / 2 : ℝ) ^ (start + (i : ℕ)) := rfl

/-- The whole moderate-box complement has a geometric start-scale bound,
uniformly in the number of blocks. -/
theorem harperTiltedCubeLaw_real_preimage_moderateBox_compl_le
    {y start n : ℕ} (t : ℝ) (u : Fin n → ℝ)
    (hstart : 8 ≤ start)
    (hvar : ∀ i : Fin n,
      harperLinearBlockVariance y
          (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) ≤
        (1 / 2 : ℝ)) :
    (harperTiltedCubeLaw y t).real
        ((harperScheduledCenteredBlockVectorVarying y start n t u) ⁻¹'
          (harperCoordinateBox
            (harperScheduledModerateRadius start n))ᶜ) ≤
      64 * (1 / 2 : ℝ) ^ start := by
  classical
  let bad : Fin n → Set (HarperPrimeCube y) := fun i ↦
    {eta |
      harperScheduledModerateRadius start n i <
        |harperScheduledCenteredBlockVectorVarying y start n t u eta i|}
  have hevent :
      (harperScheduledCenteredBlockVectorVarying y start n t u) ⁻¹'
          (harperCoordinateBox
            (harperScheduledModerateRadius start n))ᶜ =
        ⋃ i : Fin n, bad i := by
    ext eta
    simp only [Set.mem_preimage, Set.mem_compl_iff,
      mem_harperCoordinateBox, Set.mem_iUnion, bad, Set.mem_setOf_eq,
      not_forall, not_le]
  rw [hevent]
  calc
    (harperTiltedCubeLaw y t).real (⋃ i : Fin n, bad i) ≤
        ∑ i : Fin n, (harperTiltedCubeLaw y t).real (bad i) :=
      measureReal_iUnion_fintype_le bad
    _ ≤ ∑ i : Fin n,
        32 * (1 / 2 : ℝ) ^ (start + (i : ℕ)) := by
      exact Finset.sum_le_sum fun i _hi ↦
        harperTiltedCubeLaw_real_abs_scheduledCenteredBlockSum_gt_radius_le
          t u i (hstart.trans (Nat.le_add_right start i)) (hvar i)
    _ = 32 * (1 / 2 : ℝ) ^ start *
        ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := by
      rw [Fin.sum_univ_eq_sum_range
        (fun k : ℕ ↦ 32 * (1 / 2 : ℝ) ^ (start + k)) n]
      calc
        (∑ k ∈ Finset.range n,
            32 * (1 / 2 : ℝ) ^ (start + k)) =
            ∑ k ∈ Finset.range n,
              (32 * (1 / 2 : ℝ) ^ start) * (1 / 2 : ℝ) ^ k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [pow_add]
          ring
        _ = (32 * (1 / 2 : ℝ) ^ start) *
            ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := by
          rw [Finset.mul_sum]
    _ ≤ 32 * (1 / 2 : ℝ) ^ start * 2 := by
      gcongr
      exact sum_geometric_two_le n
    _ = 64 * (1 / 2 : ℝ) ^ start := by ring

/-- Eventual scheduled form: the off-diagonal mesh hypotheses provide the
variance bound required by the preceding deterministic union wrapper. -/
theorem exists_eventually_harperTiltedCubeVaryingModerateBox_compl_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, ∀ y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
          (∀ i : Fin n,
            |u i - t| *
                Real.log (harperBlockEndpoint
                  (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
            (harperTiltedCubeLaw y t).real
                ((harperScheduledCenteredBlockVectorVarying y start n t u) ⁻¹'
                  (harperCoordinateBox
                    (harperScheduledModerateRadius start n))ᶜ) ≤
              64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨Jvar, hJvar⟩ :=
    exists_eventually_harperScheduledOffDiagonalVariance_quarter_half M
  refine ⟨max 8 Jvar, ?_⟩
  intro start hstart n y hy t htLower htUpper u hscale
  have hstart8 : 8 ≤ start := (le_max_left 8 Jvar).trans hstart
  have hstartVar : Jvar ≤ start := (le_max_right 8 Jvar).trans hstart
  apply harperTiltedCubeLaw_real_preimage_moderateBox_compl_le
    t u hstart8
  intro i
  have hindex : Jvar ≤ start + (i : ℕ) :=
    hstartVar.trans (Nat.le_add_right start i)
  have hendpoint :
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  exact (hJvar (start + (i : ℕ)) hindex y hendpoint t
    htLower htUpper (u i) (hscale i)).2.le

/-! ## Unrestricted reverse-log event -/

/-- The literal reverse-log barrier event without a coordinate cutoff. -/
def harperTiltedVaryingReverseLogBarrierEvent
    (y start n : ℕ) (t : ℝ) (u : Fin n → ℝ)
    (x c : ℝ) (lower : Fin n → ℝ) : Set (HarperPrimeCube y) :=
  (harperScheduledCenteredBlockVectorVarying y start n t u) ⁻¹'
    harperPartialSumBarrierSet lower
      (harperNormalizedReverseLogBarrier n x c)

theorem measurableSet_harperTiltedVaryingReverseLogBarrierEvent
    (y start n : ℕ) (t : ℝ) (u : Fin n → ℝ)
    (x c : ℝ) (lower : Fin n → ℝ) :
    MeasurableSet
      (harperTiltedVaryingReverseLogBarrierEvent
        y start n t u x c lower) := by
  exact (measurableSet_harperPartialSumBarrierSet lower
    (harperNormalizedReverseLogBarrier n x c)).preimage
      (measurable_harperScheduledCenteredBlockVectorVarying
        y start n t u)

/-- The moderate-box restriction can be removed at the additive geometric
cost proved above. -/
theorem exists_eventually_harperTiltedCubeVaryingReverseLogBarrier_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n → ∀ y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
          (∀ i : Fin n,
            |u i - t| *
                Real.log (harperBlockEndpoint
                  (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
            ∀ x c : ℝ, 0 ≤ x → 0 ≤ c → ∀ lower : Fin n → ℝ,
              (harperTiltedCubeLaw y t).real
                  (harperTiltedVaryingReverseLogBarrierEvent
                    y start n t u x c lower) ≤
                Real.exp 2 *
                    (64 * (x + 4) / Real.sqrt (n : ℝ)) +
                  64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨Jbarrier, hJbarrier⟩ :=
    exists_eventually_harperTiltedCubeVaryingModerateReverseLogBarrier_probability_le M
  obtain ⟨Jtail, hJtail⟩ :=
    exists_eventually_harperTiltedCubeVaryingModerateBox_compl_probability_le M
  refine ⟨max Jbarrier Jtail, ?_⟩
  intro start hstart n hn y hy t htLower htUpper u hscale
    x c hx hc lower
  have hstartBarrier : Jbarrier ≤ start :=
    (le_max_left Jbarrier Jtail).trans hstart
  have hstartTail : Jtail ≤ start :=
    (le_max_right Jbarrier Jtail).trans hstart
  let path := harperScheduledCenteredBlockVectorVarying y start n t u
  let barrier := harperPartialSumBarrierSet lower
    (harperNormalizedReverseLogBarrier n x c)
  let box := harperCoordinateBox (harperScheduledModerateRadius start n)
  have hsubset : path ⁻¹' barrier ⊆
      path ⁻¹' (barrier ∩ box) ∪ path ⁻¹' boxᶜ := by
    intro eta heta
    by_cases hbox : path eta ∈ box
    · exact Or.inl ⟨heta, hbox⟩
    · exact Or.inr hbox
  calc
    (harperTiltedCubeLaw y t).real
        (harperTiltedVaryingReverseLogBarrierEvent
          y start n t u x c lower) ≤
        (harperTiltedCubeLaw y t).real
          (path ⁻¹' (barrier ∩ box) ∪ path ⁻¹' boxᶜ) := by
      exact measureReal_mono
        (by simpa only [harperTiltedVaryingReverseLogBarrierEvent,
          path, barrier, box] using! hsubset)
        (measure_ne_top (harperTiltedCubeLaw y t) _)
    _ ≤ (harperTiltedCubeLaw y t).real (path ⁻¹' (barrier ∩ box)) +
          (harperTiltedCubeLaw y t).real (path ⁻¹' boxᶜ) :=
      measureReal_union_le _ _
    _ ≤ Real.exp 2 *
            (64 * (x + 4) / Real.sqrt (n : ℝ)) +
          64 * (1 / 2 : ℝ) ^ start := by
      gcongr
      · simpa only [harperTiltedVaryingModerateReverseLogBarrierEvent,
          path, barrier, box] using!
          hJbarrier start hstartBarrier n hn y hy t htLower htUpper
            u hscale x c hx hc lower
      · simpa only [path, box] using!
          hJtail start hstartTail n y hy t htLower htUpper u hscale

end Problem520
end Erdos
