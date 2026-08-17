/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.HarmonicIteration
import ErdosProblems.Erdos144.HarmonicStageRegularity
import ErdosProblems.Erdos144.HarmonicExpectation
import ErdosProblems.Erdos144.ScaleLimits

/-!
# The explicit high-probability harmonic reservoir

This file combines the finite signed-energy stage with the explicit
eight-adic scales.  The analytic normalized-energy estimate is kept as one
named hypothesis until the largest-differing-coordinate reindexing theorem
is connected below.
-/

open scoped BigOperators Topology

namespace Erdos144.HarmonicHighProbability

noncomputable section

open HarmonicProb

attribute [local instance] Classical.propDecidable

/-- The depth of stage `j` below its top endpoint. -/
def stageDepth (s j : ℕ) : ℕ :=
  19 * Harmonic.lowerExponent s + Harmonic.stageStride s * j

theorem stageDepth_eq_stageRegularity (s j : ℕ) :
    stageDepth s j = HarmonicStageRegularity.stageDepth s j := rfl

theorem stageDepth_ge_s {s j : ℕ} (hs : 1 ≤ s) :
    s ≤ stageDepth s j := by
  have hcount : 1 ≤ Harmonic.stageCount s := Harmonic.stageCount_pos s
  have hcountSq : 1 ≤ Harmonic.stageCount s ^ 2 := one_le_pow₀ hcount
  have hsL : s ≤ Harmonic.lowerExponent s := by
    simpa [Harmonic.lowerExponent] using Nat.mul_le_mul_left s hcountSq
  unfold stageDepth
  omega

/-- The deliberately wasteful inequality `9^19 > 8^20` makes the ternary
state count dominate every explicit stage top. -/
theorem stageTop_le_nine_pow_stageDepth (s j : ℕ) :
    Harmonic.stageTop s j ≤ 9 ^ stageDepth s j := by
  let L := Harmonic.lowerExponent s
  let t := Harmonic.stageStride s * j
  have hbase : 8 ^ 20 ≤ 9 ^ 19 := by norm_num
  have htail : 8 ^ t ≤ 9 ^ t :=
    Nat.pow_le_pow_left (by norm_num : 8 ≤ 9) t
  have hmain : (8 ^ 20) ^ L ≤ (9 ^ 19) ^ L :=
    Nat.pow_le_pow_left hbase L
  calc
    Harmonic.stageTop s j = 8 ^ (20 * L + t) := by
      simp only [Harmonic.stageTop, L, t]
    _ = 8 ^ (20 * L) * 8 ^ t := pow_add _ _ _
    _ = (8 ^ 20) ^ L * 8 ^ t := by rw [pow_mul]
    _ ≤ (9 ^ 19) ^ L * 9 ^ t := Nat.mul_le_mul hmain htail
    _ = 9 ^ (19 * L) * 9 ^ t :=
      congrArg (fun x : ℕ ↦ x * 9 ^ t) (pow_mul 9 19 L).symm
    _ = 9 ^ (19 * L + t) := (pow_add _ _ _).symm
    _ = 9 ^ stageDepth s j := by simp [stageDepth, L, t]

theorem eight_mul_stageTop_le_xi_mul_nine_pow_sub
    {s j : ℕ} (hs : 1 ≤ s) :
    8 * Harmonic.stageTop s j ≤
      Harmonic.xi s * 9 ^ (stageDepth s j - s) := by
  have hsR : s ≤ stageDepth s j := stageDepth_ge_s hs
  calc
    8 * Harmonic.stageTop s j ≤ 8 * 9 ^ stageDepth s j :=
      Nat.mul_le_mul_left 8 (stageTop_le_nine_pow_stageDepth s j)
    _ = (8 * 9 ^ s) * 9 ^ (stageDepth s j - s) := by
      rw [mul_assoc]
      congr 1
      rw [← pow_add, Nat.add_sub_of_le hsR]
    _ = Harmonic.xi s * 9 ^ (stageDepth s j - s) := by
      rw [Harmonic.xi]

/-- Regularity at the deepest octave supplies enough ternary states for the
signed-energy Cauchy estimate at every explicit stage. -/
theorem state_count_of_stage_regular
    {s j : ℕ} (hs : 1 ≤ s) {B : Finset ℕ}
    (hregular : HarmonicOctaves.OctaveRegular
      (Harmonic.stageTop s j) (stageDepth s j) s B) :
    8 * Harmonic.stageTop s j ≤ Harmonic.xi s * 3 ^ B.card := by
  have hsR : s ≤ stageDepth s j := stageDepth_ge_s hs
  have htail := hregular (stageDepth s j)
    (Finset.mem_Icc.mpr ⟨hsR, le_rfl⟩)
  have hcard : 2 * (stageDepth s j - s) ≤ B.card :=
    htail.trans (Finset.card_le_card Finset.inter_subset_left)
  have hpow : 9 ^ (stageDepth s j - s) ≤ 3 ^ B.card := by
    calc
      9 ^ (stageDepth s j - s) =
          3 ^ (2 * (stageDepth s j - s)) := by
        rw [pow_mul]
        norm_num
      _ ≤ 3 ^ B.card := Nat.pow_le_pow_right (by norm_num) hcard
  exact (eight_mul_stageTop_le_xi_mul_nine_pow_sub hs).trans
    (Nat.mul_le_mul_left (Harmonic.xi s) hpow)

/-- The state-count hypothesis in the concrete iteration follows directly
from the complement of `ReservoirIrregular`. -/
theorem state_count_of_not_reservoirIrregular
    {s j : ℕ} (hs : 1 ≤ s) {B : Finset ℕ}
    (hgood : ¬ Harmonic.ReservoirIrregular
      (Harmonic.stageTop s j) (stageDepth s j) s (Harmonic.xi s) B) :
    8 * Harmonic.stageTop s j ≤ Harmonic.xi s * 3 ^ B.card := by
  apply state_count_of_stage_regular hs
  by_contra h
  exact hgood (Or.inl h)

theorem lowerScale_le_stageTop (s j : ℕ) :
    Harmonic.lowerScale s ≤ Harmonic.stageTop s j := by
  unfold Harmonic.lowerScale Harmonic.stageTop
  apply Nat.pow_le_pow_right (by norm_num)
  omega

theorem xi_le_eight_pow_two_mul_add_one (s : ℕ) :
    Harmonic.xi s ≤ 8 ^ (2 * s + 1) := by
  have hp : 9 ^ s ≤ (8 ^ 2) ^ s :=
    Nat.pow_le_pow_left (by norm_num : 9 ≤ 8 ^ 2) s
  calc
    Harmonic.xi s = 8 * 9 ^ s := by rw [Harmonic.xi]
    _ ≤ 8 * (8 ^ 2) ^ s := Nat.mul_le_mul_left 8 hp
    _ = 8 * 8 ^ (2 * s) := by rw [pow_mul]
    _ = 8 ^ (2 * s + 1) := by simp [pow_add, mul_comm]

theorem xi_lt_lowerScale {s : ℕ} (hs : 1 ≤ s) :
    Harmonic.xi s < Harmonic.lowerScale s := by
  have hxi8 : 8 ≤ Harmonic.xi s := by
    have hpow : 1 ≤ 9 ^ s := Nat.one_le_pow s 9 (by norm_num)
    simpa [Harmonic.xi] using Nat.mul_le_mul_left 8 hpow
  have hcount2 : 2 ≤ Harmonic.stageCount s := by
    unfold Harmonic.stageCount
    exact le_trans (by norm_num : 2 ≤ 8 ^ 3)
      (Nat.pow_le_pow_left hxi8 3)
  have hcountSq : 4 ≤ Harmonic.stageCount s ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hcount2 hcount2
  have hExp : 2 * s + 1 < Harmonic.lowerExponent s := by
    have hmul := Nat.mul_le_mul_left s hcountSq
    simp only [Harmonic.lowerExponent] at hmul ⊢
    nlinarith
  exact (xi_le_eight_pow_two_mul_add_one s).trans_lt
    (Nat.pow_lt_pow_right (by norm_num) hExp)

theorem xi_lt_stageTop {s : ℕ} (hs : 1 ≤ s) (j : ℕ) :
    Harmonic.xi s < Harmonic.stageTop s j :=
  (xi_lt_lowerScale hs).trans_le (lowerScale_le_stageTop s j)

/-- The sparse fresh block used at stage `j` lies inside the next full
reservoir. -/
theorem stage_union_subset_next {s : ℕ} (hs : 1 ≤ s) (j : ℕ) :
    Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j) ∪
        Finset.Ioc (Harmonic.xi s * Harmonic.stageTop s j)
          (3 * (Harmonic.xi s * Harmonic.stageTop s j)) ⊆
      Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s (j + 1)) := by
  intro n hn
  rcases Finset.mem_union.mp hn with hold | hfresh
  · have hnold := Finset.mem_Ioc.mp hold
    apply Finset.mem_Ioc.mpr
    refine ⟨hnold.1, ?_⟩
    have hxi1 : 1 ≤ Harmonic.xi s := Harmonic.xi_pos s
    have hDfresh : Harmonic.stageTop s j ≤
        3 * (Harmonic.xi s * Harmonic.stageTop s j) := by
      calc
        Harmonic.stageTop s j = 1 * Harmonic.stageTop s j := by simp
        _ ≤ (3 * Harmonic.xi s) * Harmonic.stageTop s j :=
          Nat.mul_le_mul_right _ (by omega)
        _ = 3 * (Harmonic.xi s * Harmonic.stageTop s j) := by ring
    exact hnold.2.trans <| hDfresh.trans
      (Harmonic.freshInterval_le_nextStageTop hs)
  · have hnnew := Finset.mem_Ioc.mp hfresh
    apply Finset.mem_Ioc.mpr
    refine ⟨?_, hnnew.2.trans (Harmonic.freshInterval_le_nextStageTop hs)⟩
    have hCD := lowerScale_le_stageTop s j
    have hxi1 : 1 ≤ Harmonic.xi s := Harmonic.xi_pos s
    have hDX : Harmonic.stageTop s j ≤
        Harmonic.xi s * Harmonic.stageTop s j := by
      simpa using Nat.mul_le_mul_right (Harmonic.stageTop s j) hxi1
    exact lt_of_le_of_lt (hCD.trans hDX) hnnew.1

/-- The interval at every stage consists of positive coordinates and lies
below its stage top. -/
theorem stageInterval_subset_Icc (s j : ℕ) :
    Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j) ⊆
      Finset.Icc 1 (Harmonic.stageTop s j) := by
  intro n hn
  have h := Finset.mem_Ioc.mp hn
  exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩

/-- Fully assembled finite harmonic estimate, conditional only on the two
analytic probability inputs.  The first input is discharged by the explicit
Chernoff theorem in `HarmonicStageRegularity`; the second is the finite
largest-coordinate energy reindexing theorem. -/
theorem explicit_failure_bound_of_regularity_and_expectation
    {s : ℕ} (hs : 1 ≤ s) (regularityError : ℝ)
    (hregularityError : 0 ≤ regularityError)
    (hregularity : ∀ j,
      prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
        (fun B ↦ ¬ HarmonicOctaves.OctaveRegular
          (Harmonic.stageTop s j) (stageDepth s j) s B) ≤ regularityError)
    (hexpect : ∀ j,
      HarmonicOctaves.normalizedOffDiagonalExpectation
          (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
          (HarmonicOctaves.OctaveRegular
            (Harmonic.stageTop s j) (stageDepth s j) s) ≤
        1200 * (8 : ℝ) ^ s / Harmonic.stageTop s j) :
    prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.finalTop s))
        (fun T ↦ ¬ Harmonic.HasEqualSubsums T) ≤
      Real.exp (-(Harmonic.xi s : ℝ) / 27) +
        (regularityError + 9600 * (8 : ℝ) ^ s / Harmonic.xi s +
          1 / (Harmonic.xi s : ℝ)) := by
  let delta : ℝ := regularityError +
    9600 * (8 : ℝ) ^ s / Harmonic.xi s + 1 / (Harmonic.xi s : ℝ)
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    positivity
  have hirregular : ∀ j,
      prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
        (Harmonic.ReservoirIrregular (Harmonic.stageTop s j)
          (stageDepth s j) s (Harmonic.xi s)) ≤ delta := by
    intro j
    exact Harmonic.prob_reservoirIrregular_le
      (fun n hn ↦ (Finset.mem_Icc.mp (stageInterval_subset_Icc s j hn)).1)
      (stageInterval_subset_Icc s j) (by simp [Harmonic.stageTop])
      (Harmonic.xi_pos s)
      regularityError (hregularity j) (hexpect j)
  have hxi2 : 2 ≤ Harmonic.xi s := by
    have hpow : 1 ≤ 9 ^ s := Nat.one_le_pow s 9 (by norm_num)
    have hxi8 : 8 ≤ Harmonic.xi s := by
      simpa [Harmonic.xi] using Nat.mul_le_mul_left 8 hpow
    omega
  have hbound := HarmonicIteration.harmonic_failure_probability_after_xi_cube_le_exp
    (Harmonic.lowerScale s) s (Harmonic.xi s) (Harmonic.stageTop s)
      (stageDepth s) delta
      (fun _ ↦ by simp [Harmonic.stageTop]) hxi2
      (xi_lt_stageTop hs) hdelta (stage_union_subset_next hs)
      (fun j B _ hgood ↦ state_count_of_not_reservoirIrregular hs hgood)
      hirregular
  simpa [Harmonic.finalTop, Harmonic.stageCount, delta] using hbound

/-- The full finite estimate with the concrete Chernoff regularity theorem
inserted.  Its only remaining input is the normalized signed-energy
expectation at each stage. -/
theorem explicit_failure_bound_of_expectation
    {s : ℕ} (hs : 2 ≤ s)
    (hexpect : ∀ j,
      HarmonicOctaves.normalizedOffDiagonalExpectation
          (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
          (HarmonicOctaves.OctaveRegular
            (Harmonic.stageTop s j) (stageDepth s j) s) ≤
        1200 * (8 : ℝ) ^ s / Harmonic.stageTop s j) :
    prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.finalTop s))
        (fun T ↦ ¬ Harmonic.HasEqualSubsums T) ≤
      Real.exp (-(Harmonic.xi s : ℝ) / 27) +
        (HarmonicStageRegularity.uniformStageRegularityError s +
          9600 * (8 : ℝ) ^ s / Harmonic.xi s +
          1 / (Harmonic.xi s : ℝ)) := by
  apply explicit_failure_bound_of_regularity_and_expectation (le_trans (by norm_num) hs)
    (HarmonicStageRegularity.uniformStageRegularityError s)
    (HarmonicStageRegularity.uniformStageRegularityError_nonneg s) _ hexpect
  intro j
  change prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
      (fun B ↦ ¬ HarmonicOctaves.OctaveRegular (Harmonic.stageTop s j)
        (HarmonicStageRegularity.stageDepth s j) s B) ≤ _
  calc
    _ ≤ HarmonicStageRegularity.stageRegularityError s j :=
      HarmonicStageRegularity.prob_stage_not_octaveRegular_le hs j
    _ ≤ HarmonicStageRegularity.uniformStageRegularityError s :=
      HarmonicStageRegularity.stageRegularityError_le_uniform s j

/-- Markov error for the explicit selected-cardinality cutoff. -/
def cardinalityError (s : ℕ) : ℝ :=
  (∑ i ∈ Finset.Ioc (Harmonic.lowerScale s) (Harmonic.finalTop s),
      HarmonicProb.param i) / Harmonic.cardinalCutoff s

theorem cardinalityError_nonneg (s : ℕ) : 0 ≤ cardinalityError s := by
  unfold cardinalityError
  exact div_nonneg (Finset.sum_nonneg fun i _ ↦ HarmonicProb.param_nonneg i)
    (by positivity)

/-- The probability of exceeding the explicit cutoff is controlled by its
first moment. -/
theorem prob_card_gt_cardinalCutoff_le (s : ℕ) :
    prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.finalTop s))
        (fun T ↦ Harmonic.cardinalCutoff s < T.card) ≤ cardinalityError s := by
  let I := Finset.Ioc (Harmonic.lowerScale s) (Harmonic.finalTop s)
  have hI : ∀ n ∈ I, 1 ≤ n := by
    intro n hn
    have hn0 := (Finset.mem_Ioc.mp hn).1
    omega
  calc
    prob I (fun T ↦ Harmonic.cardinalCutoff s < T.card) ≤
        prob I (fun T ↦ Harmonic.cardinalCutoff s ≤ T.card) := by
      apply prob_mono I _ _ hI
      intro T hT
      omega
    _ ≤ (∑ T ∈ I.powerset, weight I T * (T.card : ℝ)) /
          Harmonic.cardinalCutoff s := by
      simpa only [Nat.cast_le] using
        (prob_le_expectation_div I (fun T ↦ (T.card : ℝ))
          (Harmonic.cardinalCutoff s : ℝ) hI
          (fun _ _ ↦ by positivity)
          (by exact_mod_cast Harmonic.cardinalCutoff_pos s))
    _ = cardinalityError s := by
      rw [HarmonicMoments.expectation_card]
      rfl

theorem cardinalityError_le {s : ℕ} (hs : 1 ≤ s) :
    cardinalityError s ≤ 169 / (Harmonic.xi s : ℝ) := by
  have hmass :
      (∑ i ∈ Finset.Ioc (Harmonic.lowerScale s) (Harmonic.finalTop s),
          HarmonicProb.param i) ≤ 169 * Harmonic.lowerExponent s := by
    simpa only [HarmonicProb.param] using
      (Harmonic.harmonicIntervalMass_le hs)
  have hL : 0 < Harmonic.lowerExponent s := by
    simp only [Harmonic.lowerExponent]
    exact Nat.mul_pos hs (pow_pos (Harmonic.stageCount_pos s) 2)
  have hcut : Harmonic.xi s * Harmonic.lowerExponent s ≤
      Harmonic.cardinalCutoff s := by
    simp only [Harmonic.cardinalCutoff]
    exact Nat.mul_le_mul_left (Harmonic.xi s) (by omega)
  have hxiR : (0 : ℝ) < Harmonic.xi s := by
    exact_mod_cast Harmonic.xi_pos s
  have hLR : (0 : ℝ) < Harmonic.lowerExponent s := by exact_mod_cast hL
  unfold cardinalityError
  calc
    (∑ i ∈ Finset.Ioc (Harmonic.lowerScale s) (Harmonic.finalTop s),
        HarmonicProb.param i) / Harmonic.cardinalCutoff s ≤
        (169 * Harmonic.lowerExponent s) / Harmonic.cardinalCutoff s := by
      gcongr
    _ ≤ (169 * Harmonic.lowerExponent s) /
        (Harmonic.xi s * Harmonic.lowerExponent s) := by
      gcongr
      exact_mod_cast hcut
    _ = 169 / (Harmonic.xi s : ℝ) := by
      field_simp

theorem tendsto_cardinalityError_zero :
    Filter.Tendsto cardinalityError Filter.atTop (𝓝 0) := by
  have hmajor : Filter.Tendsto (fun s : ℕ ↦ 169 / (Harmonic.xi s : ℝ))
      Filter.atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp Harmonic.tendsto_xi_atTop)
  apply squeeze_zero' (g := fun s : ℕ ↦ 169 / (Harmonic.xi s : ℝ))
  · exact Filter.Eventually.of_forall cardinalityError_nonneg
  · filter_upwards [Harmonic.eventually_one_le_scaleParameter] with s hs
    exact cardinalityError_le hs
  · exact hmajor

/-- Explicit failure error from regularity, energy Markov, and the fresh
stage iteration. -/
def harmonicFailureError (s : ℕ) : ℝ :=
  Real.exp (-(Harmonic.xi s : ℝ) / 27) +
    (HarmonicStageRegularity.uniformStageRegularityError s +
      9600 * (8 : ℝ) ^ s / Harmonic.xi s +
      1 / (Harmonic.xi s : ℝ))

/-- Total error after also imposing the explicit cardinality cutoff. -/
def harmonicTotalError (s : ℕ) : ℝ :=
  harmonicFailureError s + cardinalityError s

theorem harmonicTotalError_nonneg (s : ℕ) : 0 ≤ harmonicTotalError s := by
  unfold harmonicTotalError harmonicFailureError
  have hreg := HarmonicStageRegularity.uniformStageRegularityError_nonneg s
  have hcard := cardinalityError_nonneg s
  positivity

theorem tendsto_exp_neg_xi_div_zero :
    Filter.Tendsto
      (fun s : ℕ ↦ Real.exp (-(Harmonic.xi s : ℝ) / 27))
      Filter.atTop (𝓝 0) := by
  have hxi : Filter.Tendsto (fun s : ℕ ↦ (Harmonic.xi s : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp Harmonic.tendsto_xi_atTop
  have hscaled : Filter.Tendsto
      (fun s : ℕ ↦ (1 / 27 : ℝ) * (Harmonic.xi s : ℝ))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) hxi
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled
  convert h using 1
  funext s
  dsimp only [Function.comp_apply]
  congr 1
  ring

theorem tendsto_energyMarkovError_zero :
    Filter.Tendsto
      (fun s : ℕ ↦ 9600 * (8 : ℝ) ^ s / Harmonic.xi s)
      Filter.atTop (𝓝 0) := by
  have hpow : Filter.Tendsto (fun s : ℕ ↦ ((8 / 9 : ℝ) ^ s))
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have heq :
      (fun s : ℕ ↦ 9600 * (8 : ℝ) ^ s / Harmonic.xi s) =
        (fun s : ℕ ↦ 1200 * (8 / 9 : ℝ) ^ s) := by
    funext s
    rw [Harmonic.xi]
    push_cast
    rw [div_pow]
    have h9 : (9 : ℝ) ^ s ≠ 0 := by positivity
    field_simp
    ring
  rw [heq]
  simpa using
    ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1200 : ℝ))
      Filter.atTop (𝓝 1200)).mul hpow)

theorem tendsto_inv_xi_zero :
    Filter.Tendsto (fun s : ℕ ↦ 1 / (Harmonic.xi s : ℝ))
      Filter.atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_natCast_atTop_atTop.comp Harmonic.tendsto_xi_atTop)

theorem tendsto_harmonicFailureError_zero :
    Filter.Tendsto harmonicFailureError Filter.atTop (𝓝 0) := by
  unfold harmonicFailureError
  simpa only [one_div, zero_add, add_zero] using tendsto_exp_neg_xi_div_zero.add
    ((HarmonicStageRegularity.tendsto_uniformStageRegularityError_zero.add
      tendsto_energyMarkovError_zero).add tendsto_inv_xi_zero)

theorem tendsto_harmonicTotalError_zero :
    Filter.Tendsto harmonicTotalError Filter.atTop (𝓝 0) := by
  unfold harmonicTotalError
  simpa only [zero_add, add_zero] using
    tendsto_harmonicFailureError_zero.add tendsto_cardinalityError_zero

/-- Quantitative high-probability equal-subsum theorem, conditional only on
the normalized signed-energy expectation. -/
theorem one_sub_totalError_le_good_prob_of_expectation
    {s : ℕ} (hs : 2 ≤ s)
    (hexpect : ∀ j,
      HarmonicOctaves.normalizedOffDiagonalExpectation
          (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
          (HarmonicOctaves.OctaveRegular
            (Harmonic.stageTop s j) (stageDepth s j) s) ≤
        1200 * (8 : ℝ) ^ s / Harmonic.stageTop s j) :
    1 - harmonicTotalError s ≤
      prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.finalTop s))
        (fun T ↦ Harmonic.HasEqualSubsums T ∧
          T.card ≤ Harmonic.cardinalCutoff s) := by
  let I := Finset.Ioc (Harmonic.lowerScale s) (Harmonic.finalTop s)
  let Good : Finset ℕ → Prop := fun T ↦ Harmonic.HasEqualSubsums T ∧
    T.card ≤ Harmonic.cardinalCutoff s
  have hI : ∀ n ∈ I, 1 ≤ n := by
    intro n hn
    have hn0 := (Finset.mem_Ioc.mp hn).1
    omega
  have hfailure : prob I (fun T ↦ ¬ Harmonic.HasEqualSubsums T) ≤
      harmonicFailureError s := by
    simpa only [I, harmonicFailureError] using
      explicit_failure_bound_of_expectation hs hexpect
  have hcard : prob I (fun T ↦ Harmonic.cardinalCutoff s < T.card) ≤
      cardinalityError s := by
    simpa only [I] using prob_card_gt_cardinalCutoff_le s
  have hbad : prob I (fun T ↦ ¬ Good T) ≤ harmonicTotalError s := by
    calc
      prob I (fun T ↦ ¬ Good T) =
          prob I (fun T ↦ ¬ Harmonic.HasEqualSubsums T ∨
            Harmonic.cardinalCutoff s < T.card) := by
        apply Harmonic.prob_congr
        intro T
        simp only [Good, not_and_or, not_le]
      _ ≤ prob I (fun T ↦ ¬ Harmonic.HasEqualSubsums T) +
          prob I (fun T ↦ Harmonic.cardinalCutoff s < T.card) :=
        prob_or_le I _ _ hI
      _ ≤ harmonicFailureError s + cardinalityError s :=
        add_le_add hfailure hcard
      _ = harmonicTotalError s := rfl
  have hsplit := prob_add_prob_not I Good
  change 1 - harmonicTotalError s ≤ prob I Good
  linarith

/-- Final asymptotic harmonic statement, with the single remaining finite
energy reindexing estimate exposed as a hypothesis. -/
theorem tendsto_good_prob_one_of_expectation
    (hexpect : ∀ s : ℕ, 2 ≤ s → ∀ j,
      HarmonicOctaves.normalizedOffDiagonalExpectation
          (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
          (HarmonicOctaves.OctaveRegular
            (Harmonic.stageTop s j) (stageDepth s j) s) ≤
        1200 * (8 : ℝ) ^ s / Harmonic.stageTop s j) :
    Filter.Tendsto
      (fun s : ℕ ↦
        prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.finalTop s))
          (fun T ↦ Harmonic.HasEqualSubsums T ∧
            T.card ≤ Harmonic.cardinalCutoff s))
      Filter.atTop (𝓝 1) := by
  have hlower : Filter.Tendsto (fun s : ℕ ↦ 1 - harmonicTotalError s)
      Filter.atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub tendsto_harmonicTotalError_zero :
        Filter.Tendsto (fun s : ℕ ↦ (1 : ℝ) - harmonicTotalError s)
          Filter.atTop (𝓝 (1 - 0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with s hs
    exact one_sub_totalError_le_good_prob_of_expectation hs (hexpect s hs)
  · filter_upwards with s
    apply prob_le_one
    intro n hn
    have hn0 := (Finset.mem_Ioc.mp hn).1
    omega

/-- The explicit harmonic random set has disjoint nonempty equal subsums,
within the transfer cardinality cutoff, with probability tending to one. -/
theorem tendsto_good_prob_one :
    Filter.Tendsto
      (fun s : ℕ ↦
        prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.finalTop s))
          (fun T ↦ Harmonic.HasEqualSubsums T ∧
            T.card ≤ Harmonic.cardinalCutoff s))
      Filter.atTop (𝓝 1) := by
  apply tendsto_good_prob_one_of_expectation
  intro s _hs j
  simpa only [stageDepth_eq_stageRegularity] using
    (HarmonicExpectation.stage_normalizedOffDiagonalExpectation_le_1200 s j)

end

end Erdos144.HarmonicHighProbability
