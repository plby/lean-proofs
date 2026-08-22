/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZGapEstimate
import ErdosProblems.Erdos1165.HLOZStoppedSpatialScreening

/-!
# The stopped-prefix candidate bands in HLOZ Proposition 4.8

This file replaces the much coarser Proposition 4.4 count in the gap screen.
For a deficit exponent `beta`, the actual candidates are the external-thick
sites, outside the distinguished dominoes, whose stopped total-local-time
deficit lies in the first

`ceil (m ^ (beta - kappaOne))`

strips of width `ceil (m ^ kappaOne)`.  Their cardinality is therefore exactly
the sum of the shell occupancies from `NearFavoriteShells`.

The shell recurrence uses initial threshold `(log m)^2` and growth factor two.
The resulting finite geometric sum is eventually bounded by the literal HLOZ
form

`6 * exp (8 * m ^ (beta - kappaOne)) * (log m)^2`.

The last two sections expose both realizations of Proposition 4.8 used later:
the direct canonical-walk shell estimate and the stopped finite-product-law
estimate.  Neither route uses `ExternalCountTransport44`; their remaining
inputs are the one-point external estimate and the genuine stopped spatial
balance/growth (or product-disintegration) estimates.
-/

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165.HLOZProposition48Candidates

open HLOZGapEstimate HLOZStoppedSpatialScreening
open LazyDecomposition NearFavoriteShells ScreeningInstantiation

noncomputable section

/-! ## The deficit-band exponent mesh -/

/-- HLOZ's deficit exponent
`beta_j = alpha + delta + j * (kappaOne - alpha - delta)`.  Index zero is
the deficit forced by the spatial gap; index one is exactly `kappaOne`, and
the later indices are the Proposition 4.8 bands. -/
def deficitExponent48 (alpha : ℝ) (j : ℕ) : ℝ :=
  alpha + ScreeningInstantiation.meshDelta +
    j * (ScreeningInstantiation.kappaOne - alpha -
      ScreeningInstantiation.meshDelta)

@[simp] theorem deficitExponent48_zero (alpha : ℝ) :
    deficitExponent48 alpha 0 = alpha + ScreeningInstantiation.meshDelta := by
  simp [deficitExponent48]

@[simp] theorem deficitExponent48_one (alpha : ℝ) :
    deficitExponent48 alpha 1 = ScreeningInstantiation.kappaOne := by
  simp [deficitExponent48]

/-- Every positive-index deficit band is in the Proposition 4.8 range once
the gap-forced exponent `alpha + delta` is below `kappaOne`. -/
theorem kappaOne_le_deficitExponent48 {alpha : ℝ} {j : ℕ}
    (halpha : alpha + ScreeningInstantiation.meshDelta ≤
      ScreeningInstantiation.kappaOne)
    (hj : 1 ≤ j) :
    ScreeningInstantiation.kappaOne ≤ deficitExponent48 alpha j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  simp only [deficitExponent48, Nat.cast_add, Nat.cast_one]
  have hstep : 0 ≤ ScreeningInstantiation.kappaOne - alpha -
      ScreeningInstantiation.meshDelta := by linarith
  nlinarith [mul_nonneg (Nat.cast_nonneg d) hstep]

/-! ## Concrete scales and candidates -/

/-! ## Concrete scales and candidates -/

/-- Width `ceil (m ^ kappaOne)` of one local-time deficit strip. -/
def shellWidth48 (m : ℕ) : ℕ :=
  Nat.ceil ((m : ℝ) ^ ScreeningInstantiation.kappaOne)

/-- Number `ceil (m ^ (beta-kappaOne))` of strips displayed at exponent
`beta`. -/
def shellCount48 (m : ℕ) (beta : ℝ) : ℕ :=
  Nat.ceil ((m : ℝ) ^ (beta - ScreeningInstantiation.kappaOne))

/-- The first-strip budget.  The harmless `+1` makes it positive at every
level, while remaining at most `3 (log m)^2` eventually. -/
def initialBudget48 (m : ℕ) : ℕ := Nat.ceil (Real.log (m : ℝ) ^ 2) + 1

/-- A fixed uniform upper bound for the shell-centred adjacent-row mass
ratio.  The constant is intentionally coarse; only its finiteness matters. -/
noncomputable def positiveInterfaceRatioConstant : ℝ :=
  Real.exp 50000000 * (4 / 3)

/-- A fixed adjacent-strip growth factor large enough for the uniform
shell-centred mass ratio. -/
noncomputable def shellGrowth48 : ℕ :=
  Nat.ceil (8 * (1 + positiveInterfaceRatioConstant)) + 1

/-- Fixed exponential coefficient used to dominate the geometric shell
budget for `shellGrowth48`. -/
noncomputable def candidateExponent48 : ℝ :=
  2 * (shellGrowth48 : ℝ) + 2

lemma positiveInterfaceRatioConstant_nonneg :
    0 ≤ positiveInterfaceRatioConstant := by
  unfold positiveInterfaceRatioConstant
  positivity

lemma positiveInterfaceRatioConstant_pos :
    0 < positiveInterfaceRatioConstant := by
  unfold positiveInterfaceRatioConstant
  positivity

lemma four_thirds_le_positiveInterfaceRatioConstant :
    (4 / 3 : ℝ) ≤ positiveInterfaceRatioConstant := by
  unfold positiveInterfaceRatioConstant
  have hexp : (1 : ℝ) ≤ Real.exp 50000000 := Real.one_le_exp (by norm_num)
  nlinarith

lemma shellGrowth48_pos : 0 < shellGrowth48 := by
  unfold shellGrowth48
  omega

lemma candidateExponent48_pos : 0 < candidateExponent48 := by
  unfold candidateExponent48
  positivity

/-- The explicit real HLOZ Proposition 4.8 candidate budget. -/
def candidateBudgetReal48 (m : ℕ) (beta : ℝ) : ℝ :=
  6 * Real.exp
      (candidateExponent48 *
        (m : ℝ) ^ (beta - ScreeningInstantiation.kappaOne)) *
    Real.log (m : ℝ) ^ 2

/-- Integer slot budget used by the gap enumeration. -/
def candidateBudget48 (m : ℕ) (beta : ℝ) : ℕ :=
  Nat.ceil (candidateBudgetReal48 m beta)

/-- The literal finite near-favorite set at a stopped prefix.  The cutoff `n`
and `totalLocalTime` are parameters so that the same definition applies to
each stopped-past atom produced by the prefix disintegration. -/
def stoppedCandidateSites48 (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ) (s : WalkPath) : Finset Point :=
  boundedCandidates
    (externalThickCandidates o n externalThreshold distinguished s)
    (deficitShellLabel totalLocalTime m (shellWidth48 m) s)
    (shellCount48 m beta)

/-- The candidate cardinality is exactly the sum of the concrete shell
occupancies. -/
theorem card_stoppedCandidateSites48
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ) (s : WalkPath) :
    (stoppedCandidateSites48 o n externalThreshold distinguished
        totalLocalTime m beta s).card =
      ∑ j ∈ Finset.range (shellCount48 m beta),
        externalShellOccupancy o n externalThreshold distinguished
          totalLocalTime m (shellWidth48 m) s j := by
  rw [stoppedCandidateSites48, ← sum_shellOccupancy_eq_card_boundedCandidates]
  rfl

/-- The geometric shell sum before it is relaxed to the exponential HLOZ
budget. -/
noncomputable def geometricCandidateBudget48 (m : ℕ) (beta : ℝ) : ℕ :=
  ∑ j ∈ Finset.range (shellCount48 m beta),
    geometricShellThreshold (initialBudget48 m) shellGrowth48 j

/-- Elementary finite bound for the geometric threshold sum. -/
theorem sum_geometricShellThreshold_le (J G N : ℕ) (hG : 0 < G) :
    (∑ j ∈ Finset.range N, geometricShellThreshold J G j) ≤
      J * N * G ^ N := by
  calc
    (∑ j ∈ Finset.range N, geometricShellThreshold J G j) ≤
        ∑ _j ∈ Finset.range N, J * G ^ N := by
      apply Finset.sum_le_sum
      intro j hj
      unfold geometricShellThreshold
      exact Nat.mul_le_mul_left J <|
        Nat.pow_le_pow_right hG (Finset.mem_range.mp hj).le
    _ = J * N * G ^ N := by
      simp [mul_assoc, mul_left_comm]

/-- The geometric shell sum has the claimed HLOZ exponential form.  The two
displayed assumptions are the only large-level facts used in the arithmetic:
the deficit exponent is nonnegative, and `(log m)^2` is at least one. -/
theorem geometricCandidateBudget48_le_candidateBudget48
    {m : ℕ} {beta : ℝ} (hm : 1 ≤ m)
    (hbeta : ScreeningInstantiation.kappaOne ≤ beta)
    (hlog : 1 ≤ Real.log (m : ℝ) ^ 2) :
    geometricCandidateBudget48 m beta ≤ candidateBudget48 m beta := by
  let x : ℝ := (m : ℝ) ^
    (beta - ScreeningInstantiation.kappaOne)
  let L : ℝ := Real.log (m : ℝ) ^ 2
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hexponent : 0 ≤ beta - ScreeningInstantiation.kappaOne := sub_nonneg.mpr hbeta
  have hx : 1 ≤ x := by
    dsimp only [x]
    exact Real.one_le_rpow hmReal hexponent
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hL : 1 ≤ L := by simpa only [L] using hlog
  have hJ : (initialBudget48 m : ℝ) ≤ 3 * L := by
    have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log (m : ℝ)))
    change ((Nat.ceil (Real.log (m : ℝ) ^ 2) + 1 : ℕ) : ℝ) ≤ 3 * L
    push_cast
    dsimp only [L]
    linarith
  have hN : (shellCount48 m beta : ℝ) ≤ 2 * x := by
    have hceil := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg m)
        (beta - ScreeningInstantiation.kappaOne))
    change (Nat.ceil ((m : ℝ) ^
      (beta - ScreeningInstantiation.kappaOne)) : ℝ) ≤ 2 * x
    dsimp only [x]
    linarith
  let G : ℝ := shellGrowth48
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    positivity
  have hGExp : G ≤ Real.exp G := by
    linarith [Real.add_one_le_exp G]
  have hpow : G ^ shellCount48 m beta ≤ Real.exp (2 * G * x) := by
    calc
      G ^ shellCount48 m beta ≤
          (Real.exp G) ^ shellCount48 m beta :=
        pow_le_pow_left₀ hG0 hGExp _
      _ = Real.exp ((shellCount48 m beta : ℝ) * G) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (2 * G * x) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have hxExp : x ≤ Real.exp x := by
    linarith [Real.add_one_le_exp x]
  have hbudgetReal : (geometricCandidateBudget48 m beta : ℝ) ≤
      candidateBudgetReal48 m beta := by
    calc
      (geometricCandidateBudget48 m beta : ℝ) ≤
          ((initialBudget48 m * shellCount48 m beta *
            shellGrowth48 ^ shellCount48 m beta : ℕ) : ℝ) := by
        exact_mod_cast sum_geometricShellThreshold_le
          (initialBudget48 m) shellGrowth48 (shellCount48 m beta)
            shellGrowth48_pos
      _ = (initialBudget48 m : ℝ) * (shellCount48 m beta : ℝ) *
          G ^ shellCount48 m beta := by push_cast; rfl
      _ ≤ (3 * L) * (2 * x) * Real.exp (2 * G * x) := by
        gcongr
      _ = 6 * L * (x * Real.exp (2 * G * x)) := by ring
      _ ≤ 6 * L * (Real.exp x * Real.exp (2 * G * x)) := by
        gcongr
      _ = 6 * L * Real.exp ((2 * G + 1) * x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ 6 * L * Real.exp (candidateExponent48 * x) := by
        gcongr
        unfold candidateExponent48
        dsimp only [G]
        nlinarith
      _ = candidateBudgetReal48 m beta := by
        simp only [candidateBudgetReal48, x, L]
        ring
  unfold candidateBudget48
  exact_mod_cast hbudgetReal.trans (Nat.le_ceil _)

/-- Eventual form of the preceding explicit arithmetic bound. -/
theorem eventually_geometricCandidateBudget48_le_candidateBudget48
    {beta : ℝ} (hbeta : ScreeningInstantiation.kappaOne ≤ beta) :
    ∀ᶠ m : ℕ in atTop,
      geometricCandidateBudget48 m beta ≤ candidateBudget48 m beta := by
  have hlogT : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1,
      hlogT.eventually (eventually_ge_atTop 1)] with m hm hlog
  exact geometricCandidateBudget48_le_candidateBudget48 hm hbeta
    (by nlinarith [sq_nonneg (Real.log (m : ℝ))])

/-- Overflow of the actual stopped-prefix candidate band. -/
def stoppedCandidateOverflow48 (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ) : Set WalkPath :=
  {s | candidateBudget48 m beta <
    (stoppedCandidateSites48 o n externalThreshold distinguished
      totalLocalTime m beta s).card}

/-- Once the explicit exponential budget dominates the geometric shell sum,
candidate overflow is contained in the shell-recurrence overflow. -/
theorem stoppedCandidateOverflow48_subset_totalOverflow
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ)
    (hbudget : geometricCandidateBudget48 m beta ≤
      candidateBudget48 m beta) :
    stoppedCandidateOverflow48 o n externalThreshold distinguished
        totalLocalTime m beta ⊆
      totalOverflow
        (externalShellOccupancy o n externalThreshold distinguished
          totalLocalTime m (shellWidth48 m))
        (geometricShellThreshold (initialBudget48 m) shellGrowth48)
        (shellCount48 m beta) := by
  intro s hs
  change candidateBudget48 m beta <
    (stoppedCandidateSites48 o n externalThreshold distinguished
      totalLocalTime m beta s).card at hs
  change geometricCandidateBudget48 m beta <
    ∑ j ∈ Finset.range (shellCount48 m beta),
      externalShellOccupancy o n externalThreshold distinguished
        totalLocalTime m (shellWidth48 m) s j
  rw [← card_stoppedCandidateSites48]
  exact hbudget.trans_lt hs

/-! ## Direct canonical-walk Proposition 4.8 screen -/

/-- The actual stopped-prefix candidate overflow is bounded by the checked
first-shell and adjacent-shell estimates.  In particular the candidate set,
strip width, strip count, growth factor, and final HLOZ-form slot budget are
all fixed here. -/
theorem simpleRandomWalk_real_stoppedCandidateOverflow48_le
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ)
    (balanced : ℕ → Set WalkPath)
    (pairTotal successes : ℕ → ℕ)
    (q : ℝ≥0∞) (hq : q ≠ ∞)
    (hbudget : geometricCandidateBudget48 m beta ≤
      candidateBudget48 m beta)
    (hsuccess : ∀ j < shellCount48 m beta - 1, 120 ≤ successes j)
    (hweightedOneSite : ∀ x,
      simpleRandomWalk
          (ExternalThickCount.candidateEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n)
            (ExternalThickCount.orientedLargeEvent o n externalThreshold) x) ≤
        q * simpleRandomWalk
          (ExternalThickCount.memberEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n) x))
    {balanceCost : ℕ → ℝ}
    (hspatialBalance : ∀ j < shellCount48 m beta - 1,
      simpleRandomWalk.real (balanced j)ᶜ ≤ balanceCost j)
    (hspatialGrowth : ∀ (j : ℕ) (hj : j < shellCount48 m beta - 1),
      simpleRandomWalk.real
          (balancedGrowthFailure balanced
            (externalShellOccupancy o n externalThreshold distinguished
              totalLocalTime m (shellWidth48 m)) shellGrowth48 j) ≤
        Bin(pairTotal j,
          UrnScreening.pairParameter
            (SmallWindow.windowMass (successes j)
              (upperFailureWindow (successes j)
                (canonicalWindowWidth (successes j))))
            (SmallWindow.windowMass (successes j)
              (lowerFailureWindow (successes j)
                (canonicalWindowWidth (successes j))))
            (SmallWindow.windowMass_nonneg _ _)
            (SmallWindow.windowMass_nonneg _ _)
            (add_pos_of_nonneg_of_pos (SmallWindow.windowMass_nonneg _ _)
              (SmallWindow.windowMass_pos
                (canonicalWindowWidth_numeric (hsuccess j hj)).1
                (lowerFailureWindow_nonempty
                  (canonicalWindowWidth_numeric (hsuccess j hj)).2.1)))).real
          {upper | upper ≤ pairTotal j ∧
            shellGrowth48 * (pairTotal j - upper) < upper}) :
    simpleRandomWalk.real
        (stoppedCandidateOverflow48 o n externalThreshold distinguished
          totalLocalTime m beta) ≤
      (q * (↑(n + 1) : ℝ≥0∞) / initialBudget48 m).toReal +
        ∑ j ∈ Finset.range (shellCount48 m beta - 1),
          (balanceCost j +
            (1 + adjacentLocalRatio (successes j)
                  (adjacentWindowRadius (canonicalWindowWidth (successes j)))
                  (adjacentWindowSeparation
                    (canonicalWindowWidth (successes j))) /
                (1 + adjacentLocalRatio (successes j)
                  (adjacentWindowRadius (canonicalWindowWidth (successes j)))
                  (adjacentWindowSeparation
                    (canonicalWindowWidth (successes j))))) ^ pairTotal j /
              (2 : ℝ) ^ growthCut shellGrowth48 (pairTotal j)) := by
  refine (measureReal_mono
    (stoppedCandidateOverflow48_subset_totalOverflow o n externalThreshold
      distinguished totalLocalTime m beta hbudget)).trans ?_
  exact simpleRandomWalk_externalShell_totalOverflow_le o n externalThreshold
    (initialBudget48 m) shellGrowth48 (shellCount48 m beta) distinguished
    totalLocalTime m (shellWidth48 m) balanced pairTotal successes q
    (by
      unfold initialBudget48
      omega)
    hq hsuccess hweightedOneSite hspatialBalance hspatialGrowth

/-- Convert any real-valued Proposition 4.8 overflow estimate into the
`ENNReal` form consumed by the gap union bound. -/
theorem simpleRandomWalk_stoppedCandidateOverflow48_le_of_real
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta R : ℝ)
    (hreal : simpleRandomWalk.real
      (stoppedCandidateOverflow48 o n externalThreshold distinguished
        totalLocalTime m beta) ≤ R) :
    simpleRandomWalk
        (stoppedCandidateOverflow48 o n externalThreshold distinguished
          totalLocalTime m beta) ≤ ENNReal.ofReal R := by
  change (simpleRandomWalk
    (stoppedCandidateOverflow48 o n externalThreshold distinguished
      totalLocalTime m beta)).toReal ≤ R at hreal
  have hR : 0 ≤ R := ENNReal.toReal_nonneg.trans hreal
  apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).1
  simpa [ENNReal.toReal_ofReal hR] using hreal

/-- Eventual version in which the HLOZ-form candidate budget arithmetic is
fully discharged. -/
theorem eventually_simpleRandomWalk_real_stoppedCandidateOverflow48_le
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : ℕ → WalkPath → Finset Point)
    (totalLocalTime : ℕ → WalkPath → Point → ℕ)
    (beta : ℝ) (hbeta : ScreeningInstantiation.kappaOne ≤ beta)
    (balanced : ℕ → ℕ → Set WalkPath)
    (pairTotal successes : ℕ → ℕ → ℕ)
    (q : ℕ → ℝ≥0∞) (hq : ∀ m, q m ≠ ∞)
    (hsuccess : ∀ m j, j < shellCount48 m beta - 1 →
      120 ≤ successes m j)
    (hweightedOneSite : ∀ m x,
      simpleRandomWalk
          (ExternalThickCount.candidateEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n)
            (ExternalThickCount.orientedLargeEvent o n externalThreshold) x) ≤
        q m * simpleRandomWalk
          (ExternalThickCount.memberEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n) x))
    {balanceCost : ℕ → ℕ → ℝ}
    (hspatialBalance : ∀ m j, j < shellCount48 m beta - 1 →
      simpleRandomWalk.real (balanced m j)ᶜ ≤ balanceCost m j)
    (hspatialGrowth : ∀ m (j : ℕ) (hj : j < shellCount48 m beta - 1),
      simpleRandomWalk.real
          (balancedGrowthFailure (balanced m)
            (externalShellOccupancy o n externalThreshold (distinguished m)
              (totalLocalTime m) m (shellWidth48 m)) shellGrowth48 j) ≤
        Bin(pairTotal m j,
          UrnScreening.pairParameter
            (SmallWindow.windowMass (successes m j)
              (upperFailureWindow (successes m j)
                (canonicalWindowWidth (successes m j))))
            (SmallWindow.windowMass (successes m j)
              (lowerFailureWindow (successes m j)
                (canonicalWindowWidth (successes m j))))
            (SmallWindow.windowMass_nonneg _ _)
            (SmallWindow.windowMass_nonneg _ _)
            (add_pos_of_nonneg_of_pos (SmallWindow.windowMass_nonneg _ _)
              (SmallWindow.windowMass_pos
                (canonicalWindowWidth_numeric (hsuccess m j hj)).1
                (lowerFailureWindow_nonempty
                  (canonicalWindowWidth_numeric (hsuccess m j hj)).2.1)))).real
          {upper | upper ≤ pairTotal m j ∧
            shellGrowth48 * (pairTotal m j - upper) < upper}) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk.real
          (stoppedCandidateOverflow48 o n externalThreshold (distinguished m)
            (totalLocalTime m) m beta) ≤
        (q m * (↑(n + 1) : ℝ≥0∞) / initialBudget48 m).toReal +
          ∑ j ∈ Finset.range (shellCount48 m beta - 1),
            (balanceCost m j +
              (1 + adjacentLocalRatio (successes m j)
                    (adjacentWindowRadius
                      (canonicalWindowWidth (successes m j)))
                    (adjacentWindowSeparation
                      (canonicalWindowWidth (successes m j))) /
                  (1 + adjacentLocalRatio (successes m j)
                    (adjacentWindowRadius
                      (canonicalWindowWidth (successes m j)))
                    (adjacentWindowSeparation
                      (canonicalWindowWidth (successes m j))))) ^
                  pairTotal m j /
                (2 : ℝ) ^ growthCut shellGrowth48 (pairTotal m j)) := by
  filter_upwards
      [eventually_geometricCandidateBudget48_le_candidateBudget48 hbeta]
      with m hbudget
  exact simpleRandomWalk_real_stoppedCandidateOverflow48_le o n
    externalThreshold (distinguished m) (totalLocalTime m) m beta
    (balanced m) (pairTotal m) (successes m) (q m) (hq m) hbudget
    (hsuccess m) (hweightedOneSite m) (hspatialBalance m) (hspatialGrowth m)

/-! ## Oriented families of deficit bands -/

section OrientedBands

variable {Band : Type*}

/-- The concrete Proposition 4.8 candidate sites when the domino orientation
and stopped-prefix data vary with the deficit band. -/
def orientedStoppedCandidateSites48
    (orientation : Band → Orientation)
    (cutoff externalThreshold : Band → ℕ)
    (distinguished : Band → WalkPath → Finset Point)
    (totalLocalTime : Band → WalkPath → Point → ℕ)
    (m : ℕ) (beta : Band → ℝ) (s : WalkPath) (band : Band) : Finset Point :=
  stoppedCandidateSites48 (orientation band) (cutoff band)
    (externalThreshold band) (distinguished band) (totalLocalTime band)
    m (beta band) s

/-- Some displayed Proposition 4.8 band exceeds its HLOZ-form slot budget. -/
def orientedStoppedCandidateOverflow48 (bands : Finset Band)
    (orientation : Band → Orientation)
    (cutoff externalThreshold : Band → ℕ)
    (distinguished : Band → WalkPath → Finset Point)
    (totalLocalTime : Band → WalkPath → Point → ℕ)
    (m : ℕ) (beta : Band → ℝ) : Set WalkPath :=
  candidateOverflow bands
    (orientedStoppedCandidateSites48 orientation cutoff externalThreshold
      distinguished totalLocalTime m beta)
    (fun band ↦ candidateBudget48 m (beta band))

/-- The family overflow is exactly the finite union of the individual
Proposition 4.8 overflows. -/
theorem orientedStoppedCandidateOverflow48_eq_biUnion
    (bands : Finset Band) (orientation : Band → Orientation)
    (cutoff externalThreshold : Band → ℕ)
    (distinguished : Band → WalkPath → Finset Point)
    (totalLocalTime : Band → WalkPath → Point → ℕ)
    (m : ℕ) (beta : Band → ℝ) :
    orientedStoppedCandidateOverflow48 bands orientation cutoff
        externalThreshold distinguished totalLocalTime m beta =
      ⋃ band ∈ bands,
        stoppedCandidateOverflow48 (orientation band) (cutoff band)
          (externalThreshold band) (distinguished band) (totalLocalTime band)
          m (beta band) := by
  ext s
  simp only [orientedStoppedCandidateOverflow48, candidateOverflow,
    orientedStoppedCandidateSites48, stoppedCandidateOverflow48,
    Set.mem_ofPred_eq, Set.mem_iUnion]
  tauto

/-- Finite summation of the individual shell/product screens. -/
theorem simpleRandomWalk_orientedStoppedCandidateOverflow48_le
    (bands : Finset Band) (orientation : Band → Orientation)
    (cutoff externalThreshold : Band → ℕ)
    (distinguished : Band → WalkPath → Finset Point)
    (totalLocalTime : Band → WalkPath → Point → ℕ)
    (m : ℕ) (beta : Band → ℝ) (failure : Band → ℝ≥0∞)
    (hband : ∀ band ∈ bands,
      simpleRandomWalk
          (stoppedCandidateOverflow48 (orientation band) (cutoff band)
            (externalThreshold band) (distinguished band)
            (totalLocalTime band) m (beta band)) ≤ failure band) :
    simpleRandomWalk
        (orientedStoppedCandidateOverflow48 bands orientation cutoff
          externalThreshold distinguished totalLocalTime m beta) ≤
      ∑ band ∈ bands, failure band := by
  rw [orientedStoppedCandidateOverflow48_eq_biUnion]
  exact (measure_biUnion_finset_le bands _).trans <|
    Finset.sum_le_sum fun band hmem ↦ hband band hmem

end OrientedBands

end

end Erdos1165.HLOZProposition48Candidates
