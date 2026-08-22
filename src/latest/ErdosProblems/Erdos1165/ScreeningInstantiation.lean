/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.Balancedness
import ErdosProblems.Erdos1165.ExternalThickCount
import ErdosProblems.Erdos1165.GeometricChernoff
import ErdosProblems.Erdos1165.NearFavoriteShells
import ErdosProblems.Erdos1165.NegativeBinomialLocalCLT
import ErdosProblems.Erdos1165.PathInsertion
import ErdosProblems.Erdos1165.SmallWindow
import ErdosProblems.Erdos1165.StoppedInsertion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Numerical instantiation of the HLOZ screening estimates

This file connects the finite screening APIs to the explicit negative-binomial
estimates.  In particular it fixes rational parameters satisfying HLOZ (7.1),
proves the relevant power-scale comparisons, turns the logarithmic local CLT
into pointwise upper and lower mass estimates, and feeds those estimates into
the adjacent-shell and small-window screens.

Nothing here postulates a planar-random-walk estimate.  The only hypotheses
left in the final shell theorem are the stopped-time conditional urn
domination, the balancedness exceptional-event estimate, and the first-shell
estimate.  Those are precisely the walk-specific inputs not supplied by the
finite negative-binomial calculation.
-/

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory unitInterval

namespace Erdos1165.ScreeningInstantiation

open Balancedness GeometricChernoff NearFavoriteShells NegativeBinomial
  NegativeBinomialLocalCLT PathInsertion SmallWindow

/-! ## Concrete external-thick candidate shells

The shell recurrence below is useful only after the abstract occupancy has
been tied to an actual finite family of sites.  We use the oriented external
range at a deterministic cutoff, retain only sites above an external local
time threshold, remove a (possibly path-dependent) finite distinguished set,
and label the survivors by their total-local-time deficit.  This is the
finite candidate family used in the HLOZ screening argument. -/

/-- External-thick sites outside the distinguished set.  The distinguished
set may depend on the path (at the level clock it contains the favorite
dominoes), but the candidate family is always a subset of the oriented
external thick points at the deterministic cutoff. -/
noncomputable def externalThickCandidates
    (o : LazyDecomposition.Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point) (s : WalkPath) : Finset Point :=
  (ExternalThickCount.orientedExternalVisitedSites o s n).filter fun x ↦
    externalThreshold ≤
        ExternalThickCount.orientedExternalLocalTime o s n x ∧
      x ∉ distinguished s

/-- Shell label associated with a (possibly stopped) total-local-time
profile.  Width zero is harmless at the definition level; the screening
theorems use a positive width. -/
def deficitShellLabel (totalLocalTime : WalkPath → Point → ℕ)
    (m width : ℕ) (s : WalkPath) (x : Point) : ℕ :=
  (m - totalLocalTime s x) / width

/-- Actual shell occupancy of the external-thick candidate family. -/
noncomputable def externalShellOccupancy
    (o : LazyDecomposition.Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ) (m width : ℕ)
    (s : WalkPath) (j : ℕ) : ℕ :=
  shellOccupancy (externalThickCandidates o n externalThreshold distinguished s)
    (deficitShellLabel totalLocalTime m width s) j

/-- Geometrically propagated shell budget. -/
def geometricShellThreshold (J G j : ℕ) : ℕ := J * G ^ j

@[simp] lemma geometricShellThreshold_zero (J G : ℕ) :
    geometricShellThreshold J G 0 = J := by
  simp [geometricShellThreshold]

lemma geometricShellThreshold_step (J G j : ℕ) :
    G * geometricShellThreshold J G j =
      geometricShellThreshold J G (j + 1) := by
  simp only [geometricShellThreshold, pow_succ]
  ac_rfl

lemma externalThickCandidates_card_le
    (o : LazyDecomposition.Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point) (s : WalkPath) :
    (externalThickCandidates o n externalThreshold distinguished s).card ≤
      ExternalThickCount.orientedExternalThickCount o s n externalThreshold := by
  classical
  unfold externalThickCandidates ExternalThickCount.orientedExternalThickCount
    ExternalThickCount.candidateCount ExternalThickCount.orientedLargeEvent
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1⟩

lemma externalShellOccupancy_le_thickCount
    (o : LazyDecomposition.Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ) (m width : ℕ)
    (s : WalkPath) (j : ℕ) :
    externalShellOccupancy o n externalThreshold distinguished totalLocalTime
        m width s j ≤
      ExternalThickCount.orientedExternalThickCount o s n externalThreshold := by
  classical
  calc
    externalShellOccupancy o n externalThreshold distinguished totalLocalTime
        m width s j ≤
        (externalThickCandidates o n externalThreshold distinguished s).card := by
      unfold externalShellOccupancy shellOccupancy shellCandidates Screening.shell
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ ExternalThickCount.orientedExternalThickCount o s n externalThreshold :=
      externalThickCandidates_card_le o n externalThreshold distinguished s

/-- The first-shell overflow is contained in the external thick-point count
event, without a probabilistic assumption. -/
theorem externalShellOverflow_zero_subset_thickCount
    (o : LazyDecomposition.Orientation) (n externalThreshold J G : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ) (m width : ℕ) :
    shellOverflow
        (externalShellOccupancy o n externalThreshold distinguished totalLocalTime
          m width)
        (geometricShellThreshold J G) 0 ⊆
      {s | J < ExternalThickCount.orientedExternalThickCount o s n
        externalThreshold} := by
  intro s hs
  change geometricShellThreshold J G 0 <
    externalShellOccupancy o n externalThreshold distinguished totalLocalTime
      m width s 0 at hs
  change J < ExternalThickCount.orientedExternalThickCount o s n externalThreshold
  have hfirst : J < externalShellOccupancy o n externalThreshold distinguished
      totalLocalTime m width s 0 := by
    simpa using hs
  exact hfirst.trans_le
      (externalShellOccupancy_le_thickCount o n externalThreshold distinguished
        totalLocalTime m width s 0)

/-- `ExternalThickCount` supplies the complete first-shell estimate.  Its
only probabilistic premise is the weighted one-point external-local-time
bound. -/
theorem simpleRandomWalk_externalShellOverflow_zero_le
    (o : LazyDecomposition.Orientation) (n externalThreshold J G : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ) (m width : ℕ)
    (q : ℝ≥0∞) (hJ : 0 < J)
    (hweightedOneSite : ∀ x,
      simpleRandomWalk
          (ExternalThickCount.candidateEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n)
            (ExternalThickCount.orientedLargeEvent o n externalThreshold) x) ≤
        q * simpleRandomWalk
          (ExternalThickCount.memberEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n) x)) :
    simpleRandomWalk
        (shellOverflow
          (externalShellOccupancy o n externalThreshold distinguished totalLocalTime
            m width)
          (geometricShellThreshold J G) 0) ≤
      q * (↑(n + 1) : ℝ≥0∞) / J := by
  exact (measure_mono (externalShellOverflow_zero_subset_thickCount o n
    externalThreshold J G distinguished totalLocalTime m width)).trans
      (ExternalThickCount.measure_orientedExternalThickCount_gt_le
        o n externalThreshold J q hJ hweightedOneSite)

/-- Real-valued form used directly as `hbase` by the adjacent-shell theorem. -/
theorem simpleRandomWalk_real_externalShellOverflow_zero_le
    (o : LazyDecomposition.Orientation) (n externalThreshold J G : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ) (m width : ℕ)
    (q : ℝ≥0∞) (hJ : 0 < J) (hq : q ≠ ∞)
    (hweightedOneSite : ∀ x,
      simpleRandomWalk
          (ExternalThickCount.candidateEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n)
            (ExternalThickCount.orientedLargeEvent o n externalThreshold) x) ≤
        q * simpleRandomWalk
          (ExternalThickCount.memberEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n) x)) :
    simpleRandomWalk.real
        (shellOverflow
          (externalShellOccupancy o n externalThreshold distinguished totalLocalTime
            m width)
          (geometricShellThreshold J G) 0) ≤
      (q * (↑(n + 1) : ℝ≥0∞) / J).toReal := by
  have hmul : q * (↑(n + 1) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top hq (by simp)
  have hJ0 : (J : ℝ≥0∞) ≠ 0 := by simp [hJ.ne']
  apply (ENNReal.toReal_le_toReal (by finiteness)
    (ENNReal.div_ne_top hmul hJ0)).2
  exact simpleRandomWalk_externalShellOverflow_zero_le o n externalThreshold J G
    distinguished totalLocalTime m width q hJ hweightedOneSite

/-! ## A concrete admissible choice of HLOZ exponents -/

/-- The broad-window exponent.  It lies strictly between `1/3` and `7/20`. -/
noncomputable def kappaOne : ℝ := 11 / 32

/-- The spatial-screening exponent. -/
noncomputable def kappaTwo : ℝ := 43 / 128

/-- A concrete mesh size. -/
noncomputable def meshDelta : ℝ := 1 / 1024

/-- The summability exponent occurring at the end of the three gap screens. -/
noncomputable def kappa : ℝ := kappaTwo - 2 * meshDelta

/-- A convenient upper endpoint for the broad-window argument.  It corresponds
to taking `epsilon = 1/20` in HLOZ Proposition 4.8. -/
noncomputable def alphaMax : ℝ := 3 / 4

theorem hloz_parameter_inequalities :
    1 / 3 < kappaOne ∧ kappaOne < 7 / 20 ∧
      1 / 3 < kappaTwo ∧ kappaTwo < kappaOne ∧
      kappaTwo + 2 * meshDelta < kappaOne ∧
      1 / 3 + 4 * meshDelta < kappaTwo + 2 * meshDelta ∧
      1 / 3 < kappa ∧ 1 < 3 * kappa ∧
      kappaOne ≤ alphaMax ∧ alphaMax < 4 / 5 := by
  norm_num [kappaOne, kappaTwo, meshDelta, kappa, alphaMax]

/-- The scale `m^(1-2*kappaOne)` in the balancedness cost. -/
noncomputable def balanceRateScale (m : ℕ) : ℝ :=
  (m : ℝ) ^ (1 - 2 * kappaOne)

/-- A symmetric deviation scale for the geometric-sum Chernoff bound.  The
coefficient `9` leaves more than the required factor `17` in the exponent. -/
noncomputable def geometricDeviation (m : ℕ) : ℝ :=
  9 * (m : ℝ) ^ (1 - kappaOne)

lemma balanceRateScale_nonneg (m : ℕ) : 0 ≤ balanceRateScale m := by
  exact Real.rpow_nonneg (Nat.cast_nonneg m) _

lemma geometricDeviation_nonneg (m : ℕ) : 0 ≤ geometricDeviation m := by
  exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg m) _)

lemma tendsto_nat_rpow_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun m : ℕ ↦ (m : ℝ) ^ a) atTop atTop :=
  (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop

/-- Explicit eventual bound ensuring that the chosen moderate deviation is
at most half of any external count bounded below by `m/2`. -/
theorem eventually_geometricDeviation_le_half :
    ∀ᶠ m : ℕ in atTop, geometricDeviation m ≤ (m : ℝ) / 2 := by
  have hpow := tendsto_nat_rpow_atTop (a := kappaOne)
    (by norm_num [kappaOne])
  filter_upwards [hpow.eventually (eventually_ge_atTop (18 : ℝ)),
      eventually_ge_atTop 1] with m hmPow hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfactor :
      (m : ℝ) = (m : ℝ) ^ (1 - kappaOne) * (m : ℝ) ^ kappaOne := by
    calc
      (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ = (m : ℝ) ^ ((1 - kappaOne) + kappaOne) := by congr 1; ring
      _ = (m : ℝ) ^ (1 - kappaOne) * (m : ℝ) ^ kappaOne :=
        Real.rpow_add hmR _ _
  have hnonneg : 0 ≤ (m : ℝ) ^ (1 - kappaOne) :=
    Real.rpow_nonneg hmR.le _
  unfold geometricDeviation
  nlinarith [hfactor]

/-- The broadest local-CLT window used below is eventually contained in the
finite moderate window `|deviation| ≤ i/30` whenever `i ≥ m/2`. -/
theorem eventually_broadWindow_le_thirtieth :
    ∀ᶠ m : ℕ in atTop,
      2 * (m : ℝ) ^ alphaMax ≤ (m : ℝ) / 60 := by
  have hpow := tendsto_nat_rpow_atTop (a := 1 - alphaMax)
    (by norm_num [alphaMax])
  filter_upwards [hpow.eventually (eventually_ge_atTop (120 : ℝ)),
      eventually_ge_atTop 1] with m hmPow hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfactor :
      (m : ℝ) = (m : ℝ) ^ alphaMax * (m : ℝ) ^ (1 - alphaMax) := by
    calc
      (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ = (m : ℝ) ^ (alphaMax + (1 - alphaMax)) := by congr 1; ring
      _ = (m : ℝ) ^ alphaMax * (m : ℝ) ^ (1 - alphaMax) :=
        Real.rpow_add hmR _ _
  have hnonneg : 0 ≤ (m : ℝ) ^ alphaMax := Real.rpow_nonneg hmR.le _
  nlinarith [hfactor]

lemma geometricDeviation_sq_div_four {m : ℕ} (hm : 0 < m) :
    geometricDeviation m ^ 2 / (4 * (m : ℝ)) =
      (81 / 4 : ℝ) * balanceRateScale m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpow :
      ((m : ℝ) ^ (1 - kappaOne)) ^ 2 =
        (m : ℝ) ^ (1 - 2 * kappaOne) * (m : ℝ) := by
    calc
      ((m : ℝ) ^ (1 - kappaOne)) ^ 2 =
          ((m : ℝ) ^ (1 - kappaOne)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = (m : ℝ) ^ ((1 - kappaOne) * (2 : ℝ)) :=
        (Real.rpow_mul hmR.le _ _).symm
      _ = (m : ℝ) ^ ((1 - 2 * kappaOne) + 1) := by congr 1; ring
      _ = (m : ℝ) ^ (1 - 2 * kappaOne) * (m : ℝ) := by
        rw [Real.rpow_add hmR, Real.rpow_one]
  unfold geometricDeviation balanceRateScale
  rw [mul_pow, hpow]
  field_simp
  ring

lemma seventeen_balanceRateScale_le_geometric_rate {m : ℕ} (hm : 0 < m) :
    17 * balanceRateScale m ≤
      geometricDeviation m ^ 2 / (4 * (m : ℝ)) := by
  rw [geometricDeviation_sq_div_four hm]
  exact mul_le_mul_of_nonneg_right (by norm_num)
    (balanceRateScale_nonneg m)

/-! ## Explicit two-sided geometric Chernoff instantiation -/

theorem geometricSum_upper_tail_le_balanceCost
    {m i : ℕ} (hm : 0 < m) (hi : 0 < i) (him : i ≤ m)
    (hdeviation : geometricDeviation m ≤ i) :
    (geometric15Vector i).real
        {g | (i : ℝ) / 15 + geometricDeviation m ≤ geometricSum g} ≤
      Real.exp (-17 * balanceRateScale m) := by
  refine (geometricSum_upper_tail i hi (geometricDeviation_nonneg m)
    hdeviation).trans ?_
  apply Real.exp_le_exp.mpr
  rw [show -geometricDeviation m ^ 2 / (4 * (i : ℝ)) =
      -(geometricDeviation m ^ 2 / (4 * (i : ℝ))) by ring,
    show -17 * balanceRateScale m = -(17 * balanceRateScale m) by ring]
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have himR : (i : ℝ) ≤ m := by exact_mod_cast him
  apply neg_le_neg
  refine (seventeen_balanceRateScale_le_geometric_rate hm).trans ?_
  have hsquare : 0 ≤ geometricDeviation m ^ 2 := sq_nonneg _
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ))
      (by positivity : (0 : ℝ) < 4 * (i : ℝ))]
  nlinarith

theorem geometricSum_lower_tail_le_balanceCost
    {m i : ℕ} (hm : 0 < m) (hi : 0 < i) (him : i ≤ m)
    (hdeviation : geometricDeviation m ≤ i) :
    (geometric15Vector i).real
        {g | geometricSum g ≤ (i : ℝ) / 15 - geometricDeviation m} ≤
      Real.exp (-17 * balanceRateScale m) := by
  refine (geometricSum_lower_tail i hi (geometricDeviation_nonneg m)
    hdeviation).trans ?_
  apply Real.exp_le_exp.mpr
  rw [show -geometricDeviation m ^ 2 / (4 * (i : ℝ)) =
      -(geometricDeviation m ^ 2 / (4 * (i : ℝ))) by ring,
    show -17 * balanceRateScale m = -(17 * balanceRateScale m) by ring]
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have himR : (i : ℝ) ≤ m := by exact_mod_cast him
  apply neg_le_neg
  refine (seventeen_balanceRateScale_le_geometric_rate hm).trans ?_
  have hsquare : 0 ≤ geometricDeviation m ^ 2 := sq_nonneg _
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ))
      (by positivity : (0 : ℝ) < 4 * (i : ℝ))]
  nlinarith

/-- The same numerical scale applied directly to the upper tail of the exact
negative-binomial mass.  This is the form consumed by `Balancedness` when the
conditional law has first been expressed as a tail sum. -/
theorem upperTailMass_le_balanceCost
    {m i k : ℕ} (hm : 0 < m) (hi : 0 < i) (him : i ≤ m)
    (habove : i < 15 * k) (hbelow : 15 * k ≤ 2 * i)
    (hgap : 15 * geometricDeviation m ≤ 15 * (k : ℝ) - (i : ℝ)) :
    ModerateDeviation.upperTailMass i k ≤
      Real.exp (-17 * balanceRateScale m) := by
  refine (ModerateDeviation.upperTailMass_le_exp_neg_sq_deviation
    hi habove hbelow).trans ?_
  apply Real.exp_le_exp.mpr
  rw [show -((15 * (k : ℝ) - (i : ℝ)) ^ 2 /
      (60 * (i : ℝ))) =
      -((15 * (k : ℝ) - (i : ℝ)) ^ 2 / (60 * (i : ℝ))) by ring,
    show -17 * balanceRateScale m = -(17 * balanceRateScale m) by ring]
  apply neg_le_neg
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have himR : (i : ℝ) ≤ m := by exact_mod_cast him
  have hdev0 : 0 ≤ geometricDeviation m := geometricDeviation_nonneg m
  have hgap0 : 0 ≤ 15 * (k : ℝ) - (i : ℝ) := by
    have : (i : ℝ) < 15 * (k : ℝ) := by exact_mod_cast habove
    linarith
  have hsquare : (15 * geometricDeviation m) ^ 2 ≤
      (15 * (k : ℝ) - (i : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ (mul_nonneg (by norm_num) hdev0) hgap 2
  refine (seventeen_balanceRateScale_le_geometric_rate hm).trans ?_
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ))
      (by positivity : (0 : ℝ) < 60 * (i : ℝ))]
  nlinarith [sq_nonneg (geometricDeviation m)]

/-- Finite candidate union at the exact HLOZ cost.  The two `hLaw`
hypotheses are deliberately stated as comparisons with the genuine product
geometric law: deriving them at `T_m^k` is the stopped-time insertion input. -/
theorem measure_someGeometricImbalance_le
    {Omega Site : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (sites : Finset Site)
    (lowerBad upperBad : Site → Set Omega) (budget m : ℕ)
    (successes : Site → ℕ)
    (hm : 0 < m) (hcard : sites.card ≤ budget)
    (hi : ∀ x ∈ sites, 0 < successes x)
    (him : ∀ x ∈ sites, successes x ≤ m)
    (hdeviation : ∀ x ∈ sites, geometricDeviation m ≤ successes x)
    (hlowerLaw : ∀ x ∈ sites,
      mu (lowerBad x) ≤ ENNReal.ofReal
        ((geometric15Vector (successes x)).real
          {g | geometricSum g ≤ (successes x : ℝ) / 15 - geometricDeviation m}))
    (hupperLaw : ∀ x ∈ sites,
      mu (upperBad x) ≤ ENNReal.ofReal
        ((geometric15Vector (successes x)).real
          {g | (successes x : ℝ) / 15 + geometricDeviation m ≤ geometricSum g})) :
    mu (Screening.someCandidateBad sites
        (Balancedness.twoSidedBad lowerBad upperBad)) ≤
      (budget : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
          ENNReal.ofReal (Real.exp (-17 * balanceRateScale m))) := by
  apply Balancedness.measure_someTwoSidedBad_le_budget mu sites
    lowerBad upperBad budget
    (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))
    (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m))) hcard
  · intro x hx
    exact (hlowerLaw x hx).trans (ENNReal.ofReal_le_ofReal
      (geometricSum_lower_tail_le_balanceCost hm (hi x hx) (him x hx)
        (hdeviation x hx)))
  · intro x hx
    exact (hupperLaw x hx).trans (ENNReal.ofReal_le_ofReal
      (geometricSum_upper_tail_le_balanceCost hm (hi x hx) (him x hx)
        (hdeviation x hx)))

/-! ## The logarithmic local CLT as a usable mass sandwich -/

/-- Uniform logarithmic error budget on a symmetric deviation window. -/
noncomputable def localErrorBudget (i : ℕ) (D : ℝ) : ℝ :=
  19 / Real.sqrt i + 920 * D ^ 3 / (i : ℝ) ^ 2

/-- A common positive lower reference mass for all points in the window. -/
noncomputable def localReferenceMass (i : ℕ) (D : ℝ) : ℝ :=
  Real.exp (-Real.log (2 * Real.pi * NegativeBinomialLocalCLT.variance * i) / 2 -
    D ^ 2 / (2 * NegativeBinomialLocalCLT.variance * i) - localErrorBudget i D)

/-- The pointwise mass-ratio constant furnished by the local CLT. -/
noncomputable def localRatio (i : ℕ) (D : ℝ) : ℝ :=
  Real.exp (2 * localErrorBudget i D +
    D ^ 2 / (2 * NegativeBinomialLocalCLT.variance * i))

/-- Sharper ratio for two points in adjacent windows: `D` bounds their
distance from the Gaussian center and `W` bounds their mutual separation. -/
noncomputable def adjacentLocalRatio (i : ℕ) (D W : ℝ) : ℝ :=
  Real.exp (2 * localErrorBudget i D +
    (2 * D * W) / (2 * NegativeBinomialLocalCLT.variance * i))

lemma localReferenceMass_pos (i : ℕ) (D : ℝ) :
    0 < localReferenceMass i D := by
  exact Real.exp_pos _

lemma localRatio_nonneg (i : ℕ) (D : ℝ) : 0 ≤ localRatio i D := by
  exact (Real.exp_pos _).le

lemma adjacentLocalRatio_nonneg (i : ℕ) (D W : ℝ) :
    0 ≤ adjacentLocalRatio i D W := by
  exact (Real.exp_pos _).le

lemma abs_logLocalError_le_budget {i k : ℕ} (hi : 0 < i) {D : ℝ}
    (_hD : 0 ≤ D) (hdev : |deviation i k| ≤ D)
    (hmoderate : D ≤ (i : ℝ) / 30) :
    |logLocalError i k| ≤ localErrorBudget i D := by
  refine (abs_logLocalError_le hi (hdev.trans hmoderate)).trans ?_
  unfold localErrorBudget
  have hcubic : |deviation i k| ^ 3 ≤ D ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hdev 3
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  gcongr

theorem localReferenceMass_le_hlozMass {i k : ℕ} (hi : 0 < i) {D : ℝ}
    (hD : 0 ≤ D) (hdev : |deviation i k| ≤ D)
    (hmoderate : D ≤ (i : ℝ) / 30) :
    localReferenceMass i D ≤ hlozMass i k := by
  have herr := abs_logLocalError_le_budget hi hD hdev hmoderate
  have hmass : 0 < hlozMass i k := hlozMass_pos hi k
  unfold localReferenceMass
  rw [← Real.le_log_iff_exp_le hmass]
  unfold logLocalError at herr
  have hdevsq : deviation i k ^ 2 ≤ D ^ 2 := by
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hdev 2
    simpa only [sq_abs] using hsq
  have hden : 0 < 2 * NegativeBinomialLocalCLT.variance * (i : ℝ) := by
    norm_num [NegativeBinomialLocalCLT.variance]
    exact_mod_cast hi
  have hdevdiv := div_le_div_of_nonneg_right hdevsq hden.le
  have hlower := neg_le_of_abs_le herr
  nlinarith

theorem hlozMass_le_localRatio_mul_reference {i k : ℕ} (hi : 0 < i) {D : ℝ}
    (hD : 0 ≤ D) (hdev : |deviation i k| ≤ D)
    (hmoderate : D ≤ (i : ℝ) / 30) :
    hlozMass i k ≤ localRatio i D * localReferenceMass i D := by
  have herr := abs_logLocalError_le_budget hi hD hdev hmoderate
  have hmass : 0 < hlozMass i k := hlozMass_pos hi k
  have href : 0 < localRatio i D * localReferenceMass i D :=
    mul_pos (Real.exp_pos _) (localReferenceMass_pos i D)
  apply (Real.log_le_log_iff hmass href).mp
  unfold localRatio localReferenceMass
  rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp]
  unfold logLocalError at herr
  have hupper := le_of_abs_le herr
  have hquad : 0 ≤ deviation i k ^ 2 /
      (2 * NegativeBinomialLocalCLT.variance * (i : ℝ)) := by
    apply div_nonneg (sq_nonneg _)
    have hiR : (0 : ℝ) < i := by exact_mod_cast hi
    norm_num [NegativeBinomialLocalCLT.variance]
  nlinarith

/-- Pointwise adjacent-window mass comparison.  Unlike the coarser common
reference bound, its Gaussian cost is `O(D*W/i)`, the scale used in the
iterated HLOZ shell screen. -/
theorem hlozMass_le_adjacentLocalRatio_mul {i k l : ℕ} (hi : 0 < i)
    {D W : ℝ} (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hkDev : |deviation i k| ≤ D) (hlDev : |deviation i l| ≤ D)
    (hkl : |deviation i k - deviation i l| ≤ W)
    (hmoderate : D ≤ (i : ℝ) / 30) :
    hlozMass i k ≤ adjacentLocalRatio i D W * hlozMass i l := by
  have hkerr := abs_logLocalError_le_budget hi hD hkDev hmoderate
  have hlerr := abs_logLocalError_le_budget hi hD hlDev hmoderate
  have hsum : |deviation i l + deviation i k| ≤ 2 * D := by
    calc
      |deviation i l + deviation i k| ≤
          |deviation i l| + |deviation i k| := abs_add_le _ _
      _ ≤ D + D := add_le_add hlDev hkDev
      _ = 2 * D := by ring
  have hdiff : |deviation i l - deviation i k| ≤ W := by
    simpa only [abs_sub_comm] using hkl
  have habsSquare :
      |deviation i l ^ 2 - deviation i k ^ 2| ≤ 2 * D * W := by
    rw [show deviation i l ^ 2 - deviation i k ^ 2 =
        (deviation i l - deviation i k) *
          (deviation i l + deviation i k) by ring, abs_mul]
    calc
      |deviation i l - deviation i k| *
          |deviation i l + deviation i k| ≤ W * (2 * D) :=
        mul_le_mul hdiff hsum (abs_nonneg _) hW
      _ = 2 * D * W := by ring
  have hsquare : deviation i l ^ 2 - deviation i k ^ 2 ≤ 2 * D * W :=
    (le_abs_self _).trans habsSquare
  have hden : 0 < 2 * NegativeBinomialLocalCLT.variance * (i : ℝ) := by
    have hiR : (0 : ℝ) < i := by exact_mod_cast hi
    norm_num [NegativeBinomialLocalCLT.variance]
    exact hi
  have hsquareDiv := div_le_div_of_nonneg_right hsquare hden.le
  have hdivIdentity :
      deviation i l ^ 2 /
          (2 * NegativeBinomialLocalCLT.variance * (i : ℝ)) -
        deviation i k ^ 2 /
          (2 * NegativeBinomialLocalCLT.variance * (i : ℝ)) =
        (deviation i l ^ 2 - deviation i k ^ 2) /
          (2 * NegativeBinomialLocalCLT.variance * (i : ℝ)) := by
    ring
  have hkUpper := le_of_abs_le hkerr
  have hlLower := neg_le_of_abs_le hlerr
  have hlog :
      Real.log (hlozMass i k) ≤
        2 * localErrorBudget i D +
          (2 * D * W) /
            (2 * NegativeBinomialLocalCLT.variance * (i : ℝ)) +
          Real.log (hlozMass i l) := by
    unfold logLocalError at hkUpper hlLower
    nlinarith [hsquareDiv]
  have hkPos : 0 < hlozMass i k := hlozMass_pos hi k
  have hlPos : 0 < hlozMass i l := hlozMass_pos hi l
  have hprod : 0 < adjacentLocalRatio i D W * hlozMass i l :=
    mul_pos (Real.exp_pos _) hlPos
  apply (Real.log_le_log_iff hkPos hprod).mp
  unfold adjacentLocalRatio
  rw [Real.log_mul (Real.exp_ne_zero _) hlPos.ne', Real.log_exp]
  linarith

/-! ## Adjacent-window and small-window consequences -/

/-- Two windows of the same lattice width and lying in one local-CLT window
have mass ratio at most `localRatio`.  This is the analytic hypothesis needed
by the adjacent-urn screen. -/
theorem adjacentWindowMass_le_localRatio {i : ℕ} (hi : 0 < i)
    {upper lower : Finset ℕ} {D : ℝ}
    (hD : 0 ≤ D) (hmoderate : D ≤ (i : ℝ) / 30)
    (hlower : lower.Nonempty) (hcard : upper.card ≤ lower.card)
    (hupperDev : ∀ a ∈ upper, |deviation i a| ≤ D)
    (hlowerDev : ∀ a ∈ lower, |deviation i a| ≤ D) :
    windowMass i upper ≤ localRatio i D * windowMass i lower := by
  let b := localReferenceMass i D
  have hb : 0 < b := localReferenceMass_pos i D
  have hraw := windowMass_small_le_ratio_mul_large
    (i := i) (small := upper) (large := lower)
    (b := b) (C := localRatio i D)
    (g := (upper.card : ℝ)) (f := (lower.card : ℝ))
    hb (localRatio_nonneg i D) (Nat.cast_nonneg _) (by
      exact_mod_cast hlower.card_pos)
    le_rfl le_rfl
    (fun a ha ↦ hlozMass_le_localRatio_mul_reference hi hD
      (hupperDev a ha) hmoderate)
    (fun a ha ↦ localReferenceMass_le_hlozMass hi hD
      (hlowerDev a ha) hmoderate)
  have hlowerMass : 0 ≤ windowMass i lower := windowMass_nonneg i lower
  calc
    windowMass i upper ≤
        (localRatio i D * (upper.card : ℝ) / (lower.card : ℝ)) *
          windowMass i lower := hraw
    _ ≤ localRatio i D * windowMass i lower := by
      have hcardR : (upper.card : ℝ) ≤ lower.card := by exact_mod_cast hcard
      have hlowerCard : (0 : ℝ) < lower.card := by exact_mod_cast hlower.card_pos
      have hratio : (upper.card : ℝ) / lower.card ≤ 1 :=
        (div_le_one hlowerCard).2 hcardR
      calc
        (localRatio i D * (upper.card : ℝ) / (lower.card : ℝ)) *
            windowMass i lower =
          (localRatio i D * ((upper.card : ℝ) / lower.card)) *
            windowMass i lower := by ring
        _ ≤ (localRatio i D * 1) * windowMass i lower := by
          gcongr
          exact localRatio_nonneg i D
        _ = localRatio i D * windowMass i lower := by ring

/-- Adjacent-window version using the sharper `D*W/i` pointwise comparison.
The windows need only have comparable cardinalities; no unproved mass-ratio
hypothesis remains. -/
theorem adjacentWindowMass_le_adjacentLocalRatio {i : ℕ} (hi : 0 < i)
    {upper lower : Finset ℕ} {D W : ℝ}
    (hD : 0 ≤ D) (hW : 0 ≤ W) (hmoderate : D ≤ (i : ℝ) / 30)
    (hlower : lower.Nonempty) (hcard : upper.card ≤ lower.card)
    (hupperDev : ∀ a ∈ upper, |deviation i a| ≤ D)
    (hlowerDev : ∀ a ∈ lower, |deviation i a| ≤ D)
    (hpair : ∀ a ∈ upper, ∀ b ∈ lower,
      |deviation i a - deviation i b| ≤ W) :
    windowMass i upper ≤
      adjacentLocalRatio i D W * windowMass i lower := by
  obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image lower (hlozMass i) hlower
  have hbPos : 0 < hlozMass i b := hlozMass_pos hi b
  have hraw := windowMass_small_le_ratio_mul_large
    (i := i) (small := upper) (large := lower)
    (b := hlozMass i b) (C := adjacentLocalRatio i D W)
    (g := (upper.card : ℝ)) (f := (lower.card : ℝ))
    hbPos (adjacentLocalRatio_nonneg i D W) (Nat.cast_nonneg _) (by
      exact_mod_cast hlower.card_pos)
    le_rfl le_rfl
    (fun a ha ↦ hlozMass_le_adjacentLocalRatio_mul hi hD hW
      (hupperDev a ha) (hlowerDev b hb) (hpair a ha b hb) hmoderate)
    (fun a ha ↦ hbmin a ha)
  have hlowerMass : 0 ≤ windowMass i lower := windowMass_nonneg i lower
  calc
    windowMass i upper ≤
        (adjacentLocalRatio i D W * (upper.card : ℝ) /
          (lower.card : ℝ)) * windowMass i lower := hraw
    _ ≤ adjacentLocalRatio i D W * windowMass i lower := by
      have hcardR : (upper.card : ℝ) ≤ lower.card := by exact_mod_cast hcard
      have hlowerCard : (0 : ℝ) < lower.card := by exact_mod_cast hlower.card_pos
      have hratio : (upper.card : ℝ) / lower.card ≤ 1 :=
        (div_le_one hlowerCard).2 hcardR
      calc
        (adjacentLocalRatio i D W * (upper.card : ℝ) /
            (lower.card : ℝ)) * windowMass i lower =
          (adjacentLocalRatio i D W *
            ((upper.card : ℝ) / lower.card)) * windowMass i lower := by ring
        _ ≤ (adjacentLocalRatio i D W * 1) * windowMass i lower := by
          gcongr
          exact adjacentLocalRatio_nonneg i D W
        _ = adjacentLocalRatio i D W * windowMass i lower := by ring

/-- The HLOZ Proposition 4.9 finite conclusion with all local-mass hypotheses
discharged by the checked local CLT.  Only the conditional-binomial model is
encoded in the `Bin` expression; its identification with the stopped walk is
not claimed here. -/
theorem smallWindow_one_or_more_of_localCLT
    {i n J : ℕ} (hi : 0 < i) {small large : Finset ℕ} {D g f : ℝ}
    (hnJ : n ≤ J) (hD : 0 ≤ D) (hg : 0 ≤ g) (hf : 0 < f)
    (hmoderate : D ≤ (i : ℝ) / 30)
    (hsmallCard : (small.card : ℝ) ≤ g)
    (hlargeCard : f ≤ (large.card : ℝ))
    (hsmallDev : ∀ a ∈ small, |deviation i a| ≤ D)
    (hlargeDev : ∀ a ∈ large, |deviation i a| ≤ D) :
    let hlargePos : 0 < windowMass i large := by
      apply windowMass_pos hi
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      subst large
      simp at hlargeCard
      linarith
    Bin(n, smallWindowParameter i small large hlargePos).real (Set.Ici 1) ≤
      localRatio i D * g * J / f := by
  dsimp only
  exact smallWindow_one_or_more_le hi hnJ
    (localReferenceMass_pos i D) (localRatio_nonneg i D) hg hf
    hsmallCard hlargeCard
    (fun a ha ↦ hlozMass_le_localRatio_mul_reference hi hD
      (hsmallDev a ha) hmoderate)
    (fun a ha ↦ localReferenceMass_le_hlozMass hi hD
      (hlargeDev a ha) hmoderate)

/-! ## Canonical adjacent integer windows

For an external count `i`, the failure-count mean is `i / 15`.  The two
windows below are consecutive half-open intervals of the same positive
integer width.  Their cardinals, nonemptiness, local-CLT deviation bounds,
and mutual separation are all deterministic. -/

/-- The lower of two consecutive failure-count windows, beginning at the
integer part of the negative-binomial mean. -/
def lowerFailureWindow (i width : ℕ) : Finset ℕ :=
  Finset.Ico (i / 15) (i / 15 + width)

/-- The adjacent upper failure-count window. -/
def upperFailureWindow (i width : ℕ) : Finset ℕ :=
  Finset.Ico (i / 15 + width) (i / 15 + 2 * width)

/-- A uniform deviation radius for both adjacent windows. -/
noncomputable def adjacentWindowRadius (width : ℕ) : ℝ :=
  2 * (width : ℝ) + 1

/-- A uniform bound on the difference of deviations across the two windows. -/
noncomputable def adjacentWindowSeparation (width : ℕ) : ℝ :=
  2 * (width : ℝ)

/-- A canonical positive window width once the external count has reached
`120`.  The factor `120` leaves ample room inside the local-CLT window. -/
def canonicalWindowWidth (i : ℕ) : ℕ := i / 120

lemma canonicalWindowWidth_numeric {i : ℕ} (hi : 120 ≤ i) :
    0 < i ∧ 0 < canonicalWindowWidth i ∧
      60 * canonicalWindowWidth i + 30 ≤ i := by
  unfold canonicalWindowWidth
  omega

lemma lowerFailureWindow_nonempty {i width : ℕ} (hwidth : 0 < width) :
    (lowerFailureWindow i width).Nonempty := by
  rw [lowerFailureWindow, Finset.nonempty_Ico]
  omega

@[simp] lemma lowerFailureWindow_card (i width : ℕ) :
    (lowerFailureWindow i width).card = width := by
  simp [lowerFailureWindow, Nat.card_Ico]

@[simp] lemma upperFailureWindow_card (i width : ℕ) :
    (upperFailureWindow i width).card = width := by
  rw [upperFailureWindow, Nat.card_Ico]
  omega

lemma abs_deviation_natDiv_le_one (i : ℕ) :
    |deviation i (i / 15)| ≤ 1 := by
  have hlo : 15 * (i / 15) ≤ i := by omega
  have hhi : i < 15 * (i / 15 + 1) := by omega
  have hloR : (15 : ℝ) * (i / 15 : ℕ) ≤ (i : ℝ) := by
    exact_mod_cast hlo
  have hhiR : (i : ℝ) < (15 : ℝ) * ((i / 15 : ℕ) + 1) := by
    exact_mod_cast hhi
  rw [abs_le]
  constructor <;> unfold deviation <;> push_cast at * <;> linarith

private lemma abs_deviation_le_radius_of_mem_span
    {i width k : ℕ} (hlower : i / 15 ≤ k)
    (hupper : k ≤ i / 15 + 2 * width) :
    |deviation i k| ≤ adjacentWindowRadius width := by
  have hcenter := abs_deviation_natDiv_le_one i
  have hlowerR : ((i / 15 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlower
  have hupperR : (k : ℝ) ≤
      ((i / 15 : ℕ) : ℝ) + 2 * (width : ℝ) := by
    exact_mod_cast hupper
  have hrewrite : deviation i k =
      deviation i (i / 15) + ((k : ℝ) - (i / 15 : ℕ)) := by
    unfold deviation
    push_cast
    ring
  rw [hrewrite]
  calc
    |deviation i (i / 15) + ((k : ℝ) - (i / 15 : ℕ))| ≤
        |deviation i (i / 15)| + |(k : ℝ) - (i / 15 : ℕ)| :=
      abs_add_le _ _
    _ ≤ 1 + 2 * (width : ℝ) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hlowerR)]
      linarith
    _ = adjacentWindowRadius width := by
      unfold adjacentWindowRadius
      ring

lemma lowerFailureWindow_deviation_le {i width k : ℕ}
    (hk : k ∈ lowerFailureWindow i width) :
    |deviation i k| ≤ adjacentWindowRadius width := by
  rw [lowerFailureWindow, Finset.mem_Ico] at hk
  apply abs_deviation_le_radius_of_mem_span hk.1
  omega

lemma upperFailureWindow_deviation_le {i width k : ℕ}
    (hk : k ∈ upperFailureWindow i width) :
    |deviation i k| ≤ adjacentWindowRadius width := by
  rw [upperFailureWindow, Finset.mem_Ico] at hk
  apply abs_deviation_le_radius_of_mem_span (by omega)
  omega

lemma adjacentFailureWindow_deviation_sub_le
    {i width a b : ℕ} (ha : a ∈ upperFailureWindow i width)
    (hb : b ∈ lowerFailureWindow i width) :
    |deviation i a - deviation i b| ≤ adjacentWindowSeparation width := by
  rw [upperFailureWindow, Finset.mem_Ico] at ha
  rw [lowerFailureWindow, Finset.mem_Ico] at hb
  have haLowerR : ((i / 15 : ℕ) : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast (show i / 15 ≤ a by omega)
  have haUpperR : (a : ℝ) ≤
      ((i / 15 : ℕ) : ℝ) + 2 * (width : ℝ) := by
    exact_mod_cast (show a ≤ i / 15 + 2 * width by omega)
  have hbLowerR : ((i / 15 : ℕ) : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hb.1
  have hbUpperR : (b : ℝ) ≤
      ((i / 15 : ℕ) : ℝ) + 2 * (width : ℝ) := by
    exact_mod_cast (show b ≤ i / 15 + 2 * width by omega)
  rw [abs_le]
  unfold deviation adjacentWindowSeparation
  push_cast
  constructor <;> linarith

lemma adjacentWindowRadius_nonneg (width : ℕ) :
    0 ≤ adjacentWindowRadius width := by
  unfold adjacentWindowRadius
  positivity

lemma adjacentWindowSeparation_nonneg (width : ℕ) :
    0 ≤ adjacentWindowSeparation width := by
  unfold adjacentWindowSeparation
  positivity

/-- A single integer inequality puts both concrete windows inside the
`i / 30` moderate-deviation range used by the checked local CLT. -/
lemma adjacentWindowRadius_le_thirtieth {i width : ℕ}
    (hscale : 60 * width + 30 ≤ i) :
    adjacentWindowRadius width ≤ (i : ℝ) / 30 := by
  have hscaleR : (60 : ℝ) * (width : ℝ) + 30 ≤ (i : ℝ) := by
    exact_mod_cast hscale
  unfold adjacentWindowRadius
  linarith

/-! ## Full adjacent-shell propagation with analytic hypotheses discharged -/

/-- HLOZ Proposition 4.8's finite propagation step after the local CLT has
been instantiated at every interface.  Positivity and the adjacent mass-ratio
hypotheses of `NearFavoriteShells.measureReal_totalOverflow_le_of_pair_domination`
are all proved here.  The remaining hypothesis `hdom` is exactly the
walk-specific conditional urn domination at the stopped time. -/
theorem measureReal_totalOverflow_le_of_localCLT
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (pairTotal successes : ℕ → ℕ)
    (upperWindow lowerWindow : ℕ → Finset ℕ) (D W : ℕ → ℝ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    (hi : ∀ j < shellCount - 1, 0 < successes j)
    (hD : ∀ j < shellCount - 1, 0 ≤ D j)
    (hW : ∀ j < shellCount - 1, 0 ≤ W j)
    (hmoderate : ∀ j < shellCount - 1,
      D j ≤ (successes j : ℝ) / 30)
    (hlower : ∀ j < shellCount - 1, (lowerWindow j).Nonempty)
    (hcard : ∀ j < shellCount - 1,
      (upperWindow j).card ≤ (lowerWindow j).card)
    (hupperDev : ∀ j < shellCount - 1, ∀ a ∈ upperWindow j,
      |deviation (successes j) a| ≤ D j)
    (hlowerDev : ∀ j < shellCount - 1, ∀ a ∈ lowerWindow j,
      |deviation (successes j) a| ≤ D j)
    (hpair : ∀ j < shellCount - 1, ∀ a ∈ upperWindow j,
      ∀ b ∈ lowerWindow j,
        |deviation (successes j) a - deviation (successes j) b| ≤ W j)
    {baseCost : ℝ} {balanceCost : ℕ → ℝ}
    (hbase : mu.real (shellOverflow occupancy threshold 0) ≤ baseCost)
    (hbalance : ∀ j < shellCount - 1,
      mu.real (balanced j)ᶜ ≤ balanceCost j)
    (hdom : ∀ (j : ℕ) (hj : j < shellCount - 1),
      mu.real (balancedGrowthFailure balanced occupancy G j) ≤
        Bin(pairTotal j,
          UrnScreening.pairParameter
            (windowMass (successes j) (upperWindow j))
            (windowMass (successes j) (lowerWindow j))
            (windowMass_nonneg _ _)
            (windowMass_nonneg _ _)
            (add_pos_of_nonneg_of_pos (windowMass_nonneg _ _)
              (windowMass_pos (hi j hj) (hlower j hj)))).real
          {upper | upper ≤ pairTotal j ∧
            G * (pairTotal j - upper) < upper}) :
    mu.real (totalOverflow occupancy threshold shellCount) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        (balanceCost j +
          (1 + adjacentLocalRatio (successes j) (D j) (W j) /
              (1 + adjacentLocalRatio (successes j) (D j) (W j))) ^ pairTotal j /
            (2 : ℝ) ^ growthCut G (pairTotal j)) := by
  let p : ℕ → ℝ := fun j ↦ windowMass (successes j) (upperWindow j)
  let q : ℕ → ℝ := fun j ↦ windowMass (successes j) (lowerWindow j)
  let C : ℕ → ℝ := fun j ↦ adjacentLocalRatio (successes j) (D j) (W j)
  have hp : ∀ j < shellCount - 1, 0 ≤ p j := by
    intro j hj
    exact windowMass_nonneg _ _
  have hq : ∀ j < shellCount - 1, 0 ≤ q j := by
    intro j hj
    exact windowMass_nonneg _ _
  have hpq : ∀ j < shellCount - 1, 0 < p j + q j := by
    intro j hj
    exact add_pos_of_nonneg_of_pos (windowMass_nonneg _ _)
      (windowMass_pos (hi j hj) (hlower j hj))
  have hC : ∀ j < shellCount - 1, 0 ≤ C j := by
    intro j hj
    exact adjacentLocalRatio_nonneg _ _ _
  have hratio : ∀ j < shellCount - 1, p j ≤ C j * q j := by
    intro j hj
    exact adjacentWindowMass_le_adjacentLocalRatio (hi j hj)
      (hD j hj) (hW j hj) (hmoderate j hj)
      (hlower j hj) (hcard j hj) (hupperDev j hj)
      (hlowerDev j hj) (hpair j hj)
  have hdom' : ∀ (j : ℕ) (hj : j < shellCount - 1),
      mu.real (balancedGrowthFailure balanced occupancy G j) ≤
        Bin(pairTotal j, UrnScreening.pairParameter (p j) (q j)
          (hp j hj) (hq j hj) (hpq j hj)).real
          {upper | upper ≤ pairTotal j ∧
            G * (pairTotal j - upper) < upper} := by
    intro j hj
    simpa only [p, q, C] using hdom j hj
  exact NearFavoriteShells.measureReal_totalOverflow_le_of_pair_domination
    mu balanced occupancy threshold G shellCount pairTotal p q C hstep
      hp hq hpq hC hratio hbase hbalance hdom'

/-! ## Canonical planar-walk specialization -/

/-- Transport of a measurable path event from the increment-space model to
the canonical path-space law.  This is the bridge used to state the remaining
screening inputs directly for `simpleRandomWalk`. -/
theorem simpleRandomWalk_real_eq_fairSteps_preimage
    (A : Set WalkPath) (hA : MeasurableSet A) :
    simpleRandomWalk.real A = fairSteps.real (trajectory ⁻¹' A) := by
  change ((fairSteps.map trajectory) A).toReal =
    (fairSteps (trajectory ⁻¹' A)).toReal
  rw [Measure.map_apply measurable_trajectory hA]

/-- Canonical `simpleRandomWalk` form of the checked adjacent-shell screen.

The hypotheses named `hbase`, `hbalance`, and `hdom` are not new assumptions
about an abstract measure: they are the exact remaining propositions about
the repository's canonical planar-walk law.  `StoppedInsertion` proves the
finite post-stopping factorization, but its documented boundary explains why
`hdom` for deleted excursions *before* `T_m^k`, conditioned on the favorite
event, still needs the stopped insertion-fiber disintegration. -/
theorem simpleRandomWalk_totalOverflow_le_of_localCLT
    (balanced : ℕ → Set WalkPath) (occupancy : WalkPath → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (pairTotal successes : ℕ → ℕ)
    (upperWindow lowerWindow : ℕ → Finset ℕ) (D W : ℕ → ℝ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    (hi : ∀ j < shellCount - 1, 0 < successes j)
    (hD : ∀ j < shellCount - 1, 0 ≤ D j)
    (hW : ∀ j < shellCount - 1, 0 ≤ W j)
    (hmoderate : ∀ j < shellCount - 1,
      D j ≤ (successes j : ℝ) / 30)
    (hlower : ∀ j < shellCount - 1, (lowerWindow j).Nonempty)
    (hcard : ∀ j < shellCount - 1,
      (upperWindow j).card ≤ (lowerWindow j).card)
    (hupperDev : ∀ j < shellCount - 1, ∀ a ∈ upperWindow j,
      |deviation (successes j) a| ≤ D j)
    (hlowerDev : ∀ j < shellCount - 1, ∀ a ∈ lowerWindow j,
      |deviation (successes j) a| ≤ D j)
    (hpair : ∀ j < shellCount - 1, ∀ a ∈ upperWindow j,
      ∀ b ∈ lowerWindow j,
        |deviation (successes j) a - deviation (successes j) b| ≤ W j)
    {baseCost : ℝ} {balanceCost : ℕ → ℝ}
    (hbase : simpleRandomWalk.real
      (shellOverflow occupancy threshold 0) ≤ baseCost)
    (hbalance : ∀ j < shellCount - 1,
      simpleRandomWalk.real (balanced j)ᶜ ≤ balanceCost j)
    (hdom : ∀ (j : ℕ) (hj : j < shellCount - 1),
      simpleRandomWalk.real
          (balancedGrowthFailure balanced occupancy G j) ≤
        Bin(pairTotal j,
          UrnScreening.pairParameter
            (windowMass (successes j) (upperWindow j))
            (windowMass (successes j) (lowerWindow j))
            (windowMass_nonneg _ _)
            (windowMass_nonneg _ _)
            (add_pos_of_nonneg_of_pos (windowMass_nonneg _ _)
              (windowMass_pos (hi j hj) (hlower j hj)))).real
          {upper | upper ≤ pairTotal j ∧
            G * (pairTotal j - upper) < upper}) :
    simpleRandomWalk.real
        (totalOverflow occupancy threshold shellCount) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        (balanceCost j +
          (1 + adjacentLocalRatio (successes j) (D j) (W j) /
              (1 + adjacentLocalRatio (successes j) (D j) (W j))) ^ pairTotal j /
            (2 : ℝ) ^ growthCut G (pairTotal j)) := by
  exact measureReal_totalOverflow_le_of_localCLT simpleRandomWalk
    balanced occupancy threshold G shellCount pairTotal successes
    upperWindow lowerWindow D W hstep hi hD hW hmoderate hlower hcard
    hupperDev hlowerDev hpair hbase hbalance hdom

/-- Canonical-walk shell propagation for the concrete consecutive integer
windows.  Every local-CLT side condition is now reduced to the transparent
integer conditions `0 < successes`, `0 < windowWidth`, and
`60 * windowWidth + 30 ≤ successes`. -/
theorem simpleRandomWalk_totalOverflow_le_of_concreteWindows
    (balanced : ℕ → Set WalkPath) (occupancy : WalkPath → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (pairTotal successes windowWidth : ℕ → ℕ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    (hi : ∀ j < shellCount - 1, 0 < successes j)
    (hwidth : ∀ j < shellCount - 1, 0 < windowWidth j)
    (hscale : ∀ j < shellCount - 1,
      60 * windowWidth j + 30 ≤ successes j)
    {baseCost : ℝ} {balanceCost : ℕ → ℝ}
    (hbase : simpleRandomWalk.real
      (shellOverflow occupancy threshold 0) ≤ baseCost)
    (hspatialBalance : ∀ j < shellCount - 1,
      simpleRandomWalk.real (balanced j)ᶜ ≤ balanceCost j)
    (hspatialGrowth : ∀ (j : ℕ) (hj : j < shellCount - 1),
      simpleRandomWalk.real
          (balancedGrowthFailure balanced occupancy G j) ≤
        Bin(pairTotal j,
          UrnScreening.pairParameter
            (windowMass (successes j)
              (upperFailureWindow (successes j) (windowWidth j)))
            (windowMass (successes j)
              (lowerFailureWindow (successes j) (windowWidth j)))
            (windowMass_nonneg _ _)
            (windowMass_nonneg _ _)
            (add_pos_of_nonneg_of_pos (windowMass_nonneg _ _)
              (windowMass_pos (hi j hj)
                (lowerFailureWindow_nonempty (hwidth j hj))))).real
          {upper | upper ≤ pairTotal j ∧
            G * (pairTotal j - upper) < upper}) :
    simpleRandomWalk.real
        (totalOverflow occupancy threshold shellCount) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        (balanceCost j +
          (1 + adjacentLocalRatio (successes j)
                (adjacentWindowRadius (windowWidth j))
                (adjacentWindowSeparation (windowWidth j)) /
              (1 + adjacentLocalRatio (successes j)
                (adjacentWindowRadius (windowWidth j))
                (adjacentWindowSeparation (windowWidth j)))) ^ pairTotal j /
            (2 : ℝ) ^ growthCut G (pairTotal j)) := by
  let upper : ℕ → Finset ℕ := fun j ↦
    upperFailureWindow (successes j) (windowWidth j)
  let lower : ℕ → Finset ℕ := fun j ↦
    lowerFailureWindow (successes j) (windowWidth j)
  let D : ℕ → ℝ := fun j ↦ adjacentWindowRadius (windowWidth j)
  let W : ℕ → ℝ := fun j ↦ adjacentWindowSeparation (windowWidth j)
  have hD : ∀ j < shellCount - 1, 0 ≤ D j := by
    intro j hj
    exact adjacentWindowRadius_nonneg _
  have hW : ∀ j < shellCount - 1, 0 ≤ W j := by
    intro j hj
    exact adjacentWindowSeparation_nonneg _
  have hmoderate : ∀ j < shellCount - 1, D j ≤ (successes j : ℝ) / 30 := by
    intro j hj
    exact adjacentWindowRadius_le_thirtieth (hscale j hj)
  have hlower : ∀ j < shellCount - 1, (lower j).Nonempty := by
    intro j hj
    exact lowerFailureWindow_nonempty (hwidth j hj)
  have hcard : ∀ j < shellCount - 1, (upper j).card ≤ (lower j).card := by
    intro j hj
    simp [upper, lower]
  have hupperDev : ∀ j < shellCount - 1, ∀ a ∈ upper j,
      |deviation (successes j) a| ≤ D j := by
    intro j hj a ha
    exact upperFailureWindow_deviation_le ha
  have hlowerDev : ∀ j < shellCount - 1, ∀ b ∈ lower j,
      |deviation (successes j) b| ≤ D j := by
    intro j hj b hb
    exact lowerFailureWindow_deviation_le hb
  have hpair : ∀ j < shellCount - 1, ∀ a ∈ upper j, ∀ b ∈ lower j,
      |deviation (successes j) a - deviation (successes j) b| ≤ W j := by
    intro j hj a ha b hb
    exact adjacentFailureWindow_deviation_sub_le ha hb
  have hdom : ∀ (j : ℕ) (hj : j < shellCount - 1),
      simpleRandomWalk.real
          (balancedGrowthFailure balanced occupancy G j) ≤
        Bin(pairTotal j,
          UrnScreening.pairParameter
            (windowMass (successes j) (upper j))
            (windowMass (successes j) (lower j))
            (windowMass_nonneg _ _) (windowMass_nonneg _ _)
            (add_pos_of_nonneg_of_pos (windowMass_nonneg _ _)
              (windowMass_pos (hi j hj) (hlower j hj)))).real
          {x | x ≤ pairTotal j ∧ G * (pairTotal j - x) < x} := by
    intro j hj
    simpa [upper, lower] using hspatialGrowth j hj
  exact simpleRandomWalk_totalOverflow_le_of_localCLT balanced occupancy threshold
    G shellCount pairTotal successes upper lower D W hstep hi hD hW hmoderate
    hlower hcard hupperDev hlowerDev hpair hbase hspatialBalance hdom

/-- Fully concrete first-round/adjacent-round shell screen on the canonical
walk.  The candidate set, deficit shells, geometric thresholds, base-event
inclusion, and all adjacent-window arithmetic are fixed and proved.  The only
random-walk inputs are:

* `hweightedOneSite`, the analytic external one-point bound used by
  `ExternalThickCount`;
* `hspatialBalance` and `hspatialGrowth`, the two conditional estimates whose
  proof requires spatial disintegration at the stopped favorite clock.
-/
theorem simpleRandomWalk_externalShell_totalOverflow_le
    (o : LazyDecomposition.Orientation) (n externalThreshold J G shellCount : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ) (m shellWidth : ℕ)
    (balanced : ℕ → Set WalkPath)
    (pairTotal successes : ℕ → ℕ)
    (q : ℝ≥0∞) (hJ : 0 < J) (hq : q ≠ ∞)
    (hsuccess : ∀ j < shellCount - 1, 120 ≤ successes j)
    (hweightedOneSite : ∀ x,
      simpleRandomWalk
          (ExternalThickCount.candidateEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n)
            (ExternalThickCount.orientedLargeEvent o n externalThreshold) x) ≤
        q * simpleRandomWalk
          (ExternalThickCount.memberEvent
            (fun s ↦ ExternalThickCount.orientedExternalVisitedSites o s n) x))
    {balanceCost : ℕ → ℝ}
    (hspatialBalance : ∀ j < shellCount - 1,
      simpleRandomWalk.real (balanced j)ᶜ ≤ balanceCost j)
    (hspatialGrowth : ∀ (j : ℕ) (hj : j < shellCount - 1),
      simpleRandomWalk.real
          (balancedGrowthFailure balanced
            (externalShellOccupancy o n externalThreshold distinguished
              totalLocalTime m shellWidth) G j) ≤
        Bin(pairTotal j,
          UrnScreening.pairParameter
            (windowMass (successes j)
              (upperFailureWindow (successes j)
                (canonicalWindowWidth (successes j))))
            (windowMass (successes j)
              (lowerFailureWindow (successes j)
                (canonicalWindowWidth (successes j))))
            (windowMass_nonneg _ _)
            (windowMass_nonneg _ _)
            (add_pos_of_nonneg_of_pos (windowMass_nonneg _ _)
              (windowMass_pos (canonicalWindowWidth_numeric (hsuccess j hj)).1
                (lowerFailureWindow_nonempty
                  (canonicalWindowWidth_numeric (hsuccess j hj)).2.1)))).real
          {upper | upper ≤ pairTotal j ∧
            G * (pairTotal j - upper) < upper}) :
    simpleRandomWalk.real
        (totalOverflow
          (externalShellOccupancy o n externalThreshold distinguished
            totalLocalTime m shellWidth)
          (geometricShellThreshold J G) shellCount) ≤
      (q * (↑(n + 1) : ℝ≥0∞) / J).toReal +
        ∑ j ∈ Finset.range (shellCount - 1),
          (balanceCost j +
            (1 + adjacentLocalRatio (successes j)
                  (adjacentWindowRadius (canonicalWindowWidth (successes j)))
                  (adjacentWindowSeparation (canonicalWindowWidth (successes j))) /
                (1 + adjacentLocalRatio (successes j)
                  (adjacentWindowRadius (canonicalWindowWidth (successes j)))
                  (adjacentWindowSeparation
                    (canonicalWindowWidth (successes j))))) ^ pairTotal j /
              (2 : ℝ) ^ growthCut G (pairTotal j)) := by
  have hstep : ∀ j, j + 1 < shellCount →
      G * geometricShellThreshold J G j ≤
        geometricShellThreshold J G (j + 1) := by
    intro j hj
    exact (geometricShellThreshold_step J G j).le
  have hbase : simpleRandomWalk.real
      (shellOverflow
        (externalShellOccupancy o n externalThreshold distinguished totalLocalTime
          m shellWidth)
        (geometricShellThreshold J G) 0) ≤
      (q * (↑(n + 1) : ℝ≥0∞) / J).toReal :=
    simpleRandomWalk_real_externalShellOverflow_zero_le o n externalThreshold J G
      distinguished totalLocalTime m shellWidth q hJ hq hweightedOneSite
  have hi : ∀ j < shellCount - 1, 0 < successes j := by
    intro j hj
    exact (canonicalWindowWidth_numeric (hsuccess j hj)).1
  have hwidth : ∀ j < shellCount - 1,
      0 < canonicalWindowWidth (successes j) := by
    intro j hj
    exact (canonicalWindowWidth_numeric (hsuccess j hj)).2.1
  have hscale : ∀ j < shellCount - 1,
      60 * canonicalWindowWidth (successes j) + 30 ≤ successes j := by
    intro j hj
    exact (canonicalWindowWidth_numeric (hsuccess j hj)).2.2
  exact simpleRandomWalk_totalOverflow_le_of_concreteWindows balanced
    (externalShellOccupancy o n externalThreshold distinguished totalLocalTime
      m shellWidth)
    (geometricShellThreshold J G) G shellCount pairTotal successes
    (fun j ↦ canonicalWindowWidth (successes j))
    hstep hi hwidth hscale hbase hspatialBalance hspatialGrowth

/-! ## Exact path-insertion identifications -/

lemma stoppedFailureMass_eq_hlozMass (o : LazyDecomposition.Orientation) {i : ℕ}
    (hi : 0 < i) (j : ℕ) :
    stoppedFailureMass o i j = hlozMass i j := by
  simpa only [hlozMass, hlozSuccess] using
    PathInsertion.stoppedFailureMass_eq_negativeBinomial o hi j

theorem fixedExternalConditional_windowMass {i : ℕ} (hi : 0 < i)
    (window : Finset ℕ) :
    ∑ j ∈ window,
        fixedExternalJointMass i j / fixedExternalMarginalMass i =
      windowMass i window := by
  unfold windowMass
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [hlozMass, hlozSuccess] using
    PathInsertion.fixedExternal_conditionalMass hi j

theorem stoppedFailureLaw_eq_hlozLaw (o : LazyDecomposition.Orientation) (i : ℕ)
    (hi : 0 < i) :
    stoppedFailureLaw o i hi = hlozLaw i hi := by
  ext j
  change ENNReal.ofReal (stoppedFailureMass o i j) =
    ENNReal.ofReal (hlozMass i j)
  rw [stoppedFailureMass_eq_hlozMass o hi j]

end Erdos1165.ScreeningInstantiation
