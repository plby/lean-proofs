/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZProp45SourceInterval

/-!
The two mirror estimates omitted from
`Erdos1166HLOZProp45SourceInterval`.

The first half is the source upper-endpoint estimate.  Its capped index is
the first integer strictly above
`15 b / 16 + 10 m^(1-κ)`, so the relevant holding-time sum has a
negative-binomial *lower* deviation.  The second half repeats both endpoint
arguments for a supplied shifted deletion clock.  The shifted clock is not
identified with the unprimed clock: its inverse profile, holding prefixes,
and stopped decomposition are explicit source data.
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

namespace Erdos1166.HLOZProp45SourceMirrors

open HLOZFoundation HLOZUrn HLOZDecomposition
open HLOZProp45Theta HLOZProp45SourceClock HLOZProp45SourceInterval

/-! ### The arbitrary-upper-endpoint lower-tail estimate -/

noncomputable def intervalHighCutReal (m b : ℕ) : ℝ :=
  (15 / 16 : ℝ) * b + sourceNearWidth m

/-- The least natural number strictly above the real source cutoff. -/
noncomputable def intervalHighCut (m b : ℕ) : ℕ :=
  Nat.floor (intervalHighCutReal m b) + 1

/-- Exact source-scale facts used by the upper branch. -/
structure SourceUpperScale (m b : ℕ) : Prop where
  one_le_m : 1 ≤ m
  one_le_b : 1 ≤ b
  b_le_m : b ≤ m
  highCut_le_b : intervalHighCut m b ≤ b
  prop44_le_high : sourceProp44Threshold m ≤ intervalHighCut m b

/-- At the source top endpoint `b=m`, every analytic upper-branch scale
condition holds eventually. -/
theorem eventually_sourceUpperScale_top :
    ∀ᶠ m : ℕ in Filter.atTop, SourceUpperScale m m := by
  have hnear : ∀ᶠ m : ℕ in Filter.atTop,
      sourceNearWidth m + 1 ≤ (1 / 16 : ℝ) * m := by
    have h1 := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 10) (d := 1 / 32) (p := 1 - sourceKappa) (q := 1)
      (by norm_num) (by norm_num) (by norm_num [sourceKappa])
    have h2 := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 1) (d := 1 / 32) (p := 0) (q := 1)
      (by norm_num) (by norm_num) (by norm_num)
    filter_upwards [h1, h2] with m hm1 hm2
    rw [sourceNearWidth]
    simp only [Real.rpow_zero, Real.rpow_one, mul_one] at hm1 hm2 ⊢
    nlinarith
  filter_upwards [eventually_sourceScale, hnear] with m hs hnear
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hhigh0 : 0 ≤ intervalHighCutReal m m := by
    rw [intervalHighCutReal]
    have hw : 0 ≤ sourceNearWidth m := by
      rw [sourceNearWidth]
      positivity
    positivity
  have hhighFloor : (Nat.floor (intervalHighCutReal m m) : ℝ) ≤
      intervalHighCutReal m m := Nat.floor_le hhigh0
  have hhighLe : intervalHighCut m m ≤ m := by
    have hR : (intervalHighCut m m : ℝ) ≤ m := by
      rw [intervalHighCut]
      push_cast
      rw [intervalHighCutReal] at hhighFloor ⊢
      norm_num at hhighFloor hnear ⊢
      nlinarith
    exact_mod_cast hR
  have hlowHigh : sourceLowCut m ≤ intervalHighCut m m := by
    have hmax : max (sourceLowCutReal m) 0 ≤ intervalHighCutReal m m := by
      apply max_le
      · rw [sourceLowCutReal, intervalHighCutReal]
        have hw : 0 ≤ sourceNearWidth m := by
          rw [sourceNearWidth]
          positivity
        nlinarith
      · exact hhigh0
    rw [sourceLowCut, intervalHighCut]
    exact (Nat.floor_mono hmax).trans (Nat.le_add_right _ _)
  exact
    { one_le_m := hs.one_le
      one_le_b := hs.one_le
      b_le_m := le_rfl
      highCut_le_b := hhighLe
      prop44_le_high := hs.prop44_le_split.trans (by
        exact_mod_cast hs.split_le_low.trans hlowHigh) }

noncomputable def intervalPlusDeviation (m b : ℕ) : ℝ :=
  (16 / 15 : ℝ) * intervalHighCut m b - b

def intervalDotThetaPlusAt {Ω : Type*} (m b : ℕ)
    (lazyPrefixSum : Ω → Site → ℕ) (x : Site) : Set Ω :=
  {ω | intervalHighCut m b + lazyPrefixSum ω x < b}

def intervalDotThetaPlusEvent {Ω : Type*} (sites : Finset Site) (m b : ℕ)
    (lazyPrefixSum : Ω → Site → ℕ) : Set Ω :=
  ⋃ x ∈ sites, intervalDotThetaPlusAt m b lazyPrefixSum x

noncomputable def intervalPlusCandidates (sites : Finset Site) (m b : ℕ)
    (profile : Site → ℕ) : Finset Site :=
  sites.filter fun x ↦ intervalHighCut m b ≤ profile x

lemma intervalHighCut_pos (m b : ℕ) : 1 ≤ intervalHighCut m b := by
  simp [intervalHighCut]

lemma intervalHighCutReal_lt_cut (m b : ℕ) :
    intervalHighCutReal m b < intervalHighCut m b := by
  rw [intervalHighCut]
  simpa only [Nat.cast_add, Nat.cast_one] using
    Nat.lt_floor_add_one (intervalHighCutReal m b)

lemma intervalPlusDeviation_nonneg (m b : ℕ) :
    0 ≤ intervalPlusDeviation m b := by
  have hcut := intervalHighCutReal_lt_cut m b
  rw [intervalHighCutReal] at hcut
  rw [intervalPlusDeviation]
  have hp : 0 ≤ sourceNearWidth m := by
    rw [sourceNearWidth]
    positivity
  nlinarith

lemma intervalPlusDeviation_le_index (m b : ℕ)
    (hs : SourceUpperScale m b) :
    intervalPlusDeviation m b ≤ intervalHighCut m b := by
  have hcb : (intervalHighCut m b : ℝ) ≤ b := by
    exact_mod_cast hs.highCut_le_b
  rw [intervalPlusDeviation]
  nlinarith

lemma sourceNearDeviation_lt_intervalPlusDeviation (m b : ℕ) :
    sourceNearDeviation m < intervalPlusDeviation m b := by
  have hcut := intervalHighCutReal_lt_cut m b
  rw [intervalHighCutReal] at hcut
  rw [intervalPlusDeviation, sourceNearDeviation]
  nlinarith

lemma intervalPlus_exponent (m b : ℕ) (hs : SourceUpperScale m b) :
    17 * sourceRate m ≤ intervalPlusDeviation m b ^ 2 /
      (4 * (intervalHighCut m b : ℝ)) := by
  have hiPos : (0 : ℝ) < intervalHighCut m b := by
    exact_mod_cast intervalHighCut_pos m b
  have hiM : (intervalHighCut m b : ℝ) ≤ m := by
    exact_mod_cast hs.highCut_le_b.trans hs.b_le_m
  have hd0 := intervalPlusDeviation_nonneg m b
  have hdev := le_of_lt (sourceNearDeviation_lt_intervalPlusDeviation m b)
  have hnear0 : 0 ≤ sourceNearDeviation m := by
    rw [sourceNearDeviation, sourceNearWidth]
    positivity
  have hsq : sourceNearDeviation m ^ 2 ≤ intervalPlusDeviation m b ^ 2 := by
    nlinarith [sq_nonneg (intervalPlusDeviation m b - sourceNearDeviation m)]
  calc
    17 * sourceRate m ≤ sourceNearDeviation m ^ 2 / (4 * (m : ℝ)) :=
      sourceNearExponentBase m hs.one_le_m
    _ ≤ intervalPlusDeviation m b ^ 2 / (4 * (m : ℝ)) := by
      gcongr
    _ ≤ intervalPlusDeviation m b ^ 2 /
        (4 * (intervalHighCut m b : ℝ)) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by gcongr)

lemma intervalDotThetaPlusAt_subset_lowerDeviation {Ω : Type*}
    (m b : ℕ) (lazyPrefixSum : Ω → Site → ℕ) (x : Site) :
    intervalDotThetaPlusAt m b lazyPrefixSum x ⊆
      {ω | (lazyPrefixSum ω x : ℝ) ≤
        (intervalHighCut m b : ℝ) / 15 - intervalPlusDeviation m b} := by
  intro ω hω
  change intervalHighCut m b + lazyPrefixSum ω x < b at hω
  have hR : (intervalHighCut m b : ℝ) + lazyPrefixSum ω x < b := by
    exact_mod_cast hω
  rw [intervalPlusDeviation]
  norm_num at hR ⊢
  nlinarith

lemma intervalPlusCandidates_subset_prop44 (m b : ℕ)
    (hs : SourceUpperScale m b) (sites : Finset Site)
    (profile : Site → ℕ) :
    intervalPlusCandidates sites m b profile ⊆
      sourceProp44Candidates sites m profile := by
  intro x hx
  rw [intervalPlusCandidates, Finset.mem_filter] at hx
  rw [sourceProp44Candidates, Finset.mem_filter]
  exact ⟨hx.1, hs.prop44_le_high.trans (by exact_mod_cast hx.2)⟩

theorem cond_intervalDotThetaPlusAt_le_exp_seventeen
    {Ω : Type*} [MeasurableSpace Ω]
    (m b : ℕ) (hs : SourceUpperScale m b) (μ : Measure Ω) (C : Set Ω)
    (lazyPrefixSum : Ω → Site → ℕ) (x : Site)
    (hLaw : HasLaw (fun ω ↦ lazyPrefixSum ω x)
      (negBinMeasure (intervalHighCut m b)) μ[|C]) :
    μ[|C] (intervalDotThetaPlusAt m b lazyPrefixSum x) ≤
      ENNReal.ofReal (Real.exp (-17 * sourceRate m)) := by
  calc
    μ[|C] (intervalDotThetaPlusAt m b lazyPrefixSum x) ≤
        μ[|C] {ω | (lazyPrefixSum ω x : ℝ) ≤
          (intervalHighCut m b : ℝ) / 15 - intervalPlusDeviation m b} :=
      measure_mono (intervalDotThetaPlusAt_subset_lowerDeviation
        m b lazyPrefixSum x)
    _ ≤ ENNReal.ofReal (Real.exp
          (-(intervalPlusDeviation m b ^ 2 /
            (4 * (intervalHighCut m b : ℝ))))) :=
      hasLaw_negBin_lowerDeviation_le_exp
        (fun ω ↦ lazyPrefixSum ω x) (intervalHighCut_pos m b)
        (intervalPlusDeviation m b) (intervalPlusDeviation_nonneg m b)
        (intervalPlusDeviation_le_index m b hs) hLaw
    _ ≤ ENNReal.ofReal (Real.exp (-17 * sourceRate m)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h := neg_le_neg (intervalPlus_exponent m b hs)
      nlinarith

/-- The upper branch of HLOZ (4.22): the Proposition 4.4 profile count and
the Proposition 4.2 lower-tail law are the only probabilistic inputs. -/
theorem cond_intervalDotThetaPlus_le_exp
    {Ω : Type*} [MeasurableSpace Ω]
    (m b : ℕ) (hs : SourceUpperScale m b) (μ : Measure Ω) (C : Set Ω)
    (sites : Finset Site) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ)
    (hProp44Card : ((sourceProp44Candidates sites m profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m))
    (hLaw : ∀ x ∈ intervalPlusCandidates sites m b profile,
      HasLaw (fun ω ↦ lazyPrefixSum ω x)
        (negBinMeasure (intervalHighCut m b)) μ[|C]) :
    μ[|C] (⋃ x ∈ intervalPlusCandidates sites m b profile,
      intervalDotThetaPlusAt m b lazyPrefixSum x) ≤
        ENNReal.ofReal (Real.exp (-sourceRate m)) := by
  have hcard : ((intervalPlusCandidates sites m b profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m) := by
    calc
      ((intervalPlusCandidates sites m b profile).card : ℝ) ≤
          ((sourceProp44Candidates sites m profile).card : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (intervalPlusCandidates_subset_prop44 m b hs sites profile)
      _ ≤ Real.exp (16 * sourceRate m) := hProp44Card
  apply HLOZProp45Union.finite_union_exp_sixteen_seventeen
    μ[|C] (intervalPlusCandidates sites m b profile)
    (intervalDotThetaPlusAt m b lazyPrefixSum) _ (sourceRate m)
    Set.Subset.rfl hcard
  intro x hx
  exact cond_intervalDotThetaPlusAt_le_exp_seventeen m b hs μ C
    lazyPrefixSum x (hLaw x hx)

/-! ### The completed-prefix upper branch

At a stopped time the last holding block can be unfinished.  The source
upper event nevertheless gives at least `intervalHighCut m b` external
visits, so the first `intervalHighCut m b - 1` holding blocks are complete.
The following variant is the source-faithful form needed at an arbitrary
stopping parity.  Its deviation is unchanged and its negative-binomial
index is smaller, so the same exponential estimate holds. -/

/-- Number of certainly completed holding blocks in the upper branch. -/
noncomputable def intervalPriorHighCut (m b : ℕ) : ℕ :=
  intervalHighCut m b - 1

lemma intervalHighCut_two_le (m b : ℕ) (hm : 1 ≤ m) (hb : 1 ≤ b) :
    2 ≤ intervalHighCut m b := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hpow : (1 : ℝ) ≤ (m : ℝ) ^ (1 - sourceKappa) := by
    have hexp : (0 : ℝ) ≤ 1 - sourceKappa := by
      norm_num [sourceKappa]
    simpa using Real.rpow_le_rpow_of_exponent_le hmR hexp
  have hreal : (1 : ℝ) ≤ intervalHighCutReal m b := by
    rw [intervalHighCutReal, sourceNearWidth]
    nlinarith
  have hfloor : 1 ≤ Nat.floor (intervalHighCutReal m b) := by
    exact Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ intervalHighCutReal m b by
      simpa using hreal)
  rw [intervalHighCut]
  omega

lemma intervalPriorHighCut_pos (m b : ℕ) (hs : SourceUpperScale m b) :
    1 ≤ intervalPriorHighCut m b := by
  rw [intervalPriorHighCut]
  have := intervalHighCut_two_le m b hs.one_le_m hs.one_le_b
  omega

lemma intervalPlusDeviation_le_priorIndex (m b : ℕ)
    (hs : SourceUpperScale m b) :
    intervalPlusDeviation m b ≤ intervalPriorHighCut m b := by
  have hcutTwo := intervalHighCut_two_le m b hs.one_le_m hs.one_le_b
  have hbTwo : 2 ≤ b := hcutTwo.trans hs.highCut_le_b
  have hcb : intervalHighCut m b ≤ b := hs.highCut_le_b
  rw [intervalPlusDeviation, intervalPriorHighCut]
  have hcast : (intervalHighCut m b : ℝ) ≤ b := by exact_mod_cast hcb
  have hbcast : (2 : ℝ) ≤ b := by exact_mod_cast hbTwo
  rw [Nat.cast_sub (by omega : 1 ≤ intervalHighCut m b)]
  nlinarith

lemma intervalPriorPlus_exponent (m b : ℕ) (hs : SourceUpperScale m b) :
    17 * sourceRate m ≤ intervalPlusDeviation m b ^ 2 /
      (4 * (intervalPriorHighCut m b : ℝ)) := by
  have hbase := intervalPlus_exponent m b hs
  have hpriorPos : (0 : ℝ) < intervalPriorHighCut m b := by
    exact_mod_cast intervalPriorHighCut_pos m b hs
  have hcutPos : (0 : ℝ) < intervalHighCut m b := by
    exact_mod_cast intervalHighCut_pos m b
  have hpriorLe : (intervalPriorHighCut m b : ℝ) ≤ intervalHighCut m b := by
    exact_mod_cast Nat.sub_le (intervalHighCut m b) 1
  calc
    17 * sourceRate m ≤ intervalPlusDeviation m b ^ 2 /
        (4 * (intervalHighCut m b : ℝ)) := hbase
    _ ≤ intervalPlusDeviation m b ^ 2 /
        (4 * (intervalPriorHighCut m b : ℝ)) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _)
        (by positivity) (by gcongr)

/-- The stopped upper event is controlled by the certainly completed
prefix, with the original external cutoff retained in the deterministic
inequality. -/
def intervalPriorDotThetaPlusAt {Ω : Type*} (m b : ℕ)
    (lazyPriorPrefixSum : Ω → Site → ℕ) (x : Site) : Set Ω :=
  {ω | intervalHighCut m b + lazyPriorPrefixSum ω x < b}

lemma intervalPriorDotThetaPlusAt_subset_lowerDeviation {Ω : Type*}
    (m b : ℕ) (lazyPriorPrefixSum : Ω → Site → ℕ) (x : Site) :
    intervalPriorDotThetaPlusAt m b lazyPriorPrefixSum x ⊆
      {ω | (lazyPriorPrefixSum ω x : ℝ) ≤
        (intervalPriorHighCut m b : ℝ) / 15 -
          intervalPlusDeviation m b} := by
  intro ω hω
  change intervalHighCut m b + lazyPriorPrefixSum ω x < b at hω
  have hnat : lazyPriorPrefixSum ω x ≤ b - intervalHighCut m b - 1 := by
    omega
  have hR : (lazyPriorPrefixSum ω x : ℝ) ≤
      (b - intervalHighCut m b - 1 : ℕ) := by exact_mod_cast hnat
  rw [intervalPriorHighCut, intervalPlusDeviation]
  by_cases hcb : intervalHighCut m b ≤ b
  · rw [Nat.cast_sub (by omega : 1 ≤ b - intervalHighCut m b)] at hR
    rw [Nat.cast_sub hcb] at hR
    rw [Nat.cast_sub (intervalHighCut_pos m b)]
    norm_num at hR ⊢
    nlinarith
  · have : b - intervalHighCut m b - 1 = 0 := by omega
    rw [this] at hR
    norm_num at hR
    have : intervalHighCut m b + lazyPriorPrefixSum ω x ≥ b := by omega
    omega

theorem cond_intervalPriorDotThetaPlusAt_le_exp_seventeen
    {Ω : Type*} [MeasurableSpace Ω]
    (m b : ℕ) (hs : SourceUpperScale m b) (μ : Measure Ω) (C : Set Ω)
    (lazyPriorPrefixSum : Ω → Site → ℕ) (x : Site)
    (hLaw : HasLaw (fun ω ↦ lazyPriorPrefixSum ω x)
      (negBinMeasure (intervalPriorHighCut m b)) μ[|C]) :
    μ[|C] (intervalPriorDotThetaPlusAt m b lazyPriorPrefixSum x) ≤
      ENNReal.ofReal (Real.exp (-17 * sourceRate m)) := by
  calc
    μ[|C] (intervalPriorDotThetaPlusAt m b lazyPriorPrefixSum x) ≤
        μ[|C] {ω | (lazyPriorPrefixSum ω x : ℝ) ≤
          (intervalPriorHighCut m b : ℝ) / 15 -
            intervalPlusDeviation m b} :=
      measure_mono (intervalPriorDotThetaPlusAt_subset_lowerDeviation
        m b lazyPriorPrefixSum x)
    _ ≤ ENNReal.ofReal (Real.exp
          (-(intervalPlusDeviation m b ^ 2 /
            (4 * (intervalPriorHighCut m b : ℝ))))) :=
      hasLaw_negBin_lowerDeviation_le_exp
        (fun ω ↦ lazyPriorPrefixSum ω x)
        (intervalPriorHighCut_pos m b hs)
        (intervalPlusDeviation m b) (intervalPlusDeviation_nonneg m b)
        (intervalPlusDeviation_le_priorIndex m b hs) hLaw
    _ ≤ ENNReal.ofReal (Real.exp (-17 * sourceRate m)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h := neg_le_neg (intervalPriorPlus_exponent m b hs)
      nlinarith

theorem cond_intervalPriorDotThetaPlus_le_exp
    {Ω : Type*} [MeasurableSpace Ω]
    (m b : ℕ) (hs : SourceUpperScale m b) (μ : Measure Ω) (C : Set Ω)
    (sites : Finset Site) (profile : Site → ℕ)
    (lazyPriorPrefixSum : Ω → Site → ℕ)
    (hProp44Card : ((sourceProp44Candidates sites m profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m))
    (hLaw : ∀ x ∈ intervalPlusCandidates sites m b profile,
      HasLaw (fun ω ↦ lazyPriorPrefixSum ω x)
        (negBinMeasure (intervalPriorHighCut m b)) μ[|C]) :
    μ[|C] (⋃ x ∈ intervalPlusCandidates sites m b profile,
      intervalPriorDotThetaPlusAt m b lazyPriorPrefixSum x) ≤
        ENNReal.ofReal (Real.exp (-sourceRate m)) := by
  have hcard : ((intervalPlusCandidates sites m b profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m) := by
    calc
      ((intervalPlusCandidates sites m b profile).card : ℝ) ≤
          ((sourceProp44Candidates sites m profile).card : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (intervalPlusCandidates_subset_prop44 m b hs sites profile)
      _ ≤ Real.exp (16 * sourceRate m) := hProp44Card
  apply HLOZProp45Union.finite_union_exp_sixteen_seventeen
    μ[|C] (intervalPlusCandidates sites m b profile)
    (intervalPriorDotThetaPlusAt m b lazyPriorPrefixSum) _ (sourceRate m)
    Set.Subset.rfl hcard
  intro x hx
  exact cond_intervalPriorDotThetaPlusAt_le_exp_seventeen m b hs μ C
    lazyPriorPrefixSum x (hLaw x hx)

/-! ### Concrete unprimed inverse-clock upper branch -/

def intervalCanonicalDotThetaPlusEvent (q : ℕ) (sites : Finset Site)
    (m b : ℕ) (profile : Site → ℕ) : Set (ℕ → Site) :=
  ⋃ x ∈ intervalPlusCandidates sites m b profile,
    intervalDotThetaPlusAt m b
      (fun s x ↦ inverseClockHoldingPrefix s q (intervalHighCut m b) x) x

/-- Canonical upper event formed from the prefix which is complete at every
stopping parity. -/
def intervalCanonicalPriorDotThetaPlusEvent (q : ℕ) (sites : Finset Site)
    (m b : ℕ) (profile : Site → ℕ) : Set (ℕ → Site) :=
  ⋃ x ∈ intervalPlusCandidates sites m b profile,
    intervalPriorDotThetaPlusAt m b
      (fun s x ↦ inverseClockHoldingPrefix s q
        (intervalPriorHighCut m b) x) x

def intervalStoppedThetaPlusAt (m b k : ℕ) (x : Site) : Set (ℕ → Site) :=
  {s | intervalHighCut m b ≤
      paperExternalLocalTime s (favoriteCreationHorizon m k s) x ∧
    localTime s (favoriteCreationHorizon m k s) x < b}

def intervalStoppedThetaPlusEvent
    (sites : Finset Site) (m b k : ℕ) : Set (ℕ → Site) :=
  ⋃ x ∈ sites, intervalStoppedThetaPlusAt m b k x

/-- The initial capped holding prefix is contained in the lazy contribution
already accumulated at the stopped time. -/
def SourceClockInitialPrefixCompatibleAt
    (s : ℕ → Site) (T q cut : ℕ) (x : Site) : Prop :=
  paperExternalLocalTime s T x ≤ inverseClockProfile s q x ∧
    inverseClockHoldingPrefix s q cut x ≤ paperLazyLocalTime s T x

def intervalClockInitialPrefixCompatibleEvent
    (q : ℕ) (sites : Finset Site) (m b k : ℕ) : Set (ℕ → Site) :=
  {s | ∀ x ∈ sites, SourceClockInitialPrefixCompatibleAt s
    (favoriteCreationHorizon m k s) q (intervalHighCut m b) x}

theorem intervalStoppedThetaPlus_subset_canonicalDotTheta
    (q : ℕ) (sites : Finset Site) (m b k : ℕ) (profile : Site → ℕ) :
    intervalStoppedThetaPlusEvent sites m b k ∩
        inverseClockProfileAtom q sites profile ∩
        intervalClockInitialPrefixCompatibleEvent q sites m b k ⊆
      intervalCanonicalDotThetaPlusEvent q sites m b profile := by
  intro s hs
  rcases hs with ⟨⟨hsTheta, hsProfile⟩, hsCompat⟩
  simp only [intervalStoppedThetaPlusEvent, Set.mem_iUnion] at hsTheta
  rcases hsTheta with ⟨x, hxsite, hxTheta⟩
  rw [intervalCanonicalDotThetaPlusEvent]
  simp only [Set.mem_iUnion]
  have hprofile : inverseClockProfile s q x = profile x := hsProfile x hxsite
  have hcompat := hsCompat x hxsite
  have hcandidate : x ∈ intervalPlusCandidates sites m b profile := by
    rw [intervalPlusCandidates, Finset.mem_filter]
    exact ⟨hxsite, hxTheta.1.trans (by simpa only [hprofile] using hcompat.1)⟩
  refine ⟨x, hcandidate, ?_⟩
  change intervalHighCut m b +
    inverseClockHoldingPrefix s q (intervalHighCut m b) x < b
  have hdecomp := localTime_eq_paperExternal_add_paperLazy
    s (favoriteCreationHorizon m k s) x
  calc
    intervalHighCut m b +
        inverseClockHoldingPrefix s q (intervalHighCut m b) x ≤
        paperExternalLocalTime s (favoriteCreationHorizon m k s) x +
          paperLazyLocalTime s (favoriteCreationHorizon m k s) x :=
      Nat.add_le_add hxTheta.1 hcompat.2
    _ = localTime s (favoriteCreationHorizon m k s) x := hdecomp.symm
    _ < b := hxTheta.2

theorem cond_inter_intervalStoppedThetaPlus_le_exp
    (q m b k : ℕ) (hs : SourceUpperScale m b)
    (μ : Measure (ℕ → Site)) (C H : Set (ℕ → Site))
    (sites : Finset Site) (profile : Site → ℕ)
    (hStoppedSubset :
      C ∩ H ∩ intervalStoppedThetaPlusEvent sites m b k ⊆
        intervalCanonicalDotThetaPlusEvent q sites m b profile)
    (hProp44Card : ((sourceProp44Candidates sites m profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m))
    (hLaw : ∀ x ∈ intervalPlusCandidates sites m b profile,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q (intervalHighCut m b) x)
        (negBinMeasure (intervalHighCut m b)) μ[|C]) :
    μ[|C] (C ∩ H ∩ intervalStoppedThetaPlusEvent sites m b k) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) := by
  calc
    μ[|C] (C ∩ H ∩ intervalStoppedThetaPlusEvent sites m b k) ≤
        μ[|C] (intervalCanonicalDotThetaPlusEvent q sites m b profile) := by
      exact measure_mono hStoppedSubset
    _ ≤ ENNReal.ofReal (Real.exp (-sourceRate m)) := by
      exact cond_intervalDotThetaPlus_le_exp m b hs μ C sites profile
        (fun s x ↦ inverseClockHoldingPrefix s q (intervalHighCut m b) x)
        hProp44Card hLaw

/-! ### The primed shifted deletion

The paper's primed deletion is obtained from a one-step shifted walk.  The
construction of that shifted inverse clock belongs to the reconstruction
layer.  The following structure records precisely the four natural-valued
objects used here and its exact stopped local-time decomposition.  In
particular, no equality with the unprimed clock is postulated.
-/

structure PrimedShiftedDeletionClock (m k : ℕ) where
  stoppedExternal : (ℕ → Site) → Site → ℕ
  stoppedLazy : (ℕ → Site) → Site → ℕ
  inverseProfile : (ℕ → Site) → Site → ℕ
  inverseHoldingPrefix : (ℕ → Site) → ℕ → Site → ℕ
  stopped_decomposition : ∀ s x,
    localTime s (favoriteCreationHorizon m k s) x =
      stoppedExternal s x + stoppedLazy s x

def primedInverseProfileAtom (clock : PrimedShiftedDeletionClock m k)
    (sites : Finset Site) (profile : Site → ℕ) : Set (ℕ → Site) :=
  {s | ∀ x ∈ sites, clock.inverseProfile s x = profile x}

def primedIntervalStoppedThetaMinusAt
    (clock : PrimedShiftedDeletionClock m k) (a : ℕ) (x : Site) :
    Set (ℕ → Site) :=
  {s | clock.stoppedExternal s x ≤ intervalLowCut m a ∧
    a ≤ localTime s (favoriteCreationHorizon m k s) x}

def primedIntervalStoppedThetaMinusEvent
    (clock : PrimedShiftedDeletionClock m k) (sites : Finset Site) (a : ℕ) :
    Set (ℕ → Site) :=
  ⋃ x ∈ sites, primedIntervalStoppedThetaMinusAt clock a x

def primedIntervalStoppedThetaPlusAt
    (clock : PrimedShiftedDeletionClock m k) (b : ℕ) (x : Site) :
    Set (ℕ → Site) :=
  {s | intervalHighCut m b ≤ clock.stoppedExternal s x ∧
    localTime s (favoriteCreationHorizon m k s) x < b}

def primedIntervalStoppedThetaPlusEvent
    (clock : PrimedShiftedDeletionClock m k) (sites : Finset Site) (b : ℕ) :
    Set (ℕ → Site) :=
  ⋃ x ∈ sites, primedIntervalStoppedThetaPlusAt clock b x

def primedIntervalCanonicalDotThetaMinusEvent
    (clock : PrimedShiftedDeletionClock m k) (sites : Finset Site)
    (a : ℕ) (profile : Site → ℕ) : Set (ℕ → Site) :=
  intervalDotThetaEvent sites m a profile fun s x ↦
    clock.inverseHoldingPrefix s (intervalDotIndex m a profile x) x

def primedIntervalCanonicalDotThetaPlusEvent
    (clock : PrimedShiftedDeletionClock m k) (sites : Finset Site)
    (b : ℕ) (profile : Site → ℕ) : Set (ℕ → Site) :=
  ⋃ x ∈ intervalPlusCandidates sites m b profile,
    intervalDotThetaPlusAt m b
      (fun s x ↦ clock.inverseHoldingPrefix s (intervalHighCut m b) x) x

/-- Primed canonical upper event using only certainly completed blocks. -/
def primedIntervalCanonicalPriorDotThetaPlusEvent
    (clock : PrimedShiftedDeletionClock m k) (sites : Finset Site)
    (b : ℕ) (profile : Site → ℕ) : Set (ℕ → Site) :=
  ⋃ x ∈ intervalPlusCandidates sites m b profile,
    intervalPriorDotThetaPlusAt m b
      (fun s x ↦ clock.inverseHoldingPrefix s
        (intervalPriorHighCut m b) x) x

def primedMinusPrefixCompatibleEvent
    (clock : PrimedShiftedDeletionClock m k) (sites : Finset Site)
    (a : ℕ) (profile : Site → ℕ) : Set (ℕ → Site) :=
  {s | ∀ x ∈ sites,
    clock.stoppedExternal s x ≤ clock.inverseProfile s x ∧
    clock.stoppedLazy s x ≤
      clock.inverseHoldingPrefix s (intervalDotIndex m a profile x) x}

def primedPlusInitialPrefixCompatibleEvent
    (clock : PrimedShiftedDeletionClock m k) (sites : Finset Site)
    (b : ℕ) : Set (ℕ → Site) :=
  {s | ∀ x ∈ sites,
    clock.stoppedExternal s x ≤ clock.inverseProfile s x ∧
    clock.inverseHoldingPrefix s (intervalHighCut m b) x ≤
      clock.stoppedLazy s x}

/-- Source-faithful upper compatibility: only the holding blocks which are
certainly complete at the stopped time are compared with stopped lazy time. -/
def primedPriorPlusInitialPrefixCompatibleEvent
    (clock : PrimedShiftedDeletionClock m k) (sites : Finset Site)
    (b : ℕ) : Set (ℕ → Site) :=
  {s | ∀ x ∈ sites,
    clock.stoppedExternal s x ≤ clock.inverseProfile s x ∧
    clock.inverseHoldingPrefix s (intervalPriorHighCut m b) x ≤
      clock.stoppedLazy s x}

theorem primedStoppedThetaMinus_subset_canonicalDotTheta
    (clock : PrimedShiftedDeletionClock m k) (sites : Finset Site)
    (a : ℕ) (profile : Site → ℕ) :
    primedIntervalStoppedThetaMinusEvent clock sites a ∩
        primedInverseProfileAtom clock sites profile ∩
        primedMinusPrefixCompatibleEvent clock sites a profile ⊆
      primedIntervalCanonicalDotThetaMinusEvent clock sites a profile := by
  intro s hs
  rcases hs with ⟨⟨hsTheta, hsProfile⟩, hsCompat⟩
  simp only [primedIntervalStoppedThetaMinusEvent, Set.mem_iUnion] at hsTheta
  rcases hsTheta with ⟨x, hxsite, hxTheta⟩
  rw [primedIntervalCanonicalDotThetaMinusEvent, intervalDotThetaEvent]
  simp only [Set.mem_iUnion]
  refine ⟨x, hxsite, ?_⟩
  change a ≤ intervalDotIndex m a profile x +
    clock.inverseHoldingPrefix s (intervalDotIndex m a profile x) x
  have hprofile : clock.inverseProfile s x = profile x := hsProfile x hxsite
  have hcompat := hsCompat x hxsite
  have hext : clock.stoppedExternal s x ≤ intervalDotIndex m a profile x := by
    rw [intervalDotIndex]
    apply le_min
    · simpa only [hprofile] using hcompat.1
    · exact hxTheta.1
  calc
    a ≤ localTime s (favoriteCreationHorizon m k s) x := hxTheta.2
    _ = clock.stoppedExternal s x + clock.stoppedLazy s x :=
      clock.stopped_decomposition s x
    _ ≤ intervalDotIndex m a profile x +
        clock.inverseHoldingPrefix s (intervalDotIndex m a profile x) x :=
      Nat.add_le_add hext hcompat.2

theorem primedStoppedThetaPlus_subset_canonicalDotTheta
    (clock : PrimedShiftedDeletionClock m k) (sites : Finset Site)
    (b : ℕ) (profile : Site → ℕ) :
    primedIntervalStoppedThetaPlusEvent clock sites b ∩
        primedInverseProfileAtom clock sites profile ∩
        primedPlusInitialPrefixCompatibleEvent clock sites b ⊆
      primedIntervalCanonicalDotThetaPlusEvent clock sites b profile := by
  intro s hs
  rcases hs with ⟨⟨hsTheta, hsProfile⟩, hsCompat⟩
  simp only [primedIntervalStoppedThetaPlusEvent, Set.mem_iUnion] at hsTheta
  rcases hsTheta with ⟨x, hxsite, hxTheta⟩
  rw [primedIntervalCanonicalDotThetaPlusEvent]
  simp only [Set.mem_iUnion]
  have hprofile : clock.inverseProfile s x = profile x := hsProfile x hxsite
  have hcompat := hsCompat x hxsite
  have hcandidate : x ∈ intervalPlusCandidates sites m b profile := by
    rw [intervalPlusCandidates, Finset.mem_filter]
    exact ⟨hxsite, hxTheta.1.trans (by simpa only [hprofile] using hcompat.1)⟩
  refine ⟨x, hcandidate, ?_⟩
  change intervalHighCut m b +
    clock.inverseHoldingPrefix s (intervalHighCut m b) x < b
  calc
    intervalHighCut m b +
        clock.inverseHoldingPrefix s (intervalHighCut m b) x ≤
        clock.stoppedExternal s x + clock.stoppedLazy s x :=
      Nat.add_le_add hxTheta.1 hcompat.2
    _ = localTime s (favoriteCreationHorizon m k s) x :=
      (clock.stopped_decomposition s x).symm
    _ < b := hxTheta.2

theorem primedStoppedThetaPlus_subset_canonicalPriorDotTheta
    (clock : PrimedShiftedDeletionClock m k) (sites : Finset Site)
    (b : ℕ) (profile : Site → ℕ) :
    primedIntervalStoppedThetaPlusEvent clock sites b ∩
        primedInverseProfileAtom clock sites profile ∩
        primedPriorPlusInitialPrefixCompatibleEvent clock sites b ⊆
      primedIntervalCanonicalPriorDotThetaPlusEvent clock sites b profile := by
  intro s hs
  rcases hs with ⟨⟨hsTheta, hsProfile⟩, hsCompat⟩
  simp only [primedIntervalStoppedThetaPlusEvent, Set.mem_iUnion] at hsTheta
  rcases hsTheta with ⟨x, hxsite, hxTheta⟩
  rw [primedIntervalCanonicalPriorDotThetaPlusEvent]
  simp only [Set.mem_iUnion]
  have hprofile : clock.inverseProfile s x = profile x := hsProfile x hxsite
  have hcompat := hsCompat x hxsite
  have hcandidate : x ∈ intervalPlusCandidates sites m b profile := by
    rw [intervalPlusCandidates, Finset.mem_filter]
    exact ⟨hxsite, hxTheta.1.trans (by simpa only [hprofile] using hcompat.1)⟩
  refine ⟨x, hcandidate, ?_⟩
  change intervalHighCut m b +
    clock.inverseHoldingPrefix s (intervalPriorHighCut m b) x < b
  calc
    intervalHighCut m b +
        clock.inverseHoldingPrefix s (intervalPriorHighCut m b) x ≤
        clock.stoppedExternal s x + clock.stoppedLazy s x :=
      Nat.add_le_add hxTheta.1 hcompat.2
    _ = localTime s (favoriteCreationHorizon m k s) x :=
      (clock.stopped_decomposition s x).symm
    _ < b := hxTheta.2

theorem cond_inter_primedStoppedThetaMinus_le_two_scale
    (clock : PrimedShiftedDeletionClock m k) (a : ℕ)
    (hs : SourceIntervalScale m a)
    (μ : Measure (ℕ → Site)) (C H : Set (ℕ → Site))
    (sites : Finset Site) (profile : Site → ℕ)
    (hStoppedSubset :
      C ∩ H ∩ primedIntervalStoppedThetaMinusEvent clock sites a ⊆
        primedIntervalCanonicalDotThetaMinusEvent clock sites a profile)
    (hProp44Card : ((intervalProp44Candidates sites m profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m))
    (hHorizonCard : (sites.card : ℝ) ≤ Real.exp (16 * Real.sqrt (m : ℝ)))
    (hLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ clock.inverseHoldingPrefix s
        (intervalDotIndex m a profile x) x)
        (negBinMeasure (intervalDotIndex m a profile x)) μ[|C]) :
    μ[|C] (C ∩ H ∩ primedIntervalStoppedThetaMinusEvent clock sites a) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
  calc
    μ[|C] (C ∩ H ∩ primedIntervalStoppedThetaMinusEvent clock sites a) ≤
        μ[|C] (primedIntervalCanonicalDotThetaMinusEvent
          clock sites a profile) := by
      exact measure_mono hStoppedSubset
    _ ≤ ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
      exact cond_intervalDotTheta_le_two_scale m a hs μ C sites profile
        (fun s x ↦ clock.inverseHoldingPrefix s
          (intervalDotIndex m a profile x) x)
        hProp44Card hHorizonCard hLaw

theorem cond_inter_primedStoppedThetaPlus_le_exp
    (clock : PrimedShiftedDeletionClock m k) (b : ℕ)
    (hs : SourceUpperScale m b)
    (μ : Measure (ℕ → Site)) (C H : Set (ℕ → Site))
    (sites : Finset Site) (profile : Site → ℕ)
    (hStoppedSubset :
      C ∩ H ∩ primedIntervalStoppedThetaPlusEvent clock sites b ⊆
        primedIntervalCanonicalDotThetaPlusEvent clock sites b profile)
    (hProp44Card : ((sourceProp44Candidates sites m profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m))
    (hLaw : ∀ x ∈ intervalPlusCandidates sites m b profile,
      HasLaw (fun s ↦ clock.inverseHoldingPrefix s (intervalHighCut m b) x)
        (negBinMeasure (intervalHighCut m b)) μ[|C]) :
    μ[|C] (C ∩ H ∩ primedIntervalStoppedThetaPlusEvent clock sites b) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) := by
  calc
    μ[|C] (C ∩ H ∩ primedIntervalStoppedThetaPlusEvent clock sites b) ≤
        μ[|C] (primedIntervalCanonicalDotThetaPlusEvent
          clock sites b profile) := by
      exact measure_mono hStoppedSubset
    _ ≤ ENNReal.ofReal (Real.exp (-sourceRate m)) := by
      exact cond_intervalDotThetaPlus_le_exp m b hs μ C sites profile
        (fun s x ↦ clock.inverseHoldingPrefix s (intervalHighCut m b) x)
        hProp44Card hLaw

theorem cond_inter_primedStoppedThetaPriorPlus_le_exp
    (clock : PrimedShiftedDeletionClock m k) (b : ℕ)
    (hs : SourceUpperScale m b)
    (μ : Measure (ℕ → Site)) (C H : Set (ℕ → Site))
    (sites : Finset Site) (profile : Site → ℕ)
    (hStoppedSubset :
      C ∩ H ∩ primedIntervalStoppedThetaPlusEvent clock sites b ⊆
        primedIntervalCanonicalPriorDotThetaPlusEvent clock sites b profile)
    (hProp44Card : ((sourceProp44Candidates sites m profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m))
    (hLaw : ∀ x ∈ intervalPlusCandidates sites m b profile,
      HasLaw (fun s ↦ clock.inverseHoldingPrefix s
        (intervalPriorHighCut m b) x)
        (negBinMeasure (intervalPriorHighCut m b)) μ[|C]) :
    μ[|C] (C ∩ H ∩ primedIntervalStoppedThetaPlusEvent clock sites b) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) := by
  calc
    μ[|C] (C ∩ H ∩ primedIntervalStoppedThetaPlusEvent clock sites b) ≤
        μ[|C] (primedIntervalCanonicalPriorDotThetaPlusEvent
          clock sites b profile) := measure_mono hStoppedSubset
    _ ≤ ENNReal.ofReal (Real.exp (-sourceRate m)) := by
      exact cond_intervalPriorDotThetaPlus_le_exp m b hs μ C sites profile
        (fun s x ↦ clock.inverseHoldingPrefix s
          (intervalPriorHighCut m b) x) hProp44Card hLaw

/-! ### The four-way Proposition 4.5 exceptional event -/

def fullProp45StoppedEvent (clock : PrimedShiftedDeletionClock m k)
    (sites : Finset Site) (a b : ℕ) : Set (ℕ → Site) :=
  intervalStoppedThetaMinusEvent sites m a k ∪
    intervalStoppedThetaPlusEvent sites m b k ∪
    primedIntervalStoppedThetaMinusEvent clock sites a ∪
    primedIntervalStoppedThetaPlusEvent clock sites b

/-- Full finite conditional core of HLOZ Proposition 4.5.  The external
profile atom `C` remains the conditioning event for all four Proposition 4.2
laws.  The horizon event `H` occurs only in the numerator.  This distinction
is essential: conditioning additionally on `H` would in general bias the lazy
holding variables. -/
theorem cond_inter_fullProp45StoppedEvent_le
    (q m a b k : ℕ) (hsLower : SourceIntervalScale m a)
    (hsUpper : SourceUpperScale m b)
    (clock : PrimedShiftedDeletionClock m k)
    (μ : Measure (ℕ → Site)) (C H : Set (ℕ → Site))
    (sites : Finset Site) (unprimedProfile primedProfile : Site → ℕ)
    (hUnprimedMinusSubset :
      C ∩ H ∩ intervalStoppedThetaMinusEvent sites m a k ⊆
        intervalCanonicalDotThetaEvent q sites m a unprimedProfile)
    (hUnprimedPlusSubset :
      C ∩ H ∩ intervalStoppedThetaPlusEvent sites m b k ⊆
        intervalCanonicalDotThetaPlusEvent q sites m b unprimedProfile)
    (hPrimedMinusSubset :
      C ∩ H ∩ primedIntervalStoppedThetaMinusEvent clock sites a ⊆
        primedIntervalCanonicalDotThetaMinusEvent
          clock sites a primedProfile)
    (hPrimedPlusSubset :
      C ∩ H ∩ primedIntervalStoppedThetaPlusEvent clock sites b ⊆
        primedIntervalCanonicalDotThetaPlusEvent
          clock sites b primedProfile)
    (hUnprimedProp44 :
      ((sourceProp44Candidates sites m unprimedProfile).card : ℝ) ≤
        Real.exp (16 * sourceRate m))
    (hPrimedProp44 :
      ((sourceProp44Candidates sites m primedProfile).card : ℝ) ≤
        Real.exp (16 * sourceRate m))
    (hHorizonCard : (sites.card : ℝ) ≤ Real.exp (16 * Real.sqrt (m : ℝ)))
    (hUnprimedMinusLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q
        (intervalDotIndex m a unprimedProfile x) x)
        (negBinMeasure (intervalDotIndex m a unprimedProfile x)) μ[|C])
    (hUnprimedPlusLaw : ∀ x ∈ intervalPlusCandidates sites m b unprimedProfile,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q (intervalHighCut m b) x)
        (negBinMeasure (intervalHighCut m b)) μ[|C])
    (hPrimedMinusLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ clock.inverseHoldingPrefix s
        (intervalDotIndex m a primedProfile x) x)
        (negBinMeasure (intervalDotIndex m a primedProfile x)) μ[|C])
    (hPrimedPlusLaw : ∀ x ∈ intervalPlusCandidates sites m b primedProfile,
      HasLaw (fun s ↦ clock.inverseHoldingPrefix s (intervalHighCut m b) x)
        (negBinMeasure (intervalHighCut m b)) μ[|C]) :
    μ[|C] (C ∩ H ∩ fullProp45StoppedEvent clock sites a b) ≤
      (ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
        ENNReal.ofReal (Real.exp (-sourceRate m)) +
        (ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
        ENNReal.ofReal (Real.exp (-sourceRate m)) := by
  let Uminus := C ∩ H ∩ intervalStoppedThetaMinusEvent sites m a k
  let Uplus := C ∩ H ∩ intervalStoppedThetaPlusEvent sites m b k
  let Pminus := C ∩ H ∩ primedIntervalStoppedThetaMinusEvent clock sites a
  let Pplus := C ∩ H ∩ primedIntervalStoppedThetaPlusEvent clock sites b
  have hset : C ∩ H ∩ fullProp45StoppedEvent clock sites a b =
      ((Uminus ∪ Uplus) ∪ Pminus) ∪ Pplus := by
    ext s
    simp only [fullProp45StoppedEvent, Uminus, Uplus, Pminus, Pplus,
      Set.mem_inter_iff, Set.mem_union]
    tauto
  have hUMinus : μ[|C] Uminus ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
    simpa only [Uminus] using
      cond_inter_intervalStoppedThetaMinus_le_two_scale
        q m a k hsLower μ C H sites unprimedProfile hUnprimedMinusSubset
        hUnprimedProp44 hHorizonCard hUnprimedMinusLaw
  have hUPlus : μ[|C] Uplus ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) := by
    simpa only [Uplus] using
      cond_inter_intervalStoppedThetaPlus_le_exp
        q m b k hsUpper μ C H sites unprimedProfile hUnprimedPlusSubset
        hUnprimedProp44 hUnprimedPlusLaw
  have hPMinus : μ[|C] Pminus ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
    simpa only [Pminus] using
      cond_inter_primedStoppedThetaMinus_le_two_scale
        clock a hsLower μ C H sites primedProfile hPrimedMinusSubset
        hPrimedProp44 hHorizonCard hPrimedMinusLaw
  have hPPlus : μ[|C] Pplus ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) := by
    simpa only [Pplus] using
      cond_inter_primedStoppedThetaPlus_le_exp
        clock b hsUpper μ C H sites primedProfile hPrimedPlusSubset
        hPrimedProp44 hPrimedPlusLaw
  rw [hset]
  calc
    μ[|C] (((Uminus ∪ Uplus) ∪ Pminus) ∪ Pplus) ≤
        μ[|C] ((Uminus ∪ Uplus) ∪ Pminus) + μ[|C] Pplus :=
      measure_union_le _ _
    _ ≤ (μ[|C] (Uminus ∪ Uplus) + μ[|C] Pminus) + μ[|C] Pplus := by
      gcongr
      exact measure_union_le _ _
    _ ≤ ((μ[|C] Uminus + μ[|C] Uplus) + μ[|C] Pminus) + μ[|C] Pplus := by
      gcongr
      exact measure_union_le _ _
    _ ≤ (ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
        ENNReal.ofReal (Real.exp (-sourceRate m)) +
        (ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
        ENNReal.ofReal (Real.exp (-sourceRate m)) := by
      exact add_le_add (add_le_add (add_le_add hUMinus hUPlus) hPMinus) hPPlus

end Erdos1166.HLOZProp45SourceMirrors
