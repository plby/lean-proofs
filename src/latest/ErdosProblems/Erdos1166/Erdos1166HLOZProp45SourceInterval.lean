/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZProp45SourceClock

/-!
The arbitrary-lower-endpoint, unprimed `Theta^-` part of HLOZ Proposition
4.5.  This file does not claim the `Theta^+` or primed estimates: those are
separate mirror interfaces because they use the upper endpoint `b` and the
shifted deletion.  Here `a` is the interval's lower endpoint, while `m`
continues to control all deviation widths and error rates.
-/

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace Erdos1166.HLOZProp45SourceInterval

open HLOZFoundation HLOZUrn HLOZDecomposition
open HLOZProp45SourceClock

noncomputable def intervalLowCutReal (m a : ℕ) : ℝ :=
  (15 / 16 : ℝ) * a - sourceNearWidth m

noncomputable def intervalSplitCutReal (m a : ℕ) : ℝ :=
  (15 / 16 : ℝ) * a - sourceFarWidth m

noncomputable def intervalLowCut (m a : ℕ) : ℕ :=
  Nat.floor (max (intervalLowCutReal m a) 0)

noncomputable def intervalSplitCut (m a : ℕ) : ℕ :=
  Nat.floor (max (intervalSplitCutReal m a) 0)

/-- Exact analytic conditions needed for the interval lower endpoint.  The
source application proves these uniformly from
`a ≥ m - m^(4/5-ε)`; unlike the original-time helper, no numerical
inequality is an argument of the probability theorem below. -/
structure SourceIntervalScale (m a : ℕ) : Prop where
  one_le_m : 1 ≤ m
  one_le_a : 1 ≤ a
  a_le_m : a ≤ m
  split_le_low : intervalSplitCut m a ≤ intervalLowCut m a
  split_lower : (15 / 31 : ℝ) * a ≤ intervalSplitCut m a
  prop44_le_split : sourceProp44Threshold m ≤ intervalSplitCut m a
  far_linear : 17 * Real.sqrt (m : ℝ) ≤ sourceFarDeviation m / 4

noncomputable def intervalDotIndex (m a : ℕ)
    (profile : Site → ℕ) (x : Site) : ℕ :=
  min (profile x) (intervalLowCut m a)

noncomputable def intervalDotDeviation (m a : ℕ)
    (profile : Site → ℕ) (x : Site) : ℝ :=
  (a : ℝ) - (16 / 15 : ℝ) * intervalDotIndex m a profile x

def intervalDotThetaAt {Ω : Type*} (m a : ℕ) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ) (x : Site) : Set Ω :=
  {ω | a ≤ intervalDotIndex m a profile x + lazyPrefixSum ω x}

def intervalDotThetaEvent {Ω : Type*} (sites : Finset Site) (m a : ℕ)
    (profile : Site → ℕ) (lazyPrefixSum : Ω → Site → ℕ) : Set Ω :=
  ⋃ x ∈ sites, intervalDotThetaAt m a profile lazyPrefixSum x

noncomputable def intervalNearCandidates (sites : Finset Site) (m a : ℕ)
    (profile : Site → ℕ) : Finset Site :=
  sites.filter fun x ↦ intervalSplitCut m a ≤ profile x

noncomputable def intervalFarCandidates (sites : Finset Site) (m a : ℕ)
    (profile : Site → ℕ) : Finset Site :=
  sites.filter fun x ↦ profile x < intervalSplitCut m a

noncomputable def intervalProp44Candidates (sites : Finset Site) (m : ℕ)
    (profile : Site → ℕ) : Finset Site :=
  sourceProp44Candidates sites m profile

lemma intervalDotThetaEvent_eq_near_union_far {Ω : Type*}
    (sites : Finset Site) (m a : ℕ) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ) :
    intervalDotThetaEvent sites m a profile lazyPrefixSum =
      (⋃ x ∈ intervalNearCandidates sites m a profile,
        intervalDotThetaAt m a profile lazyPrefixSum x) ∪
      (⋃ x ∈ intervalFarCandidates sites m a profile,
        intervalDotThetaAt m a profile lazyPrefixSum x) := by
  ext ω
  simp only [intervalDotThetaEvent, Set.mem_iUnion, Set.mem_union,
    intervalNearCandidates, intervalFarCandidates, Finset.mem_filter]
  constructor
  · rintro ⟨x, hx, hω⟩
    by_cases hnear : intervalSplitCut m a ≤ profile x
    · exact Or.inl ⟨x, ⟨hx, hnear⟩, hω⟩
    · exact Or.inr ⟨x, ⟨hx, by omega⟩, hω⟩
  · rintro (⟨x, ⟨hx, _⟩, hω⟩ | ⟨x, ⟨hx, _⟩, hω⟩) <;>
      exact ⟨x, hx, hω⟩

lemma intervalNearCandidates_subset_prop44 (m a : ℕ)
    (hs : SourceIntervalScale m a) (sites : Finset Site)
    (profile : Site → ℕ) :
    intervalNearCandidates sites m a profile ⊆
      intervalProp44Candidates sites m profile := by
  intro x hx
  rw [intervalNearCandidates, Finset.mem_filter] at hx
  rw [intervalProp44Candidates, sourceProp44Candidates, Finset.mem_filter]
  exact ⟨hx.1, hs.prop44_le_split.trans (by exact_mod_cast hx.2)⟩

lemma intervalSplitCut_pos (m a : ℕ) (hs : SourceIntervalScale m a) :
    1 ≤ intervalSplitCut m a := by
  have haR : (0 : ℝ) < a := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs.one_le_a)
  have hR : (0 : ℝ) < intervalSplitCut m a :=
    lt_of_lt_of_le (mul_pos (by norm_num) haR) hs.split_lower
  exact_mod_cast hR

lemma intervalLowCutReal_nonneg (m a : ℕ) (hs : SourceIntervalScale m a) :
    0 ≤ intervalLowCutReal m a := by
  have hcut : 0 < intervalLowCut m a :=
    lt_of_lt_of_le Nat.zero_lt_one
      ((intervalSplitCut_pos m a hs).trans hs.split_le_low)
  by_contra h
  have : intervalLowCut m a = 0 := by
    rw [intervalLowCut, max_eq_right (le_of_not_ge h)]
    simp
  omega

lemma intervalSplitCutReal_nonneg (m a : ℕ) (hs : SourceIntervalScale m a) :
    0 ≤ intervalSplitCutReal m a := by
  have hcut : 0 < intervalSplitCut m a :=
    lt_of_lt_of_le Nat.zero_lt_one (intervalSplitCut_pos m a hs)
  by_contra h
  have : intervalSplitCut m a = 0 := by
    rw [intervalSplitCut, max_eq_right (le_of_not_ge h)]
    simp
  omega

lemma intervalLowCut_cast_le_real (m a : ℕ)
    (hreal : 0 ≤ intervalLowCutReal m a) :
    (intervalLowCut m a : ℝ) ≤ intervalLowCutReal m a := by
  rw [intervalLowCut, max_eq_left hreal]
  exact Nat.floor_le hreal

lemma intervalSplitCut_cast_le_real (m a : ℕ)
    (hreal : 0 ≤ intervalSplitCutReal m a) :
    (intervalSplitCut m a : ℝ) ≤ intervalSplitCutReal m a := by
  rw [intervalSplitCut, max_eq_left hreal]
  exact Nat.floor_le hreal

lemma intervalDotIndex_pos (m a : ℕ) (hs : SourceIntervalScale m a)
    (profile : Site → ℕ) {x : Site} (hx : 1 ≤ profile x) :
    1 ≤ intervalDotIndex m a profile x := by
  rw [intervalDotIndex]
  exact le_min hx ((intervalSplitCut_pos m a hs).trans hs.split_le_low)

lemma intervalDotIndex_le_m (m a : ℕ) (hs : SourceIntervalScale m a)
    (profile : Site → ℕ) (x : Site) : intervalDotIndex m a profile x ≤ m := by
  have hreal : max (intervalLowCutReal m a) 0 ≤ (m : ℝ) := by
    apply max_le
    · rw [intervalLowCutReal, sourceNearWidth]
      have hp : 0 ≤ (m : ℝ) ^ (1 - sourceKappa) := by positivity
      have haR : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hs.a_le_m
      nlinarith
    · positivity
  have hcut : intervalLowCut m a ≤ m := by
    have hf : (intervalLowCut m a : ℝ) ≤ (m : ℝ) := by
      rw [intervalLowCut]
      exact (Nat.floor_le (by positivity)).trans hreal
    exact_mod_cast hf
  exact (min_le_right _ _).trans hcut

lemma intervalDotDeviation_nonneg (m a : ℕ) (hs : SourceIntervalScale m a)
    (profile : Site → ℕ) (x : Site) :
    0 ≤ intervalDotDeviation m a profile x := by
  have hreal := intervalLowCutReal_nonneg m a hs
  have hi : (intervalDotIndex m a profile x : ℝ) ≤ intervalLowCutReal m a :=
    (by exact_mod_cast min_le_right (profile x) (intervalLowCut m a) :
      (intervalDotIndex m a profile x : ℝ) ≤ intervalLowCut m a) |>.trans
        (intervalLowCut_cast_le_real m a hreal)
  rw [intervalDotDeviation]
  rw [intervalLowCutReal, sourceNearWidth] at hi
  have hp : 0 ≤ (m : ℝ) ^ (1 - sourceKappa) := by positivity
  nlinarith

lemma intervalDotThetaAt_eq_upperDeviation {Ω : Type*}
    (m a : ℕ) (profile : Site → ℕ) (lazyPrefixSum : Ω → Site → ℕ) (x : Site) :
    intervalDotThetaAt m a profile lazyPrefixSum x =
      {ω | (intervalDotIndex m a profile x : ℝ) / 15 +
        intervalDotDeviation m a profile x ≤ lazyPrefixSum ω x} := by
  ext ω
  simp only [intervalDotThetaAt, Set.mem_setOf_eq, intervalDotDeviation]
  constructor
  · intro h
    have hR : (a : ℝ) ≤ intervalDotIndex m a profile x + lazyPrefixSum ω x := by
      exact_mod_cast h
    norm_num at hR ⊢
    nlinarith
  · intro h
    have hR : (a : ℝ) ≤ intervalDotIndex m a profile x + lazyPrefixSum ω x := by
      norm_num at h ⊢
      nlinarith
    exact_mod_cast hR

lemma intervalNear_deviation_le_index (m a : ℕ)
    (hs : SourceIntervalScale m a) (sites : Finset Site)
    (profile : Site → ℕ) {x : Site}
    (hx : x ∈ intervalNearCandidates sites m a profile) :
    intervalDotDeviation m a profile x ≤ intervalDotIndex m a profile x := by
  have hxprof : intervalSplitCut m a ≤ profile x :=
    (Finset.mem_filter.mp hx).2
  have hilow : intervalSplitCut m a ≤ intervalDotIndex m a profile x := by
    rw [intervalDotIndex]
    exact le_min hxprof hs.split_le_low
  have hiR : (15 / 31 : ℝ) * a ≤ intervalDotIndex m a profile x :=
    hs.split_lower.trans (by exact_mod_cast hilow)
  rw [intervalDotDeviation]
  nlinarith

lemma intervalNear_deviation_ge (m a : ℕ)
    (hs : SourceIntervalScale m a) (sites : Finset Site)
    (profile : Site → ℕ) {x : Site}
    (_hx : x ∈ intervalNearCandidates sites m a profile) :
    sourceNearDeviation m ≤ intervalDotDeviation m a profile x := by
  have hreal := intervalLowCutReal_nonneg m a hs
  have hi : (intervalDotIndex m a profile x : ℝ) ≤ intervalLowCutReal m a :=
    (by exact_mod_cast min_le_right (profile x) (intervalLowCut m a) :
      (intervalDotIndex m a profile x : ℝ) ≤ intervalLowCut m a) |>.trans
        (intervalLowCut_cast_le_real m a hreal)
  rw [intervalLowCutReal, sourceNearWidth] at hi
  rw [sourceNearDeviation, intervalDotDeviation, sourceNearWidth]
  nlinarith

lemma intervalNear_exponent (m a : ℕ) (hs : SourceIntervalScale m a)
    (sites : Finset Site) (profile : Site → ℕ) {x : Site}
    (hx : x ∈ intervalNearCandidates sites m a profile) :
    17 * sourceRate m ≤ intervalDotDeviation m a profile x ^ 2 /
      (4 * (intervalDotIndex m a profile x : ℝ)) := by
  have hxprof : 1 ≤ profile x := by
    have hp := (Finset.mem_filter.mp hx).2
    exact (intervalSplitCut_pos m a hs).trans hp
  have hiPos : (0 : ℝ) < intervalDotIndex m a profile x := by
    exact_mod_cast intervalDotIndex_pos m a hs profile hxprof
  have hiM : (intervalDotIndex m a profile x : ℝ) ≤ m := by
    exact_mod_cast intervalDotIndex_le_m m a hs profile x
  have hd0 := intervalDotDeviation_nonneg m a hs profile x
  have hdev := intervalNear_deviation_ge m a hs sites profile hx
  have hnear0 : 0 ≤ sourceNearDeviation m := by
    rw [sourceNearDeviation, sourceNearWidth]
    positivity
  have hsq : sourceNearDeviation m ^ 2 ≤ intervalDotDeviation m a profile x ^ 2 := by
    nlinarith [sq_nonneg (intervalDotDeviation m a profile x - sourceNearDeviation m)]
  calc
    17 * sourceRate m ≤ sourceNearDeviation m ^ 2 / (4 * (m : ℝ)) :=
      sourceNearExponentBase m hs.one_le_m
    _ ≤ intervalDotDeviation m a profile x ^ 2 / (4 * (m : ℝ)) := by
      gcongr
    _ ≤ intervalDotDeviation m a profile x ^ 2 /
        (4 * (intervalDotIndex m a profile x : ℝ)) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by gcongr)

lemma intervalFar_index_eq_profile (m a : ℕ) (hs : SourceIntervalScale m a)
    (sites : Finset Site) (profile : Site → ℕ) {x : Site}
    (hx : x ∈ intervalFarCandidates sites m a profile) :
    intervalDotIndex m a profile x = profile x := by
  rw [intervalDotIndex, min_eq_left]
  exact (le_of_lt (Finset.mem_filter.mp hx).2).trans hs.split_le_low

lemma intervalFar_deviation_ge (m a : ℕ) (hs : SourceIntervalScale m a)
    (sites : Finset Site) (profile : Site → ℕ) {x : Site}
    (hx : x ∈ intervalFarCandidates sites m a profile) :
    sourceFarDeviation m ≤ intervalDotDeviation m a profile x := by
  have hsplit := intervalSplitCutReal_nonneg m a hs
  have hprof : (profile x : ℝ) < intervalSplitCutReal m a :=
    (by exact_mod_cast (Finset.mem_filter.mp hx).2 :
      (profile x : ℝ) < intervalSplitCut m a) |>.trans_le
        (intervalSplitCut_cast_le_real m a hsplit)
  rw [intervalDotDeviation, intervalFar_index_eq_profile m a hs sites profile hx]
  rw [intervalSplitCutReal, sourceFarWidth] at hprof
  rw [sourceFarDeviation, sourceFarWidth]
  nlinarith

lemma intervalFar_exponent_quadratic (m a : ℕ)
    (hs : SourceIntervalScale m a) (sites : Finset Site)
    (profile : Site → ℕ) {x : Site}
    (hx : x ∈ intervalFarCandidates sites m a profile)
    (hxpos : 1 ≤ profile x) :
    17 * Real.sqrt (m : ℝ) ≤ intervalDotDeviation m a profile x ^ 2 /
      (4 * (intervalDotIndex m a profile x : ℝ)) := by
  have hiPos : (0 : ℝ) < intervalDotIndex m a profile x := by
    exact_mod_cast intervalDotIndex_pos m a hs profile hxpos
  have hiM : (intervalDotIndex m a profile x : ℝ) ≤ m := by
    exact_mod_cast intervalDotIndex_le_m m a hs profile x
  have hd0 := intervalDotDeviation_nonneg m a hs profile x
  have hdev := intervalFar_deviation_ge m a hs sites profile hx
  have hfar0 : 0 ≤ sourceFarDeviation m := by
    rw [sourceFarDeviation, sourceFarWidth]
    positivity
  have hsq : sourceFarDeviation m ^ 2 ≤ intervalDotDeviation m a profile x ^ 2 := by
    nlinarith [sq_nonneg (intervalDotDeviation m a profile x - sourceFarDeviation m)]
  calc
    17 * Real.sqrt (m : ℝ) ≤ sourceFarDeviation m ^ 2 / (4 * (m : ℝ)) :=
      sourceFarQuadraticBase m hs.one_le_m
    _ ≤ intervalDotDeviation m a profile x ^ 2 / (4 * (m : ℝ)) := by
      gcongr
    _ ≤ intervalDotDeviation m a profile x ^ 2 /
        (4 * (intervalDotIndex m a profile x : ℝ)) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by gcongr)

theorem cond_intervalNearAt_le_exp_seventeen
    {Ω : Type*} [MeasurableSpace Ω]
    (m a : ℕ) (hs : SourceIntervalScale m a) (μ : Measure Ω) (C : Set Ω)
    (sites : Finset Site) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ) {x : Site}
    (hx : x ∈ intervalNearCandidates sites m a profile)
    (hpositive : 1 ≤ profile x)
    (hLaw : HasLaw (fun ω ↦ lazyPrefixSum ω x)
      (negBinMeasure (intervalDotIndex m a profile x)) μ[|C]) :
    μ[|C] (intervalDotThetaAt m a profile lazyPrefixSum x) ≤
      ENNReal.ofReal (Real.exp (-17 * sourceRate m)) := by
  rw [intervalDotThetaAt_eq_upperDeviation]
  calc
    μ[|C] {ω | (intervalDotIndex m a profile x : ℝ) / 15 +
        intervalDotDeviation m a profile x ≤ lazyPrefixSum ω x} ≤
        ENNReal.ofReal (Real.exp
          (-(intervalDotDeviation m a profile x ^ 2 /
            (4 * (intervalDotIndex m a profile x : ℝ))))) :=
      HLOZProp45Theta.hasLaw_negBin_upperDeviation_le_exp
        (fun ω ↦ lazyPrefixSum ω x)
        (intervalDotIndex_pos m a hs profile hpositive)
        (intervalDotDeviation m a profile x)
        (intervalDotDeviation_nonneg m a hs profile x)
        (intervalNear_deviation_le_index m a hs sites profile hx) hLaw
    _ ≤ ENNReal.ofReal (Real.exp (-17 * sourceRate m)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h := neg_le_neg (intervalNear_exponent m a hs sites profile hx)
      nlinarith

theorem cond_intervalFarAt_le_exp_seventeen
    {Ω : Type*} [MeasurableSpace Ω]
    (m a : ℕ) (hs : SourceIntervalScale m a) (μ : Measure Ω) (C : Set Ω)
    (sites : Finset Site) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ) {x : Site}
    (hx : x ∈ intervalFarCandidates sites m a profile)
    (hpositive : 1 ≤ profile x)
    (hLaw : HasLaw (fun ω ↦ lazyPrefixSum ω x)
      (negBinMeasure (intervalDotIndex m a profile x)) μ[|C]) :
    μ[|C] (intervalDotThetaAt m a profile lazyPrefixSum x) ≤
      ENNReal.ofReal (Real.exp (-17 * Real.sqrt (m : ℝ))) := by
  rw [intervalDotThetaAt_eq_upperDeviation]
  let d := intervalDotDeviation m a profile x
  let i := intervalDotIndex m a profile x
  have hi : 1 ≤ i := intervalDotIndex_pos m a hs profile hpositive
  have hd0 : 0 ≤ d := intervalDotDeviation_nonneg m a hs profile x
  rcases le_total d (i : ℝ) with hdi | hid
  · calc
      μ[|C] {ω | (i : ℝ) / 15 + d ≤ lazyPrefixSum ω x} ≤
          ENNReal.ofReal (Real.exp (-(d ^ 2 / (4 * (i : ℝ))))) :=
        HLOZProp45Theta.hasLaw_negBin_upperDeviation_le_exp
          (fun ω ↦ lazyPrefixSum ω x) hi d hd0 hdi hLaw
      _ ≤ ENNReal.ofReal (Real.exp (-17 * Real.sqrt (m : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have h := neg_le_neg
          (intervalFar_exponent_quadratic m a hs sites profile hx hpositive)
        dsimp only [d, i]
        nlinarith
  · calc
      μ[|C] {ω | (i : ℝ) / 15 + d ≤ lazyPrefixSum ω x} ≤
          ENNReal.ofReal (Real.exp (-d / 4)) :=
        hasLaw_negBin_upperDeviation_le_exp_linear
          (fun ω ↦ lazyPrefixSum ω x) hi d hid hLaw
      _ ≤ ENNReal.ofReal (Real.exp (-17 * Real.sqrt (m : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hmain : 17 * Real.sqrt (m : ℝ) ≤ d / 4 := calc
          17 * Real.sqrt (m : ℝ) ≤ sourceFarDeviation m / 4 := hs.far_linear
          _ ≤ d / 4 := div_le_div_of_nonneg_right
            (intervalFar_deviation_ge m a hs sites profile hx) (by norm_num)
        nlinarith

/-- The zero-coordinate negative-binomial law is concentrated at zero. -/
lemma negBinMeasure_zero_upper_nat (a : ℕ) (ha : 1 ≤ a) :
    negBinMeasure 0 {j : ℕ | a ≤ j} = 0 := by
  rw [negBinMeasure, Measure.map_apply (measurable_runSum 0)
    MeasurableSet.of_discrete]
  have hpre : runSum 0 ⁻¹' {j : ℕ | a ≤ j} = ∅ := by
    ext g
    simp [runSum, show ¬a ≤ 0 by omega]
  rw [hpre, measure_empty]

/-- A zero inverse profile contributes no lower-endpoint bad event.  This is
the missing boundary case that lets Proposition 4.5 avoid assuming every
site in the horizon box has positive inverse profile. -/
lemma cond_intervalDotThetaAt_eq_zero_of_profile_eq_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (m a : ℕ) (hs : SourceIntervalScale m a)
    (μ : Measure Ω) (C : Set Ω) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ) (x : Site)
    (hxzero : profile x = 0)
    (hLaw : HasLaw (fun ω ↦ lazyPrefixSum ω x)
      (negBinMeasure (intervalDotIndex m a profile x)) μ[|C]) :
    μ[|C] (intervalDotThetaAt m a profile lazyPrefixSum x) = 0 := by
  have hindex : intervalDotIndex m a profile x = 0 := by
    simp [intervalDotIndex, hxzero]
  simp only [intervalDotThetaAt, hindex, zero_add]
  calc
    μ[|C] {ω | a ≤ lazyPrefixSum ω x} =
        negBinMeasure 0 {j : ℕ | a ≤ j} := by
      simpa only [hindex] using hLaw.measure_eq MeasurableSet.of_discrete
    _ = 0 := negBinMeasure_zero_upper_nat a hs.one_le_a

theorem cond_intervalDotTheta_le_two_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (m a : ℕ) (hs : SourceIntervalScale m a) (μ : Measure Ω) (C : Set Ω)
    (sites : Finset Site) (profile : Site → ℕ)
    (lazyPrefixSum : Ω → Site → ℕ)
    (hProp44Card : ((intervalProp44Candidates sites m profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m))
    (hHorizonCard : (sites.card : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hLaw : ∀ x ∈ sites,
      HasLaw (fun ω ↦ lazyPrefixSum ω x)
        (negBinMeasure (intervalDotIndex m a profile x)) μ[|C]) :
    μ[|C] (intervalDotThetaEvent sites m a profile lazyPrefixSum) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
  let near := intervalNearCandidates sites m a profile
  let far := intervalFarCandidates sites m a profile
  let E := intervalDotThetaAt m a profile lazyPrefixSum
  have hnearCard : (near.card : ℝ) ≤ Real.exp (16 * sourceRate m) := by
    calc
      (near.card : ℝ) ≤ ((intervalProp44Candidates sites m profile).card : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (intervalNearCandidates_subset_prop44 m a hs sites profile)
      _ ≤ Real.exp (16 * sourceRate m) := hProp44Card
  have hnear : μ[|C] (⋃ x ∈ near, E x) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) := by
    apply HLOZProp45Union.finite_union_exp_sixteen_seventeen
      μ[|C] near E _ (sourceRate m) Set.Subset.rfl hnearCard
    intro x hx
    have hx' : x ∈ intervalNearCandidates sites m a profile := by simpa [near] using hx
    have hxsite : x ∈ sites := (Finset.mem_filter.mp hx').1
    have hxpositive : 1 ≤ profile x :=
      (intervalSplitCut_pos m a hs).trans (Finset.mem_filter.mp hx').2
    exact cond_intervalNearAt_le_exp_seventeen m a hs μ C sites profile
      lazyPrefixSum hx' hxpositive (hLaw x hxsite)
  have hfarCard : (far.card : ℝ) ≤ Real.exp (16 * Real.sqrt (m : ℝ)) := by
    calc
      (far.card : ℝ) ≤ (sites.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ Real.exp (16 * Real.sqrt (m : ℝ)) := hHorizonCard
  have hfar : μ[|C] (⋃ x ∈ far, E x) ≤
      ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
    apply HLOZProp45Union.finite_union_exp_sixteen_seventeen
      μ[|C] far E _ (Real.sqrt (m : ℝ)) Set.Subset.rfl hfarCard
    intro x hx
    have hx' : x ∈ intervalFarCandidates sites m a profile := by simpa [far] using hx
    have hxsite : x ∈ sites := (Finset.mem_filter.mp hx').1
    by_cases hxpositive : 1 ≤ profile x
    · exact cond_intervalFarAt_le_exp_seventeen m a hs μ C sites profile
        lazyPrefixSum hx' hxpositive (hLaw x hxsite)
    · have hxzero : profile x = 0 := by omega
      rw [cond_intervalDotThetaAt_eq_zero_of_profile_eq_zero
        m a hs μ C profile lazyPrefixSum x hxzero (hLaw x hxsite)]
      exact bot_le
  rw [intervalDotThetaEvent_eq_near_union_far]
  calc
    μ[|C] ((⋃ x ∈ near, E x) ∪ (⋃ x ∈ far, E x)) ≤
        μ[|C] (⋃ x ∈ near, E x) + μ[|C] (⋃ x ∈ far, E x) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := add_le_add hnear hfar

/-! ### Concrete inverse-clock and stopped-time interval interface -/

def intervalCanonicalDotThetaEvent (q : ℕ) (sites : Finset Site)
    (m a : ℕ) (profile : Site → ℕ) : Set (ℕ → Site) :=
  intervalDotThetaEvent sites m a profile fun s x ↦
    inverseClockHoldingPrefix s q (intervalDotIndex m a profile x) x

def intervalStoppedThetaMinusAt (m a k : ℕ) (x : Site) : Set (ℕ → Site) :=
  {s | paperExternalLocalTime s (favoriteCreationHorizon m k s) x ≤
      intervalLowCut m a ∧ a ≤ localTime s (favoriteCreationHorizon m k s) x}

def intervalStoppedThetaMinusEvent
    (sites : Finset Site) (m a k : ℕ) : Set (ℕ → Site) :=
  ⋃ x ∈ sites, intervalStoppedThetaMinusAt m a k x

def intervalClockPrefixCompatibleEvent
    (q : ℕ) (sites : Finset Site) (m a k : ℕ)
    (profile : Site → ℕ) : Set (ℕ → Site) :=
  {s | ∀ x ∈ sites, SourceClockPrefixCompatibleAt s
    (favoriteCreationHorizon m k s) q (intervalDotIndex m a profile x) x}

theorem intervalStoppedThetaMinus_subset_canonicalDotTheta
    (q : ℕ) (sites : Finset Site) (m a k : ℕ) (profile : Site → ℕ) :
    intervalStoppedThetaMinusEvent sites m a k ∩
        inverseClockProfileAtom q sites profile ∩
        intervalClockPrefixCompatibleEvent q sites m a k profile ⊆
      intervalCanonicalDotThetaEvent q sites m a profile := by
  intro s hs
  rcases hs with ⟨⟨hsTheta, hsProfile⟩, hsCompat⟩
  simp only [intervalStoppedThetaMinusEvent, Set.mem_iUnion] at hsTheta
  rcases hsTheta with ⟨x, hxsite, hxTheta⟩
  rw [intervalCanonicalDotThetaEvent, intervalDotThetaEvent]
  simp only [Set.mem_iUnion]
  refine ⟨x, hxsite, ?_⟩
  change a ≤ intervalDotIndex m a profile x +
    inverseClockHoldingPrefix s q (intervalDotIndex m a profile x) x
  have hprofile : inverseClockProfile s q x = profile x := hsProfile x hxsite
  have hcompat := hsCompat x hxsite
  have hext : paperExternalLocalTime s (favoriteCreationHorizon m k s) x ≤
      intervalDotIndex m a profile x := by
    rw [intervalDotIndex]
    apply le_min
    · simpa only [hprofile] using hcompat.1
    · exact hxTheta.1
  have hlazy := hcompat.2
  have hdecomp := localTime_eq_paperExternal_add_paperLazy
    s (favoriteCreationHorizon m k s) x
  calc
    a ≤ localTime s (favoriteCreationHorizon m k s) x := hxTheta.2
    _ = paperExternalLocalTime s (favoriteCreationHorizon m k s) x +
        paperLazyLocalTime s (favoriteCreationHorizon m k s) x := hdecomp
    _ ≤ intervalDotIndex m a profile x +
        inverseClockHoldingPrefix s q (intervalDotIndex m a profile x) x :=
      Nat.add_le_add hext hlazy

theorem cond_inter_intervalStoppedThetaMinus_le_two_scale
    (q m a k : ℕ) (hs : SourceIntervalScale m a)
    (μ : Measure (ℕ → Site)) (C H : Set (ℕ → Site))
    (sites : Finset Site) (profile : Site → ℕ)
    (hStoppedSubset :
      C ∩ H ∩ intervalStoppedThetaMinusEvent sites m a k ⊆
        intervalCanonicalDotThetaEvent q sites m a profile)
    (hProp44Card : ((intervalProp44Candidates sites m profile).card : ℝ) ≤
      Real.exp (16 * sourceRate m))
    (hHorizonCard : (sites.card : ℝ) ≤ Real.exp (16 * Real.sqrt (m : ℝ)))
    (hLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q
        (intervalDotIndex m a profile x) x)
        (negBinMeasure (intervalDotIndex m a profile x)) μ[|C]) :
    μ[|C] (C ∩ H ∩ intervalStoppedThetaMinusEvent sites m a k) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
  calc
    μ[|C] (C ∩ H ∩ intervalStoppedThetaMinusEvent sites m a k) ≤
        μ[|C] (intervalCanonicalDotThetaEvent q sites m a profile) := by
      exact measure_mono hStoppedSubset
    _ ≤ ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
      exact cond_intervalDotTheta_le_two_scale m a hs μ C sites profile
        (fun s x ↦ inverseClockHoldingPrefix s q
          (intervalDotIndex m a profile x) x)
        hProp44Card hHorizonCard hLaw

end Erdos1166.HLOZProp45SourceInterval
