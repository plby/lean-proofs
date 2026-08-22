/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.LazyDecomposition

/-!
# Counting externally thick sites

This file formalizes the Tonelli--Markov counting argument behind HLOZ
Proposition 4.4.  For a random finite visited set `V` and one-site events
`large x`, suppose that, uniformly in `x`,

`μ ({x ∈ V} ∩ large x) ≤ q * μ {x ∈ V}`.

Then the expected number of large visited sites is at most `q` times the
expected number of visited sites.  Markov's inequality consequently bounds
the probability of seeing at least `J` such sites by `q * R / J` whenever the
expected visited-set cardinality is at most `R`.

The theorem is stated for a countable site space, not for a preselected
finite box.  Since every realized visited set is finite, Tonelli's theorem
reduces the countable sum pointwise to a finite sum.

The final section specializes the bookkeeping to both HLOZ deletion
orientations in `LazyDecomposition`.  It proves measurability and the
deterministic expectation bound `n + 1`.  The remaining input is precisely
the weighted one-site external-local-time estimate.  In the HLOZ proof this
comes from the external-chain local central limit theorem, translation at the
first hit, and the strong Markov property; no such estimate is asserted here.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.ExternalThickCount

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Random finite sets and their candidate counts -/

variable {Ω Site : Type*}

/-- The event that a site belongs to a random finite visited set. -/
def memberEvent (visited : Ω → Finset Site) (x : Site) : Set Ω :=
  {ω | x ∈ visited ω}

/-- A site is a candidate when it has been visited and its one-site large
event occurs. -/
def candidateEvent (visited : Ω → Finset Site) (large : Site → Set Ω)
    (x : Site) : Set Ω :=
  memberEvent visited x ∩ large x

/-- Number of sites in the random visited set satisfying `large`. -/
def candidateCount [DecidableEq Site]
    (visited : Ω → Finset Site) (large : Site → Set Ω) (ω : Ω) : ℕ :=
  ((visited ω).filter fun x ↦ ω ∈ large x).card

section Pointwise

variable [DecidableEq Site]

/- A finite-set cardinality is the countable sum of its membership
indicators.  The sum has finite support for each `ω`. -/
omit [DecidableEq Site] in
lemma ennreal_card_eq_tsum_memberIndicator (visited : Ω → Finset Site) (ω : Ω) :
    ((visited ω).card : ℝ≥0∞) =
      ∑' x, (memberEvent visited x).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  rw [tsum_eq_sum (s := visited ω)]
  · calc
      ((visited ω).card : ℝ≥0∞) = ∑ x ∈ visited ω, (1 : ℝ≥0∞) := by simp
      _ = ∑ x ∈ visited ω,
          (memberEvent visited x).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [memberEvent, Set.indicator, hx]
  · intro x hx
    simp [memberEvent, Set.indicator, hx]

/-- The candidate count is the countable sum of the candidate-event
indicators, again with finite support pointwise. -/
lemma ennreal_candidateCount_eq_tsum_indicator
    (visited : Ω → Finset Site) (large : Site → Set Ω) (ω : Ω) :
    (candidateCount visited large ω : ℝ≥0∞) =
      ∑' x, (candidateEvent visited large x).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  rw [tsum_eq_sum (s := (visited ω).filter fun x ↦ ω ∈ large x)]
  · calc
      (candidateCount visited large ω : ℝ≥0∞) =
          ∑ x ∈ (visited ω).filter (fun x ↦ ω ∈ large x), (1 : ℝ≥0∞) := by
        simp [candidateCount]
      _ = ∑ x ∈ (visited ω).filter (fun x ↦ ω ∈ large x),
          (candidateEvent visited large x).indicator
            (fun _ ↦ (1 : ℝ≥0∞)) ω := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        simp [candidateEvent, memberEvent, Set.indicator, hx'.1, hx'.2]
  · intro x hx
    simp only [Finset.mem_filter, not_and_or] at hx
    rcases hx with hx | hx
    · simp [candidateEvent, memberEvent, Set.indicator, hx]
    · simp [candidateEvent, memberEvent, Set.indicator, hx]

end Pointwise

section Tonelli

variable [MeasurableSpace Ω] [Countable Site] [DecidableEq Site]

omit [DecidableEq Site] in
lemma measurable_ennreal_card
    (visited : Ω → Finset Site)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x)) :
    Measurable fun ω ↦ ((visited ω).card : ℝ≥0∞) := by
  rw [show (fun ω ↦ ((visited ω).card : ℝ≥0∞)) = fun ω ↦
      ∑' x, (memberEvent visited x).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω by
    funext ω
    exact ennreal_card_eq_tsum_memberIndicator visited ω]
  exact Measurable.tsum fun x ↦ measurable_const.indicator (hvisited x)

lemma measurable_candidateCount
    (visited : Ω → Finset Site) (large : Site → Set Ω)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x)) :
    Measurable fun ω ↦ (candidateCount visited large ω : ℝ≥0∞) := by
  rw [show (fun ω ↦ (candidateCount visited large ω : ℝ≥0∞)) = fun ω ↦
      ∑' x, (candidateEvent visited large x).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) ω by
    funext ω
    exact ennreal_candidateCount_eq_tsum_indicator visited large ω]
  exact Measurable.tsum fun x ↦ measurable_const.indicator
    ((hvisited x).inter (hlarge x))

/- The expected cardinality of a random finite set is the sum of its
one-site membership probabilities. -/
omit [DecidableEq Site] in
lemma lintegral_card_eq_tsum_measure_member
    (μ : Measure Ω) (visited : Ω → Finset Site)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x)) :
    ∫⁻ ω, ((visited ω).card : ℝ≥0∞) ∂μ =
      ∑' x, μ (memberEvent visited x) := by
  rw [show (fun ω ↦ ((visited ω).card : ℝ≥0∞)) = fun ω ↦
      ∑' x, (memberEvent visited x).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω by
    funext ω
    exact ennreal_card_eq_tsum_memberIndicator visited ω]
  calc
    (∫⁻ ω, ∑' x, (memberEvent visited x).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) ω ∂μ) =
        ∑' x, ∫⁻ ω, (memberEvent visited x).indicator
          (fun _ ↦ (1 : ℝ≥0∞)) ω ∂μ :=
      lintegral_tsum fun x ↦ (measurable_const.indicator (hvisited x)).aemeasurable
    _ = ∑' x, μ (memberEvent visited x) := by
      congr 1
      funext x
      exact lintegral_indicator_one (hvisited x)

/-- The expected candidate count is the sum of the one-site candidate
probabilities. -/
lemma lintegral_candidateCount_eq_tsum
    (μ : Measure Ω) (visited : Ω → Finset Site) (large : Site → Set Ω)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x)) :
    ∫⁻ ω, (candidateCount visited large ω : ℝ≥0∞) ∂μ =
      ∑' x, μ (candidateEvent visited large x) := by
  rw [show (fun ω ↦ (candidateCount visited large ω : ℝ≥0∞)) = fun ω ↦
      ∑' x, (candidateEvent visited large x).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) ω by
    funext ω
    exact ennreal_candidateCount_eq_tsum_indicator visited large ω]
  calc
    (∫⁻ ω, ∑' x, (candidateEvent visited large x).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) ω ∂μ) =
        ∑' x, ∫⁻ ω, (candidateEvent visited large x).indicator
          (fun _ ↦ (1 : ℝ≥0∞)) ω ∂μ := by
      apply lintegral_tsum
      intro x
      exact (measurable_const.indicator
        ((hvisited x).inter (hlarge x))).aemeasurable
    _ = ∑' x, μ (candidateEvent visited large x) := by
      congr 1
      funext x
      exact lintegral_indicator_one ((hvisited x).inter (hlarge x))

/-! ## The Tonelli--Markov reduction -/

/-- The uniform weighted one-site tail lifts to an expectation bound for the
whole candidate count.  This is the Tonelli step of HLOZ Proposition 4.4. -/
theorem lintegral_candidateCount_le_mul
    (μ : Measure Ω) (visited : Ω → Finset Site) (large : Site → Set Ω)
    (q : ℝ≥0∞)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x))
    (hweightedOneSite : ∀ x,
      μ (candidateEvent visited large x) ≤ q * μ (memberEvent visited x)) :
    (∫⁻ ω, (candidateCount visited large ω : ℝ≥0∞) ∂μ) ≤
      q * ∫⁻ ω, ((visited ω).card : ℝ≥0∞) ∂μ := by
  rw [lintegral_candidateCount_eq_tsum μ visited large hvisited hlarge,
    lintegral_card_eq_tsum_measure_member μ visited hvisited]
  calc
    ∑' x, μ (candidateEvent visited large x) ≤
        ∑' x, q * μ (memberEvent visited x) :=
      ENNReal.summable.tsum_le_tsum hweightedOneSite ENNReal.summable
    _ = q * ∑' x, μ (memberEvent visited x) := ENNReal.tsum_mul_left

/-- **External-thick candidate count bound.**  A weighted uniform one-site
tail, together with an expected visited-site bound, controls the probability
of at least `J` candidates.

The weighting by `μ {x ∈ visited}` is the exact form obtained by restarting
the walk at its first visit to `x`. -/
theorem measure_candidateCount_ge_le
    (μ : Measure Ω) (visited : Ω → Finset Site) (large : Site → Set Ω)
    (q R : ℝ≥0∞) (J : ℕ) (hJ : 0 < J)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x))
    (hweightedOneSite : ∀ x,
      μ (candidateEvent visited large x) ≤ q * μ (memberEvent visited x))
    (hvisitExpectation :
      ∫⁻ ω, ((visited ω).card : ℝ≥0∞) ∂μ ≤ R) :
    μ {ω | J ≤ candidateCount visited large ω} ≤ q * R / J := by
  let candidateMass : Ω → ℝ≥0∞ :=
    fun ω ↦ (candidateCount visited large ω : ℝ≥0∞)
  have hcandidateMeas : Measurable candidateMass :=
    measurable_candidateCount visited large hvisited hlarge
  have hmarkov : μ {ω | (J : ℝ≥0∞) ≤ candidateMass ω} ≤
      (∫⁻ ω, candidateMass ω ∂μ) / J := by
    apply meas_ge_le_lintegral_div hcandidateMeas.aemeasurable
    · exact_mod_cast hJ.ne'
    · simp
  have hintegral : ∫⁻ ω, candidateMass ω ∂μ ≤ q * R := by
    calc
      (∫⁻ ω, candidateMass ω ∂μ) ≤
          q * ∫⁻ ω, ((visited ω).card : ℝ≥0∞) ∂μ :=
        lintegral_candidateCount_le_mul μ visited large q hvisited hlarge hweightedOneSite
      _ ≤ q * R := by gcongr
  have hset : {ω | J ≤ candidateCount visited large ω} =
      {ω | (J : ℝ≥0∞) ≤ candidateMass ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, candidateMass]
    norm_cast
  rw [hset]
  exact hmarkov.trans (ENNReal.div_le_div_right hintegral _)

/-- Strict-tail version with the same positive threshold in the denominator. -/
theorem measure_candidateCount_gt_le
    (μ : Measure Ω) (visited : Ω → Finset Site) (large : Site → Set Ω)
    (q R : ℝ≥0∞) (J : ℕ) (hJ : 0 < J)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x))
    (hweightedOneSite : ∀ x,
      μ (candidateEvent visited large x) ≤ q * μ (memberEvent visited x))
    (hvisitExpectation :
      ∫⁻ ω, ((visited ω).card : ℝ≥0∞) ∂μ ≤ R) :
    μ {ω | J < candidateCount visited large ω} ≤ q * R / J := by
  refine (measure_mono ?_).trans (measure_candidateCount_ge_le μ visited large q R J hJ
    hvisited hlarge hweightedOneSite hvisitExpectation)
  intro ω hω
  change J < candidateCount visited large ω at hω
  change J ≤ candidateCount visited large ω
  exact hω.le

/-- A sharper strict-tail form, using `J+1` in the denominator. -/
theorem measure_candidateCount_gt_le_succ
    (μ : Measure Ω) (visited : Ω → Finset Site) (large : Site → Set Ω)
    (q R : ℝ≥0∞) (J : ℕ)
    (hvisited : ∀ x, MeasurableSet (memberEvent visited x))
    (hlarge : ∀ x, MeasurableSet (large x))
    (hweightedOneSite : ∀ x,
      μ (candidateEvent visited large x) ≤ q * μ (memberEvent visited x))
    (hvisitExpectation :
      ∫⁻ ω, ((visited ω).card : ℝ≥0∞) ∂μ ≤ R) :
    μ {ω | J < candidateCount visited large ω} ≤
      q * R / (↑(J + 1) : ℝ≥0∞) := by
  simpa only [Nat.succ_le_iff] using
    measure_candidateCount_ge_le μ visited large q R (J + 1) (by omega)
      hvisited hlarge hweightedOneSite hvisitExpectation

end Tonelli

/-! ## Specialization to the two deleted paths -/

open Erdos1165.LazyDecomposition

/-- The external list used for the two HLOZ orientations.  The shifted
orientation drops time zero before deleting excursions. -/
def orientedExternalPath {n : ℕ} (o : Orientation)
    (u : Fin (n + 1) → Point) : List Point :=
  match o with
  | .even => finiteExternalPath .even u
  | .shifted => shiftedExternalPath u

@[simp] lemma orientedExternalPath_even {n : ℕ} (u : Fin (n + 1) → Point) :
    orientedExternalPath .even u = finiteExternalPath .even u := rfl

@[simp] lemma orientedExternalPath_shifted {n : ℕ} (u : Fin (n + 1) → Point) :
    orientedExternalPath .shifted u = shiftedExternalPath u := rfl

/-- The checkerboard class screened by an orientation. -/
def orientationClass : Orientation → Point → Prop
  | .even => EvenPoint
  | .shifted => OddPoint

@[simp] lemma orientationClass_even : orientationClass .even = EvenPoint := rfl

@[simp] lemma orientationClass_shifted : orientationClass .shifted = OddPoint := rfl

/-- Sites in the appropriate checkerboard class visited by the chosen
external list. -/
def orientedExternalVisitedSites (o : Orientation) (s : WalkPath) (n : ℕ) : Finset Point :=
  (orientedExternalPath o (pathPrefix s n)).toFinset.filter (orientationClass o)

/-- External local time in the appropriate deletion orientation. -/
def orientedExternalLocalTime (o : Orientation) (s : WalkPath) (n : ℕ) (x : Point) : ℕ :=
  listLocalTime (orientedExternalPath o (pathPrefix s n)) x

@[simp] lemma orientedExternalLocalTime_even (s : WalkPath) (n : ℕ) (x : Point) :
    orientedExternalLocalTime .even s n x = externalLocalTime .even s n x := rfl

@[simp] lemma orientedExternalLocalTime_shifted (s : WalkPath) (n : ℕ) (x : Point) :
    orientedExternalLocalTime .shifted s n x = shiftedExternalLocalTimeAt s n x := rfl

/-- Event that the oriented external local time at `x` reaches `threshold`. -/
def orientedLargeEvent (o : Orientation) (n threshold : ℕ) (x : Point) : Set WalkPath :=
  {s | threshold ≤ orientedExternalLocalTime o s n x}

/-- Number of sites in the selected checkerboard class with external local
time at least `threshold`. -/
def orientedExternalThickCount (o : Orientation) (s : WalkPath)
    (n threshold : ℕ) : ℕ :=
  candidateCount (fun s ↦ orientedExternalVisitedSites o s n)
    (orientedLargeEvent o n threshold) s

lemma orientedExternalPath_length_le (o : Orientation)
    {n : ℕ} (u : Fin (n + 1) → Point) :
    (orientedExternalPath o u).length ≤ n + 1 := by
  cases o with
  | even =>
      have h := externalPath_length_add_lazyPoints_length .even (finitePathList u)
      have hle : (externalPath .even (finitePathList u)).length ≤
          (externalPath .even (finitePathList u)).length +
            (lazyPoints .even (finitePathList u)).length := by omega
      rw [h] at hle
      simpa [orientedExternalPath, finiteExternalPath, finitePathList] using hle
  | shifted =>
      have h := externalPath_length_add_lazyPoints_length .shifted (shiftedInput u)
      have hle : (externalPath .shifted (shiftedInput u)).length ≤
          (externalPath .shifted (shiftedInput u)).length +
            (lazyPoints .shifted (shiftedInput u)).length := by omega
      rw [h] at hle
      calc
        (orientedExternalPath .shifted u).length =
            (externalPath .shifted (shiftedInput u)).length := rfl
        _ ≤ (shiftedInput u).length := hle
        _ ≤ n + 1 := by simp [shiftedInput, finitePathList]

lemma orientedExternalVisitedSites_card_le (o : Orientation)
    (s : WalkPath) (n : ℕ) :
    (orientedExternalVisitedSites o s n).card ≤ n + 1 := by
  calc
    (orientedExternalVisitedSites o s n).card ≤
        (orientedExternalPath o (pathPrefix s n)).toFinset.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (orientedExternalPath o (pathPrefix s n)).length := List.toFinset_card_le _
    _ ≤ n + 1 := orientedExternalPath_length_le o (pathPrefix s n)

lemma measurable_orientedExternalVisitedSites (o : Orientation) (n : ℕ) :
    Measurable fun s : WalkPath ↦ orientedExternalVisitedSites o s n := by
  exact (measurable_of_countable fun u : Fin (n + 1) → Point ↦
    (orientedExternalPath o u).toFinset.filter (orientationClass o)).comp
      (measurable_pathPrefix n)

lemma measurableSet_member_orientedExternalVisitedSites
    (o : Orientation) (n : ℕ) (x : Point) :
    MeasurableSet (memberEvent (fun s ↦ orientedExternalVisitedSites o s n) x) := by
  exact measurable_orientedExternalVisitedSites o n
    ((Set.to_countable {v : Finset Point | x ∈ v}).measurableSet)

lemma measurable_orientedExternalLocalTime (o : Orientation) (n : ℕ) (x : Point) :
    Measurable fun s : WalkPath ↦ orientedExternalLocalTime o s n x := by
  exact (measurable_of_countable fun u : Fin (n + 1) → Point ↦
    listLocalTime (orientedExternalPath o u) x).comp (measurable_pathPrefix n)

lemma measurableSet_orientedLargeEvent (o : Orientation) (n threshold : ℕ) (x : Point) :
    MeasurableSet (orientedLargeEvent o n threshold x) := by
  exact measurableSet_le measurable_const (measurable_orientedExternalLocalTime o n x)

/-- The selected external range has expected cardinality at most `n+1` under
the canonical path measure.  No random-walk estimate is needed. -/
theorem lintegral_orientedExternalVisitedSites_card_le (o : Orientation) (n : ℕ) :
    ∫⁻ s, ((orientedExternalVisitedSites o s n).card : ℝ≥0∞) ∂simpleRandomWalk ≤
      (n + 1 : ℕ) := by
  calc
    (∫⁻ s, ((orientedExternalVisitedSites o s n).card : ℝ≥0∞) ∂simpleRandomWalk) ≤
        ∫⁻ _s : WalkPath, (n + 1 : ℕ) ∂simpleRandomWalk := by
      apply lintegral_mono
      intro s
      change ((orientedExternalVisitedSites o s n).card : ℝ≥0∞) ≤
        ((n + 1 : ℕ) : ℝ≥0∞)
      exact_mod_cast orientedExternalVisitedSites_card_le o s n
    _ = (n + 1 : ℕ) := by simp

/-- Canonical-walk specialization of the generic Proposition-4.4 counting
step, valid in either deletion orientation.  The premise
`hweightedOneSite` is the sole missing probabilistic input. -/
theorem measure_orientedExternalThickCount_ge_le
    (o : Orientation) (n threshold J : ℕ) (q : ℝ≥0∞) (hJ : 0 < J)
    (hweightedOneSite : ∀ x,
      simpleRandomWalk
          (candidateEvent (fun s ↦ orientedExternalVisitedSites o s n)
            (orientedLargeEvent o n threshold) x) ≤
        q * simpleRandomWalk
          (memberEvent (fun s ↦ orientedExternalVisitedSites o s n) x)) :
    simpleRandomWalk {s | J ≤ orientedExternalThickCount o s n threshold} ≤
      q * (↑(n + 1) : ℝ≥0∞) / J := by
  exact measure_candidateCount_ge_le simpleRandomWalk
    (fun s ↦ orientedExternalVisitedSites o s n)
    (orientedLargeEvent o n threshold) q (↑(n + 1) : ℝ≥0∞) J hJ
    (measurableSet_member_orientedExternalVisitedSites o n)
    (measurableSet_orientedLargeEvent o n threshold)
    hweightedOneSite (lintegral_orientedExternalVisitedSites_card_le o n)

/-- Strict-tail form matching the `# candidates > budget` event in HLOZ
Proposition 4.4. -/
theorem measure_orientedExternalThickCount_gt_le
    (o : Orientation) (n threshold J : ℕ) (q : ℝ≥0∞) (hJ : 0 < J)
    (hweightedOneSite : ∀ x,
      simpleRandomWalk
          (candidateEvent (fun s ↦ orientedExternalVisitedSites o s n)
            (orientedLargeEvent o n threshold) x) ≤
        q * simpleRandomWalk
          (memberEvent (fun s ↦ orientedExternalVisitedSites o s n) x)) :
    simpleRandomWalk {s | J < orientedExternalThickCount o s n threshold} ≤
      q * (↑(n + 1) : ℝ≥0∞) / J := by
  exact measure_candidateCount_gt_le simpleRandomWalk
    (fun s ↦ orientedExternalVisitedSites o s n)
    (orientedLargeEvent o n threshold) q (↑(n + 1) : ℝ≥0∞) J hJ
    (measurableSet_member_orientedExternalVisitedSites o n)
    (measurableSet_orientedLargeEvent o n threshold)
    hweightedOneSite (lintegral_orientedExternalVisitedSites_card_le o n)

end

end Erdos1165.ExternalThickCount
