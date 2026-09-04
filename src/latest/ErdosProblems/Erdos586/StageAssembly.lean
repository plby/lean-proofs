/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.Core
import ErdosProblems.Erdos586.PrimeStages
import ErdosProblems.Erdos586.FiniteProbability
import ErdosProblems.Erdos586.CongruenceMass
import ErdosProblems.Erdos586.Moments
import ErdosProblems.Erdos586.Sieve

/-!
# Assembly of a concrete prime stage for Erdős Problem 586

This file connects occurrence-indexed congruence systems to the finite
fibre random variables used by the BBMST distortion sieve.  A stage index
contains its membership in the chosen minimal subcover and the proof that
its modulus is newly exposed at the current prime.  Consequently all
divisibility proofs used to define the old and new congruence events are
data, rather than side assumptions.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

attribute [local instance] Classical.propDecidable

private lemma stagePrime_pos_all (r : ℕ) : 0 < stagePrime r := by
  cases r with
  | zero => norm_num [stagePrime]
  | succ r => exact stagePrime_pos (Nat.succ_pos r)

local instance partialPeriod.instNeZero (Q r : ℕ) : NeZero (partialPeriod Q r) :=
  ⟨(partialPeriod_pos Q r).ne'⟩

local instance stagePower.instNeZero (Q r : ℕ) :
    NeZero (stagePrime r ^ stageExponent Q r) :=
  ⟨(pow_pos (stagePrime_pos_all r) _).ne'⟩

/-- Occurrences of the chosen subcover which are exposed at prime stage
`r`.  The subtype retains both facts needed by the moment calculation. -/
abbrev MomentStageIndex (A : CoveringFamily)
    (s : Finset (Fin A.length)) (Q r : ℕ) :=
  {i : Fin A.length // i ∈ s ∧ IsNewModulus Q r (A.get i).modulus}

/-- The old part of the modulus represented by a stage occurrence. -/
def momentStageOldPart {A : CoveringFamily} {s : Finset (Fin A.length)}
    {Q r : ℕ} (i : MomentStageIndex A s Q r) : ℕ :=
  oldPart (A.get i.1).modulus r

/-- The positive exponent of the new stage prime in an occurrence. -/
def momentStageExponent {A : CoveringFamily} {s : Finset (Fin A.length)}
    {Q r : ℕ} (i : MomentStageIndex A s Q r) : ℕ :=
  (A.get i.1).modulus.factorization (stagePrime r)

lemma momentStageExponent_pos {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ}
    (i : MomentStageIndex A s Q r) : 0 < momentStageExponent i :=
  i.2.2.2.2.1

lemma momentStageExponent_le {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ} (hQ : Q ≠ 0)
    (i : MomentStageIndex A s Q r) :
    momentStageExponent i ≤ stageExponent Q r :=
  newModulus_stageExponent_le hQ i.2.2

lemma momentStageOldPart_dvd {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ}
    (i : MomentStageIndex A s Q r) :
    momentStageOldPart i ∣ partialPeriod Q (r - 1) :=
  i.2.2.2.2.2

lemma momentStagePrimePower_dvd {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ} (hQ : Q ≠ 0)
    (i : MomentStageIndex A s Q r) :
    stagePrime r ^ momentStageExponent i ∣
      stagePrime r ^ stageExponent Q r :=
  Nat.pow_dvd_pow _ (momentStageExponent_le hQ i)

/-- Exact factorization of a newly exposed modulus into its old part and
the positive power of the new prime. -/
lemma momentStageModulus_eq {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ} (hQ : Q ≠ 0)
    (i : MomentStageIndex A s Q r) :
    (A.get i.1).modulus = momentStageOldPart i *
      stagePrime r ^ momentStageExponent i := by
  exact (newModulus_eq_oldPart_mul_pow hQ i.2.2).1

/-- The event imposed on the already exposed coordinates by a stage
occurrence. -/
def momentStageOldEvent {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ}
    (i : MomentStageIndex A s Q r) :
    Set (ZMod (partialPeriod Q (r - 1))) :=
  congruenceClass (partialPeriod Q (r - 1)) (momentStageOldPart i)
    (momentStageOldPart_dvd i) (A.get i.1).residue

/-- The event imposed on the newly exposed prime-power coordinate. -/
def momentStageNewEvent {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ} (hQ : Q ≠ 0)
    (i : MomentStageIndex A s Q r) :
    Set (ZMod (stagePrime r ^ stageExponent Q r)) :=
  congruenceClass (stagePrime r ^ stageExponent Q r)
    (stagePrime r ^ momentStageExponent i)
    (momentStagePrimePower_dvd hQ i) (A.get i.1).residue

/-- The product-coordinate congruence class belonging to one occurrence. -/
def momentStageClass {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ} (hQ : Q ≠ 0)
    (i : MomentStageIndex A s Q r) :
    Set (ZMod (partialPeriod Q (r - 1)) ×
      ZMod (stagePrime r ^ stageExponent Q r)) :=
  {z | z.1 ∈ momentStageOldEvent i ∧ z.2 ∈ momentStageNewEvent hQ i}

/-- Union of the newly exposed congruence classes in CRT product
coordinates. -/
def momentStageBadSet (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) :
    Set (ZMod (partialPeriod Q (r - 1)) ×
      ZMod (stagePrime r ^ stageExponent Q r)) :=
  {z | ∃ i : MomentStageIndex A s Q r, z ∈ momentStageClass hQ i}

/-- Reciprocal of the new prime power in a stage modulus. -/
def momentStageCoefficient {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ}
    (i : MomentStageIndex A s Q r) : ℝ :=
  1 / (stagePrime r : ℝ) ^ momentStageExponent i

lemma momentStageCoefficient_nonneg {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ}
    (i : MomentStageIndex A s Q r) : 0 ≤ momentStageCoefficient i := by
  unfold momentStageCoefficient
  positivity

/-- Multiplying the new-coordinate fibre fraction by the uniform mass of
the old congruence class recovers the reciprocal of the complete modulus.
This is the per-occurrence identity used at the initial `2,3,5` stages. -/
lemma momentStageCoefficient_mul_inv_oldPart {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ} (hQ : Q ≠ 0)
    (i : MomentStageIndex A s Q r) :
    momentStageCoefficient i * (1 / (momentStageOldPart i : ℝ)) =
      1 / ((A.get i.1).modulus : ℝ) := by
  have hp0 : stagePrime r ≠ 0 := (stagePrime_pos i.2.2.1).ne'
  have hm0 : momentStageOldPart i ≠ 0 := by
    intro hm
    have hmod := momentStageModulus_eq hQ i
    rw [hm, zero_mul] at hmod
    have hlt := (A.get i.1).one_lt_modulus
    omega
  rw [momentStageModulus_eq hQ i]
  simp only [Nat.cast_mul, Nat.cast_pow]
  unfold momentStageCoefficient
  field_simp [hp0, hm0]

/-- A stage of a minimal antichain cover inherits the exclusion of prime
powers.  This is the point at which minimality enters the refined moment
argument. -/
lemma momentStage_not_primePower {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ}
    (hminimal : IsMinimalCover A s)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus)
    (i : MomentStageIndex A s Q r) :
    ¬ IsPrimePow (A.get i.1).modulus :=
  no_prime_power_modulus_of_minimal_antichain_cover A s hminimal hanti i.1 i.2.1

/-- Distinct occurrences in one stage retain the original divisibility
antichain property. -/
lemma momentStage_moduli_antichain {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ}
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus)
    (i j : MomentStageIndex A s Q r) (hij : i ≠ j) :
    ¬ (A.get i.1).modulus ∣ (A.get j.1).modulus := by
  apply hanti i.1 i.2.1 j.1 j.2.1
  intro h
  apply hij
  exact Subtype.ext h

/-! ## Fibre union estimate -/

private lemma momentStageNewEvent_card {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ} (hQ : Q ≠ 0)
    (hr : 0 < r) (i : MomentStageIndex A s Q r) :
    (momentStageNewEvent hQ i).ncard =
      (stagePrime r ^ stageExponent Q r) /
        (stagePrime r ^ momentStageExponent i) := by
  let : NeZero (stagePrime r ^ stageExponent Q r) :=
    ⟨(pow_pos (stagePrime_pos hr) _).ne'⟩
  exact card_congruenceClass (momentStagePrimePower_dvd hQ i)
    (pow_pos (stagePrime_pos hr) _) (A.get i.1).residue

private lemma momentStageNewEvent_fraction {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ} (hQ : Q ≠ 0)
    (hr : 0 < r) (i : MomentStageIndex A s Q r) :
    ((momentStageNewEvent hQ i).ncard : ℝ) /
        (stagePrime r ^ stageExponent Q r : ℕ) =
      momentStageCoefficient i := by
  have hdiv := momentStagePrimePower_dvd hQ i
  have hP : 0 < stagePrime r ^ stageExponent Q r :=
    pow_pos (stagePrime_pos hr) _
  have he : 0 < stagePrime r ^ momentStageExponent i :=
    pow_pos (stagePrime_pos hr) _
  rw [momentStageNewEvent_card hQ hr i]
  unfold momentStageCoefficient
  have hmul := Nat.div_mul_cancel hdiv
  norm_num only [Nat.cast_pow]
  have hpR : (0 : ℝ) < stagePrime r := by
    exact_mod_cast stagePrime_pos hr
  rw [div_eq_div_iff
    ((pow_pos hpR (stageExponent Q r)).ne')
    ((pow_pos hpR (momentStageExponent i)).ne')]
  norm_num only [one_mul]
  exact_mod_cast hmul

private lemma sum_realIndicator_eq_ncard {X : Type*} [Fintype X]
    (S : Set X) :
    (∑ x : X, if x ∈ S then (1 : ℝ) else 0) = (S.ncard : ℝ) := by
  rw [Finset.sum_boole]
  congr 1
  rw [Set.ncard_eq_toFinset_card]
  congr
  ext x
  simp

/-- The fibre density of the union of the new classes is at most the sum
of their exact individual fibre densities.  This is equation (2.4) in the
finite occurrence-indexed form used by the moment expansion. -/
theorem momentStage_fiberFraction_le_indicatorSum
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 0 < r)
    (x : ZMod (partialPeriod Q (r - 1))) :
    fiberFraction (momentStageBadSet A s Q r hQ) x ≤
      weightedIndicatorSum
        (Finset.univ : Finset (MomentStageIndex A s Q r))
        momentStageCoefficient momentStageOldEvent x := by
  classical
  let P := stagePrime r ^ stageExponent Q r
  let I := MomentStageIndex A s Q r
  have hP : 0 < P := by
    dsimp [P]
    exact pow_pos (stagePrime_pos hr) _
  have hpoint (y : ZMod P) :
      (if (x, y) ∈ momentStageBadSet A s Q r hQ then (1 : ℝ) else 0) ≤
        ∑ i : I,
          if x ∈ momentStageOldEvent i ∧ y ∈ momentStageNewEvent hQ i
          then 1 else 0 := by
    by_cases hy : (x, y) ∈ momentStageBadSet A s Q r hQ
    · rw [if_pos hy]
      obtain ⟨i, hi⟩ := hy
      have hi' : x ∈ momentStageOldEvent i ∧ y ∈ momentStageNewEvent hQ i := hi
      let g : I → ℝ := fun j =>
        if x ∈ momentStageOldEvent j ∧ y ∈ momentStageNewEvent hQ j then 1 else 0
      have hg : ∀ j ∈ (Finset.univ : Finset I), 0 ≤ g j := by
        intro j hj
        unfold g
        split <;> norm_num
      have hone : g i = 1 := by simp [g, hi']
      calc
        (1 : ℝ) = g i := hone.symm
        _ ≤ ∑ j : I, g j := Finset.single_le_sum hg (Finset.mem_univ i)
    · simp [hy]
  have hcount :
      (fiberCount (momentStageBadSet A s Q r hQ) x : ℝ) ≤
        ∑ y : ZMod P, ∑ i : I,
          if x ∈ momentStageOldEvent i ∧ y ∈ momentStageNewEvent hQ i
          then 1 else 0 := by
    rw [show (fiberCount (momentStageBadSet A s Q r hQ) x : ℝ) =
        ∑ y : ZMod P,
          if (x, y) ∈ momentStageBadSet A s Q r hQ then 1 else 0 by
      unfold fiberCount
      exact Finset.natCast_card_filter (R := ℝ)
        (fun y : ZMod P => (x, y) ∈ momentStageBadSet A s Q r hQ)
        (Finset.univ : Finset (ZMod P))]
    exact Finset.sum_le_sum fun y hy => hpoint y
  rw [Finset.sum_comm] at hcount
  have hsum :
      (∑ i : I, ∑ y : ZMod P,
          if x ∈ momentStageOldEvent i ∧ y ∈ momentStageNewEvent hQ i
          then 1 else 0) /
          (P : ℝ) =
        weightedIndicatorSum (Finset.univ : Finset I)
          momentStageCoefficient momentStageOldEvent x := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : x ∈ momentStageOldEvent i
    · have hcard :
          (∑ y : ZMod P,
            if x ∈ momentStageOldEvent i ∧ y ∈ momentStageNewEvent hQ i
            then 1 else 0) = ((momentStageNewEvent hQ i).ncard : ℝ) := by
          simp only [hx, true_and]
          exact sum_realIndicator_eq_ncard (momentStageNewEvent hQ i)
      rw [hcard, momentStageNewEvent_fraction hQ hr i]
      simp [weightedIndicatorSum, realIndicator, hx]
    · simp [weightedIndicatorSum, realIndicator, hx]
  unfold fiberFraction
  simp only [ZMod.card]
  change (fiberCount (momentStageBadSet A s Q r hQ) x : ℝ) / (P : ℝ) ≤ _
  rw [← hsum]
  exact div_le_div_of_nonneg_right hcount (by positivity)

/-- The concrete first-moment inequality for a prime stage. -/
theorem momentStage_firstMoment_le
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 0 < r)
    (μ : FiniteProbability (ZMod (partialPeriod Q (r - 1)))) :
    firstMoment μ (momentStageBadSet A s Q r hQ) ≤
      ∑ i : MomentStageIndex A s Q r,
        momentStageCoefficient i * μ.mass (momentStageOldEvent i) := by
  unfold firstMoment
  exact firstMoment_le_indicator_sum μ Finset.univ momentStageCoefficient
    momentStageOldEvent _
    (momentStage_fiberFraction_le_indicatorSum A s hQ hr)

/-! ## The concrete LCM second-moment sum -/

lemma partialPeriod_ne_zero_of_Q_ne_zero (Q r : ℕ) (hQ : Q ≠ 0) :
    partialPeriod Q r ≠ 0 :=
  (partialPeriod_pos Q r).ne'

/-- The class-mass invariant maintained by the preceding distortion stages.
It is stated for every divisor of the current old period, so it is stable
under the LCM which occurs in a second-moment expansion. -/
def HasProcessedClassMassBound {Q r : ℕ}
    (μ : FiniteProbability (ZMod (partialPeriod Q (r - 1))))
    (δ : ℕ → ℝ) : Prop :=
  ∀ (m : ℕ) (hm : m ∣ partialPeriod Q (r - 1)) (hm0 : 0 < m) (b : ℤ),
    μ.mass (congruenceClass (partialPeriod Q (r - 1)) m hm b) ≤
      (1 / (m : ℝ)) * processedClassFactor stagePrime δ m (r - 1)

/-- Intersecting the two old-coordinate events gives a class modulo their
LCM (or the empty set), and the processed class-mass invariant bounds it.
-/
lemma momentStage_oldEvent_inter_mass_le
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 0 < r)
    (μ : FiniteProbability (ZMod (partialPeriod Q (r - 1))))
    (δ : ℕ → ℝ) (hclass : HasProcessedClassMassBound μ δ)
    (i j : MomentStageIndex A s Q r) :
    μ.mass (momentStageOldEvent i ∩ momentStageOldEvent j) ≤
      (1 / (Nat.lcm (momentStageOldPart i) (momentStageOldPart j) : ℕ)) *
        processedClassFactor stagePrime δ
          (Nat.lcm (momentStageOldPart i) (momentStageOldPart j)) (r - 1) := by
  let q := partialPeriod Q (r - 1)
  let : NeZero q := ⟨partialPeriod_ne_zero_of_Q_ne_zero Q (r - 1) hQ⟩
  have hi0 : 0 < momentStageOldPart i := by
    exact Nat.pos_of_dvd_of_pos (momentStageOldPart_dvd i) (NeZero.pos q)
  have hj0 : 0 < momentStageOldPart j := by
    exact Nat.pos_of_dvd_of_pos (momentStageOldPart_dvd j) (NeZero.pos q)
  have hl0 : 0 < Nat.lcm (momentStageOldPart i) (momentStageOldPart j) :=
    Nat.lcm_pos hi0 hj0
  have hldiv : Nat.lcm (momentStageOldPart i) (momentStageOldPart j) ∣ q :=
    Nat.lcm_dvd (momentStageOldPart_dvd i) (momentStageOldPart_dvd j)
  rcases congruenceClass_inter_eq_empty_or_lcm
      (momentStageOldPart_dvd i) (momentStageOldPart_dvd j)
      (A.get i.1).residue (A.get j.1).residue with hempty | ⟨b, hb⟩
  · have hempty' : momentStageOldEvent i ∩ momentStageOldEvent j = ∅ := by
      simpa only [momentStageOldEvent] using hempty
    rw [hempty', FiniteProbability.mass_empty]
    exact (μ.mass_nonneg
      (congruenceClass q
        (Nat.lcm (momentStageOldPart i) (momentStageOldPart j)) hldiv 0)).trans
      (hclass _ hldiv hl0 0)
  · have hb' :
        momentStageOldEvent i ∩ momentStageOldEvent j =
          congruenceClass q
            (Nat.lcm (momentStageOldPart i) (momentStageOldPart j)) hldiv b := by
      simpa only [momentStageOldEvent] using hb
    rw [hb']
    exact hclass _ hldiv hl0 b

/-- Fully concrete second-moment expansion at a prime stage.  No analytic
or smooth-number estimate is hidden here: the right side is the exact
finite LCM sum which the BBMST 5-smooth/rough argument subsequently bounds.
-/
theorem momentStage_secondMoment_le_lcmSum
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 0 < r)
    (μ : FiniteProbability (ZMod (partialPeriod Q (r - 1))))
    (δ : ℕ → ℝ) (hclass : HasProcessedClassMassBound μ δ) :
    secondMoment μ (momentStageBadSet A s Q r hQ) ≤
      ∑ i : MomentStageIndex A s Q r,
        ∑ j : MomentStageIndex A s Q r,
          (momentStageCoefficient i * momentStageCoefficient j) *
            ((1 / (Nat.lcm (momentStageOldPart i)
              (momentStageOldPart j) : ℕ)) *
              processedClassFactor stagePrime δ
                (Nat.lcm (momentStageOldPart i)
                  (momentStageOldPart j)) (r - 1)) := by
  unfold secondMoment
  calc
    μ.expectation
        (fun x => fiberFraction (momentStageBadSet A s Q r hQ) x ^ 2) ≤
        ∑ i : MomentStageIndex A s Q r,
          ∑ j : MomentStageIndex A s Q r,
            (momentStageCoefficient i * momentStageCoefficient j) *
              μ.mass (momentStageOldEvent i ∩ momentStageOldEvent j) := by
      exact secondMoment_le_indicator_sum μ Finset.univ
        momentStageCoefficient momentStageOldEvent _
        (fiberFraction_nonneg _) (fun i hi => momentStageCoefficient_nonneg i)
        (momentStage_fiberFraction_le_indicatorSum A s hQ hr)
    _ ≤ ∑ i : MomentStageIndex A s Q r,
          ∑ j : MomentStageIndex A s Q r,
            (momentStageCoefficient i * momentStageCoefficient j) *
              ((1 / (Nat.lcm (momentStageOldPart i)
                (momentStageOldPart j) : ℕ)) *
                processedClassFactor stagePrime δ
                  (Nat.lcm (momentStageOldPart i)
                    (momentStageOldPart j)) (r - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (momentStage_oldEvent_inter_mass_le A s hQ hr μ δ hclass i j)
        (mul_nonneg (momentStageCoefficient_nonneg i)
          (momentStageCoefficient_nonneg j))

/-! ## Distortion cost in the concrete stage coordinates -/

/-- The first-moment cost estimate specialized to the actual union of
newly exposed congruence classes.  It is used at the initial undistorted
prime stages. -/
theorem momentStage_distortedMass_le_firstMoment
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0)
    (μ : FiniteProbability (ZMod (partialPeriod Q (r - 1))))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    (distort μ (momentStageBadSet A s Q r hQ) δ hδ0 hδhalf).mass
        (momentStageBadSet A s Q r hQ) ≤
      firstMoment μ (momentStageBadSet A s Q r hQ) :=
  stage_cost_first_le μ (momentStageBadSet A s Q r hQ) δ hδ0 hδhalf

/-- The second-moment distortion cost specialized to a concrete prime
stage.  This is the exact cost premise used by
`Sieve.oneStep_of_secondMoment`, before transport through the stage CRT
equivalence. -/
theorem momentStage_distortedMass_le_secondMoment
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0)
    (μ : FiniteProbability (ZMod (partialPeriod Q (r - 1))))
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    (distort μ (momentStageBadSet A s Q r hQ) δ hδ.le hδhalf).mass
        (momentStageBadSet A s Q r hQ) ≤
      secondMoment μ (momentStageBadSet A s Q r hQ) /
        (4 * δ * (1 - δ)) :=
  stage_cost_second_le μ (momentStageBadSet A s Q r hQ) hδ hδhalf

end

end Erdos586
