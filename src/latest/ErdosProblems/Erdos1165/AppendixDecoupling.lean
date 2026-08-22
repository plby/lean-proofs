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

import ErdosProblems.Erdos1165.Markov
import ErdosProblems.Erdos1165.Annulus
import ErdosProblems.Erdos1165.ThickPoint

/-!
# The exact part of the appendix decoupling argument

Hao--Li--Okada--Zheng's Lemma A.2 compares the law of the excursions inside
an annulus, conditionally on the outer excursions, with an unconditional
law.  There are two logically distinct ingredients.

* The strong Markov property gives an exact factorization once the entrance
  point and a finite piece of the future path have been specified.
* A planar Harnack estimate says that the relevant conditional probabilities
  change only slightly when an entrance point is changed.

This file proves the first ingredient for the product-space walk in
`Markov.lean` and isolates the second ingredient as a concrete comparison of
finite kernels.  In particular, no Harnack estimate is asserted here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AppendixDecoupling

/-! ## Finite paths and entrance points -/

/-- Extend a finite block of increments by the zero-th direction.  Only
times at most the block length are used below. -/
def extendBlock {k : ℕ} (u : Fin k → Direction) : StepPath :=
  fun j ↦ if h : j < k then u ⟨j, h⟩ else 0

/-- Position at time `t` of the finite walk started from `a`. -/
def finitePosition {k : ℕ} (a : Point) (u : Fin k → Direction) (t : ℕ) : Point :=
  a + trajectory (extendBlock u) t

@[simp] lemma finitePosition_zero {k : ℕ} (a : Point) (u : Fin k → Direction) :
    finitePosition a u 0 = a := by
  simp [finitePosition]

lemma finitePosition_succ {k : ℕ} (a : Point) (u : Fin k → Direction)
    {t : ℕ} (ht : t < k) :
    finitePosition a u (t + 1) = finitePosition a u t + directionVector (u ⟨t, ht⟩) := by
  simp [finitePosition, trajectory_succ, extendBlock, ht, add_assoc]

/-- The times at which a finite block, including its initial point, lies in `B`. -/
def entranceTimes {k : ℕ} (a : Point) (B : Set Point) [DecidablePred (· ∈ B)]
    (u : Fin k → Direction) : Finset ℕ :=
  (Finset.range (k + 1)).filter fun t ↦ finitePosition a u t ∈ B

/-- The first entrance time in a finite block, or `none` if the block misses `B`. -/
def firstEntranceTime {k : ℕ} (a : Point) (B : Set Point) [DecidablePred (· ∈ B)]
    (u : Fin k → Direction) : Option ℕ :=
  if h : (entranceTimes a B u).Nonempty then some ((entranceTimes a B u).min' h) else none

/-- The corresponding first entrance point in a finite block. -/
def firstEntrancePoint {k : ℕ} (a : Point) (B : Set Point) [DecidablePred (· ∈ B)]
    (u : Fin k → Direction) : Option Point :=
  (firstEntranceTime a B u).map (finitePosition a u)

/-- Boundary data visible in a truncated inner excursion: its first entrance
point in `B` and its position at the end of the block.  Rosen's proof of the
decoupling lemma compares kernels indexed by both the entrance point and the
terminal outer-boundary point. -/
def entranceExitData {k : ℕ} (a : Point) (B : Set Point) [DecidablePred (· ∈ B)]
    (u : Fin k → Direction) : Option Point × Point :=
  (firstEntrancePoint a B u, finitePosition a u k)

lemma firstEntranceTime_eq_none_iff {k : ℕ} (a : Point) (B : Set Point)
    [DecidablePred (· ∈ B)] (u : Fin k → Direction) :
    firstEntranceTime a B u = none ↔ (entranceTimes a B u).Nonempty = False := by
  simp [firstEntranceTime]

lemma firstEntranceTime_eq_some_mem {k : ℕ} (a : Point) (B : Set Point)
    [DecidablePred (· ∈ B)] (u : Fin k → Direction) {t : ℕ}
    (ht : firstEntranceTime a B u = some t) :
    t ∈ entranceTimes a B u := by
  unfold firstEntranceTime at ht
  split at ht
  · simpa using Option.some.inj ht ▸ Finset.min'_mem _ ‹_›
  · simp at ht

lemma firstEntranceTime_le {k : ℕ} (a : Point) (B : Set Point)
    [DecidablePred (· ∈ B)] (u : Fin k → Direction) {t : ℕ}
    (ht : firstEntranceTime a B u = some t) : t ≤ k := by
  have hmem := firstEntranceTime_eq_some_mem a B u ht
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hmem).1)

lemma firstEntranceTime_mem {k : ℕ} (a : Point) (B : Set Point)
    [DecidablePred (· ∈ B)] (u : Fin k → Direction) {t : ℕ}
    (ht : firstEntranceTime a B u = some t) : finitePosition a u t ∈ B := by
  exact (Finset.mem_filter.mp (firstEntranceTime_eq_some_mem a B u ht)).2

lemma firstEntranceTime_minimal {k : ℕ} (a : Point) (B : Set Point)
    [DecidablePred (· ∈ B)] (u : Fin k → Direction) {t : ℕ}
    (ht : firstEntranceTime a B u = some t) {j : ℕ}
    (hj : j ≤ k) (hjB : finitePosition a u j ∈ B) : t ≤ j := by
  have hjmem : j ∈ entranceTimes a B u := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj), hjB⟩
  unfold firstEntranceTime at ht
  split at ht
  · simpa using (Option.some.inj ht) ▸ Finset.min'_le _ _ hjmem
  · simp at ht

lemma firstEntrancePoint_eq_some_iff {k : ℕ} (a : Point) (B : Set Point)
    [DecidablePred (· ∈ B)] (u : Fin k → Direction) (y : Point) :
    firstEntrancePoint a B u = some y ↔
      ∃ t ≤ k, firstEntranceTime a B u = some t ∧ finitePosition a u t = y := by
  simp only [firstEntrancePoint, Option.map_eq_some_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, firstEntranceTime_le a B u ht, ht, rfl⟩
  · rintro ⟨t, _htk, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

lemma firstEntrancePoint_mem {k : ℕ} (a : Point) (B : Set Point)
    [DecidablePred (· ∈ B)] (u : Fin k → Direction) {y : Point}
    (hy : firstEntrancePoint a B u = some y) : y ∈ B := by
  obtain ⟨t, _htk, ht, rfl⟩ := (firstEntrancePoint_eq_some_iff a B u y).mp hy
  exact firstEntranceTime_mem a B u ht

/-! ## Exact finite-dimensional Markov factorization -/

/-- A finite future-block event obtained by applying any statistic `stat` to
the block.  Taking `stat` to be `firstEntrancePoint a B` gives the law of a
truncated annulus entrance point. -/
def futureStatisticEvent {k : ℕ} {β : Type*} (τ : StepPath → ℕ)
    (stat : (Fin k → Direction) → β) (C : Set β) : Set StepPath :=
  {ω | stat (postStoppingBlock τ k ω) ∈ C}

theorem finite_future_statistic_factorization {k : ℕ} {β : Type*}
    (hτ : IsFiniteStoppingTime τ) (hA : IsMeasurableAtStopping τ A)
    (stat : (Fin k → Direction) → β) (C : Set β) :
    fairSteps (A ∩ futureStatisticEvent τ stat C) =
      fairSteps A * fairBlock k (stat ⁻¹' C) := by
  change fairSteps (A ∩ postStoppingBlock τ k ⁻¹' (stat ⁻¹' C)) =
    fairSteps A * fairBlock k (stat ⁻¹' C)
  exact strongMarkov_stoppedEvent_set hτ hA k (stat ⁻¹' C)

/-- Quotient form of the preceding factorization.  Thus, whenever the
stopped-past event has positive probability, the conditional distribution of
every finite future statistic is exactly its fresh-walk distribution. -/
theorem finite_future_statistic_conditional {k : ℕ} {β : Type*}
    (hτ : IsFiniteStoppingTime τ) (hA : IsMeasurableAtStopping τ A)
    (hApos : fairSteps A ≠ 0)
    (stat : (Fin k → Direction) → β) (C : Set β) :
    fairSteps (A ∩ futureStatisticEvent τ stat C) / fairSteps A =
      fairBlock k (stat ⁻¹' C) := by
  rw [finite_future_statistic_factorization hτ hA, mul_comm]
  exact ENNReal.mul_div_cancel_right hApos (measure_ne_top fairSteps A)

/-- Exact factorization for the entrance point of a finite post-stopping
block.  This is the finite-path strong-Markov identity used before any
Harnack comparison enters HLOZ Lemma A.2. -/
theorem finite_entrance_point_factorization {k : ℕ}
    (hτ : IsFiniteStoppingTime τ) (hA : IsMeasurableAtStopping τ A)
    (a : Point) (B : Set Point) [DecidablePred (· ∈ B)] (D : Set (Option Point)) :
    fairSteps (A ∩ futureStatisticEvent τ (firstEntrancePoint (k := k) a B) D) =
      fairSteps A * fairBlock k ((firstEntrancePoint (k := k) a B) ⁻¹' D) := by
  exact finite_future_statistic_factorization hτ hA (firstEntrancePoint (k := k) a B) D

/-- Conditional-law form for the truncated entrance point. -/
theorem finite_entrance_point_conditional {k : ℕ}
    (hτ : IsFiniteStoppingTime τ) (hA : IsMeasurableAtStopping τ A)
    (hApos : fairSteps A ≠ 0)
    (a : Point) (B : Set Point) [DecidablePred (· ∈ B)] (D : Set (Option Point)) :
    fairSteps
        (A ∩ futureStatisticEvent τ (firstEntrancePoint (k := k) a B) D) /
      fairSteps A =
        fairBlock k ((firstEntrancePoint (k := k) a B) ⁻¹' D) := by
  exact finite_future_statistic_conditional hτ hA hApos
    (firstEntrancePoint (k := k) a B) D

/-- Exact conditional law of the entrance/terminal-point pair of a finite
post-stopping block.  This exposes both pieces of boundary data in Rosen's
finite-path disintegration. -/
theorem finite_entranceExit_conditional {k : ℕ}
    (hτ : IsFiniteStoppingTime τ) (hA : IsMeasurableAtStopping τ A)
    (hApos : fairSteps A ≠ 0)
    (a : Point) (B : Set Point) [DecidablePred (· ∈ B)]
    (D : Set (Option Point × Point)) :
    fairSteps
        (A ∩ futureStatisticEvent τ (entranceExitData (k := k) a B) D) /
      fairSteps A =
        fairBlock k ((entranceExitData (k := k) a B) ⁻¹' D) := by
  exact finite_future_statistic_conditional hτ hA hApos
    (entranceExitData (k := k) a B) D

/-- The truncated entrance statistic specialized to the Euclidean lattice
boundaries used in the HLOZ appendix. -/
noncomputable def discBoundaryEntrancePoint {k : ℕ}
    (a x : Point) (r : ℝ) (u : Fin k → Direction) : Option Point := by
  classical
  exact firstEntrancePoint a (ThickPoint.discBoundary x r) u

/-- Exact conditional law of a finite-block entrance point on an HLOZ disc
boundary.  Its right-hand side is a fresh finite random-walk probability and
is the object to which a quantitative annular Harnack estimate must be
applied. -/
theorem finite_discBoundary_entrance_conditional {k : ℕ}
    (hτ : IsFiniteStoppingTime τ) (hA : IsMeasurableAtStopping τ A)
    (hApos : fairSteps A ≠ 0) (a x : Point) (r : ℝ)
    (D : Set (Option Point)) :
    fairSteps
        (A ∩ futureStatisticEvent τ
          (discBoundaryEntrancePoint (k := k) a x r) D) /
      fairSteps A =
        fairBlock k ((discBoundaryEntrancePoint (k := k) a x r) ⁻¹' D) := by
  classical
  exact finite_future_statistic_conditional hτ hA hApos
    (discBoundaryEntrancePoint (k := k) a x r) D

/-- Singleton version: the conditional numerator for entrance at `y` factors
as the stopped-past mass times the fresh entrance mass. -/
theorem finite_entrance_point_singleton_factorization {k : ℕ}
    (hτ : IsFiniteStoppingTime τ) (hA : IsMeasurableAtStopping τ A)
    (a : Point) (B : Set Point) [DecidablePred (· ∈ B)] (y : Point) :
    fairSteps (A ∩ futureStatisticEvent τ (firstEntrancePoint (k := k) a B) {some y}) =
      fairSteps A * fairBlock k {u | firstEntrancePoint a B u = some y} := by
  change fairSteps
      (A ∩ futureStatisticEvent τ (firstEntrancePoint (k := k) a B) {some y}) =
    fairSteps A * fairBlock k ((firstEntrancePoint (k := k) a B) ⁻¹' {some y})
  exact finite_entrance_point_factorization hτ hA a B ({some y} : Set (Option Point))

/-! ## Entrance distributions and the Harnack reduction -/

/-- A probability distribution on a finite set of possible boundary data.
Usually `ι` is the inner entrance boundary, but it may equally well be a pair
of inner entrance and outer terminal points.  The reduction uses only
nonnegativity and total mass one, not the geometry of the boundaries. -/
structure EntranceDistribution (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  sum_weight : ∑ i, weight i = 1

/-- Average a conditional probability over a distribution of entrance points. -/
def EntranceDistribution.mix {ι : Type*} [Fintype ι]
    (ν : EntranceDistribution ι) (q : ι → ℝ) : ℝ :=
  ∑ i, ν.weight i * q i

lemma EntranceDistribution.mix_nonneg {ι : Type*} [Fintype ι]
    (ν : EntranceDistribution ι) {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i) :
    0 ≤ ν.mix q := by
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (ν.nonneg i) (hq i)

lemma EntranceDistribution.mix_const {ι : Type*} [Fintype ι]
    (ν : EntranceDistribution ι) (c : ℝ) :
    ν.mix (fun _ ↦ c) = c := by
  simp [EntranceDistribution.mix, ← Finset.sum_mul, ν.sum_weight]

/-- A mixture preserves pointwise lower and upper bounds.  This is the exact
measure-theoretic core of the entrance-point decoupling step. -/
theorem EntranceDistribution.mix_mem_Icc {ι : Type*} [Fintype ι]
    (ν : EntranceDistribution ι) (q : ι → ℝ) (lower upper : ℝ)
    (hq : ∀ i, q i ∈ Set.Icc lower upper) :
    ν.mix q ∈ Set.Icc lower upper := by
  constructor
  · calc
      lower = ν.mix (fun _ ↦ lower) := (ν.mix_const lower).symm
      _ ≤ ν.mix q := Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left (hq i).1 (ν.nonneg i)
  · calc
      ν.mix q ≤ ν.mix (fun _ ↦ upper) := Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left (hq i).2 (ν.nonneg i)
      _ = upper := ν.mix_const upper

/-- HLOZ's Condition `(∗)` for one conditional excursion event, stated as a
uniform multiplicative comparison of its probability at entrance points. -/
def ConditionStar {ι : Type*} [Fintype ι]
    (ε : ℝ) (q : ι → ℝ) : Prop :=
  ∀ y z, (1 - ε) * q y ≤ q z ∧ q z ≤ (1 + ε) * q y

/-- **Harnack reduction for one excursion.**  Once Condition `(∗)` is known,
conditioning the outer path can change the distribution of the entrance
point arbitrarily and nevertheless changes the inner-event probability by at
most the same multiplicative factors. -/
theorem mix_conditionStar {ι : Type*} [Fintype ι]
    (ν : EntranceDistribution ι) {ε : ℝ} {q : ι → ℝ}
    (hq : ConditionStar ε q) (y : ι) :
    ν.mix q ∈ Set.Icc ((1 - ε) * q y) ((1 + ε) * q y) := by
  apply ν.mix_mem_Icc
  intro z
  exact hq y z

/-! ## Several excursions: product kernels -/

/-- The conditional probability of a rectangular event in `m` successive
inner excursions, when the entrance point of excursion `j` is `u j`. -/
def productKernel {ι : Type*} {m : ℕ}
    (q : Fin m → ι → ℝ) (u : Fin m → ι) : ℝ :=
  ∏ j, q j (u j)

lemma productKernel_nonneg {ι : Type*} {m : ℕ}
    {q : Fin m → ι → ℝ} (hq : ∀ j y, 0 ≤ q j y) (u : Fin m → ι) :
    0 ≤ productKernel q u := by
  exact Finset.prod_nonneg fun j _ ↦ hq j (u j)

/-- Componentwise comparison multiplies over successive excursions. -/
theorem productKernel_mem_Icc {ι : Type*} {m : ℕ}
    {q : Fin m → ι → ℝ} {lower upper : Fin m → ℝ}
    (hlower : ∀ j, 0 ≤ lower j)
    (hq : ∀ j y, q j y ∈ Set.Icc (lower j) (upper j))
    (u : Fin m → ι) :
    productKernel q u ∈ Set.Icc (∏ j, lower j) (∏ j, upper j) := by
  constructor
  · exact Finset.prod_le_prod (fun j _ ↦ hlower j) (fun j _ ↦ (hq j (u j)).1)
  · exact Finset.prod_le_prod (fun j _ ↦ (hlower j).trans (hq j (u j)).1)
      (fun j _ ↦ (hq j (u j)).2)

/-- Exact multi-excursion Harnack reduction.  The outer path is represented
only through an arbitrary probability distribution `ν` on the vector of
entrance points.  The result reduces the desired conditional comparison to
pointwise comparisons of the inner kernels. -/
theorem mix_productKernel_mem_Icc {ι : Type*} [Fintype ι] {m : ℕ}
    (ν : EntranceDistribution (Fin m → ι))
    {q : Fin m → ι → ℝ} {lower upper : Fin m → ℝ}
    (hlower : ∀ j, 0 ≤ lower j)
    (hq : ∀ j y, q j y ∈ Set.Icc (lower j) (upper j)) :
    ν.mix (productKernel q) ∈
      Set.Icc (∏ j, lower j) (∏ j, upper j) := by
  exact ν.mix_mem_Icc _ _ _ (productKernel_mem_Icc hlower hq)

/-- Multiplicative Condition `(∗)` at every excursion gives the precise
power loss before the analytic linearization used in HLOZ Lemma A.2. -/
theorem mix_productKernel_conditionStar {ι : Type*} [Fintype ι] {m : ℕ}
    (ν : EntranceDistribution (Fin m → ι))
    {ε : ℝ} (hε : ε ≤ 1) (q : Fin m → ι → ℝ)
    (hqnonneg : ∀ j y, 0 ≤ q j y)
    (hqstar : ∀ j, ConditionStar ε (q j))
    (reference : Fin m → ι) :
    ν.mix (productKernel q) ∈ Set.Icc
      ((1 - ε) ^ m * productKernel q reference)
      ((1 + ε) ^ m * productKernel q reference) := by
  have hfac : 0 ≤ 1 - ε := sub_nonneg.mpr hε
  have hbounds : ∀ j y, q j y ∈ Set.Icc
      ((1 - ε) * q j (reference j)) ((1 + ε) * q j (reference j)) := by
    intro j y
    exact hqstar j (reference j) y
  have h := mix_productKernel_mem_Icc ν
    (lower := fun j ↦ (1 - ε) * q j (reference j))
    (upper := fun j ↦ (1 + ε) * q j (reference j))
    (fun j ↦ mul_nonneg hfac (hqnonneg j (reference j))) hbounds
  simpa [productKernel, Finset.prod_mul_distrib] using h

/-! ## Linearizing the product error -/

/-- The lower Bernoulli bound needed to turn a product of `m` errors into a
linear error. -/
theorem one_sub_nat_mul_le_pow_one_sub {ε : ℝ} (hε : ε ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * ε ≤ (1 - ε) ^ m := by
  simpa [sub_eq_add_neg] using
    (one_add_mul_le_pow (a := -ε) (n := m) (by linarith : (-2 : ℝ) ≤ -ε))

/-- An elementary upper linearization.  The explicit hypothesis that the
power is at most two is exactly what is later discharged from smallness of
`m ε`; keeping it visible avoids smuggling an exponential estimate into the
decoupling lemma. -/
theorem pow_one_add_le_one_add_two_nat_mul {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε) (hpow : (1 + ε) ^ m ≤ 2) :
    (1 + ε) ^ m ≤ 1 + 2 * (m : ℝ) * ε := by
  have hbase : 1 ≤ 1 + ε := by linarith
  have hterm : ∀ i ∈ Finset.range m, (1 + ε) ^ i ≤ (2 : ℝ) := by
    intro i hi
    exact (pow_le_pow_right₀ hbase (Finset.mem_range.mp hi).le).trans hpow
  have hsum : (∑ i ∈ Finset.range m, (1 + ε) ^ i) ≤ (m : ℝ) * 2 := by
    calc
      (∑ i ∈ Finset.range m, (1 + ε) ^ i) ≤
          ∑ _i ∈ Finset.range m, (2 : ℝ) := Finset.sum_le_sum hterm
      _ = (m : ℝ) * 2 := by simp
  calc
    (1 + ε) ^ m = (∑ i ∈ Finset.range m, (1 + ε) ^ i) * ε + 1 := by
      simpa [add_comm] using (geom_sum_mul_add ε m).symm
    _ ≤ ((m : ℝ) * 2) * ε + 1 := by gcongr
    _ = 1 + 2 * (m : ℝ) * ε := by ring

/-- The fully algebraic `1 ± O(m ε)` conclusion.  At this point the only
probabilistic input is Condition `(∗)`; the outer conditioning is represented
by an arbitrary distribution on all entrance/terminal boundary data. -/
theorem mix_productKernel_conditionStar_linear {ι : Type*} [Fintype ι] {m : ℕ}
    (ν : EntranceDistribution (Fin m → ι))
    {ε : ℝ} (hεnonneg : 0 ≤ ε) (hε : ε ≤ 1)
    (q : Fin m → ι → ℝ)
    (hqnonneg : ∀ j y, 0 ≤ q j y)
    (hqstar : ∀ j, ConditionStar ε (q j))
    (reference : Fin m → ι)
    (hsmall : (1 + ε) ^ m ≤ 2) :
    ν.mix (productKernel q) ∈ Set.Icc
      ((1 - (m : ℝ) * ε) * productKernel q reference)
      ((1 + 2 * (m : ℝ) * ε) * productKernel q reference) := by
  have href : 0 ≤ productKernel q reference :=
    productKernel_nonneg hqnonneg reference
  have hpower := mix_productKernel_conditionStar ν hε q hqnonneg hqstar reference
  constructor
  · exact (mul_le_mul_of_nonneg_right
      (one_sub_nat_mul_le_pow_one_sub hε m) href).trans hpower.1
  · exact hpower.2.trans (mul_le_mul_of_nonneg_right
      (pow_one_add_le_one_add_two_nat_mul hεnonneg hsmall) href)

/-! ## Disjoint-union closure -/

/-- A uniform multiplicative comparison survives an arbitrary countable
disjoint-union decomposition.  Countable additivity converts the measures of
the pieces into the two `tsum`s appearing here; this is the final formal step
from rectangular excursion events to the event class in HLOZ Lemma A.2. -/
theorem tsum_comparison {κ : Type*} (lower upper : ℝ≥0∞)
    (p q : κ → ℝ≥0∞)
    (hp : ∀ i, lower * q i ≤ p i ∧ p i ≤ upper * q i) :
    lower * ∑' i, q i ≤ ∑' i, p i ∧
      ∑' i, p i ≤ upper * ∑' i, q i := by
  constructor
  · rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun i ↦ (hp i).1
  · rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun i ↦ (hp i).2

/-! ## What remains analytic

The preceding theorems are deliberately phrased so that the missing input is
visible: for the actual lattice boundaries one must prove Condition `(∗)`
uniformly over entrance points, and one must pass from finite truncations to
the successive (a.s. finite) annular entrance and exit times.  HLOZ obtain the
needed `O(n⁻³ log n)` comparison from planar potential-kernel/Harnack
estimates, citing Rosen's Lemma 6.3.  Neither that quantitative Harnack bound
nor the required unbounded stopping-time construction is presently available
in the local development, so this file does not state Lemma A.2 itself.
-/

end Erdos1165.AppendixDecoupling
