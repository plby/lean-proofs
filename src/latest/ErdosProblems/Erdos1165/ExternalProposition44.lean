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

import ErdosProblems.Erdos1165.ExternalThickCount
import ErdosProblems.Erdos1165.ExternalOnePoint
import ErdosProblems.Erdos1165.ExternalGreenTail
import ErdosProblems.Erdos1165.LevelTail
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The external thick-site count reduction

This file gives the probabilistic counting argument in HLOZ Proposition 4.4
for the retained-block external walk.  It reduces the probability of having
many sites with large external local time to one origin-local-time tail.

The deterministic device is to charge each thick site to the first occurrence
used by a recursive scan.  Its remaining suffix contains all later visits to
that site.  Distinct charged sites use distinct suffixes.  Translation of a
suffix to the origin, invariance of the IID retained-block law under time
shifts, and monotonicity in the horizon give the uniform one-point estimate.
Tonelli and Markov's inequality then give the factor `(n + 1) / (J + 1)`.

No sharp origin-local-time tail is postulated here.  The final theorem takes
that analytic estimate as its sole probabilistic input.  The existing exact
renewal identities in `ExternalGreenRenewal` do not yet imply HLOZ (7.4),
whose proof needs the sharp external Green-function asymptotic.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.ExternalProposition44

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## A deterministic suffix charging lemma -/

variable {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]

/-- Number of distinct entries occurring at least `k` times in a list. -/
def listThickCount (p : List α) (k : ℕ) : ℕ :=
  (p.toFinset.filter fun x ↦ k ≤ p.count x).card

/-- Number of suffix heads which occur at least `k` times in their suffix. -/
def suffixGoodCount (k : ℕ) : List α → ℕ
  | [] => 0
  | a :: p => (if k ≤ (a :: p).count a then 1 else 0) + suffixGoodCount k p

lemma listThickCount_cons_le (a : α) (p : List α) (k : ℕ) :
    listThickCount (a :: p) k ≤
      (if k ≤ (a :: p).count a then 1 else 0) + listThickCount p k := by
  by_cases ha : k ≤ (a :: p).count a
  · have hsubset : ((a :: p).toFinset.filter fun x ↦ k ≤ (a :: p).count x) ⊆
        insert a (p.toFinset.filter fun x ↦ k ≤ p.count x) := by
      intro x hx
      simp only [List.toFinset_cons, Finset.mem_filter, Finset.mem_insert] at hx ⊢
      by_cases hxa : x = a
      · exact Or.inl hxa
      · right
        refine ⟨hx.1.resolve_left hxa, ?_⟩
        simpa [List.count_cons, Ne.symm hxa] using hx.2
    calc
      listThickCount (a :: p) k ≤
          (insert a (p.toFinset.filter fun x ↦ k ≤ p.count x)).card :=
        Finset.card_le_card hsubset
      _ ≤ 1 + listThickCount p k := by
        simp only [listThickCount]
        simpa [Nat.add_comm] using Finset.card_insert_le a
          (p.toFinset.filter fun x ↦ k ≤ p.count x)
      _ = (if k ≤ (a :: p).count a then 1 else 0) + listThickCount p k := by
        rw [if_pos ha]
  · have hsubset : ((a :: p).toFinset.filter fun x ↦ k ≤ (a :: p).count x) ⊆
        (p.toFinset.filter fun x ↦ k ≤ p.count x) := by
      intro x hx
      simp only [List.toFinset_cons, Finset.mem_filter, Finset.mem_insert] at hx ⊢
      by_cases hxa : x = a
      · subst x
        exact False.elim (ha hx.2)
      · refine ⟨hx.1.resolve_left hxa, ?_⟩
        simpa [List.count_cons, Ne.symm hxa] using hx.2
    calc
      listThickCount (a :: p) k ≤ listThickCount p k :=
        Finset.card_le_card hsubset
      _ = (if k ≤ (a :: p).count a then 1 else 0) + listThickCount p k := by
        rw [if_neg ha]
        simp

theorem listThickCount_le_suffixGoodCount (p : List α) (k : ℕ) :
    listThickCount p k ≤ suffixGoodCount k p := by
  induction p with
  | nil => simp [listThickCount, suffixGoodCount]
  | cons a p ih =>
      exact (listThickCount_cons_le a p k).trans
        (Nat.add_le_add_left ih _)

/-- The head of the suffix beginning at `t` is `k`-fold recurrent in that
suffix.  The proposition is false once `t` is outside the list. -/
def suffixGoodAt (p : List α) (k t : ℕ) : Prop :=
  match p.drop t with
  | [] => False
  | a :: q => k ≤ (a :: q).count a

omit [DecidableEq α] in
theorem suffixGoodCount_eq_card_filter (p : List α) (k : ℕ) :
    suffixGoodCount k p =
      ((Finset.range p.length).filter fun t ↦ suffixGoodAt p k t).card := by
  induction p with
  | nil => simp [suffixGoodCount]
  | cons a p ih =>
      simp only [suffixGoodCount, List.length_cons, Finset.card_filter] at ih ⊢
      rw [ih]
      rw [Finset.sum_range_succ']
      simp only [suffixGoodAt, List.drop_zero, List.drop_succ_cons]
      simp [Nat.add_comm]

/-! ## The finite Tonelli--Markov reduction -/

section Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A uniform probability bound for all good suffixes controls the number of
distinct thick entries.  This is the abstract finite-list form of the
counting step in HLOZ Proposition 4.4. -/
theorem measure_listThickCount_gt_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Ω → List α) (n k J : ℕ) (q : ℝ≥0∞)
    (hlen : ∀ ω, (p ω).length = n + 1)
    (hmeas : ∀ t, MeasurableSet {ω | suffixGoodAt (p ω) k t})
    (htail : ∀ t < n + 1, μ {ω | suffixGoodAt (p ω) k t} ≤ q) :
    μ {ω | J < listThickCount (p ω) k} ≤
      q * (n + 1) / (↑(J + 1) : ℝ≥0∞) := by
  let visited : Ω → Finset ℕ := fun _ ↦ Finset.range (n + 1)
  let large : ℕ → Set Ω := fun t ↦ {ω | suffixGoodAt (p ω) k t}
  have hvisited : ∀ t, MeasurableSet
      (ExternalThickCount.memberEvent visited t) := by
    intro t
    by_cases ht : t < n + 1
    · have heq : ExternalThickCount.memberEvent visited t = Set.univ := by
        ext ω
        simp [ExternalThickCount.memberEvent, visited, ht]
      rw [heq]
      exact MeasurableSet.univ
    · have heq : ExternalThickCount.memberEvent visited t = ∅ := by
        ext ω
        simp [ExternalThickCount.memberEvent, visited, ht]
      rw [heq]
      exact MeasurableSet.empty
  have hweighted : ∀ t,
      μ (ExternalThickCount.candidateEvent visited large t) ≤
        q * μ (ExternalThickCount.memberEvent visited t) := by
    intro t
    by_cases ht : t < n + 1
    · simpa [ExternalThickCount.candidateEvent,
        ExternalThickCount.memberEvent, visited, large, ht] using htail t ht
    · simp [ExternalThickCount.candidateEvent,
        ExternalThickCount.memberEvent, visited, large, ht]
  have hexpect : ∫⁻ ω,
      (((visited ω).card : ℕ) : ℝ≥0∞) ∂μ ≤ (n + 1 : ℝ≥0∞) := by
    simp [visited]
  refine (measure_mono ?_).trans
    (ExternalThickCount.measure_candidateCount_gt_le_succ
      μ visited large q (n + 1) J hvisited hmeas hweighted hexpect)
  intro ω hω
  change J < listThickCount (p ω) k at hω
  change J < ExternalThickCount.candidateCount visited large ω
  apply hω.trans_le
  calc
    listThickCount (p ω) k ≤ suffixGoodCount k (p ω) :=
      listThickCount_le_suffixGoodCount (p ω) k
    _ = ((Finset.range (p ω).length).filter fun t ↦
        suffixGoodAt (p ω) k t).card := suffixGoodCount_eq_card_filter (p ω) k
    _ = ExternalThickCount.candidateCount visited large ω := by
      simp [ExternalThickCount.candidateCount, visited, large, hlen ω]

end Probability

/-! ## Suffixes of the retained-block external walk -/

open ExternalWalk ExternalOnePoint LazyDecomposition

/-- The external-chain positions from time zero through time `n`. -/
def externalPositionList (o : Orientation) (η : ℕ → RetainedBlock o) (n : ℕ) :
    List Point :=
  List.ofFn fun j : Fin (n + 1) ↦ externalPosition o η j

@[simp] lemma externalPositionList_length (o : Orientation)
    (η : ℕ → RetainedBlock o) (n : ℕ) :
    (externalPositionList o η n).length = n + 1 := by
  simp [externalPositionList]

/-- Delete the first `t` retained blocks. -/
def externalShift (t : ℕ) (η : ℕ → RetainedBlock o) : ℕ → RetainedBlock o :=
  fun j ↦ η (t + j)

lemma measurable_externalShift (o : Orientation) (t : ℕ) :
    Measurable (externalShift (o := o) t) := by
  exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply (t + j)

/-- The IID product law is invariant under every forward shift. -/
theorem externalBlocks_map_externalShift (o : Orientation) (t : ℕ) :
    (externalBlocks o).map (externalShift (o := o) t) = externalBlocks o := by
  unfold externalBlocks externalShift
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ retainedBlockLaw o)
    (f := fun j : ℕ ↦ t + j) (fun _ _ h ↦ Nat.add_left_cancel h)

/-- The shifted chain is the translated suffix of the original chain. -/
lemma externalPosition_shift (o : Orientation) (t j : ℕ)
    (η : ℕ → RetainedBlock o) :
    externalPosition o (externalShift (o := o) t η) j =
      externalPosition o η (t + j) - externalPosition o η t := by
  unfold externalPosition externalShift
  rw [Finset.sum_range_add]
  simp only [add_sub_cancel_left]

lemma drop_externalPositionList (o : Orientation) (η : ℕ → RetainedBlock o)
    (n t : ℕ) :
    (externalPositionList o η n).drop t =
      List.ofFn (fun j : Fin ((n + 1) - t) ↦ externalPosition o η (t + j)) := by
  apply List.ext_get
  · simp [externalPositionList]
  · intro r hr₁ hr₂
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_drop]
    unfold externalPositionList
    rw [List.getElem_ofFn, List.getElem_ofFn]

lemma shiftedPositionList_count_eq (o : Orientation)
    (η : ℕ → RetainedBlock o) (t m : ℕ) :
    (List.ofFn (fun j : Fin (m + 1) ↦
      externalPosition o η (t + j))).count (externalPosition o η t) =
      externalOriginLocalTime o (externalShift (o := o) t η) m := by
  change listLocalTime
      (List.ofFn (fun j : Fin (m + 1) ↦ externalPosition o η (t + j)))
      (externalPosition o η t) = _
  rw [← finiteLocalTime_eq_listLocalTime]
  unfold externalOriginLocalTime
  rw [Finset.card_filter, Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ if externalPosition o η (t + j) = externalPosition o η t then 1 else 0)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [externalPosition_shift]
  by_cases h : externalPosition o η (t + j) = externalPosition o η t
  · simp [h]
  · simp [h, sub_ne_zero.mpr h]

/-- A good suffix is exactly an origin-local-time event for a fresh shifted
external walk, with the remaining horizon `n - t`. -/
lemma suffixGoodAt_externalPositionList_iff (o : Orientation)
    (η : ℕ → RetainedBlock o) (n k t : ℕ) (ht : t < n + 1) :
    suffixGoodAt (externalPositionList o η n) k t ↔
      k ≤ externalOriginLocalTime o (externalShift (o := o) t η) (n - t) := by
  unfold suffixGoodAt
  rw [drop_externalPositionList]
  have harith : (n + 1) - t = (n - t) + 1 := by omega
  rw [harith, List.ofFn_succ]
  simp only
  have hcount := shiftedPositionList_count_eq o η t (n - t)
  rw [List.ofFn_succ] at hcount
  exact iff_of_eq (congrArg (fun r ↦ k ≤ r) hcount)

lemma externalOriginLocalTime_mono (o : Orientation) (η : ℕ → RetainedBlock o)
    {a b : ℕ} (hab : a ≤ b) :
    externalOriginLocalTime o η a ≤ externalOriginLocalTime o η b := by
  unfold externalOriginLocalTime
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨by omega, hj.2⟩

lemma measurableSet_externalOriginLocalTime_ge_shift (o : Orientation)
    (t m k : ℕ) : MeasurableSet {η : ℕ → RetainedBlock o |
      k ≤ externalOriginLocalTime o (externalShift (o := o) t η) m} := by
  have hm : Measurable fun η : ℕ → RetainedBlock o ↦
      (externalOriginLocalTime o (externalShift (o := o) t η) m : ℝ≥0∞) :=
    (measurable_externalOriginLocalTime_ennreal o m).comp (measurable_externalShift o t)
  have hs : MeasurableSet {η : ℕ → RetainedBlock o |
      (k : ℝ≥0∞) ≤
        (externalOriginLocalTime o (externalShift (o := o) t η) m : ℝ≥0∞)} :=
    measurableSet_le (measurable_const : Measurable fun _ : ℕ → RetainedBlock o ↦
      (k : ℝ≥0∞)) hm
  simpa only [Nat.cast_le] using hs

lemma measurableSet_suffixGoodAt_externalPositionList (o : Orientation)
    (n k t : ℕ) : MeasurableSet {η : ℕ → RetainedBlock o |
      suffixGoodAt (externalPositionList o η n) k t} := by
  by_cases ht : t < n + 1
  · have hset : {η : ℕ → RetainedBlock o |
        suffixGoodAt (externalPositionList o η n) k t} =
        {η | k ≤ externalOriginLocalTime o (externalShift (o := o) t η) (n - t)} := by
      ext η
      exact suffixGoodAt_externalPositionList_iff o η n k t ht
    rw [hset]
    exact measurableSet_externalOriginLocalTime_ge_shift o t (n - t) k
  · have hdrop : ∀ η : ℕ → RetainedBlock o,
        (externalPositionList o η n).drop t = [] := by
      intro η
      exact List.drop_eq_nil_of_le (by simpa using (Nat.le_of_not_gt ht))
    have hset : {η : ℕ → RetainedBlock o |
        suffixGoodAt (externalPositionList o η n) k t} = ∅ := by
      ext η
      simp [suffixGoodAt, hdrop η]
    rw [hset]
    exact MeasurableSet.empty

/-- Time-shifting does not change the law of the external origin local time. -/
lemma measure_externalOriginLocalTime_ge_shift (o : Orientation)
    (t m k : ℕ) :
    externalBlocks o {η | k ≤
      externalOriginLocalTime o (externalShift (o := o) t η) m} =
      externalBlocks o {η | k ≤ externalOriginLocalTime o η m} := by
  let s : Set (ℕ → RetainedBlock o) :=
    {η | k ≤ externalOriginLocalTime o η m}
  have hs : MeasurableSet s := by
    have hm := measurableSet_externalOriginLocalTime_ge_shift o 0 m k
    have heq : s = {η : ℕ → RetainedBlock o |
        k ≤ externalOriginLocalTime o (externalShift (o := o) 0 η) m} := by
      ext η
      have hz : externalShift (o := o) 0 η = η := by
        funext j
        simp [externalShift]
      simp only [s, Set.mem_ofPred_eq, hz]
    rw [heq]
    exact hm
  calc
    externalBlocks o {η | k ≤
        externalOriginLocalTime o (externalShift (o := o) t η) m} =
        (externalBlocks o).map (externalShift (o := o) t) s := by
      rw [Measure.map_apply (measurable_externalShift o t) hs]
      rfl
    _ = externalBlocks o s := by rw [externalBlocks_map_externalShift]
    _ = externalBlocks o {η | k ≤ externalOriginLocalTime o η m} := rfl

lemma measure_suffixGoodAt_le_of_onePoint (o : Orientation)
    (n k t : ℕ) (q : ℝ≥0∞) (ht : t < n + 1)
    (hone : externalBlocks o {η | k ≤ externalOriginLocalTime o η n} ≤ q) :
    externalBlocks o {η | suffixGoodAt (externalPositionList o η n) k t} ≤ q := by
  have hset : {η : ℕ → RetainedBlock o |
      suffixGoodAt (externalPositionList o η n) k t} =
      {η | k ≤ externalOriginLocalTime o (externalShift (o := o) t η) (n - t)} := by
    ext η
    exact suffixGoodAt_externalPositionList_iff o η n k t ht
  rw [hset, measure_externalOriginLocalTime_ge_shift]
  refine (measure_mono ?_).trans hone
  intro η hη
  exact hη.trans (externalOriginLocalTime_mono o η (Nat.sub_le n t))

/-! ## External thick sites -/

/-- Number of distinct sites visited by external time `n` at least `k` times. -/
def externalThickCount (o : Orientation) (η : ℕ → RetainedBlock o)
    (n k : ℕ) : ℕ :=
  listThickCount (externalPositionList o η n) k

/-- The HLOZ Proposition 4.4 counting argument, reduced exactly to a
one-point tail at the origin of the retained-block walk. -/
theorem measure_externalThickCount_gt_le_of_onePoint (o : Orientation)
    (n k J : ℕ) (q : ℝ≥0∞)
    (hone : externalBlocks o {η | k ≤ externalOriginLocalTime o η n} ≤ q) :
    externalBlocks o {η | J < externalThickCount o η n k} ≤
      q * (n + 1) / (↑(J + 1) : ℝ≥0∞) := by
  exact measure_listThickCount_gt_le (externalBlocks o)
    (fun η ↦ externalPositionList o η n) n k J q
    (fun η ↦ externalPositionList_length o η n)
    (measurableSet_suffixGoodAt_externalPositionList o n k)
    (fun t ht ↦ measure_suffixGoodAt_le_of_onePoint o n k t q ht hone)

/-! ## The exact HLOZ Proposition 4.4 parameters -/

/-- The concrete admissible value `κ₁ = 11/32` used elsewhere in the
development. -/
noncomputable def hlozKappaOne44 : ℝ := 11 / 32

/-- HLOZ's `δ = 7/5 - 4κ₁`; at `κ₁ = 11/32` it is `1/40`. -/
noncomputable def hlozDelta44 : ℝ := 1 / 40

lemma hlozDelta44_eq :
    hlozDelta44 = 7 / 5 - 4 * hlozKappaOne44 := by
  norm_num [hlozDelta44, hlozKappaOne44]

lemma hlozKappaOne44_range :
    1 / 3 < hlozKappaOne44 ∧ hlozKappaOne44 < 7 / 20 := by
  norm_num [hlozKappaOne44]

/-- The deterministic external-time cutoff.  This is the repository's exact
natural-valued version of `ψₘ`, namely the ceiling of the displayed real
exponential cutoff. -/
noncomputable def hlozCutoff44 (m : ℕ) : ℕ :=
  levelCutoffTime hlozDelta44 m

/-- The exponent `1 - 2κ₁ = 5/16`. -/
noncomputable def hlozRateScale44 (m : ℕ) : ℝ :=
  (m : ℝ) ^ (5 / 16 : ℝ)

/-- The natural threshold representing the strict inequality
`external local time > 15m/16 - m^(4/5)`. -/
noncomputable def hlozThickThresholdReal44 (m : ℕ) : ℝ :=
  (15 / 16 : ℝ) * m - (m : ℝ) ^ (4 / 5 : ℝ)

noncomputable def hlozThickLevel44 (m : ℕ) : ℕ :=
  ⌊hlozThickThresholdReal44 m⌋₊ + 1

/-- The HLOZ one-point threshold at the cutoff time.  A natural local time
above this ceiling is above the real threshold in (7.4). -/
noncomputable def hlozOnePointThresholdReal44 (m : ℕ) : ℝ :=
  (15 / (16 * Real.pi) : ℝ) * levelCutoffLog hlozDelta44 m ^ 2 -
    2 * levelCutoffLog hlozDelta44 m ^ (13 / 8 : ℝ)

noncomputable def hlozOnePointLevel44 (m : ℕ) : ℕ :=
  ⌈hlozOnePointThresholdReal44 m⌉₊

/-- The strict cardinality cutoff `exp(16 m^(1-2κ₁))`. -/
noncomputable def hlozSiteBudget44 (m : ℕ) : ℕ :=
  ⌊Real.exp (16 * hlozRateScale44 m)⌋₊

/-- The right side of HLOZ (7.4), specialized to `κ₁ = 11/32`:
`n⁻¹ exp(8 (log n)^(2-4κ₁))`. -/
noncomputable def hlozOnePointRate44 (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-levelCutoffLog hlozDelta44 m +
      8 * levelCutoffLog hlozDelta44 m ^ (5 / 8 : ℝ)))

/-- The target exceptional probability in Proposition 4.4. -/
noncomputable def hlozFailureRate44 (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-hlozRateScale44 m))

/-- The cutoff is exactly HLOZ's
`exp(π^(1/2)m^(1/2) + π^(2-2κ₁)m^(1-2κ₁))`, before taking the
natural ceiling. -/
lemma hlozCutoffLog44_eq {m : ℕ} (hm : 0 < m) :
    levelCutoffLog hlozDelta44 m =
      Real.pi ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) +
        Real.pi ^ (21 / 16 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ) := by
  rw [levelCutoffLog_eq_hloz hlozDelta44 hm]
  congr 1 <;> norm_num [hlozDelta44]

/-- A fixed multiple of a smaller positive power is eventually bounded by a
larger power.  This helper keeps the HLOZ cutoff comparisons pointwise and
explicit. -/
lemma eventually_const_mul_nat_rpow_le (C a b : ℝ) (hab : a < b) :
    ∀ᶠ m : ℕ in atTop, C * (m : ℝ) ^ a ≤ (m : ℝ) ^ b := by
  have ht : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop C), eventually_ge_atTop 1]
      with m hmPow hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    C * (m : ℝ) ^ a ≤ (m : ℝ) ^ (b - a) * (m : ℝ) ^ a := by
      exact mul_le_mul_of_nonneg_right hmPow (Real.rpow_nonneg hmR.le _)
    _ = (m : ℝ) ^ b := by
      rw [mul_comm, ← Real.rpow_add hmR]
      congr 1
      ring

lemma hlozLeading_rpow_thirteen_eighths (m : ℕ) :
    levelCutoffLeading m ^ (13 / 8 : ℝ) =
      Real.pi ^ (13 / 16 : ℝ) * (m : ℝ) ^ (13 / 16 : ℝ) := by
  rw [levelCutoffLeading_eq_hloz]
  rw [Real.mul_rpow (Real.rpow_nonneg Real.pi_pos.le _) (by positivity)]
  rw [← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_mul (Nat.cast_nonneg m)]
  congr 1 <;> norm_num

lemma hlozLeading_mul_correction (m : ℕ) :
    levelCutoffLeading m * levelCutoffCorrection hlozDelta44 m =
      Real.pi ^ (29 / 16 : ℝ) * (m : ℝ) ^ (13 / 16 : ℝ) := by
  by_cases hm : m = 0
  · subst m
    norm_num [levelCutoffLeading, levelCutoffCorrection, levelTailExponent,
      hlozDelta44]
  · have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    rw [levelCutoffLeading_eq_hloz, levelCutoffCorrection_eq_hloz hlozDelta44
      (Nat.pos_of_ne_zero hm)]
    norm_num [hlozDelta44]
    calc
      (Real.pi ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ)) *
          (Real.pi ^ (21 / 16 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ)) =
        (Real.pi ^ (1 / 2 : ℝ) * Real.pi ^ (21 / 16 : ℝ)) *
          ((m : ℝ) ^ (1 / 2 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add Real.pi_pos, ← Real.rpow_add hmR]
        norm_num

lemma hlozCorrection_sq (m : ℕ) :
    levelCutoffCorrection hlozDelta44 m ^ 2 =
      Real.pi ^ (21 / 8 : ℝ) * (m : ℝ) ^ (5 / 8 : ℝ) := by
  by_cases hm : m = 0
  · subst m
    norm_num [levelCutoffCorrection, levelCutoffLeading, levelTailExponent,
      hlozDelta44]
  · rw [levelCutoffCorrection_eq_hloz hlozDelta44 (Nat.pos_of_ne_zero hm)]
    have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    norm_num [hlozDelta44]
    calc
      (Real.pi ^ (21 / 16 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ)) ^ 2 =
        (Real.pi ^ (21 / 16 : ℝ) * Real.pi ^ (21 / 16 : ℝ)) *
          ((m : ℝ) ^ (5 / 16 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ)) := by
            ring
      _ = _ := by
        rw [← Real.rpow_add Real.pi_pos,
          ← Real.rpow_add hmR]
        norm_num

lemma hlozOnePointThresholdReal44_le_expansion (m : ℕ) :
    hlozOnePointThresholdReal44 m ≤
      (15 / 16 : ℝ) * m -
        (1 / 8 : ℝ) * Real.pi ^ (13 / 16 : ℝ) *
          (m : ℝ) ^ (13 / 16 : ℝ) +
        (15 / (16 * Real.pi) : ℝ) * Real.pi ^ (21 / 8 : ℝ) *
          (m : ℝ) ^ (5 / 8 : ℝ) := by
  let a := levelCutoffLeading m
  let b := levelCutoffCorrection hlozDelta44 m
  have ha : 0 ≤ a := levelCutoffLeading_nonneg m
  have hb : 0 ≤ b := levelCutoffCorrection_nonneg hlozDelta44 m
  have hpow : a ^ (13 / 8 : ℝ) ≤ (a + b) ^ (13 / 8 : ℝ) :=
    Real.rpow_le_rpow ha (le_add_of_nonneg_right hb) (by norm_num)
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  unfold hlozOnePointThresholdReal44 levelCutoffLog
  change (15 / (16 * Real.pi) : ℝ) * (a + b) ^ 2 -
      2 * (a + b) ^ (13 / 8 : ℝ) ≤ _
  calc
    (15 / (16 * Real.pi) : ℝ) * (a + b) ^ 2 -
        2 * (a + b) ^ (13 / 8 : ℝ) ≤
      (15 / (16 * Real.pi) : ℝ) * (a + b) ^ 2 -
        2 * a ^ (13 / 8 : ℝ) := by gcongr
    _ = _ := by
      rw [add_sq,
        show a ^ 2 = Real.pi * m by simpa [a] using levelCutoffLeading_sq m,
        show 2 * a * b = 2 * (Real.pi ^ (29 / 16 : ℝ) *
            (m : ℝ) ^ (13 / 16 : ℝ)) by
          calc
            2 * a * b = 2 * (a * b) := by ring
            _ = _ := by rw [show a * b = Real.pi ^ (29 / 16 : ℝ) *
              (m : ℝ) ^ (13 / 16 : ℝ) by
                simpa [a, b] using hlozLeading_mul_correction m],
        show b ^ 2 = Real.pi ^ (21 / 8 : ℝ) *
            (m : ℝ) ^ (5 / 8 : ℝ) by
          simpa [b] using hlozCorrection_sq m,
        show a ^ (13 / 8 : ℝ) = Real.pi ^ (13 / 16 : ℝ) *
            (m : ℝ) ^ (13 / 16 : ℝ) by
          simpa [a] using hlozLeading_rpow_thirteen_eighths m]
      have hpiPow : Real.pi ^ (29 / 16 : ℝ) =
          Real.pi * Real.pi ^ (13 / 16 : ℝ) := by
        calc
          Real.pi ^ (29 / 16 : ℝ) = Real.pi ^ (1 + 13 / 16 : ℝ) := by
            norm_num
          _ = Real.pi ^ (1 : ℝ) * Real.pi ^ (13 / 16 : ℝ) :=
            Real.rpow_add Real.pi_pos 1 (13 / 16)
          _ = _ := by rw [Real.rpow_one]
      rw [hpiPow]
      field_simp
      ring

/-- The one-point level in (7.4) is eventually below the thick-site level
`15m/16 - m^(4/5)`.  This is the cutoff cancellation for
`δ = 1/40`, with all lower powers absorbed explicitly. -/
theorem eventually_hlozOnePointLevel44_le_thickLevel44 :
    ∀ᶠ m : ℕ in atTop, hlozOnePointLevel44 m ≤ hlozThickLevel44 m := by
  let D : ℝ := (1 / 8 : ℝ) * Real.pi ^ (13 / 16 : ℝ)
  let E : ℝ := (15 / (16 * Real.pi) : ℝ) * Real.pi ^ (21 / 8 : ℝ)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hfourFifths : (4 / 5 : ℝ) < 13 / 16 := by norm_num
  have hfiveEighths : (5 / 8 : ℝ) < 13 / 16 := by norm_num
  filter_upwards
      [eventually_const_mul_nat_rpow_le (2 / D) (4 / 5) (13 / 16)
        hfourFifths,
       eventually_const_mul_nat_rpow_le (2 * E / D) (5 / 8) (13 / 16)
        hfiveEighths]
      with m hmMain hmError
  have hmMain' : 2 * (m : ℝ) ^ (4 / 5 : ℝ) ≤
      D * (m : ℝ) ^ (13 / 16 : ℝ) := by
    have hdiv : (2 * (m : ℝ) ^ (4 / 5 : ℝ)) / D ≤
        (m : ℝ) ^ (13 / 16 : ℝ) := by
      convert hmMain using 1 <;> ring
    simpa [mul_comm] using (div_le_iff₀ hD).mp hdiv
  have hmError' : 2 * E * (m : ℝ) ^ (5 / 8 : ℝ) ≤
      D * (m : ℝ) ^ (13 / 16 : ℝ) := by
    have hdiv : (2 * E * (m : ℝ) ^ (5 / 8 : ℝ)) / D ≤
        (m : ℝ) ^ (13 / 16 : ℝ) := by
      convert hmError using 1 <;> ring
    simpa [mul_comm] using (div_le_iff₀ hD).mp hdiv
  have hreal : hlozOnePointThresholdReal44 m ≤
      hlozThickThresholdReal44 m := by
    have hexpansion := hlozOnePointThresholdReal44_le_expansion m
    change hlozOnePointThresholdReal44 m ≤
      (15 / 16 : ℝ) * m - (m : ℝ) ^ (4 / 5 : ℝ)
    change hlozOnePointThresholdReal44 m ≤
      (15 / 16 : ℝ) * m -
        D * (m : ℝ) ^ (13 / 16 : ℝ) +
        E * (m : ℝ) ^ (5 / 8 : ℝ) at hexpansion
    nlinarith
  unfold hlozOnePointLevel44 hlozThickLevel44
  apply Nat.ceil_le.mpr
  have hfloor := (Nat.lt_floor_add_one (hlozThickThresholdReal44 m)).le
  exact hreal.trans (by simpa only [Nat.cast_add, Nat.cast_one] using hfloor)

lemma eventually_hlozCutoffLog44_le_nine_fifths_sqrt :
    ∀ᶠ m : ℕ in atTop,
      levelCutoffLog hlozDelta44 m ≤
        (9 / 5 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) := by
  have hsqrtPi : Real.pi ^ (1 / 2 : ℝ) < 71 / 40 := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_lt' (by norm_num)).2
    nlinarith [Real.pi_lt_d2]
  filter_upwards
      [eventually_const_mul_nat_rpow_le
        (40 * Real.pi ^ (21 / 16 : ℝ)) (5 / 16) (1 / 2) (by norm_num),
       eventually_ge_atTop 1]
      with m hcorrection hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hleading : Real.pi ^ (1 / 2 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) ≤
      (71 / 40 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right hsqrtPi.le (Real.rpow_nonneg hmR.le _)
  have hcorrection' : Real.pi ^ (21 / 16 : ℝ) *
      (m : ℝ) ^ (5 / 16 : ℝ) ≤
        (1 / 40 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) := by
    nlinarith
  rw [hlozCutoffLog44_eq hm]
  nlinarith

/-- The logarithmic correction in the one-point rate uses at most fourteen
of the sixteen available units of `m^(5/16)`; the remaining two absorb the
finite ceiling factor. -/
lemma eventually_hlozLogRate44_le :
    ∀ᶠ m : ℕ in atTop,
      8 * levelCutoffLog hlozDelta44 m ^ (5 / 8 : ℝ) + 2 ≤
        15 * hlozRateScale44 m := by
  filter_upwards
      [eventually_hlozCutoffLog44_le_nine_fifths_sqrt,
       eventually_const_mul_nat_rpow_le (10 / 3) 0 (5 / 16) (by norm_num),
       eventually_ge_atTop 1]
      with m hlog hconstant hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlogNonneg : 0 ≤ levelCutoffLog hlozDelta44 m :=
    levelCutoffLog_nonneg hlozDelta44 m
  have hpow := Real.rpow_le_rpow hlogNonneg hlog (by norm_num : (0 : ℝ) ≤ 5 / 8)
  have hcoeff : (9 / 5 : ℝ) ^ (5 / 8 : ℝ) ≤ 9 / 5 :=
    by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le (x := (9 / 5 : ℝ))
          (y := (5 / 8 : ℝ)) (z := 1) (by norm_num) (by norm_num))
  have hrhs : ((9 / 5 : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ)) ^
      (5 / 8 : ℝ) ≤ (9 / 5 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hmR.le _)]
    rw [← Real.rpow_mul hmR.le]
    norm_num
    exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hmR.le _)
  have hlogPow : levelCutoffLog hlozDelta44 m ^ (5 / 8 : ℝ) ≤
      (9 / 5 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ) := hpow.trans hrhs
  have hconstant' : (10 / 3 : ℝ) ≤ (m : ℝ) ^ (5 / 16 : ℝ) := by
    simpa using hconstant
  have habsorb : (2 : ℝ) ≤
      (3 / 5 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ) := by
    calc
      (2 : ℝ) = (3 / 5 : ℝ) * (10 / 3 : ℝ) := by norm_num
      _ ≤ (3 / 5 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ) := by gcongr
  unfold hlozRateScale44
  calc
    8 * levelCutoffLog hlozDelta44 m ^ (5 / 8 : ℝ) + 2 ≤
        8 * ((9 / 5 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ)) + 2 := by
      gcongr
    _ ≤ 15 * (m : ℝ) ^ (5 / 16 : ℝ) := by
      calc
        8 * ((9 / 5 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ)) + 2 ≤
            8 * ((9 / 5 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ)) +
              (3 / 5 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ) :=
          by simpa [add_comm] using
            (add_le_add_left habsorb
              (8 * ((9 / 5 : ℝ) * (m : ℝ) ^ (5 / 16 : ℝ))))
        _ = _ := by ring

lemma hlozCutoff44_cast_add_one_le (m : ℕ) :
    ((hlozCutoff44 m + 1 : ℕ) : ℝ) ≤
      3 * Real.exp (levelCutoffLog hlozDelta44 m) := by
  have hceil : ((hlozCutoff44 m : ℕ) : ℝ) <
      Real.exp (levelCutoffLog hlozDelta44 m) + 1 := by
    simpa [hlozCutoff44, levelCutoffTime, levelCutoff] using
      (Nat.ceil_lt_add_one (Real.exp_nonneg (levelCutoffLog hlozDelta44 m)))
  have hone : (1 : ℝ) ≤ Real.exp (levelCutoffLog hlozDelta44 m) :=
    Real.one_le_exp_iff.mpr (levelCutoffLog_nonneg hlozDelta44 m)
  push_cast
  linarith

lemma hlozBudget44_real_lt_cast_add_one (m : ℕ) :
    Real.exp (16 * hlozRateScale44 m) <
      ((hlozSiteBudget44 m + 1 : ℕ) : ℝ) := by
  simpa [hlozSiteBudget44] using
    (Nat.lt_floor_add_one (Real.exp (16 * hlozRateScale44 m)))

lemma eventually_hlozMarkovRate44_real_lt :
    ∀ᶠ m : ℕ in atTop,
      Real.exp (-levelCutoffLog hlozDelta44 m +
          8 * levelCutoffLog hlozDelta44 m ^ (5 / 8 : ℝ)) *
          ((hlozCutoff44 m + 1 : ℕ) : ℝ) /
          ((hlozSiteBudget44 m + 1 : ℕ) : ℝ) <
        Real.exp (-hlozRateScale44 m) := by
  filter_upwards [eventually_hlozLogRate44_le] with m hrate
  let L := levelCutoffLog hlozDelta44 m
  let S := hlozRateScale44 m
  have hnum : Real.exp (-L + 8 * L ^ (5 / 8 : ℝ)) *
      ((hlozCutoff44 m + 1 : ℕ) : ℝ) ≤
        Real.exp (15 * S) := by
    calc
      Real.exp (-L + 8 * L ^ (5 / 8 : ℝ)) *
          ((hlozCutoff44 m + 1 : ℕ) : ℝ) ≤
        Real.exp (-L + 8 * L ^ (5 / 8 : ℝ)) *
          (3 * Real.exp L) := by
            gcongr
            exact hlozCutoff44_cast_add_one_le m
      _ = 3 * Real.exp (8 * L ^ (5 / 8 : ℝ)) := by
        rw [Real.exp_add]
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
      _ ≤ Real.exp (2 + 8 * L ^ (5 / 8 : ℝ)) := by
        rw [Real.exp_add]
        gcongr
        nlinarith [Real.add_one_le_exp (2 : ℝ)]
      _ ≤ Real.exp (15 * S) := by
        apply Real.exp_le_exp.mpr
        simpa [L, S, add_comm] using hrate
  have hden : Real.exp (16 * S) <
      ((hlozSiteBudget44 m + 1 : ℕ) : ℝ) := by
    simpa [S] using hlozBudget44_real_lt_cast_add_one m
  have hdenPos : (0 : ℝ) < ((hlozSiteBudget44 m + 1 : ℕ) : ℝ) := by
    positivity
  apply (div_lt_iff₀ hdenPos).2
  calc
    Real.exp (-L + 8 * L ^ (5 / 8 : ℝ)) *
        ((hlozCutoff44 m + 1 : ℕ) : ℝ) ≤ Real.exp (15 * S) := hnum
    _ = Real.exp (-S) * Real.exp (16 * S) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ < Real.exp (-S) * ((hlozSiteBudget44 m + 1 : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_left hden (Real.exp_pos _)

/-- All of the Markov/budget arithmetic in Proposition 4.4, including the
integer ceiling and floor conventions, holds eventually. -/
theorem eventually_hlozMarkovRate44_lt_failureRate44 :
    ∀ᶠ m : ℕ in atTop,
      hlozOnePointRate44 m * (hlozCutoff44 m + 1) /
          (↑(hlozSiteBudget44 m + 1) : ℝ≥0∞) < hlozFailureRate44 m := by
  filter_upwards [eventually_hlozMarkovRate44_real_lt] with m hm
  unfold hlozOnePointRate44 hlozFailureRate44
  have hcut : ((↑(hlozCutoff44 m) : ℝ≥0∞) + 1) =
      ENNReal.ofReal (((hlozCutoff44 m + 1 : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_natCast]
    norm_cast
  rw [hcut, ← ENNReal.ofReal_natCast (hlozSiteBudget44 m + 1),
    ← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← ENNReal.ofReal_div_of_pos (by positivity :
      (0 : ℝ) < (hlozSiteBudget44 m + 1 : ℕ))]
  exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2 hm

/-- Fully specialized Markov estimate at the HLOZ cutoff.  The level
comparison is the elementary cutoff expansion used in the paper; the
probabilistic premise is precisely the still-missing sharp one-point bound
(7.4). -/
theorem hloz_externalThickCount_markov44 (o : Orientation) (m : ℕ)
    (hlevel : hlozOnePointLevel44 m ≤ hlozThickLevel44 m)
    (hone : externalBlocks o {η |
      hlozOnePointLevel44 m ≤
        externalOriginLocalTime o η (hlozCutoff44 m)} ≤ hlozOnePointRate44 m) :
    externalBlocks o {η |
        hlozSiteBudget44 m < externalThickCount o η
          (hlozCutoff44 m) (hlozThickLevel44 m)} ≤
      hlozOnePointRate44 m * (hlozCutoff44 m + 1) /
        (↑(hlozSiteBudget44 m + 1) : ℝ≥0∞) := by
  apply measure_externalThickCount_gt_le_of_onePoint
  refine (measure_mono ?_).trans hone
  intro η hη
  exact hlevel.trans hη

/-- Exact implication giving the numerical conclusion of HLOZ Proposition
4.4.  Apart from (7.4), its remaining premise is the explicit real-arithmetic
comparison between the displayed cutoff, budget, and failure rate. -/
theorem hloz_externalThickCount_failure44 (o : Orientation) (m : ℕ)
    (hlevel : hlozOnePointLevel44 m ≤ hlozThickLevel44 m)
    (harith : hlozOnePointRate44 m * (hlozCutoff44 m + 1) /
      (↑(hlozSiteBudget44 m + 1) : ℝ≥0∞) ≤ hlozFailureRate44 m)
    (hone : externalBlocks o {η |
      hlozOnePointLevel44 m ≤
        externalOriginLocalTime o η (hlozCutoff44 m)} ≤ hlozOnePointRate44 m) :
    externalBlocks o {η |
        hlozSiteBudget44 m < externalThickCount o η
          (hlozCutoff44 m) (hlozThickLevel44 m)} ≤
      hlozFailureRate44 m :=
  (hloz_externalThickCount_markov44 o m hlevel hone).trans harith

/-- What the presently checked Green-renewal layer gives at the Proposition
4.4 parameters.  A Green increment and logarithmic upper bound produce the
exact geometric one-point rate; recovering HLOZ's sharper rate requires the
missing sharp Green/local-time analysis. -/
theorem hloz_externalThickCount_of_logarithmicGreen44 (o : Orientation) (m : ℕ)
    (c : ℝ≥0∞) (C : ℝ)
    (hlevel : hlozOnePointLevel44 m ≤ hlozThickLevel44 m)
    (hk : 0 < hlozOnePointLevel44 m)
    (hincrement : ExternalRenewal.externalTruncatedGreen o (2 * hlozCutoff44 m) - 1 ≤
      ExternalRenewal.externalTruncatedGreen o (hlozCutoff44 m) - c)
    (hgreen : ExternalRenewal.externalTruncatedGreen o (hlozCutoff44 m) ≤
      ENNReal.ofReal (C * Real.log (hlozCutoff44 m + 2))) :
    externalBlocks o {η |
        hlozSiteBudget44 m < externalThickCount o η
          (hlozCutoff44 m) (hlozThickLevel44 m)} ≤
      (1 - c / ENNReal.ofReal (C * Real.log (hlozCutoff44 m + 2))) ^
          (hlozOnePointLevel44 m - 1) * (hlozCutoff44 m + 1) /
        (↑(hlozSiteBudget44 m + 1) : ℝ≥0∞) := by
  apply measure_externalThickCount_gt_le_of_onePoint
  have hsubset : {η : ℕ → RetainedBlock o |
      hlozThickLevel44 m ≤ externalOriginLocalTime o η (hlozCutoff44 m)} ⊆
      {η | hlozOnePointLevel44 m ≤
        externalOriginLocalTime o η (hlozCutoff44 m)} := by
    intro η hη
    exact hlevel.trans hη
  refine (measure_mono hsubset).trans ?_
  have htail := ExternalRenewal.externalOriginLocalTime_tail_le_logarithmic
    o (hlozOnePointLevel44 m - 1) (hlozCutoff44 m) c C hincrement hgreen
  simpa only [Nat.sub_add_cancel hk] using htail

/-- The sole unresolved probabilistic statement needed by the specialized
Proposition 4.4 count. -/
def HLOZSharpExternalOnePointTail44 (o : Orientation) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    externalBlocks o {η |
      hlozOnePointLevel44 m ≤
        externalOriginLocalTime o η (hlozCutoff44 m)} ≤ hlozOnePointRate44 m

/-- Proposition 4.4 for one deletion orientation.  All deterministic,
measurability, shift, threshold, ceiling/floor, and exponential-rate work is
discharged; the only hypothesis is HLOZ's sharp one-point local-time tail. -/
theorem eventually_hloz_externalThickCount_failure44 (o : Orientation)
    (hone : HLOZSharpExternalOnePointTail44 o) :
    ∀ᶠ m : ℕ in atTop,
      externalBlocks o {η |
          hlozSiteBudget44 m < externalThickCount o η
            (hlozCutoff44 m) (hlozThickLevel44 m)} < hlozFailureRate44 m := by
  filter_upwards [eventually_hlozOnePointLevel44_le_thickLevel44,
      eventually_hlozMarkovRate44_lt_failureRate44, hone]
      with m hlevel harith honeM
  exact (hloz_externalThickCount_markov44 o m hlevel honeM).trans_lt harith

end
end Erdos1165.ExternalProposition44
