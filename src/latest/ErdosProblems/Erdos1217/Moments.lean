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

import ErdosProblems.Erdos1217.Basic
import ErdosProblems.Erdos1217.ReverseFatou
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The moment argument for Erdős Problem 1217

This file isolates the probabilistic part of the ABLLPSTT argument.  The
random variable `visitedCount A X ω` counts the elements of `A ∩ [1,X)`
visited by the path `ω`.  Its first moment is the sum of the hitting
probabilities.  Strict upward divisibility gives the deterministic square
bound

`visitedCount² ≤ ∑ (2 * Ω(n) + 1) 1_{ω hits n}`.

The last theorem packages the reverse-Fatou extraction.  It is deliberately
stated for an arbitrary probability law on paths; `UpwardChain.Data.pathMeasure`
is the intended application, with hitting probabilities supplied by
`UpwardChain.Data.hitMass` and then identified with `nuLambda`.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal ArithmeticFunction.Omega

noncomputable section

namespace Erdos1217

attribute [local instance] Classical.propDecidable

/-- The event that a path visits the state `n`. -/
def hitEvent (n : ℕ) : Set (ℕ → ℕ) :=
  { ω | ∃ k, ω k = n }

lemma measurableSet_hitEvent (n : ℕ) : MeasurableSet (hitEvent n) := by
  have hcoord (k : ℕ) : MeasurableSet {ω : ℕ → ℕ | ω k = n} :=
    (measurableSet_singleton n).preimage (measurable_pi_apply k)
  simpa only [hitEvent, Set.mem_setOf_eq, Set.iUnion_setOf] using
    (MeasurableSet.iUnion hcoord)

/-- States of `A ∩ [1,X)` visited by a path. -/
noncomputable def visitedBelow (A : Set ℕ) (X : ℕ) (ω : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (positiveBelowNat X).filter fun n ↦ n ∈ A ∧ ω ∈ hitEvent n

/-- Number of states of `A ∩ [1,X)` visited by a path. -/
noncomputable def visitedCount (A : Set ℕ) (X : ℕ) (ω : ℕ → ℕ) : ℕ :=
  (visitedBelow A X ω).card

@[simp] lemma mem_visitedBelow_iff {A : Set ℕ} {X n : ℕ} {ω : ℕ → ℕ} :
    n ∈ visitedBelow A X ω ↔ 1 ≤ n ∧ n < X ∧ n ∈ A ∧ ω ∈ hitEvent n := by
  simp [visitedBelow, and_assoc]

lemma visitedCount_eq_sum_indicator (A : Set ℕ) (X : ℕ) (ω : ℕ → ℕ) :
    visitedCount A X ω =
      ∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A),
        if ω ∈ hitEvent n then 1 else 0 := by
  classical
  rw [visitedCount, visitedBelow, Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnA : n ∈ A <;> by_cases hh : ω ∈ hitEvent n <;> simp [hnA, hh]

lemma measurable_visitedCount (A : Set ℕ) (X : ℕ) :
    Measurable (visitedCount A X) := by
  classical
  have hind (n : ℕ) : Measurable fun ω : ℕ → ℕ ↦
      if ω ∈ hitEvent n then (1 : ℕ) else 0 :=
    measurable_const.ite (measurableSet_hitEvent n) measurable_const
  have hsum : Measurable fun ω : ℕ → ℕ ↦
      ∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A),
        if ω ∈ hitEvent n then 1 else 0 := by
    fun_prop
  have heq : visitedCount A X = fun ω : ℕ → ℕ ↦
      ∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A),
        if ω ∈ hitEvent n then 1 else 0 := by
    funext ω
    exact visitedCount_eq_sum_indicator A X ω
  rw [heq]
  exact hsum

/-- ENNReal-valued count, the form convenient for `lintegral`. -/
def visitedCountENNReal (A : Set ℕ) (X : ℕ) (ω : ℕ → ℕ) : ENNReal :=
  visitedCount A X ω

lemma measurable_visitedCountENNReal (A : Set ℕ) (X : ℕ) :
    Measurable (visitedCountENNReal A X) := by
  exact (measurable_of_countable fun n : ℕ ↦ (n : ENNReal)).comp
    (measurable_visitedCount A X)

lemma visitedCountENNReal_ne_top (A : Set ℕ) (X : ℕ) (ω : ℕ → ℕ) :
    visitedCountENNReal A X ω ≠ ∞ := by
  simp [visitedCountENNReal]

lemma visitedCountENNReal_eq_sum_indicator (A : Set ℕ) (X : ℕ) (ω : ℕ → ℕ) :
    visitedCountENNReal A X ω =
      ∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A),
        if ω ∈ hitEvent n then (1 : ENNReal) else 0 := by
  rw [visitedCountENNReal, visitedCount_eq_sum_indicator]
  push_cast
  rfl

/-- The first moment is the finite sum of the hitting probabilities. -/
theorem lintegral_visitedCountENNReal
    {mu : Measure (ℕ → ℕ)} (A : Set ℕ) (X : ℕ) (v : ℕ → ENNReal)
    (hhit : ∀ n, mu (hitEvent n) = v n) :
    (∫⁻ ω, visitedCountENNReal A X ω ∂mu) =
      ∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A), v n := by
  rw [show (fun ω ↦ visitedCountENNReal A X ω) = fun ω ↦
      ∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A),
        if ω ∈ hitEvent n then (1 : ENNReal) else 0 by
    funext ω
    exact visitedCountENNReal_eq_sum_indicator A X ω]
  rw [lintegral_finsetSum]
  apply Finset.sum_congr rfl
  intro n hn
  have hfun : (fun a : ℕ → ℕ ↦ if a ∈ hitEvent n then (1 : ENNReal) else 0) =
      (hitEvent n).indicator (fun _ ↦ (1 : ENNReal)) := by
    funext a
    simp only [Set.indicator_apply]
  rw [hfun]
  calc
    (∫⁻ a, (hitEvent n).indicator (fun _ ↦ (1 : ENNReal)) a ∂mu) =
        mu (hitEvent n) := by
      change (∫⁻ a, (hitEvent n).indicator (1 : (ℕ → ℕ) → ENNReal) a ∂mu) = _
      exact lintegral_indicator_one (μ := mu) (measurableSet_hitEvent n)
    _ = v n := hhit n
  · intro n hn
    exact measurable_const.ite (measurableSet_hitEvent n) measurable_const

/-! ## The deterministic square bound -/

/-- Among distinct natural times, the sum of `2k+1` dominates the square of
their number. -/
lemma card_sq_le_sum_two_mul_add_one (s : Finset ℕ) :
    s.card ^ 2 ≤ ∑ k ∈ s, (2 * k + 1) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
      by_cases hs : s.Nonempty
      · let m := s.max' hs
        have hm : m ∈ s := s.max'_mem hs
        have hsub : s.erase m ⊂ s := Finset.erase_ssubset hm
        have hih := ih (s.erase m) hsub
        have heraseRange : s.erase m ⊆ Finset.range m := by
          intro k hk
          rw [Finset.mem_range]
          exact s.lt_max'_of_mem_erase_max' hs hk
        have hcard : (s.erase m).card ≤ m := by
          simpa using Finset.card_le_card heraseRange
        have hcardEq : s.card = (s.erase m).card + 1 := by
          have hspos : 0 < s.card := Finset.card_pos.mpr hs
          rw [Finset.card_erase_of_mem hm]
          omega
        have hsumEq : (∑ k ∈ s, (2 * k + 1)) =
            (∑ k ∈ s.erase m, (2 * k + 1)) + (2 * m + 1) := by
          simpa only [Finset.sum_erase_add _ _ hm]
        rw [hcardEq, hsumEq]
        calc
          ((s.erase m).card + 1) ^ 2 =
              (s.erase m).card ^ 2 + (2 * (s.erase m).card + 1) := by ring
          _ ≤ (∑ k ∈ s.erase m, (2 * k + 1)) + (2 * m + 1) :=
            Nat.add_le_add hih (by omega)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
        simp

/-- Positivity and strict upward divisibility of a path. -/
def IsStrictDivisibilityPath (ω : ℕ → ℕ) : Prop :=
  (∀ k, 0 < ω k) ∧ (∀ k, ω k ∣ ω (k + 1) ∧ ω k < ω (k + 1))

lemma IsStrictDivisibilityPath.strictMono { ω : ℕ → ℕ }
    (hω : IsStrictDivisibilityPath ω) : StrictMono ω :=
  strictMono_nat_of_lt_succ fun k ↦ (hω.2 k).2

/-- The first time at which a path hits `n`; it is used only when `n` is
actually hit. -/
noncomputable def firstHitTime (ω : ℕ → ℕ) (n : ℕ) : ℕ :=
  if h : ∃ k, ω k = n then Nat.find h else 0

lemma firstHitTime_spec {ω : ℕ → ℕ} {n : ℕ} (hn : ω ∈ hitEvent n) :
    ω (firstHitTime ω n) = n := by
  have hex : ∃ k, ω k = n := by simpa only [hitEvent, Set.mem_setOf_eq] using hn
  rw [firstHitTime, dif_pos hex]
  exact Nat.find_spec hex

lemma firstHitTime_injective_on { ω : ℕ → ℕ }
    (hω : IsStrictDivisibilityPath ω) :
    Set.InjOn (firstHitTime ω) {n | ω ∈ hitEvent n} := by
  intro m hm n hn hmn
  rw [← firstHitTime_spec hm, ← firstHitTime_spec hn]
  exact congrArg ω hmn

/-- The prime-factor rank bounds the first hitting time along a strict
divisibility path. -/
lemma firstHitTime_le_cardFactors { ω : ℕ → ℕ }
    (hω : IsStrictDivisibilityPath ω) {n : ℕ} (hn : ω ∈ hitEvent n) :
    firstHitTime ω n ≤ Ω n := by
  have hindex : ∀ j, j ≤ Ω (ω j) := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
        have hlt : Ω (ω j) < Ω (ω (j + 1)) := by
          obtain ⟨c, hc⟩ := (hω.2 j).1
          have hcOne : 1 < c := by
            by_contra hc'
            have hcLe : c ≤ 1 := Nat.le_of_not_gt hc'
            have hnextPos := hω.1 (j + 1)
            have hstrict := (hω.2 j).2
            interval_cases c <;> simp_all
          rw [hc]
          rw [ArithmeticFunction.cardFactors_mul (hω.1 j).ne' (by omega : c ≠ 0)]
          have hcOmega : 0 < Ω c :=
            ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hcOne
          omega
        omega
  simpa only [firstHitTime_spec hn] using hindex (firstHitTime ω n)

/-- The deterministic second-moment estimate: the square of the number of
visited states is charged to the prime-factor rank of each visited state. -/
theorem visitedCount_sq_le_sum_cardFactors (A : Set ℕ) (X : ℕ)
    { ω : ℕ → ℕ } (hω : IsStrictDivisibilityPath ω) :
    (visitedCount A X ω) ^ 2 ≤
      ∑ n ∈ visitedBelow A X ω, (2 * Ω n + 1) := by
  let S := visitedBelow A X ω
  let T := S.image (firstHitTime ω)
  have hinj : Set.InjOn (firstHitTime ω) S := by
    apply (firstHitTime_injective_on hω).mono
    intro n hn
    exact (mem_visitedBelow_iff.mp hn).2.2.2
  have hcard : T.card = S.card := by
    exact Finset.card_image_of_injOn hinj
  calc
    (visitedCount A X ω) ^ 2 = S.card ^ 2 := rfl
    _ = T.card ^ 2 := by rw [hcard]
    _ ≤ ∑ k ∈ T, (2 * k + 1) := card_sq_le_sum_two_mul_add_one T
    _ = ∑ n ∈ S, (2 * firstHitTime ω n + 1) := by
      exact Finset.sum_image hinj
    _ ≤ ∑ n ∈ S, (2 * Ω n + 1) := by
      apply Finset.sum_le_sum
      intro n hn
      have htime := firstHitTime_le_cardFactors hω
        ((mem_visitedBelow_iff.mp hn).2.2.2)
      omega

/-- The deterministic square bound with a fixed summation set and hit
indicators, ready to integrate. -/
theorem visitedCountENNReal_sq_le_sum_hitIndicators (A : Set ℕ) (X : ℕ)
    { ω : ℕ → ℕ } (hω : IsStrictDivisibilityPath ω) :
    (visitedCountENNReal A X ω) ^ 2 ≤
      ∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A),
        if ω ∈ hitEvent n then ((2 * Ω n + 1 : ℕ) : ENNReal) else 0 := by
  have hnat := visitedCount_sq_le_sum_cardFactors A X hω
  have hcast : ((visitedCount A X ω) ^ 2 : ℕ) ≤
      ∑ n ∈ visitedBelow A X ω, (2 * Ω n + 1) := hnat
  have hsum : (∑ n ∈ visitedBelow A X ω, (2 * Ω n + 1)) =
      ∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A),
        if ω ∈ hitEvent n then (2 * Ω n + 1) else 0 := by
    rw [visitedBelow]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hnA : n ∈ A <;> by_cases hhit : ω ∈ hitEvent n <;>
      simp [hnA, hhit]
  rw [hsum] at hcast
  change ((visitedCount A X ω : ℕ) : ENNReal) ^ 2 ≤ _
  exact_mod_cast hcast

/-- The Omega-weighted sum of hitting masses at cutoff `X`. -/
def omegaHitMoment (A : Set ℕ) (X : ℕ) (v : ℕ → ENNReal) : ENNReal :=
  ∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A),
    ((2 * Ω n + 1 : ℕ) : ENNReal) * v n

/-- Integrated second-moment bound from exact hitting probabilities and an
almost-sure strict divisibility path. -/
theorem lintegral_visitedCountENNReal_sq_le_omegaHitMoment
    {mu : Measure (ℕ → ℕ)} (A : Set ℕ) (X : ℕ) (v : ℕ → ENNReal)
    (hhit : ∀ n, mu (hitEvent n) = v n)
    (hpath : ∀ᵐ ω ∂mu, IsStrictDivisibilityPath ω) :
    (∫⁻ ω, (visitedCountENNReal A X ω) ^ 2 ∂mu) ≤ omegaHitMoment A X v := by
  calc
    (∫⁻ ω, (visitedCountENNReal A X ω) ^ 2 ∂mu) ≤
        ∫⁻ ω, ∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A),
          if ω ∈ hitEvent n then ((2 * Ω n + 1 : ℕ) : ENNReal) else 0 ∂mu :=
      lintegral_mono_ae (hpath.mono fun ω hω ↦
        visitedCountENNReal_sq_le_sum_hitIndicators A X hω)
    _ = omegaHitMoment A X v := by
      rw [lintegral_finsetSum]
      · unfold omegaHitMoment
        apply Finset.sum_congr rfl
        intro n hn
        have hfun : (fun a : ℕ → ℕ ↦
            if a ∈ hitEvent n then ((2 * Ω n + 1 : ℕ) : ENNReal) else 0) =
            (hitEvent n).indicator
              (fun _ ↦ ((2 * Ω n + 1 : ℕ) : ENNReal)) := by
          funext a
          simp only [Set.indicator_apply]
        rw [hfun, lintegral_indicator (measurableSet_hitEvent n)]
        simp only [setLIntegral_const, hhit n, ENNReal.coe_natCast]
      · intro n hn
        exact measurable_const.ite (measurableSet_hitEvent n) measurable_const

/-! ## Normalization and reverse-Fatou extraction -/

/-- Natural-cutoff normalized count of the states of `A` visited by a path. -/
def visitedTermNat (A : Set ℕ) (X : ℕ) (ω : ℕ → ℕ) : ENNReal :=
  ENNReal.ofReal
    ((visitedCount A X ω : ℝ) / Real.log (Real.log (X : ℝ)))

lemma measurable_visitedTermNat (A : Set ℕ) (X : ℕ) :
    Measurable (visitedTermNat A X) := by
  unfold visitedTermNat
  apply ENNReal.measurable_ofReal.comp
  exact ((measurable_of_countable fun n : ℕ ↦ (n : ℝ)).comp
    (measurable_visitedCount A X)).div_const _

lemma visitedTermNat_ne_top (A : Set ℕ) (X : ℕ) (ω : ℕ → ℕ) :
    visitedTermNat A X ω ≠ ∞ := by
  simp [visitedTermNat]

lemma visitedTermNat_eq_div (A : Set ℕ) {X : ℕ}
    (hX : 0 < Real.log (Real.log (X : ℝ))) (ω : ℕ → ℕ) :
    visitedTermNat A X ω = visitedCountENNReal A X ω /
      ENNReal.ofReal (Real.log (Real.log (X : ℝ))) := by
  rw [visitedTermNat, ENNReal.ofReal_div_of_pos hX]
  simp [visitedCountENNReal]

/-- Normalized first moment at cutoffs where the double logarithm is
positive. -/
theorem lintegral_visitedTermNat
    {mu : Measure (ℕ → ℕ)} (A : Set ℕ) {X : ℕ}
    (hX : 0 < Real.log (Real.log (X : ℝ))) (v : ℕ → ENNReal)
    (hhit : ∀ n, mu (hitEvent n) = v n) :
    (∫⁻ ω, visitedTermNat A X ω ∂mu) =
      (∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A), v n) /
        ENNReal.ofReal (Real.log (Real.log (X : ℝ))) := by
  have hfun : (fun ω ↦ visitedTermNat A X ω) = fun ω ↦
      visitedCountENNReal A X ω /
        ENNReal.ofReal (Real.log (Real.log (X : ℝ))) := by
    funext ω
    exact visitedTermNat_eq_div A hX ω
  rw [hfun]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const _ (measurable_visitedCountENNReal A X),
    lintegral_visitedCountENNReal (mu := mu) A X v hhit]

/-- The normalized second moment is controlled by `omegaHitMoment`. -/
theorem lintegral_visitedTermNat_sq_le
    {mu : Measure (ℕ → ℕ)} (A : Set ℕ) {X : ℕ}
    (hX : 0 < Real.log (Real.log (X : ℝ))) (v : ℕ → ENNReal)
    (hhit : ∀ n, mu (hitEvent n) = v n)
    (hpath : ∀ᵐ ω ∂mu, IsStrictDivisibilityPath ω) :
    (∫⁻ ω, (visitedTermNat A X ω) ^ 2 ∂mu) ≤
      omegaHitMoment A X v /
        (ENNReal.ofReal (Real.log (Real.log (X : ℝ)))) ^ 2 := by
  simp_rw [visitedTermNat_eq_div A hX]
  simp_rw [div_eq_mul_inv]
  simp_rw [mul_pow]
  rw [lintegral_mul_const _ ((measurable_visitedCountENNReal A X).pow_const 2)]
  rw [← ENNReal.inv_pow]
  simpa only [mul_comm] using mul_le_mul_right
    (lintegral_visitedCountENNReal_sq_le_omegaHitMoment A X v hhit hpath)
    ((ENNReal.ofReal (Real.log (Real.log (X : ℝ))) ^ 2)⁻¹)

lemma visitedBelow_subset_range_inter (A : Set ℕ) (X : ℕ) (ω : ℕ → ℕ) :
    ↑(visitedBelow A X ω) ⊆ Set.range ω ∩ A := by
  intro n hn
  have hn' := mem_visitedBelow_iff.mp hn
  constructor
  · rcases hn'.2.2.2 with ⟨k, hk⟩
    exact ⟨k, hk⟩
  · exact hn'.2.2.1

lemma visitedCount_le_ncard_range_inter (A : Set ℕ) (X : ℕ) (ω : ℕ → ℕ)
    (hfinite : (Set.range ω ∩ A).Finite) :
    visitedCount A X ω ≤ (Set.range ω ∩ A).ncard := by
  rw [visitedCount]
  simpa using Set.ncard_le_ncard (visitedBelow_subset_range_inter A X ω) hfinite

/-- A path meeting `A` only finitely often has normalized visit count tending
to zero. -/
theorem tendsto_visitedTermNat_zero_of_finite_range_inter
    (A : Set ℕ) (ω : ℕ → ℕ) (hfinite : (Set.range ω ∩ A).Finite) :
    Tendsto (fun X ↦ visitedTermNat A X ω) atTop (nhds 0) := by
  let C : ℝ := ((Set.range ω ∩ A).ncard : ℝ)
  have hbound (X : ℕ) : (visitedCount A X ω : ℝ) ≤ C := by
    dsimp [C]
    exact_mod_cast visitedCount_le_ncard_range_inter A X ω hfinite
  have hreal : Tendsto
      (fun X : ℕ ↦ (visitedCount A X ω : ℝ) /
        Real.log (Real.log (X : ℝ))) atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_log_log_natCast_pos] with X hX
      exact div_nonneg (by positivity) hX.le
    · filter_upwards [eventually_log_log_natCast_pos] with X hX
      exact div_le_div_of_nonneg_right (hbound X) hX.le
    · exact tendsto_log_log_natCast_atTop.const_div_atTop C
  simpa only [visitedTermNat, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal

/-- A positive limsup of normalized visits forces infinitely many visited
elements of `A`. -/
theorem infinite_range_inter_of_pos_le_limsup_visitedTermNat
    {A : Set ℕ} {ω : ℕ → ℕ} {δ : ENNReal} (hδ : 0 < δ)
    (hle : δ ≤ limsup (fun X ↦ visitedTermNat A X ω) atTop) :
    (Set.range ω ∩ A).Infinite := by
  by_contra hnot
  have hfinite : (Set.range ω ∩ A).Finite := Set.not_infinite.mp hnot
  have hzero := (tendsto_visitedTermNat_zero_of_finite_range_inter A ω hfinite).limsup_eq
  rw [hzero] at hle
  exact (not_lt_of_ge hle) hδ

/-- Uniform second moments give a finite uniform bound for first moments. -/
theorem limsup_lintegral_le_one_add_of_uniform_secondMoment
    {Sample : Type*} [MeasurableSpace Sample] {mu : Measure Sample} [IsProbabilityMeasure mu]
    (Z : ℕ → Sample → ENNReal) (hZ : ∀ n, Measurable (Z n))
    (hfinite : ∀ n ω, Z n ω ≠ ∞) {M : ENNReal}
    (hsecond : ∀ n, ∫⁻ ω, (Z n ω) ^ 2 ∂mu ≤ M) :
    limsup (fun n ↦ ∫⁻ ω, Z n ω ∂mu) atTop ≤ 1 + M := by
  have hfirst (n : ℕ) : (∫⁻ ω, Z n ω ∂mu) ≤ 1 + M := by
    have htrunc : (∫⁻ ω, min (Z n ω) 1 ∂mu) ≤ 1 := by
      calc
        (∫⁻ ω, min (Z n ω) 1 ∂mu) ≤ ∫⁻ _ : Sample, 1 ∂mu :=
          lintegral_mono fun ω ↦ min_le_right _ _
        _ = 1 := by simp
    have htail := lintegral_le_truncated_add_secondMoment_div Z hZ hfinite
      hsecond one_ne_zero (by simp) n
    exact htail.trans (by
      simpa only [div_one, add_comm] using add_le_add_right htrunc M)
  exact limsup_le_of_le (hf := by isBoundedDefault) (Eventually.of_forall hfirst)

/-- Abstract sample-path extraction.  Applications establish the mean lower
bound from the exact first moment and the `nuLambda` comparison, and the
uniform square bound from `lintegral_visitedCountENNReal_sq_le_omegaHitMoment`
and `OmegaBound.exists_omegaLogSum_le_log_log_sq`. -/
theorem exists_path_with_limsup_visitedTermNat_ge
    {mu : Measure (ℕ → ℕ)} [IsProbabilityMeasure mu]
    (A : Set ℕ) {M : ENNReal} (hM : M ≠ ∞)
    (hsecond : ∀ X, ∫⁻ ω, (visitedTermNat A X ω) ^ 2 ∂mu ≤ M)
    (hmean : weightedRateNat A ≤
      limsup (fun X ↦ ∫⁻ ω, visitedTermNat A X ω ∂mu) atTop)
    {N : Set (ℕ → ℕ)} (hN : mu N = 0) :
    ∃ ω ∉ N, weightedRateNat A ≤
      limsup (fun X ↦ visitedTermNat A X ω) atTop := by
  have hlim : limsup (fun X ↦ ∫⁻ ω, visitedTermNat A X ω ∂mu) atTop ≤
      1 + M := limsup_lintegral_le_one_add_of_uniform_secondMoment
        (fun X ω ↦ visitedTermNat A X ω) (measurable_visitedTermNat A)
        (fun X ω ↦ visitedTermNat_ne_top A X ω) hsecond
  have hrate : weightedRateNat A ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness : 1 + M ≠ ∞) (hmean.trans hlim)
  exact exists_limsup_ge_of_uniform_secondMoment
    (fun X ω ↦ visitedTermNat A X ω)
    (measurable_visitedTermNat A)
    (fun X ω ↦ visitedTermNat_ne_top A X ω)
    hM hsecond hmean hrate hN

/-- An eventual uniform second-moment bound forces every target below the
limsup of the first moments to be finite. -/
theorem target_ne_top_of_le_limsup_lintegral_of_eventually_secondMoment
    {Sample : Type*} [MeasurableSpace Sample]
    {mu : Measure Sample} [IsProbabilityMeasure mu]
    (Z : ℕ → Sample → ENNReal) (hZ : ∀ n, Measurable (Z n))
    (hfinite : ∀ n ω, Z n ω ≠ ∞) (N₀ : ℕ) {M δ : ENNReal}
    (hM : M ≠ ∞)
    (hsecond : ∀ n, N₀ ≤ n → ∫⁻ ω, (Z n ω) ^ 2 ∂mu ≤ M)
    (hmean : δ ≤ limsup (fun n ↦ ∫⁻ ω, Z n ω ∂mu) atTop) :
    δ ≠ ∞ := by
  let Y : ℕ → Sample → ENNReal := fun n ω ↦ Z (n + N₀) ω
  have hYsecond : ∀ n, ∫⁻ ω, (Y n ω) ^ 2 ∂mu ≤ M := fun n ↦
    hsecond (n + N₀) (Nat.le_add_left N₀ n)
  have hYlim : limsup (fun n ↦ ∫⁻ ω, Y n ω ∂mu) atTop ≤ 1 + M :=
    limsup_lintegral_le_one_add_of_uniform_secondMoment Y
      (fun n ↦ hZ (n + N₀)) (fun n ω ↦ hfinite (n + N₀) ω) hYsecond
  have hshift : limsup (fun n ↦ ∫⁻ ω, Y n ω ∂mu) atTop =
      limsup (fun n ↦ ∫⁻ ω, Z n ω ∂mu) atTop := by
    exact limsup_nat_add (fun n ↦ ∫⁻ ω, Z n ω ∂mu) N₀
  exact ne_top_of_le_ne_top (by finiteness : 1 + M ≠ ∞)
    (hmean.trans (hshift ▸ hYlim))

/-- Reverse-Fatou extraction when the uniform square bound starts only at a
fixed natural cutoff. -/
theorem exists_limsup_ge_of_eventually_uniform_secondMoment
    {Sample : Type*} [MeasurableSpace Sample]
    {mu : Measure Sample} [IsProbabilityMeasure mu]
    (Z : ℕ → Sample → ENNReal) (hZ : ∀ n, Measurable (Z n))
    (hfinite : ∀ n ω, Z n ω ≠ ∞) (N₀ : ℕ) {M δ : ENNReal}
    (hM : M ≠ ∞)
    (hsecond : ∀ n, N₀ ≤ n → ∫⁻ ω, (Z n ω) ^ 2 ∂mu ≤ M)
    (hmean : δ ≤ limsup (fun n ↦ ∫⁻ ω, Z n ω ∂mu) atTop)
    (hδ : δ ≠ ∞) {N : Set Sample} (hN : mu N = 0) :
    ∃ ω ∉ N, δ ≤ limsup (fun n ↦ Z n ω) atTop := by
  let Y : ℕ → Sample → ENNReal := fun n ω ↦ Z (n + N₀) ω
  have hYsecond : ∀ n, ∫⁻ ω, (Y n ω) ^ 2 ∂mu ≤ M := fun n ↦
    hsecond (n + N₀) (Nat.le_add_left N₀ n)
  have hYmean : δ ≤ limsup (fun n ↦ ∫⁻ ω, Y n ω ∂mu) atTop := by
    rw [limsup_nat_add (fun n ↦ ∫⁻ ω, Z n ω ∂mu) N₀]
    exact hmean
  obtain ⟨ω, hωN, hω⟩ := exists_limsup_ge_of_uniform_secondMoment
    Y (fun n ↦ hZ (n + N₀)) (fun n ω ↦ hfinite (n + N₀) ω)
    hM hYsecond hYmean hδ hN
  refine ⟨ω, hωN, ?_⟩
  rw [← limsup_nat_add (fun n ↦ Z n ω) N₀]
  exact hω

/-- Eventual version of the extraction theorem.  This is the form used with
an asymptotic Omega estimate, and avoids treating the finitely many small
cutoffs separately. -/
theorem exists_path_with_limsup_visitedTermNat_ge_of_eventually_secondMoment
    {mu : Measure (ℕ → ℕ)} [IsProbabilityMeasure mu]
    (A : Set ℕ) (N₀ : ℕ) {M : ENNReal} (hM : M ≠ ∞)
    (hsecond : ∀ X, N₀ ≤ X →
      ∫⁻ ω, (visitedTermNat A X ω) ^ 2 ∂mu ≤ M)
    (hmean : weightedRateNat A ≤
      limsup (fun X ↦ ∫⁻ ω, visitedTermNat A X ω ∂mu) atTop)
    {N : Set (ℕ → ℕ)} (hN : mu N = 0) :
    ∃ ω ∉ N, weightedRateNat A ≤
      limsup (fun X ↦ visitedTermNat A X ω) atTop := by
  have hrate : weightedRateNat A ≠ ∞ :=
    target_ne_top_of_le_limsup_lintegral_of_eventually_secondMoment
      (fun X ω ↦ visitedTermNat A X ω) (measurable_visitedTermNat A)
      (fun X ω ↦ visitedTermNat_ne_top A X ω) N₀ hM hsecond hmean
  exact exists_limsup_ge_of_eventually_uniform_secondMoment
    (fun X ω ↦ visitedTermNat A X ω) (measurable_visitedTermNat A)
    (fun X ω ↦ visitedTermNat_ne_top A X ω) N₀ hM hsecond hmean hrate hN

/-- Positive target rate upgrades the extracted path to one meeting `A`
infinitely often. -/
theorem exists_infinite_path_with_limsup_visitedTermNat_ge_of_eventually_secondMoment
    {mu : Measure (ℕ → ℕ)} [IsProbabilityMeasure mu]
    (A : Set ℕ) (N₀ : ℕ) {M : ENNReal} (hM : M ≠ ∞)
    (hsecond : ∀ X, N₀ ≤ X →
      ∫⁻ ω, (visitedTermNat A X ω) ^ 2 ∂mu ≤ M)
    (hmean : weightedRateNat A ≤
      limsup (fun X ↦ ∫⁻ ω, visitedTermNat A X ω ∂mu) atTop)
    (hpos : 0 < weightedRateNat A)
    {N : Set (ℕ → ℕ)} (hN : mu N = 0) :
    ∃ ω ∉ N, weightedRateNat A ≤
        limsup (fun X ↦ visitedTermNat A X ω) atTop ∧
      (Set.range ω ∩ A).Infinite := by
  obtain ⟨ω, hωN, hωrate⟩ :=
    exists_path_with_limsup_visitedTermNat_ge_of_eventually_secondMoment
      A N₀ hM hsecond hmean hN
  exact ⟨ω, hωN, hωrate,
    infinite_range_inter_of_pos_le_limsup_visitedTermNat hpos hωrate⟩

end Erdos1217
