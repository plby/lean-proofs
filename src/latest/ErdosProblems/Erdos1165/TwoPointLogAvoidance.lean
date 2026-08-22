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
import ErdosProblems.Erdos1165.PlanarPotential
import ErdosProblems.Erdos1165.OffDiagonal
import ErdosProblems.Erdos1165.PotentialKernel
import ErdosProblems.Erdos1165.TwoPointAvoidance
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Int

/-!
# Uniform logarithmic avoidance of two points

This file proves the finite estimate used as (4.4) by
Hao--Li--Okada--Zheng.  If `S` is planar simple random walk started at the
origin, then uniformly in the second point `x`,

`P(S_k ∉ {0,x} for 1 ≤ k ≤ n) ≥ c / log n`.

The proof is a finite last-exit argument.  Decomposing a length `8n` path at
its last visit to `{0,x}` gives a convolution between the endpoint kernel and
the two-point survival probability.  The last eighth of the convolution has
mass at most `4/7`, using the elementary uniform heat-kernel estimate
`P(S_k=y) ≤ 2/(k+1)`.  The remaining Green sum is at most a constant times a
harmonic sum.  No infinite potential kernel or asymptotic theorem is needed.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165
namespace TwoPointLogAvoidance

open PlanarPotential PotentialKernel

/-! ## Finite avoidance events -/

/-- The increment path avoids both `0` and `x` at all positive times through
`n`. -/
def avoidsPair (x : Point) (n : ℕ) : Set StepPath :=
  {ω | ∀ k, 0 < k → k ≤ n →
    trajectory ω k ≠ (0 : Point) ∧ trajectory ω k ≠ x}

lemma measurableSet_avoidsPair (x : Point) (n : ℕ) :
    MeasurableSet (avoidsPair x n) := by
  have heq : avoidsPair x n = ⋂ k : Fin (n + 1),
      if 0 < (k : ℕ) then
        {ω | trajectory ω k ≠ (0 : Point) ∧ trajectory ω k ≠ x}
      else Set.univ := by
    ext ω
    simp only [avoidsPair, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h k
      by_cases hk : 0 < (k : ℕ)
      · simpa [hk] using h k hk (Nat.le_of_lt_succ k.isLt)
      · simp [hk]
    · intro h k hk hkn
      have h' := h ⟨k, Nat.lt_succ_of_le hkn⟩
      simpa [hk] using h'
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  split_ifs
  · have htraj : Measurable (fun ω : StepPath ↦ trajectory ω (k : ℕ)) :=
      (measurable_pi_apply (k : ℕ)).comp measurable_trajectory
    exact (measurableSet_eq_fun htraj measurable_const).compl.inter
      (measurableSet_eq_fun htraj measurable_const).compl
  · exact MeasurableSet.univ

/-- Real-valued survival probability. -/
noncomputable def avoidanceProbability (x : Point) (n : ℕ) : ℝ :=
  fairSteps.real (avoidsPair x n)

lemma avoidanceProbability_nonneg (x : Point) (n : ℕ) :
    0 ≤ avoidanceProbability x n := measureReal_nonneg

lemma avoidanceProbability_le_one (x : Point) (n : ℕ) :
    avoidanceProbability x n ≤ 1 := by
  rw [avoidanceProbability]
  have h := MeasureTheory.measureReal_mono (μ := fairSteps)
    (subset_univ (avoidsPair x n)) (by finiteness)
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one] using h

lemma avoidsPair_mono {x : Point} {m n : ℕ} (hmn : m ≤ n) :
    avoidsPair x n ⊆ avoidsPair x m := by
  intro ω hω k hk hkm
  exact hω k hk (hkm.trans hmn)

lemma avoidanceProbability_antitone (x : Point) :
    Antitone (avoidanceProbability x) := by
  intro m n hmn
  exact MeasureTheory.measureReal_mono (avoidsPair_mono hmn)

/-! ## A uniform endpoint estimate -/

/-- Real-valued endpoint probability, expressed by the exact finite count
from `OffDiagonal.lean`. -/
noncomputable def endpointProbabilityReal (n : ℕ) (x : Point) : ℝ :=
  (planarEndpointCount n x : ℝ) / (4 : ℝ) ^ n

lemma endpointProbabilityReal_nonneg (n : ℕ) (x : Point) :
    0 ≤ endpointProbabilityReal n x := by
  unfold endpointProbabilityReal
  positivity

lemma simpleRandomWalk_endpoint_toReal (n : ℕ) (x : Point) :
    (simpleRandomWalk {s | s n = x}).toReal = endpointProbabilityReal n x := by
  rw [simpleRandomWalk_endpoint_apply]
  unfold endpointProbabilityReal
  rw [ENNReal.toReal_div]
  simp

lemma fairSteps_endpoint_toReal (n : ℕ) (x : Point) :
    (fairSteps {w | trajectory w n = x}).toReal = endpointProbabilityReal n x := by
  have hmeas : MeasurableSet {s : WalkPath | s n = x} :=
    measurableSet_eq_fun (measurable_pi_apply n) measurable_const
  have hmap : simpleRandomWalk {s | s n = x} =
      fairSteps {w | trajectory w n = x} := by
    rw [simpleRandomWalk, Measure.map_apply measurable_trajectory hmeas]
    rfl
  rw [← simpleRandomWalk_endpoint_toReal, hmap]

lemma oneDimEndpointCount_le_middle (n : ℕ) (z : ℤ) :
    oneDimEndpointCount n z ≤ n.choose (n / 2) := by
  unfold oneDimEndpointCount
  split_ifs
  · exact Nat.choose_le_middle _ _
  · exact Nat.zero_le _

lemma planarEndpointCount_le_middle_sq (n : ℕ) (x : Point) :
    planarEndpointCount n x ≤ (n.choose (n / 2)) ^ 2 := by
  unfold planarEndpointCount
  simpa [pow_two] using Nat.mul_le_mul
    (oneDimEndpointCount_le_middle n (x.1 + x.2))
    (oneDimEndpointCount_le_middle n (x.1 - x.2))

lemma central_odd_probability_le_even (m : ℕ) :
    (((2 * m + 1).choose m : ℝ) ^ 2) / (4 : ℝ) ^ (2 * m + 1) ≤
      (((2 * m).choose m : ℝ) ^ 2) / (4 : ℝ) ^ (2 * m) := by
  have hchoose : (2 * m + 1).choose m ≤ 2 * (2 * m).choose m := by
    calc
      (2 * m + 1).choose m = (2 * m + 1).choose (m + 1) := by
        simpa [two_mul, Nat.add_assoc] using
          (Nat.choose_symm_add (a := m) (b := m + 1))
      _ = (2 * m).choose m + (2 * m).choose (m + 1) := by
        simpa only [Nat.succ_eq_add_one] using Nat.choose_succ_succ' (2 * m) m
      _ ≤ (2 * m).choose m + (2 * m).choose m := by
        gcongr
        have hhalf : (2 * m) / 2 = m := by omega
        simpa [hhalf] using Nat.choose_le_middle (m + 1) (2 * m)
      _ = 2 * (2 * m).choose m := by omega
  have hchooseR : ((2 * m + 1).choose m : ℝ) ≤
      2 * ((2 * m).choose m : ℝ) := by exact_mod_cast hchoose
  have hsquare : (((2 * m + 1).choose m : ℝ) ^ 2) ≤
      (2 * ((2 * m).choose m : ℝ)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hchooseR
  calc
    (((2 * m + 1).choose m : ℝ) ^ 2) / (4 : ℝ) ^ (2 * m + 1) ≤
        (2 * ((2 * m).choose m : ℝ)) ^ 2 /
          (4 : ℝ) ^ (2 * m + 1) := by gcongr
    _ = (((2 * m).choose m : ℝ) ^ 2) / (4 : ℝ) ^ (2 * m) := by
      rw [pow_succ]
      ring

/-- The heat kernel is uniformly bounded by `2/(n+1)`.  The constant is
chosen so that the same formula covers both parities. -/
theorem endpointProbabilityReal_le (n : ℕ) (x : Point) :
    endpointProbabilityReal n x ≤ 2 / (n + 1 : ℝ) := by
  have hcount := planarEndpointCount_le_middle_sq n x
  have hcountR : (planarEndpointCount n x : ℝ) ≤
      ((n.choose (n / 2) : ℕ) : ℝ) ^ 2 := by exact_mod_cast hcount
  have hmiddle : endpointProbabilityReal n x ≤
      ((n.choose (n / 2) : ℕ) : ℝ) ^ 2 / (4 : ℝ) ^ n := by
    unfold endpointProbabilityReal
    gcongr
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, rfl⟩ := hn
    have hhalf : (m + m) / 2 = m := by omega
    have heven : endpointProbabilityReal (2 * m) x ≤ 2 / (2 * m + 1 : ℝ) := by
      calc
      endpointProbabilityReal (2 * m) x ≤
          (((2 * m).choose m : ℕ) : ℝ) ^ 2 / (4 : ℝ) ^ (2 * m) := by
            simpa [two_mul, hhalf] using hmiddle
      _ = planarReturnProbability m := by
        unfold planarReturnProbability
        rw [show (4 : ℝ) ^ (2 * m) = 16 ^ m by
          rw [pow_mul]
          norm_num]
        rfl
      _ ≤ 1 / (m + 1 : ℝ) := planarReturnProbability_upper_bound m
      _ ≤ 2 / (2 * m + 1 : ℝ) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
    simpa [two_mul] using heven
  · obtain ⟨m, rfl⟩ := hn
    have hhalf : (m + m + 1) / 2 = m := by omega
    have hodd : endpointProbabilityReal (2 * m + 1) x ≤
        (((2 * m + 1).choose m : ℕ) : ℝ) ^ 2 /
          (4 : ℝ) ^ (2 * m + 1) := by
        simpa [two_mul, hhalf] using hmiddle
    have hoddFinal : endpointProbabilityReal (2 * m + 1) x ≤
        2 / (2 * m + 1 + 1 : ℝ) := by
      calc
      endpointProbabilityReal (2 * m + 1) x ≤
          (((2 * m + 1).choose m : ℕ) : ℝ) ^ 2 /
            (4 : ℝ) ^ (2 * m + 1) := hodd
      _ ≤ (((2 * m).choose m : ℕ) : ℝ) ^ 2 /
            (4 : ℝ) ^ (2 * m) := central_odd_probability_le_even m
      _ = planarReturnProbability m := by
        unfold planarReturnProbability
        rw [show (4 : ℝ) ^ (2 * m) = 16 ^ m by
          rw [pow_mul]
          norm_num]
        rfl
      _ ≤ 1 / (m + 1 : ℝ) := planarReturnProbability_upper_bound m
      _ = 2 / (2 * m + 1 + 1 : ℝ) := by
        field_simp
        ring
    simpa [two_mul] using hoddFinal

/-! ## Reflection and deterministic-time factorization -/

lemma trajectory_reverseSteps_apply (w : StepPath) (k : ℕ) :
    trajectory (reverseSteps w) k = -trajectory w k := by
  exact congrFun (trajectory_reverseSteps w) k

lemma reverseSteps_preimage_avoidsPair (x : Point) (n : ℕ) :
    reverseSteps ⁻¹' avoidsPair x n = avoidsPair (-x) n := by
  ext w
  simp only [Set.mem_preimage, avoidsPair, Set.mem_ofPred_eq,
    trajectory_reverseSteps_apply]
  constructor
  · intro h k hk hkn
    have hk' := h k hk hkn
    constructor
    · intro hz
      apply hk'.1
      rw [hz, neg_zero]
    · intro hx
      apply hk'.2
      rw [hx, neg_neg]
  · intro h k hk hkn
    have hk' := h k hk hkn
    constructor
    · intro hz
      apply hk'.1
      exact neg_eq_zero.mp hz
    · intro hx
      apply hk'.2
      have hx' := congrArg Neg.neg hx
      simpa using hx'

theorem avoidanceProbability_neg (x : Point) (n : ℕ) :
    avoidanceProbability (-x) n = avoidanceProbability x n := by
  rw [avoidanceProbability, avoidanceProbability]
  have hmap := congrArg (fun μ : Measure StepPath ↦ μ (avoidsPair x n))
    fairSteps_map_reverseSteps
  rw [Measure.map_apply measurable_reverseSteps (measurableSet_avoidsPair x n)] at hmap
  rw [reverseSteps_preimage_avoidsPair] at hmap
  exact congrArg ENNReal.toReal hmap

/-- Extend a finite increment block arbitrarily after its endpoint. -/
def extendBlock {n : ℕ} (u : Fin n → Direction) : StepPath :=
  fun j ↦ if h : j < n then u ⟨j, h⟩ else 0

@[simp] lemma extendBlock_apply_lt {n : ℕ} (u : Fin n → Direction)
    {j : ℕ} (hj : j < n) : extendBlock u j = u ⟨j, hj⟩ := by
  simp [extendBlock, hj]

lemma trajectory_eq_of_eq_lt {w v : StepPath} {n k : ℕ}
    (h : ∀ j < n, w j = v j) (hk : k ≤ n) :
    trajectory w k = trajectory v k := by
  unfold trajectory
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j ((Finset.mem_range.mp hj).trans_le hk)]

/-- The finite-block version of `avoidsPair`. -/
def avoidingBlocks (x : Point) (n : ℕ) : Set (Fin n → Direction) :=
  {u | extendBlock u ∈ avoidsPair x n}

lemma measurableSet_avoidingBlocks (x : Point) (n : ℕ) :
    MeasurableSet (avoidingBlocks x n) := (Set.to_countable _).measurableSet

lemma mem_avoidingBlocks_stepPrefix_iff (x : Point) (n : ℕ) (w : StepPath) :
    stepPrefix n w ∈ avoidingBlocks x n ↔ w ∈ avoidsPair x n := by
  unfold avoidingBlocks
  simp only [Set.mem_ofPred_eq]
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro hk
  apply imp_congr_right
  intro hkn
  have heq : trajectory (extendBlock (stepPrefix n w)) k = trajectory w k := by
    apply trajectory_eq_of_eq_lt _ hkn
    intro j hj
    simp [stepPrefix, extendBlock, hj]
  rw [heq]

lemma stepBlock_mem_avoidingBlocks_iff (x : Point) (k n : ℕ) (w : StepPath) :
    stepBlock k n w ∈ avoidingBlocks x n ↔
      shiftSteps k w ∈ avoidsPair x n := by
  rw [← mem_avoidingBlocks_stepPrefix_iff]
  rfl

lemma fairBlock_avoidingBlocks_toReal (x : Point) (n : ℕ) :
    (fairBlock n (avoidingBlocks x n)).toReal = avoidanceProbability x n := by
  rw [avoidanceProbability]
  have hmap := congrArg (fun μ : Measure (Fin n → Direction) ↦
      μ (avoidingBlocks x n)) (fairSteps_map_stepBlock 0 n)
  rw [Measure.map_apply (measurable_stepBlock 0 n)
    (measurableSet_avoidingBlocks x n)] at hmap
  have hevent : stepBlock 0 n ⁻¹' avoidingBlocks x n = avoidsPair x n := by
    ext w
    have hshift : shiftSteps 0 w = w := by funext j; simp [shiftSteps]
    simpa [hshift] using stepBlock_mem_avoidingBlocks_iff x 0 n w
  rw [hevent] at hmap
  exact congrArg ENNReal.toReal hmap.symm

/-- A finite block has prescribed displacement. -/
def endpointBlocksSet (n : ℕ) (a : Point) : Set (Fin n → Direction) :=
  {u | markovBlockDisplacement u = a}

lemma measurableSet_endpointBlocksSet (n : ℕ) (a : Point) :
    MeasurableSet (endpointBlocksSet n a) := (Set.to_countable _).measurableSet

lemma stepPrefix_mem_endpointBlocksSet_iff (n : ℕ) (a : Point) (w : StepPath) :
    stepPrefix n w ∈ endpointBlocksSet n a ↔ trajectory w n = a := by
  simp only [endpointBlocksSet, Set.mem_ofPred_eq]
  exact (trajectory_eq_markovBlockDisplacement_stepPrefix w n).symm ▸ Iff.rfl

/-- Independence of a prescribed endpoint and a translated future avoidance
event, stated directly in real probabilities. -/
theorem endpoint_inter_shiftAvoids_measureReal (k h : ℕ) (a x : Point) :
    fairSteps.real ({w | trajectory w k = a} ∩
      {w | shiftSteps k w ∈ avoidsPair x h}) =
      endpointProbabilityReal k a * avoidanceProbability x h := by
  let B := endpointBlocksSet k a
  let C := avoidingBlocks x h
  have hind := (indepFun_stepPrefix_stepBlock k h).measure_inter_preimage_eq_mul
    B C (measurableSet_endpointBlocksSet k a) (measurableSet_avoidingBlocks x h)
  have hfirst : stepPrefix k ⁻¹' B = {w | trajectory w k = a} := by
    ext w
    exact stepPrefix_mem_endpointBlocksSet_iff k a w
  have hsecond : stepBlock k h ⁻¹' C = {w | shiftSteps k w ∈ avoidsPair x h} := by
    ext w
    exact stepBlock_mem_avoidingBlocks_iff x k h w
  rw [hfirst, hsecond] at hind
  have hshift : fairSteps {w | shiftSteps k w ∈ avoidsPair x h} =
      fairSteps (avoidsPair x h) := by
    change fairSteps (shiftSteps k ⁻¹' avoidsPair x h) = fairSteps (avoidsPair x h)
    rw [← Measure.map_apply (measurable_shiftSteps k)
      (measurableSet_avoidsPair x h), fairSteps_map_shiftSteps]
  rw [measureReal_def, hind, ENNReal.toReal_mul, fairSteps_endpoint_toReal,
    hshift]
  rfl

/-! ## The finite last-exit decomposition -/

/-- Visit times to the two-point set through a fixed horizon. -/
def pairVisitTimes (x : Point) (N : ℕ) (w : StepPath) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun k ↦
    trajectory w k = (0 : Point) ∨ trajectory w k = x

lemma zero_mem_pairVisitTimes (x : Point) (N : ℕ) (w : StepPath) :
    0 ∈ pairVisitTimes x N w := by
  simp [pairVisitTimes, trajectory_zero]

lemma pairVisitTimes_nonempty (x : Point) (N : ℕ) (w : StepPath) :
    (pairVisitTimes x N w).Nonempty :=
  ⟨0, zero_mem_pairVisitTimes x N w⟩

/-- Last visit to `{0,x}` no later than `N`.  Time zero makes the defining
finite set nonempty. -/
noncomputable def lastPairVisit (x : Point) (N : ℕ) (w : StepPath) : ℕ :=
  (pairVisitTimes x N w).max' (pairVisitTimes_nonempty x N w)

lemma lastPairVisit_mem (x : Point) (N : ℕ) (w : StepPath) :
    lastPairVisit x N w ∈ pairVisitTimes x N w := by
  exact Finset.max'_mem _ _

lemma lastPairVisit_le (x : Point) (N : ℕ) (w : StepPath) :
    lastPairVisit x N w ≤ N := by
  have hmem := lastPairVisit_mem x N w
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hmem).1)

lemma lastPairVisit_position (x : Point) (N : ℕ) (w : StepPath) :
    trajectory w (lastPairVisit x N w) = 0 ∨
      trajectory w (lastPairVisit x N w) = x := by
  exact (Finset.mem_filter.mp (lastPairVisit_mem x N w)).2

lemma visit_le_lastPairVisit {x : Point} {N k : ℕ} {w : StepPath}
    (hkN : k ≤ N) (hk : trajectory w k = 0 ∨ trajectory w k = x) :
    k ≤ lastPairVisit x N w := by
  apply Finset.le_max'
  rw [pairVisitTimes, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hkN), hk⟩

/-- Last visit at time `k`, with the Boolean recording which of the two
points was visited (`false` for `0`, `true` for `x`). -/
def lastVisitPiece (x : Point) (N : ℕ) (i : Fin (N + 1) × Bool) : Set StepPath :=
  if i.2 then
    {w | lastPairVisit x N w = (i.1 : ℕ) ∧ trajectory w i.1 = x}
  else
    {w | lastPairVisit x N w = (i.1 : ℕ) ∧ trajectory w i.1 = 0}

lemma trajectory_shift_eq_of_endpoint (w : StepPath) (k t : ℕ) (a : Point)
    (hk : trajectory w k = a) :
    trajectory (shiftSteps k w) t = trajectory w (k + t) - a := by
  rw [← hk]
  exact (trajectory_add_sub_trajectory w k t).symm

lemma lastVisitPiece_false_eq {x : Point} {N : ℕ} (k : Fin (N + 1)) :
    lastVisitPiece x N (k, false) =
      {w | trajectory w k = 0} ∩
        {w | shiftSteps k w ∈ avoidsPair x (N - k)} := by
  ext w
  simp only [lastVisitPiece, Bool.false_eq_true, if_false, Set.mem_ofPred_eq,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨hlast, hkzero⟩
    refine ⟨hkzero, ?_⟩
    intro t ht hthorizon
    have hktN : (k : ℕ) + t ≤ N := by omega
    have hshift := trajectory_shift_eq_of_endpoint w k t 0 hkzero
    simp only [sub_zero] at hshift
    constructor
    · intro hz
      have hvis : trajectory w ((k : ℕ) + t) = 0 ∨
          trajectory w ((k : ℕ) + t) = x := Or.inl (hshift.symm.trans hz)
      have hle := visit_le_lastPairVisit hktN hvis
      rw [hlast] at hle
      omega
    · intro hx
      have hvis : trajectory w ((k : ℕ) + t) = 0 ∨
          trajectory w ((k : ℕ) + t) = x := Or.inr (hshift.symm.trans hx)
      have hle := visit_le_lastPairVisit hktN hvis
      rw [hlast] at hle
      omega
  · rintro ⟨hkzero, hfuture⟩
    refine ⟨Nat.le_antisymm ?_
      (visit_le_lastPairVisit (Nat.le_of_lt_succ k.isLt) (Or.inl hkzero)), hkzero⟩
    apply Finset.max'_le
    intro j hj
    have hjparts := Finset.mem_filter.mp hj
    have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hjparts.1)
    by_contra hjk
    have hkj : (k : ℕ) < j := lt_of_not_ge hjk
    let t := j - (k : ℕ)
    have ht : 0 < t := by dsimp [t]; omega
    have hthorizon : t ≤ N - (k : ℕ) := by dsimp [t]; omega
    have havoid := hfuture t ht hthorizon
    have hshift := trajectory_shift_eq_of_endpoint w k t 0 hkzero
    have htime : (k : ℕ) + t = j := by dsimp [t]; omega
    rw [htime, sub_zero] at hshift
    rcases hjparts.2 with hjzero | hjx
    · exact havoid.1 (hshift.trans hjzero)
    · exact havoid.2 (hshift.trans hjx)

lemma lastVisitPiece_true_eq {x : Point} {N : ℕ} (k : Fin (N + 1)) :
    lastVisitPiece x N (k, true) =
      {w | trajectory w k = x} ∩
        {w | shiftSteps k w ∈ avoidsPair (-x) (N - k)} := by
  ext w
  simp only [lastVisitPiece, if_true, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hlast, hkx⟩
    refine ⟨hkx, ?_⟩
    intro t ht hthorizon
    have hktN : (k : ℕ) + t ≤ N := by omega
    have hshift := trajectory_shift_eq_of_endpoint w k t x hkx
    constructor
    · intro hz
      have hvis : trajectory w ((k : ℕ) + t) = 0 ∨
          trajectory w ((k : ℕ) + t) = x := by
        right
        apply sub_eq_zero.mp
        rw [← hshift]
        exact hz
      have hle := visit_le_lastPairVisit hktN hvis
      rw [hlast] at hle
      omega
    · intro hnegx
      have hpos : trajectory w ((k : ℕ) + t) = 0 := by
        have := congrArg (fun z : Point ↦ z + x) (hshift.symm.trans hnegx)
        simpa [sub_eq_add_neg, add_assoc] using this
      have hle := visit_le_lastPairVisit (x := x) hktN (Or.inl hpos)
      rw [hlast] at hle
      omega
  · rintro ⟨hkx, hfuture⟩
    refine ⟨Nat.le_antisymm ?_
      (visit_le_lastPairVisit (Nat.le_of_lt_succ k.isLt) (Or.inr hkx)), hkx⟩
    apply Finset.max'_le
    intro j hj
    have hjparts := Finset.mem_filter.mp hj
    have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hjparts.1)
    by_contra hjk
    have hkj : (k : ℕ) < j := lt_of_not_ge hjk
    let t := j - (k : ℕ)
    have ht : 0 < t := by dsimp [t]; omega
    have hthorizon : t ≤ N - (k : ℕ) := by dsimp [t]; omega
    have havoid := hfuture t ht hthorizon
    have hshift := trajectory_shift_eq_of_endpoint w k t x hkx
    have htime : (k : ℕ) + t = j := by dsimp [t]; omega
    rw [htime] at hshift
    rcases hjparts.2 with hjzero | hjx
    · apply havoid.2
      rw [hshift, hjzero, zero_sub]
    · apply havoid.1
      rw [hshift, hjx, sub_self]

lemma measurableSet_lastVisitPiece (x : Point) (N : ℕ)
    (i : Fin (N + 1) × Bool) : MeasurableSet (lastVisitPiece x N i) := by
  rcases i with ⟨k, b⟩
  cases b
  · rw [lastVisitPiece_false_eq]
    exact (measurableSet_eq_fun
      ((measurable_pi_apply (k : ℕ)).comp measurable_trajectory) measurable_const).inter
      ((measurable_shiftSteps k) (measurableSet_avoidsPair x (N - k)))
  · rw [lastVisitPiece_true_eq]
    exact (measurableSet_eq_fun
      ((measurable_pi_apply (k : ℕ)).comp measurable_trajectory) measurable_const).inter
      ((measurable_shiftSteps k) (measurableSet_avoidsPair (-x) (N - k)))

lemma mem_lastVisitPiece_time {x : Point} {N : ℕ}
    {i : Fin (N + 1) × Bool} {w : StepPath} (hw : w ∈ lastVisitPiece x N i) :
    lastPairVisit x N w = (i.1 : ℕ) := by
  unfold lastVisitPiece at hw
  split at hw <;> exact hw.1

lemma lastVisitPiece_pairwiseDisjoint {x : Point} {N : ℕ} (hx : x ≠ 0) :
    ((Finset.univ : Finset (Fin (N + 1) × Bool)) : Set (Fin (N + 1) × Bool)).PairwiseDisjoint
      (lastVisitPiece x N) := by
  intro i _ j _ hij
  change Disjoint (lastVisitPiece x N i) (lastVisitPiece x N j)
  rw [Set.disjoint_left]
  intro w hwi hwj
  have htime : i.1 = j.1 := by
    apply Fin.ext
    exact (mem_lastVisitPiece_time hwi).symm.trans (mem_lastVisitPiece_time hwj)
  by_cases hbool : i.2 = j.2
  · apply hij
    exact Prod.ext htime hbool
  · rcases i with ⟨i, bi⟩
    rcases j with ⟨j, bj⟩
    cases bi <;> cases bj
    · exact (hbool rfl).elim
    · simp only [lastVisitPiece, Bool.false_eq_true, if_false, if_true,
        Set.mem_ofPred_eq] at hwi hwj
      simp only at htime
      subst j
      exact hx (hwj.2.symm.trans hwi.2)
    · simp only [lastVisitPiece, Bool.false_eq_true, if_false, if_true,
        Set.mem_ofPred_eq] at hwi hwj
      simp only at htime
      subst j
      exact hx (hwi.2.symm.trans hwj.2)
    · exact (hbool rfl).elim

lemma iUnion_lastVisitPiece (x : Point) (N : ℕ) :
    (⋃ i ∈ (Finset.univ : Finset (Fin (N + 1) × Bool)), lastVisitPiece x N i) =
      (Set.univ : Set StepPath) := by
  ext w
  simp only [Set.mem_iUnion, Finset.mem_univ, Set.mem_univ, iff_true]
  let k : Fin (N + 1) :=
    ⟨lastPairVisit x N w, Nat.lt_succ_of_le (lastPairVisit_le x N w)⟩
  rcases lastPairVisit_position x N w with hzero | hx
  · refine ⟨(k, false), True.intro, ?_⟩
    exact ⟨rfl, hzero⟩
  · refine ⟨(k, true), True.intro, ?_⟩
    exact ⟨rfl, hx⟩

lemma lastVisitPiece_measureReal_false (x : Point) (N : ℕ) (k : Fin (N + 1)) :
    fairSteps.real (lastVisitPiece x N (k, false)) =
      endpointProbabilityReal k 0 * avoidanceProbability x (N - k) := by
  rw [lastVisitPiece_false_eq]
  exact endpoint_inter_shiftAvoids_measureReal k (N - k) 0 x

lemma lastVisitPiece_measureReal_true (x : Point) (N : ℕ) (k : Fin (N + 1)) :
    fairSteps.real (lastVisitPiece x N (k, true)) =
      endpointProbabilityReal k x * avoidanceProbability x (N - k) := by
  rw [lastVisitPiece_true_eq, endpoint_inter_shiftAvoids_measureReal,
    avoidanceProbability_neg]

/-- Exact finite last-exit convolution for a genuine two-point set. -/
theorem lastExit_convolution {x : Point} (hx : x ≠ 0) (N : ℕ) :
    1 = ∑ k ∈ Finset.range (N + 1),
      (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
        avoidanceProbability x (N - k) := by
  have hdis := lastVisitPiece_pairwiseDisjoint (x := x) (N := N) hx
  have hmeasure := MeasureTheory.measureReal_biUnion_finset (μ := fairSteps)
    hdis (fun i _ ↦ measurableSet_lastVisitPiece x N i)
    (fun _ _ ↦ by finiteness)
  rw [iUnion_lastVisitPiece] at hmeasure
  have huniv : fairSteps.real (Set.univ : Set StepPath) = 1 := by
    rw [measureReal_def, measure_univ]
    simp
  rw [huniv] at hmeasure
  have hprod :
      (∑ i : Fin (N + 1) × Bool, fairSteps.real (lastVisitPiece x N i)) =
        ∑ k : Fin (N + 1),
          (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
            avoidanceProbability x (N - k) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k _
    rw [Fintype.sum_bool, lastVisitPiece_measureReal_true,
      lastVisitPiece_measureReal_false]
    ring
  rw [hprod] at hmeasure
  calc
    1 = ∑ k : Fin (N + 1),
        (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
          avoidanceProbability x (N - k) := hmeasure
    _ = ∑ k ∈ Finset.range (N + 1),
        (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
          avoidanceProbability x (N - k) :=
      Fin.sum_univ_eq_sum_range
        (fun k ↦ (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
          avoidanceProbability x (N - k)) (N + 1)

/-! ## Bounding the two pieces of the convolution -/

lemma pairEndpointProbabilityReal_nonneg (k : ℕ) (x : Point) :
    0 ≤ endpointProbabilityReal k 0 + endpointProbabilityReal k x :=
  add_nonneg (endpointProbabilityReal_nonneg k 0) (endpointProbabilityReal_nonneg k x)

lemma pairEndpointProbabilityReal_le (k : ℕ) (x : Point) :
    endpointProbabilityReal k 0 + endpointProbabilityReal k x ≤
      4 / (k + 1 : ℝ) := by
  have h0 := endpointProbabilityReal_le k 0
  have hx := endpointProbabilityReal_le k x
  calc
    endpointProbabilityReal k 0 + endpointProbabilityReal k x ≤
        2 / (k + 1 : ℝ) + 2 / (k + 1 : ℝ) := add_le_add h0 hx
    _ = 4 / (k + 1 : ℝ) := by ring

lemma sum_pairEndpointProbabilityReal_le (M : ℕ) (x : Point) :
    (∑ k ∈ Finset.range M,
        (endpointProbabilityReal k 0 + endpointProbabilityReal k x)) ≤
      4 * (harmonic M : ℝ) := by
  calc
    (∑ k ∈ Finset.range M,
        (endpointProbabilityReal k 0 + endpointProbabilityReal k x)) ≤
        ∑ k ∈ Finset.range M, 4 / (k + 1 : ℝ) := by
      exact Finset.sum_le_sum fun k _ ↦ pairEndpointProbabilityReal_le k x
    _ = 4 * (harmonic M : ℝ) := by
      calc
        (∑ k ∈ Finset.range M, 4 / (k + 1 : ℝ)) =
            4 * ∑ k ∈ Finset.range M, 1 / (k + 1 : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = 4 * (harmonic M : ℝ) := by
          congr 1
          simp [harmonic, one_div]

lemma lastExit_prefix_le {x : Point} (n : ℕ) :
    (∑ k ∈ Finset.range (7 * n + 1),
        (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
          avoidanceProbability x (8 * n - k)) ≤
      avoidanceProbability x n * (4 * (harmonic (7 * n + 1) : ℝ)) := by
  calc
    (∑ k ∈ Finset.range (7 * n + 1),
        (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
          avoidanceProbability x (8 * n - k)) ≤
        ∑ k ∈ Finset.range (7 * n + 1),
          (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
            avoidanceProbability x n := by
      apply Finset.sum_le_sum
      intro k hk
      have hk7 : k ≤ 7 * n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hn : n ≤ 8 * n - k := by omega
      exact mul_le_mul_of_nonneg_left
        (avoidanceProbability_antitone x hn)
        (pairEndpointProbabilityReal_nonneg k x)
    _ = avoidanceProbability x n *
        (∑ k ∈ Finset.range (7 * n + 1),
          (endpointProbabilityReal k 0 + endpointProbabilityReal k x)) := by
      calc
        (∑ k ∈ Finset.range (7 * n + 1),
            (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
              avoidanceProbability x n) =
            (∑ k ∈ Finset.range (7 * n + 1),
              (endpointProbabilityReal k 0 + endpointProbabilityReal k x)) *
                avoidanceProbability x n := by
              rw [Finset.sum_mul]
        _ = _ := mul_comm _ _
    _ ≤ avoidanceProbability x n * (4 * (harmonic (7 * n + 1) : ℝ)) := by
      gcongr
      · exact avoidanceProbability_nonneg x n
      · exact sum_pairEndpointProbabilityReal_le (7 * n + 1) x

lemma lastExit_tail_le {x : Point} {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.Ico (7 * n + 1) (8 * n + 1),
        (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
          avoidanceProbability x (8 * n - k)) ≤ 4 / 7 := by
  calc
    (∑ k ∈ Finset.Ico (7 * n + 1) (8 * n + 1),
        (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
          avoidanceProbability x (8 * n - k)) ≤
        ∑ _k ∈ Finset.Ico (7 * n + 1) (8 * n + 1),
          (4 : ℝ) / (7 * n + 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkmem := Finset.mem_Ico.mp hk
      have hpnonneg := pairEndpointProbabilityReal_nonneg k x
      calc
        (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
            avoidanceProbability x (8 * n - k) ≤
            endpointProbabilityReal k 0 + endpointProbabilityReal k x := by
          exact mul_le_of_le_one_right hpnonneg
            (avoidanceProbability_le_one x (8 * n - k))
        _ ≤ 4 / (k + 1 : ℝ) := pairEndpointProbabilityReal_le k x
        _ ≤ 4 / (7 * n + 2 : ℝ) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          have hkR : ((7 * n + 2 : ℕ) : ℝ) ≤ k + 1 := by
            exact_mod_cast (show 7 * n + 2 ≤ k + 1 by omega)
          norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hkR ⊢
          exact mul_le_mul_of_nonneg_left hkR (by norm_num)
    _ = (n : ℝ) * (4 / (7 * n + 2 : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.Ico (7 * n + 1) (8 * n + 1)).card = n := by
        simp
        omega
      rw [hcard]
    _ ≤ 4 / 7 := by
      field_simp
      nlinarith

/-- Explicit logarithmic two-point survival estimate.  Constants are kept
visible because later applications only use the order `1 / log n`. -/
theorem avoidanceProbability_lower_log_of_ne {x : Point} (hx : x ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    3 / (28 * (1 + Real.log (7 * n + 1 : ℝ))) ≤
      avoidanceProbability x n := by
  let f : ℕ → ℝ := fun k ↦
    (endpointProbabilityReal k 0 + endpointProbabilityReal k x) *
      avoidanceProbability x (8 * n - k)
  have hconv := lastExit_convolution hx (8 * n)
  have hsplit := Finset.sum_range_add_sum_Ico f
    (show 7 * n + 1 ≤ 8 * n + 1 by omega)
  have htotal : 1 =
      (∑ k ∈ Finset.range (7 * n + 1), f k) +
        ∑ k ∈ Finset.Ico (7 * n + 1) (8 * n + 1), f k := by
    rw [hsplit]
    simpa [f] using hconv
  have hprefix := lastExit_prefix_le (x := x) n
  have htail := lastExit_tail_le (x := x) hn
  change (∑ k ∈ Finset.range (7 * n + 1), f k) ≤ _ at hprefix
  change (∑ k ∈ Finset.Ico (7 * n + 1) (8 * n + 1), f k) ≤ _ at htail
  have hcore : (3 / 7 : ℝ) ≤
      avoidanceProbability x n * (4 * (harmonic (7 * n + 1) : ℝ)) := by
    linarith
  have hHpos : 0 < (harmonic (7 * n + 1) : ℝ) := by
    exact_mod_cast harmonic_pos (by omega : 7 * n + 1 ≠ 0)
  have hraw : 3 / (28 * (harmonic (7 * n + 1) : ℝ)) ≤
      avoidanceProbability x n := by
    apply (div_le_iff₀ (by positivity : 0 < 28 * (harmonic (7 * n + 1) : ℝ))).2
    nlinarith
  have hHlog : (harmonic (7 * n + 1) : ℝ) ≤
      1 + Real.log (7 * n + 1 : ℝ) := by
    exact_mod_cast harmonic_le_one_add_log (7 * n + 1)
  have hDpos : 0 < 1 + Real.log (7 * n + 1 : ℝ) := hHpos.trans_le hHlog
  calc
    3 / (28 * (1 + Real.log (7 * n + 1 : ℝ))) ≤
        3 / (28 * (harmonic (7 * n + 1) : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith
    _ ≤ avoidanceProbability x n := hraw

/-- Conventional `c / log n` form of the bound, with an explicit universal
constant. -/
theorem avoidanceProbability_lower_one_div_log_of_ne {x : Point} (hx : x ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) :
    1 / (100 * Real.log n) ≤ avoidanceProbability x n := by
  have hbase := avoidanceProbability_lower_log_of_ne hx (show 0 < n by omega)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hfactor : 0 ≤ ((n : ℝ) - 2) *
      ((n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + 4 * n + 1) := by
    positivity
  have hpoly : (7 * (n : ℝ) + 1) ≤ (n : ℝ) ^ 4 := by
    nlinarith
  have hlogpoly : Real.log (7 * n + 1 : ℝ) ≤ 4 * Real.log n := by
    calc
      Real.log (7 * n + 1 : ℝ) ≤ Real.log ((n : ℝ) ^ 4) := by
        apply Real.log_le_log (by positivity)
        exact hpoly
      _ = 4 * Real.log n := by rw [Real.log_pow]; norm_num
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hlogMono : Real.log 2 ≤ Real.log n := by
    apply Real.log_le_log (by norm_num)
    exact hnR
  have hone : (1 : ℝ) ≤ 2 * Real.log n := by nlinarith
  have hden : 1 + Real.log (7 * n + 1 : ℝ) ≤ 6 * Real.log n := by
    linarith
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hDpos : 0 < 1 + Real.log (7 * n + 1 : ℝ) := by
    have : (1 : ℝ) < 7 * n + 1 := by
      exact_mod_cast (show 1 < 7 * n + 1 by omega)
    nlinarith [Real.log_pos this]
  calc
    1 / (100 * Real.log n) ≤
        3 / (28 * (1 + Real.log (7 * n + 1 : ℝ))) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith
    _ ≤ avoidanceProbability x n := hbase

/-- The same explicit estimate also covers `x = 0`; compare with avoidance
of the origin and one fixed neighboring point. -/
theorem avoidanceProbability_lower_log (x : Point) {n : ℕ} (hn : 0 < n) :
    3 / (28 * (1 + Real.log (7 * n + 1 : ℝ))) ≤
      avoidanceProbability x n := by
  by_cases hx : x = 0
  · subst x
    let e : Point := directionVector 0
    have he : e ≠ 0 := by
      intro h
      norm_num [e, directionVector] at h
    have hlower := avoidanceProbability_lower_log_of_ne he hn
    have hsubset : avoidsPair e n ⊆ avoidsPair 0 n := by
      intro w hw k hk hkn
      have h := hw k hk hkn
      exact ⟨h.1, h.1⟩
    exact hlower.trans (MeasureTheory.measureReal_mono hsubset)
  · exact avoidanceProbability_lower_log_of_ne hx hn

theorem avoidanceProbability_lower_one_div_log (x : Point) {n : ℕ} (hn : 2 ≤ n) :
    1 / (100 * Real.log n) ≤ avoidanceProbability x n := by
  by_cases hx : x = 0
  · subst x
    let e : Point := directionVector 0
    have he : e ≠ 0 := by
      intro h
      norm_num [e, directionVector] at h
    have hlower := avoidanceProbability_lower_one_div_log_of_ne he hn
    have hsubset : avoidsPair e n ⊆ avoidsPair 0 n := by
      intro w hw k hk hkn
      have h := hw k hk hkn
      exact ⟨h.1, h.1⟩
    exact hlower.trans (MeasureTheory.measureReal_mono hsubset)
  · exact avoidanceProbability_lower_one_div_log_of_ne hx hn

/-- Increment-space form, convenient after a strong-Markov restart. -/
theorem fairSteps_avoidsPair_lower_log (x : Point) {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal (1 / (100 * Real.log n)) ≤ fairSteps (avoidsPair x n) := by
  apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).2
  exact avoidanceProbability_lower_one_div_log x hn

/-! ## Canonical walk-space statement -/

lemma simpleRandomWalk_walkAvoidsTwoPointsThrough_toReal (x : Point) (n : ℕ) :
    (simpleRandomWalk (TwoPointAvoidance.walkAvoidsTwoPointsThrough x n)).toReal =
      avoidanceProbability x n := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (TwoPointAvoidance.measurableSet_walkAvoidsTwoPointsThrough x n)]
  rfl

/-- Uniform logarithmic two-point avoidance in the exact canonical walk law.
This is the lower-bound half of HLOZ (4.4), with explicit constants. -/
theorem simpleRandomWalk_walkAvoidsTwoPointsThrough_lower_log
    (x : Point) {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal (1 / (100 * Real.log n)) ≤
      simpleRandomWalk (TwoPointAvoidance.walkAvoidsTwoPointsThrough x n) := by
  apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).2
  rw [simpleRandomWalk_walkAvoidsTwoPointsThrough_toReal]
  exact avoidanceProbability_lower_one_div_log x hn



end TwoPointLogAvoidance
end Erdos1165
