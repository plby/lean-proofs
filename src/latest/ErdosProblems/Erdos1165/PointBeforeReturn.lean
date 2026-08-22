/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.Recurrence
import ErdosProblems.Erdos1165.PotentialAsymptotic
import ErdosProblems.Erdos1165.TwoPointLogAvoidance

/-!
# Hitting a point before the first positive return

For planar simple random walk started at the origin and `x != 0`, this file
proves the classical exact identity

`P_0(H_x < H_0^+) = 1 / (2 * a(x))`,

where `a` is the planar potential kernel.  The proof is a renewal argument at
the first positive visit to the two-point set `{0,x}`.  It uses only the
already proved IID block factorization, recurrence of the origin, and the
chronological convergence of the potential kernel.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos1165
namespace PointBeforeReturn

open PlanarPotential EndpointDiagonal PotentialKernel PotentialConvergence PotentialAsymptotic
open TwoPointLogAvoidance

/-- The first strictly positive visit to `{0,x}` occurs at time `n` and is at
the origin. -/
def firstPairZeroAt (x : Point) (n : ℕ) : Set StepPath :=
  {ω | 0 < n ∧ trajectory ω n = 0 ∧
    ∀ j, 0 < j → j < n → trajectory ω j ≠ 0 ∧ trajectory ω j ≠ x}

/-- The first strictly positive visit to `{0,x}` occurs at time `n` and is at
`x`. -/
def firstPairTargetAt (x : Point) (n : ℕ) : Set StepPath :=
  {ω | 0 < n ∧ trajectory ω n = x ∧
    ∀ j, 0 < j → j < n → trajectory ω j ≠ 0 ∧ trajectory ω j ≠ x}

/-- The event denoted `H_x < H_0^+`: the walk reaches `x` before its first
strictly positive return to the origin. -/
def pointBeforePositiveReturn (x : Point) : Set StepPath :=
  ⋃ n, firstPairTargetAt x n

lemma measurableSet_trajectory_eq_filtration (n : ℕ) (x : Point) :
    MeasurableSet[incrementFiltration n] {w : StepPath | trajectory w n = x} := by
  have heq : {w : StepPath | trajectory w n = x} =
      stepPrefix n ⁻¹' {u | markovBlockDisplacement u = x} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [trajectory_eq_markovBlockDisplacement_stepPrefix]
  rw [heq, incrementFiltration_apply]
  exact ⟨_, measurableSet_eq_fun (measurable_of_countable _) measurable_const, rfl⟩

lemma measurableSet_firstPairZeroAt_filtration (x : Point) (n : ℕ) :
    MeasurableSet[incrementFiltration n] (firstPairZeroAt x n) := by
  by_cases hn : 0 < n
  · have hend : MeasurableSet[incrementFiltration n]
        {w : StepPath | trajectory w n = 0} := by
      exact measurableSet_returnAt_filtration n
    have hbefore : MeasurableSet[incrementFiltration n]
        (⋂ j : ℕ, ⋂ (_ : 0 < j), ⋂ (_ : j < n),
          ({w : StepPath | trajectory w j = 0}ᶜ ∩
            {w : StepPath | trajectory w j = x}ᶜ)) := by
      apply MeasurableSet.iInter
      intro j
      apply MeasurableSet.iInter
      intro hjpos
      apply MeasurableSet.iInter
      intro hj
      exact (incrementFiltration.mono (Nat.le_of_lt hj)) _
        ((measurableSet_trajectory_eq_filtration j 0).compl.inter
          (measurableSet_trajectory_eq_filtration j x).compl)
    have heq : firstPairZeroAt x n = {w : StepPath | trajectory w n = 0} ∩
        (⋂ j : ℕ, ⋂ (_ : 0 < j), ⋂ (_ : j < n),
          ({w : StepPath | trajectory w j = 0}ᶜ ∩
            {w : StepPath | trajectory w j = x}ᶜ)) := by
      ext w
      simp [firstPairZeroAt, hn]
    rw [heq]
    exact hend.inter hbefore
  · have heq : firstPairZeroAt x n = ∅ := by
      ext w
      simp [firstPairZeroAt, hn]
    rw [heq]
    exact (incrementFiltration n).measurableSet_empty

lemma measurableSet_firstPairTargetAt_filtration (x : Point) (n : ℕ) :
    MeasurableSet[incrementFiltration n] (firstPairTargetAt x n) := by
  by_cases hn : 0 < n
  · have hend : MeasurableSet[incrementFiltration n]
        {w : StepPath | trajectory w n = x} :=
      measurableSet_trajectory_eq_filtration n x
    have hbefore : MeasurableSet[incrementFiltration n]
        (⋂ j : ℕ, ⋂ (_ : 0 < j), ⋂ (_ : j < n),
          ({w : StepPath | trajectory w j = 0}ᶜ ∩
            {w : StepPath | trajectory w j = x}ᶜ)) := by
      apply MeasurableSet.iInter
      intro j
      apply MeasurableSet.iInter
      intro hjpos
      apply MeasurableSet.iInter
      intro hj
      exact (incrementFiltration.mono (Nat.le_of_lt hj)) _
        ((measurableSet_trajectory_eq_filtration j 0).compl.inter
          (measurableSet_trajectory_eq_filtration j x).compl)
    have heq : firstPairTargetAt x n = {w : StepPath | trajectory w n = x} ∩
        (⋂ j : ℕ, ⋂ (_ : 0 < j), ⋂ (_ : j < n),
          ({w : StepPath | trajectory w j = 0}ᶜ ∩
            {w : StepPath | trajectory w j = x}ᶜ)) := by
      ext w
      simp [firstPairTargetAt, hn]
    rw [heq]
    exact hend.inter hbefore
  · have heq : firstPairTargetAt x n = ∅ := by
      ext w
      simp [firstPairTargetAt, hn]
    rw [heq]
    exact (incrementFiltration n).measurableSet_empty

lemma measurableSet_firstPairZeroAt (x : Point) (n : ℕ) :
    MeasurableSet (firstPairZeroAt x n) :=
  incrementFiltration.le n _ (measurableSet_firstPairZeroAt_filtration x n)

lemma measurableSet_firstPairTargetAt (x : Point) (n : ℕ) :
    MeasurableSet (firstPairTargetAt x n) :=
  incrementFiltration.le n _ (measurableSet_firstPairTargetAt_filtration x n)

lemma firstPairZeroAt_pairwiseDisjoint (x : Point) :
    Pairwise fun i j ↦ Disjoint (firstPairZeroAt x i) (firstPairZeroAt x j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro w hi hj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact (hj.2.2 i hi.1 hlt).1 hi.2.1
  · exact hij heq
  · exact (hi.2.2 j hj.1 hgt).1 hj.2.1

lemma firstPairTargetAt_pairwiseDisjoint (x : Point) :
    Pairwise fun i j ↦ Disjoint (firstPairTargetAt x i) (firstPairTargetAt x j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro w hi hj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact (hj.2.2 i hi.1 hlt).2 hi.2.1
  · exact hij heq
  · exact (hi.2.2 j hj.1 hgt).2 hj.2.1

lemma firstPairZeroAt_disjoint_firstPairTargetAt {x : Point} (hx : x ≠ 0)
    (i j : ℕ) : Disjoint (firstPairZeroAt x i) (firstPairTargetAt x j) := by
  rw [Set.disjoint_left]
  intro w hi hj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact (hj.2.2 i hi.1 hlt).1 hi.2.1
  · subst j
    exact hx (hj.2.1.symm.trans hi.2.1)
  · exact (hi.2.2 j hj.1 hgt).2 hj.2.1

lemma measurableSet_pointBeforePositiveReturn (x : Point) :
    MeasurableSet (pointBeforePositiveReturn x) := by
  unfold pointBeforePositiveReturn
  exact MeasurableSet.iUnion (measurableSet_firstPairTargetAt x)

/-- The real probability `P_0(H_x < H_0^+)`. -/
noncomputable def pointBeforeReturnProbability (x : Point) : ℝ :=
  fairSteps.real (pointBeforePositiveReturn x)

lemma pointBeforeReturnProbability_nonneg (x : Point) :
    0 ≤ pointBeforeReturnProbability x := measureReal_nonneg

lemma pointBeforeReturnProbability_le_one (x : Point) :
    pointBeforeReturnProbability x ≤ 1 := by
  unfold pointBeforeReturnProbability
  have h := MeasureTheory.measureReal_mono (μ := fairSteps)
    (subset_univ (pointBeforePositiveReturn x)) (by finiteness)
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one] using h

/-! ## Renewal factorization at the first two-point visit -/

/-- The displacement during the `m` steps following time `n` is `a`. -/
def relativeEndpointAt (n m : ℕ) (a : Point) : Set StepPath :=
  {w | trajectory w (n + m) - trajectory w n = a}

lemma isMeasurableAtStopping_firstPairZeroAt_const (x : Point) (k : ℕ) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ k) (firstPairZeroAt x k) := by
  intro n
  by_cases hnk : n = k
  · subst n
    simpa using measurableSet_firstPairZeroAt_filtration x k
  · have heq : firstPairZeroAt x k ∩ {w : StepPath | k = n} = ∅ := by
      ext w
      simp [Ne.symm hnk]
    rw [heq]
    exact (incrementFiltration n).measurableSet_empty

lemma isMeasurableAtStopping_firstPairTargetAt_const (x : Point) (k : ℕ) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ k) (firstPairTargetAt x k) := by
  intro n
  by_cases hnk : n = k
  · subst n
    simpa using measurableSet_firstPairTargetAt_filtration x k
  · have heq : firstPairTargetAt x k ∩ {w : StepPath | k = n} = ∅ := by
      ext w
      simp [Ne.symm hnk]
    rw [heq]
    exact (incrementFiltration n).measurableSet_empty

lemma relativeEndpointAt_eq_postStoppingBlock_preimage (n m : ℕ) (a : Point) :
    relativeEndpointAt n m a =
      postStoppingBlock (fun _ : StepPath ↦ n) m ⁻¹'
        {u | markovBlockDisplacement u = a} := by
  ext w
  simp only [relativeEndpointAt, Set.mem_ofPred_eq, Set.mem_preimage]
  rw [show postStoppingBlock (fun _ : StepPath ↦ n) m w = stepBlock n m w from rfl]
  rw [show markovBlockDisplacement (stepBlock n m w) =
      trajectory (shiftSteps n w) m by
        exact (trajectory_eq_markovBlockDisplacement_stepPrefix (shiftSteps n w) m).symm]
  rw [← trajectory_add_sub_trajectory]

lemma fairBlock_endpoint (m : ℕ) (a : Point) :
    fairBlock m {u | markovBlockDisplacement u = a} =
      fairSteps {w | trajectory w m = a} := by
  have hset : stepBlock 0 m ⁻¹' {u | markovBlockDisplacement u = a} =
      {w : StepPath | trajectory w m = a} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [show stepBlock 0 m w = stepPrefix m w by ext j; simp [stepBlock, stepPrefix]]
    rw [← trajectory_eq_markovBlockDisplacement_stepPrefix]
  rw [← fairSteps_map_stepBlock 0 m]
  rw [Measure.map_apply (measurable_stepBlock 0 m)
    (measurableSet_eq_fun (measurable_of_countable _) measurable_const)]
  rw [hset]

lemma measure_firstPairZeroAt_inter_relativeEndpointAt
    (x : Point) (k m : ℕ) (a : Point) :
    fairSteps (firstPairZeroAt x k ∩ relativeEndpointAt k m a) =
      fairSteps (firstPairZeroAt x k) * fairSteps {w | trajectory w m = a} := by
  rw [relativeEndpointAt_eq_postStoppingBlock_preimage]
  rw [strongMarkov_stoppedEvent_set (isFiniteStoppingTime_const k)
    (isMeasurableAtStopping_firstPairZeroAt_const x k) m
    {u | markovBlockDisplacement u = a}]
  rw [fairBlock_endpoint]

lemma measure_firstPairTargetAt_inter_relativeEndpointAt
    (x : Point) (k m : ℕ) (a : Point) :
    fairSteps (firstPairTargetAt x k ∩ relativeEndpointAt k m a) =
      fairSteps (firstPairTargetAt x k) * fairSteps {w | trajectory w m = a} := by
  rw [relativeEndpointAt_eq_postStoppingBlock_preimage]
  rw [strongMarkov_stoppedEvent_set (isFiniteStoppingTime_const k)
    (isMeasurableAtStopping_firstPairTargetAt_const x k) m
    {u | markovBlockDisplacement u = a}]
  rw [fairBlock_endpoint]

/-- The contribution of paths whose first positive visit to `{0,x}` is at
time `k`, to the endpoint `z` at time `n`. -/
def firstPairRenewalPiece (x : Point) (n : ℕ) (z : Point) (k : ℕ) : Set StepPath :=
  (firstPairZeroAt x k ∩ relativeEndpointAt k (n - k) z) ∪
    (firstPairTargetAt x k ∩ relativeEndpointAt k (n - k) (z - x))

lemma measurableSet_relativeEndpointAt (n m : ℕ) (a : Point) :
    MeasurableSet (relativeEndpointAt n m a) := by
  rw [relativeEndpointAt_eq_postStoppingBlock_preimage]
  exact (measurable_postStoppingBlock (isFiniteStoppingTime_const n) m)
    (measurableSet_eq_fun (measurable_of_countable _) measurable_const)

lemma measurableSet_firstPairRenewalPiece (x : Point) (n : ℕ) (z : Point) (k : ℕ) :
    MeasurableSet (firstPairRenewalPiece x n z k) := by
  exact ((measurableSet_firstPairZeroAt x k).inter
      (measurableSet_relativeEndpointAt k (n - k) z)).union
    ((measurableSet_firstPairTargetAt x k).inter
      (measurableSet_relativeEndpointAt k (n - k) (z - x)))

lemma firstPairRenewalPiece_pairwiseDisjoint {x : Point} (hx : x ≠ 0)
    (n : ℕ) (z : Point) :
    Set.PairwiseDisjoint (↑(Finset.Icc 1 n) : Set ℕ)
      (firstPairRenewalPiece x n z) := by
  intro i hi j hj hij
  change Disjoint (firstPairRenewalPiece x n z i) (firstPairRenewalPiece x n z j)
  rw [Set.disjoint_left]
  intro w hwi hwj
  rcases hwi with (hi0 | hix) <;> rcases hwj with (hj0 | hjx)
  · exact (firstPairZeroAt_pairwiseDisjoint x hij).le_bot ⟨hi0.1, hj0.1⟩
  · exact (firstPairZeroAt_disjoint_firstPairTargetAt hx i j).le_bot ⟨hi0.1, hjx.1⟩
  · exact (firstPairZeroAt_disjoint_firstPairTargetAt hx j i).symm.le_bot ⟨hix.1, hj0.1⟩
  · exact (firstPairTargetAt_pairwiseDisjoint x hij).le_bot ⟨hix.1, hjx.1⟩

lemma firstPairRenewalPiece_zero_target_disjoint {x : Point} (hx : x ≠ 0)
    (n : ℕ) (z : Point) (k : ℕ) :
    Disjoint
      (firstPairZeroAt x k ∩ relativeEndpointAt k (n - k) z)
      (firstPairTargetAt x k ∩ relativeEndpointAt k (n - k) (z - x)) :=
  (firstPairZeroAt_disjoint_firstPairTargetAt hx k k).mono inter_subset_left inter_subset_left

private lemma firstPair_exists_of_pair_endpoint {x : Point} {w : StepPath} {n : ℕ}
    (hn : 0 < n) (hend : trajectory w n = 0 ∨ trajectory w n = x) :
    ∃ k ∈ Finset.Icc 1 n,
      w ∈ firstPairZeroAt x k ∨ w ∈ firstPairTargetAt x k := by
  let k := Nat.find (show ∃ k, 0 < k ∧
      (trajectory w k = 0 ∨ trajectory w k = x) from ⟨n, hn, hend⟩)
  have hk := Nat.find_spec (show ∃ k, 0 < k ∧
      (trajectory w k = 0 ∨ trajectory w k = x) from ⟨n, hn, hend⟩)
  have hkn : k ≤ n := Nat.find_min' _ ⟨hn, hend⟩
  have hbefore : ∀ j, 0 < j → j < k →
      trajectory w j ≠ 0 ∧ trajectory w j ≠ x := by
    intro j hjpos hjlt
    constructor <;> intro hjend
    · exact (Nat.not_lt_of_ge (Nat.find_min'
        (show ∃ k, 0 < k ∧ (trajectory w k = 0 ∨ trajectory w k = x) from
          ⟨n, hn, hend⟩) ⟨hjpos, Or.inl hjend⟩)) hjlt
    · exact (Nat.not_lt_of_ge (Nat.find_min'
        (show ∃ k, 0 < k ∧ (trajectory w k = 0 ∨ trajectory w k = x) from
          ⟨n, hn, hend⟩) ⟨hjpos, Or.inr hjend⟩)) hjlt
  refine ⟨k, Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hk.1, hkn⟩, ?_⟩
  rcases hk.2 with hk0 | hkx
  · exact Or.inl ⟨hk.1, hk0, hbefore⟩
  · exact Or.inr ⟨hk.1, hkx, hbefore⟩

lemma endpoint_eq_iUnion_firstPairRenewalPiece {x z : Point} (hx : x ≠ 0)
    (hz : z = 0 ∨ z = x) {n : ℕ} (hn : 0 < n) :
    {w : StepPath | trajectory w n = z} =
      ⋃ k ∈ Finset.Icc 1 n, firstPairRenewalPiece x n z k := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, firstPairRenewalPiece,
    Set.mem_union, Set.mem_inter_iff, relativeEndpointAt, Set.mem_ofPred_eq]
  constructor
  · intro hend
    obtain ⟨k, hk, hkfirst⟩ := firstPair_exists_of_pair_endpoint hn (hend ▸ hz)
    refine ⟨k, hk, ?_⟩
    have hkn := (Finset.mem_Icc.mp hk).2
    rcases hkfirst with hk0 | hkx
    · left
      refine ⟨hk0, ?_⟩
      rw [Nat.add_sub_of_le hkn, hend, hk0.2.1, sub_zero]
    · right
      refine ⟨hkx, ?_⟩
      rw [Nat.add_sub_of_le hkn, hend, hkx.2.1]
  · rintro ⟨k, hk, hpiece⟩
    have hkn := (Finset.mem_Icc.mp hk).2
    rcases hpiece with hk0 | hkx
    · have hrel := hk0.2
      rw [Nat.add_sub_of_le hkn, hk0.1.2.1, sub_zero] at hrel
      exact hrel
    · have hrel := hkx.2
      rw [Nat.add_sub_of_le hkn, hkx.1.2.1] at hrel
      exact (sub_eq_iff_eq_add.mp hrel).trans (by abel)

theorem measure_endpoint_renewal {x z : Point} (hx : x ≠ 0)
    (hz : z = 0 ∨ z = x) {n : ℕ} (hn : 0 < n) :
    fairSteps {w : StepPath | trajectory w n = z} =
      ∑ k ∈ Finset.Icc 1 n,
        (fairSteps (firstPairZeroAt x k) *
            fairSteps {w : StepPath | trajectory w (n - k) = z} +
          fairSteps (firstPairTargetAt x k) *
            fairSteps {w : StepPath | trajectory w (n - k) = z - x}) := by
  rw [endpoint_eq_iUnion_firstPairRenewalPiece hx hz hn]
  rw [measure_biUnion_finset (firstPairRenewalPiece_pairwiseDisjoint hx n z)
    (fun k _ ↦ measurableSet_firstPairRenewalPiece x n z k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [firstPairRenewalPiece, measure_union
    (firstPairRenewalPiece_zero_target_disjoint hx n z k)
    ((measurableSet_firstPairTargetAt x k).inter
      (measurableSet_relativeEndpointAt k (n - k) (z - x)))]
  rw [measure_firstPairZeroAt_inter_relativeEndpointAt,
    measure_firstPairTargetAt_inter_relativeEndpointAt]

/-! ## Real-valued renewal equation -/

noncomputable def firstPairZeroProbability (x : Point) (n : ℕ) : ℝ :=
  fairSteps.real (firstPairZeroAt x n)

noncomputable def firstPairTargetProbability (x : Point) (n : ℕ) : ℝ :=
  fairSteps.real (firstPairTargetAt x n)

lemma firstPairZeroProbability_nonneg (x : Point) (n : ℕ) :
    0 ≤ firstPairZeroProbability x n := measureReal_nonneg

lemma firstPairTargetProbability_nonneg (x : Point) (n : ℕ) :
    0 ≤ firstPairTargetProbability x n := measureReal_nonneg

lemma card_endpointBlocks_eq_planarEndpointCount (n : ℕ) (x : Point) :
    (endpointBlocks n x).card = planarEndpointCount n x := by
  let e : ↥(endpointBlocks n x) ≃
      {u : Fin n → Direction // blockDisplacement u = x} :=
    { toFun := fun u ↦ ⟨u.1, mem_endpointBlocks.mp u.2⟩
      invFun := fun u ↦ ⟨u.1, mem_endpointBlocks.mpr u.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    (endpointBlocks n x).card =
        Fintype.card ↥(endpointBlocks n x) := (Fintype.card_coe _).symm
    _ = Fintype.card {u : Fin n → Direction // blockDisplacement u = x} :=
      Fintype.card_congr e
    _ = Nat.card {u : Fin n → Direction // blockDisplacement u = x} :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card {u : Fin n → Direction // finiteDirectionEndpoint u = x} := by
      congr 2
      funext u
      rw [finiteDirectionEndpoint_eq_sum]
      rfl
    _ = planarEndpointCount n x := by
      simpa using card_finiteDirectionEndpoint_fiber (Fin n) x

lemma endpointProbability_eq_endpointProbabilityReal (n : ℕ) (x : Point) :
    endpointProbability n x = endpointProbabilityReal n x := by
  unfold endpointProbability endpointProbabilityReal
  rw [card_endpointBlocks_eq_planarEndpointCount]

lemma endpointProbability_neg (n : ℕ) (x : Point) :
    endpointProbability n (-x) = endpointProbability n x := by
  rw [endpointProbability_eq_endpointProbabilityReal,
    endpointProbability_eq_endpointProbabilityReal]
  have hmap := congrArg (fun μ : Measure StepPath ↦
      μ {w | trajectory w n = x}) fairSteps_map_reverseSteps
  rw [Measure.map_apply measurable_reverseSteps
    (measurableSet_trajectory_eq_filtration n x |> incrementFiltration.le n _)] at hmap
  have hpre : reverseSteps ⁻¹' {w : StepPath | trajectory w n = x} =
      {w : StepPath | trajectory w n = -x} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [congrFun (trajectory_reverseSteps w) n]
    change -trajectory w n = x ↔ trajectory w n = -x
    constructor <;> intro h
    · simpa using congrArg Neg.neg h
    · simpa using congrArg Neg.neg h
  rw [hpre] at hmap
  rw [← fairSteps_endpoint_toReal, ← fairSteps_endpoint_toReal, hmap]

theorem endpointProbability_renewal {x z : Point} (hx : x ≠ 0)
    (hz : z = 0 ∨ z = x) {n : ℕ} (hn : 0 < n) :
    endpointProbability n z =
      ∑ k ∈ Finset.Icc 1 n,
        (firstPairZeroProbability x k * endpointProbability (n - k) z +
          firstPairTargetProbability x k * endpointProbability (n - k) (z - x)) := by
  have h := congrArg ENNReal.toReal (measure_endpoint_renewal hx hz hn)
  rw [fairSteps_endpoint_toReal] at h
  rw [ENNReal.toReal_sum (by
    intro k hk
    exact ENNReal.add_ne_top.mpr ⟨
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)⟩)] at h
  have hterm (k : ℕ) :
      (fairSteps (firstPairZeroAt x k) *
            fairSteps {w : StepPath | trajectory w (n - k) = z} +
          fairSteps (firstPairTargetAt x k) *
            fairSteps {w : StepPath | trajectory w (n - k) = z - x}).toReal =
        fairSteps.real (firstPairZeroAt x k) * endpointProbabilityReal (n - k) z +
          fairSteps.real (firstPairTargetAt x k) *
            endpointProbabilityReal (n - k) (z - x) := by
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      fairSteps_endpoint_toReal, fairSteps_endpoint_toReal]
    simp only [Measure.real]
  simp_rw [hterm] at h
  simpa only [firstPairZeroProbability, firstPairTargetProbability,
    fairSteps_endpoint_toReal, endpointProbability_eq_endpointProbabilityReal] using h

/-- Signed renewal coefficient: first hit at `0` minus first hit at `x`. -/
noncomputable def firstPairDifference (x : Point) (n : ℕ) : ℝ :=
  firstPairZeroProbability x n - firstPairTargetProbability x n

theorem potentialTerm_renewal {x : Point} (hx : x ≠ 0) {n : ℕ} (hn : 0 < n) :
    potentialTerm x n =
      ∑ k ∈ Finset.Icc 1 n,
        firstPairDifference x k * potentialTerm x (n - k) := by
  have h0 := endpointProbability_renewal hx (Or.inl rfl) hn
  have hx' := endpointProbability_renewal hx (Or.inr rfl) hn
  simp only [zero_sub] at h0
  simp_rw [endpointProbability_neg] at h0
  simp only [sub_self] at hx'
  rw [potentialTerm]
  rw [h0, hx', ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold firstPairDifference potentialTerm
  ring

/-! ## Total first-visit mass -/

def firstPairZeroEvent (x : Point) : Set StepPath :=
  ⋃ n, firstPairZeroAt x n

lemma measurableSet_firstPairZeroEvent (x : Point) :
    MeasurableSet (firstPairZeroEvent x) := by
  unfold firstPairZeroEvent
  exact MeasurableSet.iUnion (measurableSet_firstPairZeroAt x)

lemma firstPairZeroEvent_disjoint_pointBeforePositiveReturn {x : Point} (hx : x ≠ 0) :
    Disjoint (firstPairZeroEvent x) (pointBeforePositiveReturn x) := by
  rw [Set.disjoint_left]
  intro w hw0 hwx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw0
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hwx
  exact (firstPairZeroAt_disjoint_firstPairTargetAt hx i j).le_bot ⟨hi, hj⟩

lemma positiveReturnEvent_subset_firstPairEvent (x : Point) :
    positiveReturnEvent ⊆ firstPairZeroEvent x ∪ pointBeforePositiveReturn x := by
  intro w hw
  obtain ⟨n, hn, hn0⟩ := hw
  obtain ⟨k, hk, hkfirst⟩ := firstPair_exists_of_pair_endpoint hn (Or.inl hn0)
  rcases hkfirst with hk0 | hkx
  · exact Or.inl (Set.mem_iUnion.mpr ⟨k, hk0⟩)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨k, hkx⟩)

theorem fairSteps_firstPairEvent_union {x : Point} (hx : x ≠ 0) :
    fairSteps (firstPairZeroEvent x ∪ pointBeforePositiveReturn x) = 1 := by
  apply le_antisymm prob_le_one
  rw [← fairSteps_positiveReturnEvent]
  exact measure_mono (positiveReturnEvent_subset_firstPairEvent x)

theorem summable_firstPairZeroProbability (x : Point) :
    Summable (firstPairZeroProbability x) := by
  unfold firstPairZeroProbability
  exact summable_measure_toReal (measurableSet_firstPairZeroAt x)
    (firstPairZeroAt_pairwiseDisjoint x)

theorem summable_firstPairTargetProbability (x : Point) :
    Summable (firstPairTargetProbability x) := by
  unfold firstPairTargetProbability
  exact summable_measure_toReal (measurableSet_firstPairTargetAt x)
    (firstPairTargetAt_pairwiseDisjoint x)

theorem tsum_firstPairZeroProbability (x : Point) :
    ∑' n, firstPairZeroProbability x n = fairSteps.real (firstPairZeroEvent x) := by
  unfold firstPairZeroProbability firstPairZeroEvent Measure.real
  rw [MeasureTheory.measure_iUnion (firstPairZeroAt_pairwiseDisjoint x)
      (measurableSet_firstPairZeroAt x),
    ENNReal.tsum_toReal_eq (fun n ↦ measure_ne_top _ _)]

theorem tsum_firstPairTargetProbability (x : Point) :
    ∑' n, firstPairTargetProbability x n = pointBeforeReturnProbability x := by
  unfold firstPairTargetProbability pointBeforeReturnProbability pointBeforePositiveReturn
    Measure.real
  rw [MeasureTheory.measure_iUnion (firstPairTargetAt_pairwiseDisjoint x)
      (measurableSet_firstPairTargetAt x),
    ENNReal.tsum_toReal_eq (fun n ↦ measure_ne_top _ _)]

theorem firstPairZeroProbability_add_targetProbability {x : Point} (hx : x ≠ 0) :
    fairSteps.real (firstPairZeroEvent x) + pointBeforeReturnProbability x = 1 := by
  unfold pointBeforeReturnProbability
  rw [← MeasureTheory.measureReal_union
    (firstPairZeroEvent_disjoint_pointBeforePositiveReturn hx)
    (measurableSet_pointBeforePositiveReturn x)]
  rw [Measure.real, fairSteps_firstPairEvent_union hx, ENNReal.toReal_one]

theorem summable_firstPairDifference (x : Point) :
    Summable (firstPairDifference x) := by
  unfold firstPairDifference
  exact (summable_firstPairZeroProbability x).sub
    (summable_firstPairTargetProbability x)

theorem tsum_firstPairDifference {x : Point} (hx : x ≠ 0) :
    ∑' n, firstPairDifference x n =
      1 - 2 * pointBeforeReturnProbability x := by
  rw [show (∑' n, firstPairDifference x n) =
      (∑' n, firstPairZeroProbability x n) -
        ∑' n, firstPairTargetProbability x n by
    unfold firstPairDifference
    exact Summable.tsum_sub (summable_firstPairZeroProbability x)
      (summable_firstPairTargetProbability x)]
  rw [tsum_firstPairZeroProbability, tsum_firstPairTargetProbability]
  have hmass := firstPairZeroProbability_add_targetProbability hx
  linarith

/-! ## Partial-potential renewal and its limit -/

lemma potentialTerm_zero_of_ne {x : Point} (hx : x ≠ 0) :
    potentialTerm x 0 = 1 := by
  have hzero : endpointBlocks 0 0 = {default} := by
    ext u
    rw [mem_endpointBlocks, Finset.mem_singleton]
    constructor
    · intro hu
      exact Subsingleton.elim _ _
    · intro hu
      simp [blockDisplacement]
  have htarget : endpointBlocks 0 x = ∅ := by
    ext u
    simp only [Finset.notMem_empty, iff_false]
    intro hu
    apply hx
    rw [← mem_endpointBlocks.mp hu]
    simp [blockDisplacement]
  unfold potentialTerm endpointProbability
  rw [hzero, htarget]
  norm_num

theorem potentialTerm_succ_renewal {x : Point} (hx : x ≠ 0) (n : ℕ) :
    potentialTerm x (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        firstPairDifference x (k + 1) * potentialTerm x (n - k) := by
  have h := potentialTerm_renewal hx (show 0 < n + 1 by omega)
  rw [sum_Icc_one_succ_eq_sum_range] at h
  simpa using h

lemma potentialPartial_succ (x : Point) (N : ℕ) :
    potentialPartial x (N + 1) = potentialPartial x N + potentialTerm x N := by
  unfold potentialPartial
  rw [Finset.sum_range_succ]

/-- Finite renewal identity for the chronological potential prefix. -/
theorem potentialPartial_renewal {x : Point} (hx : x ≠ 0) (N : ℕ) :
    potentialPartial x (N + 1) =
      1 + ∑ k ∈ Finset.range N,
        firstPairDifference x (k + 1) * potentialPartial x (N - k) := by
  induction N with
  | zero =>
      simp [potentialPartial, potentialTerm_zero_of_ne hx]
  | succ N ih =>
      rw [potentialPartial_succ, ih, potentialTerm_succ_renewal hx N]
      rw [Finset.sum_range_succ]
      have hpartial (k : ℕ) (hk : k ∈ Finset.range N) :
          potentialPartial x (N + 1 - k) =
            potentialPartial x (N - k) + potentialTerm x (N - k) := by
        have hkN : k ≤ N := Nat.le_of_lt (Finset.mem_range.mp hk)
        rw [Nat.succ_sub hkN, potentialPartial_succ]
      have hsum :
          (∑ k ∈ Finset.range N,
              firstPairDifference x (k + 1) * potentialPartial x (N + 1 - k)) =
            (∑ k ∈ Finset.range N,
              firstPairDifference x (k + 1) * potentialPartial x (N - k)) +
              ∑ k ∈ Finset.range N,
                firstPairDifference x (k + 1) * potentialTerm x (N - k) := by
        calc
          _ = ∑ k ∈ Finset.range N,
                (firstPairDifference x (k + 1) * potentialPartial x (N - k) +
                  firstPairDifference x (k + 1) * potentialTerm x (N - k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hpartial k hk]
              ring
          _ = _ := Finset.sum_add_distrib
      rw [Finset.sum_range_succ, hsum]
      have hAone : potentialPartial x 1 = 1 := by
        simp [potentialPartial, potentialTerm_zero_of_ne hx]
      rw [show N + 1 - N = 1 by omega, hAone,
        show N - N = 0 by omega, potentialTerm_zero_of_ne hx]
      ring

lemma potentialPair_nonneg (x : Point) (n : ℕ) :
    0 ≤ potentialPair x n := by
  by_cases hx : Even (x.1 + x.2)
  · rw [potentialPair_eq_diagonalProductLoss_of_even hx]
    exact diagonalProductLoss_nonneg _ _ _
  · rw [potentialPair_eq_neighbor_average_of_not_even hx]
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro d hd
    rw [potentialPair_eq_diagonalProductLoss_of_even
      (neighbor_even_of_not_even hx d)]
    exact diagonalProductLoss_nonneg _ _ _

lemma planarPotentialKernel_nonneg (x : Point) :
    0 ≤ planarPotentialKernel x := by
  unfold planarPotentialKernel
  exact tsum_nonneg (potentialPair_nonneg x)

lemma potentialPartial_abs_le (x : Point) (N : ℕ) :
    |potentialPartial x N| ≤ planarPotentialKernel x + 1 := by
  have hpairs :
      (∑ n ∈ Finset.range (N / 2), potentialPair x n) ≤
        planarPotentialKernel x := by
    unfold planarPotentialKernel
    exact (summable_potentialPair x).sum_le_tsum _
      (fun n hn ↦ potentialPair_nonneg x n)
  have hremAbs := abs_chronologicalRemainder_le x N
  have hden : 1 / (((N / 2 + 1 : ℕ) : ℝ)) ≤ 1 := by
    have hpos : (0 : ℝ) < (N / 2 + 1 : ℕ) := by positivity
    rw [div_le_one hpos]
    exact_mod_cast (show 1 ≤ N / 2 + 1 by omega)
  have heq : potentialPartial x N =
      (∑ n ∈ Finset.range (N / 2), potentialPair x n) +
        chronologicalRemainder x N := by
    unfold chronologicalRemainder
    ring
  rw [heq]
  calc
    |(∑ n ∈ Finset.range (N / 2), potentialPair x n) +
        chronologicalRemainder x N| ≤
      |∑ n ∈ Finset.range (N / 2), potentialPair x n| +
        |chronologicalRemainder x N| := abs_add_le _ _
    _ ≤ planarPotentialKernel x + 1 := by
      have hsumNonneg : 0 ≤ ∑ n ∈ Finset.range (N / 2), potentialPair x n :=
        Finset.sum_nonneg fun n hn ↦ potentialPair_nonneg x n
      rw [abs_of_nonneg hsumNonneg]
      exact add_le_add hpairs (hremAbs.trans hden)

noncomputable def renewalSummand (x : Point) (N k : ℕ) : ℝ :=
  if k < N then
    firstPairDifference x (k + 1) * potentialPartial x (N - k)
  else 0

lemma tsum_renewalSummand (x : Point) (N : ℕ) :
    ∑' k, renewalSummand x N k =
      ∑ k ∈ Finset.range N,
        firstPairDifference x (k + 1) * potentialPartial x (N - k) := by
  rw [tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl
    intro k hk
    simp [renewalSummand, Finset.mem_range.mp hk]
  · intro k hk
    have hkn : ¬k < N := by
      simpa only [Finset.mem_range] using hk
    simp [renewalSummand, hkn]

lemma firstPairDifference_zero (x : Point) : firstPairDifference x 0 = 0 := by
  unfold firstPairDifference firstPairZeroProbability firstPairTargetProbability
  have hz : firstPairZeroAt x 0 = ∅ := by
    ext w
    simp [firstPairZeroAt]
  have hx : firstPairTargetAt x 0 = ∅ := by
    ext w
    simp [firstPairTargetAt]
  rw [hz, hx]
  simp

lemma tsum_firstPairDifference_succ (x : Point) :
    ∑' k, firstPairDifference x (k + 1) = ∑' k, firstPairDifference x k := by
  have hsplit := (summable_firstPairDifference x).sum_add_tsum_nat_add 1
  simpa [firstPairDifference_zero] using hsplit

theorem tendsto_renewalSummand_tsum (x : Point) :
    Tendsto (fun N ↦ ∑' k, renewalSummand x N k) atTop
      (nhds (planarPotentialKernel x * ∑' k, firstPairDifference x k)) := by
  let B : ℕ → ℝ := fun k ↦
    (planarPotentialKernel x + 1) * |firstPairDifference x (k + 1)|
  have hB : Summable B := by
    dsimp [B]
    exact (((summable_nat_add_iff 1).mpr
      (summable_firstPairDifference x).abs).mul_left (planarPotentialKernel x + 1))
  have hpoint (k : ℕ) : Tendsto (renewalSummand x · k) atTop
      (nhds (firstPairDifference x (k + 1) * planarPotentialKernel x)) := by
    have hA := (tendsto_potentialPartial_planarPotentialKernel x).comp
      (tendsto_sub_atTop_nat k)
    have hmul := hA.const_mul (firstPairDifference x (k + 1))
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop (k + 1)] with N hN
    simp [renewalSummand, show k < N by omega]
  have hbound : ∀ᶠ N in atTop, ∀ k, ‖renewalSummand x N k‖ ≤ B k := by
    filter_upwards [] with N
    intro k
    by_cases hk : k < N
    · rw [renewalSummand, if_pos hk, Real.norm_eq_abs, abs_mul]
      dsimp [B]
      have hA := potentialPartial_abs_le x (N - k)
      calc
        |firstPairDifference x (k + 1)| * |potentialPartial x (N - k)| ≤
            |firstPairDifference x (k + 1)| * (planarPotentialKernel x + 1) :=
          mul_le_mul_of_nonneg_left hA (abs_nonneg _)
        _ = (planarPotentialKernel x + 1) *
            |firstPairDifference x (k + 1)| := mul_comm _ _
    · simp [renewalSummand, hk, B]
      exact mul_nonneg (by linarith [planarPotentialKernel_nonneg x]) (abs_nonneg _)
  have ht := tendsto_tsum_of_dominated_convergence hB hpoint hbound
  convert ht using 1
  rw [tsum_mul_right]
  rw [tsum_firstPairDifference_succ]
  ring

theorem potentialKernel_probability_equation {x : Point} (hx : x ≠ 0) :
    planarPotentialKernel x =
      1 + planarPotentialKernel x *
        (1 - 2 * pointBeforeReturnProbability x) := by
  have hleft := (tendsto_potentialPartial_planarPotentialKernel x).comp
    (tendsto_add_atTop_nat 1)
  change Tendsto (fun N ↦ potentialPartial x (N + 1)) atTop
    (nhds (planarPotentialKernel x)) at hleft
  have hright := (tendsto_renewalSummand_tsum x).const_add 1
  have heq : (fun N ↦ potentialPartial x (N + 1)) =
      fun N ↦ 1 + ∑' k, renewalSummand x N k := by
    funext N
    rw [potentialPartial_renewal hx, tsum_renewalSummand]
  rw [heq] at hleft
  have hlimits := tendsto_nhds_unique hleft hright
  rw [tsum_firstPairDifference hx] at hlimits
  exact hlimits

/-- **Exact point-before-return identity.**  For nonzero `x`, the probability
of reaching `x` before the first strictly positive return to the origin is
the reciprocal of twice the planar potential kernel. -/
theorem pointBeforeReturnProbability_eq {x : Point} (hx : x ≠ 0) :
    pointBeforeReturnProbability x = 1 / (2 * planarPotentialKernel x) := by
  have heq := potentialKernel_probability_equation hx
  have hmul : 2 * planarPotentialKernel x * pointBeforeReturnProbability x = 1 := by
    linarith
  have hne : 2 * planarPotentialKernel x ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmul
    norm_num at hmul
  apply (eq_div_iff hne).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-! ## Explicit logarithmic lower bound (HLOZ (4.5)) -/

/-- A positive cubic radial scale which simultaneously dominates the four
parity-correct diagonal cutoffs adjacent to `x`. -/
def pointBeforeReturnLogScale (x : Point) : ℕ :=
  24 * (2 * manhattanNorm x + 3) ^ 3

lemma pointBeforeReturnLogScale_pos (x : Point) :
    0 < pointBeforeReturnLogScale x := by
  unfold pointBeforeReturnLogScale
  positivity

lemma diagonalOffset_sum_le_two_manhattan (x : Point) :
    firstDiagonalOffset x + secondDiagonalOffset x ≤ 2 * manhattanNorm x := by
  have hplus := Int.natAbs_add_le x.1 x.2
  have hminus := Int.natAbs_sub_le x.1 x.2
  unfold firstDiagonalOffset secondDiagonalOffset manhattanNorm
  have hdivPlus : (x.1 + x.2).natAbs / 2 ≤ (x.1 + x.2).natAbs := Nat.div_le_self _ _
  have hdivMinus : (x.1 - x.2).natAbs / 2 ≤ (x.1 - x.2).natAbs := Nat.div_le_self _ _
  omega

lemma manhattanNorm_sub_direction_le (x : Point) (d : Direction) :
    manhattanNorm (x - directionVector d) ≤ manhattanNorm x + 1 := by
  fin_cases d <;> simp [manhattanNorm, directionVector] <;>
    omega

lemma radialCutoff_le_pointBeforeReturnLogScale_neighbor
    (x : Point) (d : Direction) :
    radialCutoff (firstDiagonalOffset (x - directionVector d))
        (secondDiagonalOffset (x - directionVector d)) ≤
      pointBeforeReturnLogScale x := by
  let y := x - directionVector d
  have hoff := diagonalOffset_sum_le_two_manhattan y
  have hnorm : manhattanNorm y ≤ manhattanNorm x + 1 := by
    simpa [y] using manhattanNorm_sub_direction_le x d
  have hbase : firstDiagonalOffset y + secondDiagonalOffset y + 1 ≤
      2 * manhattanNorm x + 3 := by omega
  unfold radialCutoff pointBeforeReturnLogScale
  exact Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hbase 3)

lemma radialCutoff_le_pointBeforeReturnLogScale (x : Point) :
    radialCutoff (firstDiagonalOffset x) (secondDiagonalOffset x) ≤
      pointBeforeReturnLogScale x := by
  have hoff := diagonalOffset_sum_le_two_manhattan x
  have hbase : firstDiagonalOffset x + secondDiagonalOffset x + 1 ≤
      2 * manhattanNorm x + 3 := by omega
  unfold radialCutoff pointBeforeReturnLogScale
  exact Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hbase 3)

lemma diagonalLogUpper_le_pointBeforeReturnLogBound
    {d e : ℕ} {x : Point} (hcut : radialCutoff d e ≤ pointBeforeReturnLogScale x) :
    diagonalLogUpper d e ≤
      2 + Real.log (pointBeforeReturnLogScale x : ℝ) := by
  unfold diagonalLogUpper
  have hlog : Real.log (radialCutoff d e : ℝ) ≤
      Real.log (pointBeforeReturnLogScale x : ℝ) :=
    Real.log_le_log (by exact_mod_cast radialCutoff_pos d e) (by exact_mod_cast hcut)
  linarith

theorem pointLogUpper_le_explicitLogBound (x : Point) :
    pointLogUpper x ≤ 2 + Real.log (pointBeforeReturnLogScale x : ℝ) := by
  by_cases hx : Even (x.1 + x.2)
  · rw [pointLogUpper, if_pos hx]
    exact diagonalLogUpper_le_pointBeforeReturnLogBound
      (radialCutoff_le_pointBeforeReturnLogScale x)
  · rw [pointLogUpper, if_neg hx]
    have hterm (d : Direction) :
        diagonalLogUpper (firstDiagonalOffset (x - directionVector d))
            (secondDiagonalOffset (x - directionVector d)) ≤
          2 + Real.log (pointBeforeReturnLogScale x : ℝ) :=
      diagonalLogUpper_le_pointBeforeReturnLogBound
        (radialCutoff_le_pointBeforeReturnLogScale_neighbor x d)
    calc
      (1 / 4 : ℝ) * ∑ d : Direction,
          diagonalLogUpper (firstDiagonalOffset (x - directionVector d))
            (secondDiagonalOffset (x - directionVector d)) ≤
        (1 / 4 : ℝ) * ∑ _d : Direction,
          (2 + Real.log (pointBeforeReturnLogScale x : ℝ)) := by
            gcongr with d
            exact hterm d
      _ = 2 + Real.log (pointBeforeReturnLogScale x : ℝ) := by
        simp [Direction]
        ring

lemma planarPotentialKernel_pos_of_ne {x : Point} (hx : x ≠ 0) :
    0 < planarPotentialKernel x := by
  have heq := potentialKernel_probability_equation hx
  have hmul : 2 * planarPotentialKernel x * pointBeforeReturnProbability x = 1 := by
    linarith
  have hp := pointBeforeReturnProbability_nonneg x
  by_contra h
  have ha : planarPotentialKernel x ≤ 0 := le_of_not_gt h
  have hnonpos : 2 * planarPotentialKernel x * pointBeforeReturnProbability x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hp
  linarith

/-- Explicit form of HLOZ (4.5).  The denominator is a universal constant
plus the logarithm of a cubic lattice radius, hence is `O(log |x|)`. -/
theorem pointBeforeReturnProbability_lower_log {x : Point} (hx : x ≠ 0) :
    1 / (4 + 2 * Real.log (pointBeforeReturnLogScale x : ℝ)) ≤
      pointBeforeReturnProbability x := by
  have hpot : planarPotentialKernel x ≤
      2 + Real.log (pointBeforeReturnLogScale x : ℝ) :=
    (pointLogLower_le_planarPotentialKernel_le_pointLogUpper x).2.trans
      (pointLogUpper_le_explicitLogBound x)
  have hpos := planarPotentialKernel_pos_of_ne hx
  rw [pointBeforeReturnProbability_eq hx]
  have hden : 2 * planarPotentialKernel x ≤
      4 + 2 * Real.log (pointBeforeReturnLogScale x : ℝ) := by linarith
  exact one_div_le_one_div_of_le (by positivity : 0 < 2 * planarPotentialKernel x) hden

/-! ## Canonical coordinate-path formulation -/

/-- Coordinate-path version of `H_x < H_0^+`. -/
def walkPointBeforePositiveReturn (x : Point) : Set WalkPath :=
  {s | ∃ n, 0 < n ∧ s n = x ∧
    ∀ j, 0 < j → j < n → s j ≠ 0 ∧ s j ≠ x}

lemma measurableSet_walkPointBeforePositiveReturn (x : Point) :
    MeasurableSet (walkPointBeforePositiveReturn x) := by
  have heq : walkPointBeforePositiveReturn x =
      ⋃ n : ℕ, if 0 < n then
        {s : WalkPath | s n = x} ∩
          ⋂ j : ℕ, ⋂ (_ : 0 < j), ⋂ (_ : j < n),
            ({s : WalkPath | s j = 0}ᶜ ∩ {s : WalkPath | s j = x}ᶜ)
      else ∅ := by
    ext s
    simp [walkPointBeforePositiveReturn]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  split_ifs
  · measurability
  · exact MeasurableSet.empty

lemma trajectory_preimage_walkPointBeforePositiveReturn (x : Point) :
    trajectory ⁻¹' walkPointBeforePositiveReturn x = pointBeforePositiveReturn x := by
  ext w
  simp only [Set.mem_preimage, walkPointBeforePositiveReturn, Set.mem_ofPred_eq,
    pointBeforePositiveReturn, Set.mem_iUnion, firstPairTargetAt]

theorem simpleRandomWalk_walkPointBeforePositiveReturn_toReal (x : Point) :
    (simpleRandomWalk (walkPointBeforePositiveReturn x)).toReal =
      pointBeforeReturnProbability x := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (measurableSet_walkPointBeforePositiveReturn x)]
  rw [trajectory_preimage_walkPointBeforePositiveReturn]
  rfl

theorem simpleRandomWalk_walkPointBeforePositiveReturn_eq {x : Point} (hx : x ≠ 0) :
    (simpleRandomWalk (walkPointBeforePositiveReturn x)).toReal =
      1 / (2 * planarPotentialKernel x) := by
  rw [simpleRandomWalk_walkPointBeforePositiveReturn_toReal,
    pointBeforeReturnProbability_eq hx]

theorem simpleRandomWalk_walkPointBeforePositiveReturn_lower_log
    {x : Point} (hx : x ≠ 0) :
    1 / (4 + 2 * Real.log (pointBeforeReturnLogScale x : ℝ)) ≤
      (simpleRandomWalk (walkPointBeforePositiveReturn x)).toReal := by
  rw [simpleRandomWalk_walkPointBeforePositiveReturn_toReal]
  exact pointBeforeReturnProbability_lower_log hx

end PointBeforeReturn
end Erdos1165
