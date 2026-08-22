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

import ErdosProblems.Erdos1165.Basic

/-!
# Finite-time counting and hitting estimates for planar simple random walk

This file develops the elementary, finite combinatorial part of the planar
simple-random-walk estimates used in Erdős Problem 1165.  A planar step is
encoded by its two diagonal signs.  This gives a bijection between length-`m`
planar paths and pairs of length-`m` binary words.  At even time `2n`, return
to the origin is therefore equivalent to both binary words being balanced,
and the number of returning paths is exactly `choose (2n) n ^ 2`.

We also record finite prefix-extension and union bounds for visiting or
hitting the origin.  No limiting theorem or asymptotic estimate is used here.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.Hitting

abbrev FiniteStepPath (n : ℕ) := Fin n → Direction

/-! ## Diagonal binary encoding -/

/-- The two diagonal signs of a planar nearest-neighbor step.  The value `0`
means sign `+1`, and `1` means sign `-1`.  Thus east, west, north, and south
are encoded respectively as `(0,0)`, `(1,1)`, `(0,1)`, and `(1,0)`. -/
def diagonalBits : Direction ≃ Fin 2 × Fin 2 where
  toFun d := ![(0, 0), (1, 1), (0, 1), (1, 0)] d
  invFun p := ![0, 2, 3, 1] (finProdFinEquiv p)
  left_inv d := by fin_cases d <;> rfl
  right_inv p := by
    rcases p with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> rfl

@[simp] lemma diagonalBits_zero : diagonalBits 0 = (0, 0) := rfl
@[simp] lemma diagonalBits_one : diagonalBits 1 = (1, 1) := rfl
@[simp] lemma diagonalBits_two : diagonalBits 2 = (0, 1) := rfl
@[simp] lemma diagonalBits_three : diagonalBits 3 = (1, 0) := rfl

/-- Pointwise diagonal encoding of an entire finite path. -/
def pathBitsEquiv (m : ℕ) : FiniteStepPath m ≃ (Fin m → Fin 2) × (Fin m → Fin 2) where
  toFun ω := (fun i ↦ (diagonalBits (ω i)).1, fun i ↦ (diagonalBits (ω i)).2)
  invFun uv := fun i ↦ diagonalBits.symm (uv.1 i, uv.2 i)
  left_inv ω := by ext i; simp
  right_inv uv := by ext i <;> simp

/-- Indices at which a binary word has negative (`-1`) sign. -/
def negativeSupport {m : ℕ} (u : Fin m → Fin 2) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ u i = 1

@[simp] lemma mem_negativeSupport {m : ℕ} (u : Fin m → Fin 2) (i : Fin m) :
    i ∈ negativeSupport u ↔ u i = 1 := by simp [negativeSupport]

/-- Binary words are equivalent to their negative supports. -/
def wordSupportEquiv (m : ℕ) : (Fin m → Fin 2) ≃ Finset (Fin m) where
  toFun := negativeSupport
  invFun S i := if i ∈ S then 1 else 0
  left_inv u := by
    funext i
    by_cases hi : u i = 1
    · simp [negativeSupport, hi]
    · have hz : u i = 0 := by omega
      simp [negativeSupport, hz]
  right_inv S := by ext i; simp [negativeSupport]

/-- A balanced binary word of length `2n` has exactly `n` negative signs. -/
abbrev BalancedWord (n : ℕ) :=
  {u : Fin (2 * n) → Fin 2 // (negativeSupport u).card = n}

/-- Balanced words correspond exactly to the `n`-subsets of `Fin (2n)`. -/
def balancedWordEquiv (n : ℕ) :
    BalancedWord n ≃ {S : Finset (Fin (2 * n)) // S ∈ Finset.univ.powersetCard n} :=
  Equiv.subtypeEquiv (wordSupportEquiv (2 * n)) fun u ↦ by
    change (negativeSupport u).card = n ↔
      negativeSupport u ∈ Finset.univ.powersetCard n
    simp [Finset.mem_powersetCard]

theorem card_balancedWord (n : ℕ) : Fintype.card (BalancedWord n) = (2 * n).choose n := by
  rw [Fintype.card_congr (balancedWordEquiv n), Fintype.card_coe,
    Finset.card_powersetCard]
  simp

/-! ## Return paths -/

/-- A binary diagonal coordinate contributes `+1` at bit `0` and `-1` at bit `1`. -/
def diagonalSign (b : Fin 2) : ℤ := if b = 1 then -1 else 1

/-- The invertible diagonal change of coordinates `(x,y) ↦ (x+y,x-y)`. -/
def diagonalTransform (z : Point) : Point := (z.1 + z.2, z.1 - z.2)

@[simp] lemma diagonalTransform_zero : diagonalTransform (0, 0) = (0, 0) := by
  simp [diagonalTransform]

lemma diagonalTransform_eq_zero_iff (z : Point) :
    diagonalTransform z = (0, 0) ↔ z = (0, 0) := by
  rcases z with ⟨x, y⟩
  simp only [diagonalTransform, Prod.mk.injEq]
  omega

lemma directionVector_diagonal (d : Direction) :
    diagonalTransform (directionVector d) =
      (diagonalSign (diagonalBits d).1, diagonalSign (diagonalBits d).2) := by
  fin_cases d <;> norm_num [diagonalTransform, directionVector, diagonalSign, diagonalBits]

lemma directionVector_diagonal_fst (d : Direction) :
    (directionVector d).1 + (directionVector d).2 = diagonalSign (diagonalBits d).1 := by
  exact congrArg Prod.fst (directionVector_diagonal d)

lemma directionVector_diagonal_snd (d : Direction) :
    (directionVector d).1 - (directionVector d).2 = diagonalSign (diagonalBits d).2 := by
  exact congrArg Prod.snd (directionVector_diagonal d)

/-- Endpoint after all steps of a finite path. -/
def finiteEndpoint {m : ℕ} (ω : FiniteStepPath m) : Point :=
  ∑ i, directionVector (ω i)

lemma finiteEndpoint_diagonal {m : ℕ} (ω : FiniteStepPath m) :
    diagonalTransform (finiteEndpoint ω) =
      (∑ i, diagonalSign (diagonalBits (ω i)).1,
        ∑ i, diagonalSign (diagonalBits (ω i)).2) := by
  apply Prod.ext
  · simp only [finiteEndpoint, diagonalTransform, Prod.fst_sum, Prod.snd_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ directionVector_diagonal_fst (ω i)
  · simp only [finiteEndpoint, diagonalTransform, Prod.fst_sum, Prod.snd_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ directionVector_diagonal_snd (ω i)

/-- The signed sum of a binary word is its length minus twice the number of
negative signs. -/
lemma sum_diagonalSign {m : ℕ} (u : Fin m → Fin 2) :
    ∑ i, diagonalSign (u i) = (m : ℤ) - 2 * ((negativeSupport u).card : ℤ) := by
  have hpoint (b : Fin 2) :
      diagonalSign b = 1 - 2 * (if b = 1 then (1 : ℤ) else 0) := by
    fin_cases b <;> norm_num [diagonalSign]
  have htwo :
      (∑ i : Fin m, if u i = 1 then (2 : ℤ) else 0) =
        2 * ((negativeSupport u).card : ℤ) := by
    rw [show (∑ i : Fin m, if u i = 1 then (2 : ℤ) else 0) =
        ∑ i ∈ Finset.univ.filter (fun i ↦ u i = 1), (2 : ℤ) by
      rw [Finset.sum_filter]]
    simp [negativeSupport, mul_comm]
  have htwo' :
      (∑ i : Fin m, 2 * (if u i = 1 then (1 : ℤ) else 0)) =
        2 * ((negativeSupport u).card : ℤ) := by
    simpa [mul_ite] using htwo
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  rw [htwo']
  simp

lemma sum_diagonalSign_eq_zero_iff {n : ℕ} (u : Fin (2 * n) → Fin 2) :
    (∑ i, diagonalSign (u i)) = 0 ↔ (negativeSupport u).card = n := by
  rw [sum_diagonalSign]
  omega

/-- A length-`2n` planar path returns to the origin exactly when both of its
diagonal binary coordinates are balanced. -/
theorem finiteEndpoint_eq_zero_iff {n : ℕ} (ω : FiniteStepPath (2 * n)) :
    finiteEndpoint ω = (0, 0) ↔
      (negativeSupport (pathBitsEquiv (2 * n) ω).1).card = n ∧
        (negativeSupport (pathBitsEquiv (2 * n) ω).2).card = n := by
  rw [← diagonalTransform_eq_zero_iff (finiteEndpoint ω), finiteEndpoint_diagonal]
  simp only [Prod.mk.injEq, pathBitsEquiv]
  exact and_congr (sum_diagonalSign_eq_zero_iff _) (sum_diagonalSign_eq_zero_iff _)

/-- The finite type of length-`2n` step words returning to the origin. -/
abbrev ReturnPath (n : ℕ) :=
  {ω : FiniteStepPath (2 * n) // finiteEndpoint ω = (0, 0)}

/-- A returning planar path is a pair of balanced diagonal binary words. -/
def returnPathEquiv (n : ℕ) : ReturnPath n ≃ BalancedWord n × BalancedWord n :=
  (Equiv.subtypeEquiv (pathBitsEquiv (2 * n)) fun ω ↦ finiteEndpoint_eq_zero_iff ω).trans
    Equiv.subtypeProdEquivProd

/-- Exact path-count form of the planar return-probability formula. -/
theorem card_returnPath (n : ℕ) :
    Fintype.card (ReturnPath n) = ((2 * n).choose n) ^ 2 := by
  rw [Fintype.card_congr (returnPathEquiv n), Fintype.card_prod, card_balancedWord]
  ring

/-- The returning length-`2n` paths as a concrete finite set. -/
def returnPathSet (n : ℕ) : Finset (FiniteStepPath (2 * n)) :=
  Finset.univ.filter fun ω ↦ finiteEndpoint ω = (0, 0)

@[simp] lemma mem_returnPathSet {n : ℕ} (ω : FiniteStepPath (2 * n)) :
    ω ∈ returnPathSet n ↔ finiteEndpoint ω = (0, 0) := by
  simp [returnPathSet]

theorem card_returnPathSet (n : ℕ) :
    (returnPathSet n).card = ((2 * n).choose n) ^ 2 := by
  rw [← card_returnPath n]
  exact (Fintype.card_subtype fun ω : FiniteStepPath (2 * n) ↦
    finiteEndpoint ω = (0, 0)).symm

/-! ## Exact finite probabilities and elementary bounds -/

/-- Uniform measure on all length-`m` step words. -/
noncomputable def finiteStepMeasure (m : ℕ) : MeasureTheory.Measure (FiniteStepPath m) :=
  (PMF.uniformOfFintype (FiniteStepPath m)).toMeasure

noncomputable instance (m : ℕ) : MeasureTheory.IsProbabilityMeasure (finiteStepMeasure m) := by
  unfold finiteStepMeasure
  infer_instance

/-- The finite-dimensional return probability at time `2n`. -/
noncomputable def returnProbability (n : ℕ) : ℝ≥0∞ :=
  finiteStepMeasure (2 * n) {ω | finiteEndpoint ω = (0, 0)}

/-- Exact probability formula
`P(S_(2n)=0) = choose(2n,n)^2 / 4^(2n)`. -/
theorem returnProbability_eq (n : ℕ) :
    returnProbability n =
      (((2 * n).choose n : ℝ≥0∞) ^ 2) / ((4 : ℝ≥0∞) ^ (2 * n)) := by
  rw [returnProbability, finiteStepMeasure,
    PMF.toMeasure_uniformOfFintype_apply (s := {ω : FiniteStepPath (2 * n) |
      finiteEndpoint ω = (0, 0)}) ((Set.to_countable _).measurableSet)]
  change (Fintype.card (ReturnPath n) : ℝ≥0∞) /
      (Fintype.card (FiniteStepPath (2 * n)) : ℝ≥0∞) = _
  rw [card_returnPath]
  simp

/-- Restriction of an infinite increment sequence to its first `m` steps. -/
def prefixSteps (m : ℕ) (w : StepPath) : FiniteStepPath m := fun i ↦ w i

lemma measurable_prefixSteps (m : ℕ) : Measurable (prefixSteps m) := by
  apply measurable_pi_lambda
  intro i
  change Measurable (fun w : StepPath ↦ w (i : ℕ))
  fun_prop

lemma finiteStepMeasure_singleton (m : ℕ) (u : FiniteStepPath m) :
    finiteStepMeasure m {u} = 1 / ((4 : ℝ≥0∞) ^ m) := by
  rw [finiteStepMeasure,
    PMF.toMeasure_uniformOfFintype_apply (s := ({u} : Set (FiniteStepPath m)))
      (measurableSet_singleton u)]
  simp

lemma fairSteps_prefix_singleton (m : ℕ) (u : FiniteStepPath m) :
    fairSteps ((prefixSteps m) ⁻¹' {u}) = 1 / ((4 : ℝ≥0∞) ^ m) := by
  classical
  let t : ℕ → Set Direction := fun i ↦ if hi : i < m then {u ⟨i, hi⟩} else Set.univ
  have hevent : (prefixSteps m) ⁻¹' {u} = Set.pi (Finset.range m) t := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Finset.mem_coe,
      Finset.mem_range]
    constructor
    · intro hw i hi
      simpa [t, hi, prefixSteps] using congrFun hw ⟨i, hi⟩
    · intro hw
      funext i
      simpa [t, i.isLt, prefixSteps] using hw i i.isLt
  rw [hevent, fairSteps, Measure.infinitePi_pi]
  · calc
      ∏ i ∈ Finset.range m, fairStep (t i) =
          ∏ _i ∈ Finset.range m, (1 / 4 : ℝ≥0∞) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        simp [t, hi, fairStep_singleton]
      _ = 1 / ((4 : ℝ≥0∞) ^ m) := by
        rw [Finset.prod_const, Finset.card_range, one_div, one_div]
        exact ENNReal.inv_pow.symm
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp [t, hi]

/-- The actual IID increment law restricts to the uniform finite-word law. -/
theorem fairSteps_map_prefixSteps (m : ℕ) :
    fairSteps.map (prefixSteps m) = finiteStepMeasure m := by
  apply Measure.ext_of_singleton
  intro u
  rw [Measure.map_apply (measurable_prefixSteps m) (measurableSet_singleton u)]
  exact fairSteps_prefix_singleton m u |>.trans (finiteStepMeasure_singleton m u).symm

/-- Thus the exact counting formula applies to the increment law used by the
main planar random-walk construction. -/
theorem fairSteps_even_return_probability (n : ℕ) :
    fairSteps {w | finiteEndpoint (prefixSteps (2 * n) w) = (0, 0)} =
      (((2 * n).choose n : ℝ≥0∞) ^ 2) / ((4 : ℝ≥0∞) ^ (2 * n)) := by
  have hmeas : MeasurableSet
      {ω : FiniteStepPath (2 * n) | finiteEndpoint ω = (0, 0)} :=
    (Set.to_countable _).measurableSet
  rw [← returnProbability_eq n, returnProbability, ← fairSteps_map_prefixSteps (2 * n),
    Measure.map_apply (measurable_prefixSteps (2 * n)) hmeas]
  rfl

lemma trajectory_eq_finiteEndpoint_prefix (w : StepPath) (m : ℕ) :
    trajectory w m = finiteEndpoint (prefixSteps m w) := by
  unfold trajectory finiteEndpoint prefixSteps
  exact (Fin.sum_univ_eq_sum_range (fun i ↦ directionVector (w i)) m).symm

/-- Exact return probability stated directly for the increment-space
trajectory from the main development. -/
theorem fairSteps_trajectory_even_return_probability (n : ℕ) :
    fairSteps {w | trajectory w (2 * n) = (0, 0)} =
      (((2 * n).choose n : ℝ≥0∞) ^ 2) / ((4 : ℝ≥0∞) ^ (2 * n)) := by
  simpa only [trajectory_eq_finiteEndpoint_prefix] using fairSteps_even_return_probability n

/-- A planar nearest-neighbor walk cannot return to the origin at an odd
time. -/
theorem finiteEndpoint_odd_ne_zero (n : ℕ) (ω : FiniteStepPath (2 * n + 1)) :
    finiteEndpoint ω ≠ (0, 0) := by
  intro hzero
  have hdiag : diagonalTransform (finiteEndpoint ω) = (0, 0) := by simp [hzero]
  rw [finiteEndpoint_diagonal] at hdiag
  have hfst := congrArg Prod.fst hdiag
  change (∑ i, diagonalSign (diagonalBits (ω i)).1) = 0 at hfst
  rw [sum_diagonalSign] at hfst
  omega

theorem fairSteps_trajectory_odd_return_probability (n : ℕ) :
    fairSteps {w | trajectory w (2 * n + 1) = (0, 0)} = 0 := by
  have hempty : {w : StepPath | trajectory w (2 * n + 1) = (0, 0)} = ∅ := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hw
    apply finiteEndpoint_odd_ne_zero n (prefixSteps (2 * n + 1) w)
    rw [← trajectory_eq_finiteEndpoint_prefix]
    exact hw
  simp [hempty]

/-- Exact even-time return probability for the path-space measure
`simpleRandomWalk` used in the main theorem. -/
theorem simpleRandomWalk_even_return_probability (n : ℕ) :
    simpleRandomWalk {s | s (2 * n) = (0, 0)} =
      (((2 * n).choose n : ℝ≥0∞) ^ 2) / ((4 : ℝ≥0∞) ^ (2 * n)) := by
  have hmeas : MeasurableSet {s : WalkPath | s (2 * n) = (0, 0)} :=
    measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory hmeas]
  exact fairSteps_trajectory_even_return_probability n

theorem simpleRandomWalk_odd_return_probability (n : ℕ) :
    simpleRandomWalk {s | s (2 * n + 1) = (0, 0)} = 0 := by
  have hmeas : MeasurableSet {s : WalkPath | s (2 * n + 1) = (0, 0)} :=
    measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory hmeas]
  exact fairSteps_trajectory_odd_return_probability n

/-- Real-valued form of the exact even-time return probability. -/
noncomputable def returnProbabilityReal (n : ℕ) : ℝ :=
  (((2 * n).choose n : ℝ) ^ 2) / ((4 : ℝ) ^ (2 * n))

lemma returnProbabilityReal_nonneg (n : ℕ) : 0 ≤ returnProbabilityReal n := by
  unfold returnProbabilityReal
  exact div_nonneg (sq_nonneg _) (by positivity)

lemma returnProbabilityReal_le_one (n : ℕ) : returnProbabilityReal n ≤ 1 := by
  rw [returnProbabilityReal, div_le_one (by positivity)]
  norm_cast
  have h := Nat.centralBinom_le_four_pow n
  calc
    (2 * n).choose n ^ 2 = n.centralBinom * n.centralBinom := by
      simp [Nat.centralBinom, pow_two]
    _ ≤ 4 ^ n * 4 ^ n := Nat.mul_le_mul h h
    _ = 4 ^ (2 * n) := by rw [← pow_add]; congr 1; omega

/-- A division-free lower estimate for the return numerator.  This is the
classical elementary central-binomial bound available in Mathlib. -/
lemma four_pow_sq_le_return_numerator (n : ℕ) (hn : 0 < n) :
    ((4 : ℕ) ^ n) ^ 2 ≤ (2 * n) ^ 2 * ((2 * n).choose n) ^ 2 := by
  have h := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  simpa only [Nat.centralBinom, pow_two, mul_assoc, mul_left_comm, mul_comm] using
    Nat.mul_le_mul h h

/-- Consequently the elementary finite path count gives the crude bound
`P(S_(2n)=0) ≥ 1/(4n²)`.  A sharper Wallis-product induction follows below. -/
theorem returnProbabilityReal_lower_crude (n : ℕ) (hn : 0 < n) :
    1 / (4 * (n : ℝ) ^ 2) ≤ returnProbabilityReal n := by
  have hnat := four_pow_sq_le_return_numerator n hn
  have hreal : (((4 : ℕ) ^ n : ℕ) : ℝ) ^ 2 ≤
      (((2 * n : ℕ) : ℝ) ^ 2) * (((2 * n).choose n : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hnat
  rw [returnProbabilityReal]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (0 : ℝ) < (4 : ℝ) ^ (2 * n) := by positivity
  have hden : (0 : ℝ) < 4 * (n : ℝ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hpow]
  push_cast at hreal
  rw [← pow_mul] at hreal
  norm_num at hreal ⊢
  ring_nf at hreal ⊢
  exact hreal

/-- Successive even-time return probabilities satisfy the exact Wallis-product
recurrence. -/
lemma returnProbabilityReal_succ (n : ℕ) :
    returnProbabilityReal (n + 1) = returnProbabilityReal n *
      (((2 * n + 1 : ℕ) : ℝ) / (2 * (n + 1 : ℕ) : ℕ)) ^ 2 := by
  have hrecNat := Nat.succ_mul_centralBinom_succ n
  have hrec : ((n + 1 : ℕ) : ℝ) * (((2 * (n + 1)).choose (n + 1) : ℕ) : ℝ) =
      2 * (2 * n + 1 : ℕ) * (((2 * n).choose n : ℕ) : ℝ) := by
    exact_mod_cast hrecNat
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hc : (((2 * (n + 1)).choose (n + 1) : ℕ) : ℝ) =
      (2 * (2 * n + 1 : ℕ) * (((2 * n).choose n : ℕ) : ℝ)) /
        (n + 1 : ℕ) := by
    exact (eq_div_iff hn1).2 (by simpa [mul_comm] using hrec)
  rw [returnProbabilityReal, returnProbabilityReal]
  rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
  rw [show 2 * n + 2 = 2 * (n + 1) by omega, hc]
  norm_num
  field_simp
  ring

/-- The rational factor in the Wallis recurrence preserves the inductive
lower bound `1/(4n)`. -/
lemma wallisStep_lower (n : ℕ) (hn : 0 < n) :
    1 / (4 * ((n + 1 : ℕ) : ℝ)) ≤
      1 / (4 * (n : ℝ)) *
        (((2 * n + 1 : ℕ) : ℝ) / (2 * (n + 1 : ℕ) : ℕ)) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  field_simp
  push_cast
  nlinarith [sq_nonneg (n : ℝ)]

/-- A sharp enough elementary finite-time estimate for recurrence:
`P(S_(2n)=0) ≥ 1/(4n)` for every positive `n`. -/
theorem returnProbabilityReal_lower (n : ℕ) (hn : 0 < n) :
    1 / (4 * (n : ℝ)) ≤ returnProbabilityReal n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [returnProbabilityReal_succ]
      by_cases hn0 : n = 0
      · subst n
        norm_num [returnProbabilityReal, Nat.choose]
      · calc
          1 / (4 * ((n + 1 : ℕ) : ℝ)) ≤
              1 / (4 * (n : ℝ)) *
                (((2 * n + 1 : ℕ) : ℝ) / (2 * (n + 1 : ℕ) : ℕ)) ^ 2 :=
            wallisStep_lower n (Nat.pos_of_ne_zero hn0)
          _ ≤ returnProbabilityReal n *
                (((2 * n + 1 : ℕ) : ℝ) / (2 * (n + 1 : ℕ) : ℕ)) ^ 2 :=
            mul_le_mul_of_nonneg_right (ih (Nat.pos_of_ne_zero hn0)) (sq_nonneg _)

/-- The sum of the even-time return probabilities diverges.  This is the
finite-estimate half of the usual recurrence proof; converting it into almost
sure recurrence additionally uses the Markov/renewal argument. -/
theorem not_summable_returnProbabilityReal : ¬ Summable returnProbabilityReal := by
  intro hsum
  have hshift : Summable (fun n ↦ returnProbabilityReal (n + 1)) :=
    (summable_nat_add_iff 1).2 hsum
  have hminor : Summable (fun n : ℕ ↦ 1 / (4 * ((n + 1 : ℕ) : ℝ))) :=
    hshift.of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦
      returnProbabilityReal_lower (n + 1) (by omega)
  have hharmShift : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) := by
    refine (hminor.mul_left 4).congr fun n ↦ ?_
    have hn : (0 : ℝ) < n + 1 := by positivity
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 hharmShift)

/-! ## First-return (hitting-time) paths -/

/-- Endpoint after the first `k` steps of a length-`m` finite word, where
`k : Fin (m+1)` packages the bound `k ≤ m`. -/
def partialEndpoint {m : ℕ} (ω : FiniteStepPath m) (k : Fin (m + 1)) : Point :=
  ∑ j : Fin k, directionVector
    (ω ⟨j, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ k.isLt)⟩)

@[simp] lemma partialEndpoint_zero {m : ℕ} (ω : FiniteStepPath m) :
    partialEndpoint ω 0 = (0, 0) := by
  rw [partialEndpoint]
  apply Finset.sum_eq_zero
  intro j _
  exact Fin.elim0 j

/-- Returning paths whose endpoint time is their first strictly positive
return to the origin. -/
def firstReturnPathSet (n : ℕ) : Finset (FiniteStepPath (2 * n)) :=
  (returnPathSet n).filter fun ω ↦
    ∀ k : Fin (2 * n + 1), 0 < k → k < 2 * n → partialEndpoint ω k ≠ (0, 0)

@[simp] lemma mem_firstReturnPathSet {n : ℕ} (ω : FiniteStepPath (2 * n)) :
    ω ∈ firstReturnPathSet n ↔
      finiteEndpoint ω = (0, 0) ∧
        ∀ k : Fin (2 * n + 1), 0 < k → k < 2 * n → partialEndpoint ω k ≠ (0, 0) := by
  simp [firstReturnPathSet]

theorem firstReturnPathSet_subset (n : ℕ) : firstReturnPathSet n ⊆ returnPathSet n :=
  Finset.filter_subset _ _

theorem card_firstReturnPathSet_le (n : ℕ) :
    (firstReturnPathSet n).card ≤ ((2 * n).choose n) ^ 2 := by
  rw [← card_returnPathSet]
  exact Finset.card_le_card (firstReturnPathSet_subset n)

/-- Finite uniform probability that the first positive return occurs exactly
at time `2n`. -/
noncomputable def firstReturnProbabilityReal (n : ℕ) : ℝ :=
  ((firstReturnPathSet n).card : ℝ) / ((4 : ℝ) ^ (2 * n))

lemma firstReturnProbabilityReal_nonneg (n : ℕ) :
    0 ≤ firstReturnProbabilityReal n := by
  unfold firstReturnProbabilityReal
  positivity

/-- The elementary hitting estimate `P(T₀=2n) ≤ P(S_(2n)=0)`. -/
theorem firstReturnProbabilityReal_le_returnProbabilityReal (n : ℕ) :
    firstReturnProbabilityReal n ≤ returnProbabilityReal n := by
  rw [firstReturnProbabilityReal, returnProbabilityReal]
  apply (div_le_div_iff_of_pos_right (by positivity)).2
  exact_mod_cast card_firstReturnPathSet_le n

end Erdos1165.Hitting
