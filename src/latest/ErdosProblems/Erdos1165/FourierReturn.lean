/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Basic

/-!
# Exact return probabilities for planar simple random walk

This file proves, directly from the canonical product measure in `Basic`, the
classical identity

`P(S_{2n} = 0) = binom(2n,n)^2 / 16^n`.

The enumeration uses the usual diagonal change of coordinates: the four
axis-parallel steps correspond bijectively to pairs of signs.  A planar word
returns precisely when both sign words contain equally many positive and
negative signs.  We also prove the elementary lower bound `P(S_{2n}=0) >=
1/(4n)` and hence divergence of the sum of return probabilities.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165

/-! ## The diagonal encoding of a finite block -/

/-- A Boolean sign, with `true` representing `+1`. -/
def boolSign : Bool → ℤ
  | true => 1
  | false => -1

/-- The four directions, encoded by their two diagonal signs. -/
def directionBits : Direction ≃ Bool × Bool where
  toFun
    | ⟨0, _⟩ => (true, true)
    | ⟨1, _⟩ => (false, false)
    | ⟨2, _⟩ => (true, false)
    | ⟨3, _⟩ => (false, true)
  invFun
    | (true, true) => 0
    | (false, false) => 1
    | (true, false) => 2
    | (false, true) => 3
  left_inv d := by fin_cases d <;> rfl
  right_inv p := by rcases p with ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- The additive diagonal change of coordinates `(x,y) ↦ (x+y,x-y)`. -/
def diagonalMap : Point →+ Point where
  toFun p := (p.1 + p.2, p.1 - p.2)
  map_zero' := by ext <;> simp
  map_add' p q := by ext <;> simp <;> ring

lemma diagonalMap_injective : Function.Injective diagonalMap := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  change (x + y, x - y) = (x' + y', x' - y') at h
  simp only [Prod.mk.injEq] at h
  ext <;> omega

@[simp] lemma diagonalMap_directionVector (d : Direction) :
    diagonalMap (directionVector d) =
      (boolSign (directionBits d).1, boolSign (directionBits d).2) := by
  fin_cases d <;> rfl

/-- The displacement of a finite word of increments. -/
def blockDisplacement {N : ℕ} (u : Fin N → Direction) : Point :=
  ∑ i, directionVector (u i)

/-- Splitting every direction into its two diagonal signs is an equivalence of
finite words. -/
def blockBitsEquiv (N : ℕ) :
    (Fin N → Direction) ≃ (Fin N → Bool) × (Fin N → Bool) where
  toFun u := (fun i ↦ (directionBits (u i)).1, fun i ↦ (directionBits (u i)).2)
  invFun p i := directionBits.symm (p.1 i, p.2 i)
  left_inv u := by
    funext i
    exact directionBits.symm_apply_apply (u i)
  right_inv p := by
    rcases p with ⟨a, b⟩
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst (directionBits.apply_symm_apply (a i, b i))
    · exact congrArg Prod.snd (directionBits.apply_symm_apply (a i, b i))

/-- The positions at which a Boolean word has positive sign. -/
def truePositions {N : ℕ} (f : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ f i = true

lemma sum_boolSign_eq (f : Fin N → Bool) :
    ∑ i, boolSign (f i) = 2 * (truePositions f).card - N := by
  classical
  have hpoint (i : Fin N) :
      boolSign (f i) = 2 * (if f i = true then (1 : ℤ) else 0) - 1 := by
    cases h : f i <;> simp [boolSign] at h ⊢
  simp_rw [hpoint]
  calc
    (∑ i : Fin N, ((2 * if f i = true then (1 : ℤ) else 0) - 1)) =
        2 * (∑ i : Fin N, if f i = true then (1 : ℤ) else 0) - N := by
      simp [Finset.sum_sub_distrib]
      rw [← Finset.sum_boole (R := ℤ) (fun i : Fin N ↦ f i = true) Finset.univ,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> norm_num
    _ = 2 * (truePositions f).card - N := by simp [truePositions]

lemma sum_boolSign_eq_zero_iff (f : Fin (2 * n) → Bool) :
    (∑ i, boolSign (f i)) = 0 ↔ (truePositions f).card = n := by
  rw [sum_boolSign_eq]
  constructor
  · intro h
    exact_mod_cast (show ((truePositions f).card : ℤ) = n by omega)
  · intro h
    rw [h]
    norm_num

lemma blockDisplacement_eq_zero_iff (u : Fin (2 * n) → Direction) :
    blockDisplacement u = 0 ↔
      (truePositions (blockBitsEquiv (2 * n) u).1).card = n ∧
        (truePositions (blockBitsEquiv (2 * n) u).2).card = n := by
  have hdiag : diagonalMap (blockDisplacement u) =
      (∑ i, boolSign ((blockBitsEquiv (2 * n) u).1 i),
        ∑ i, boolSign ((blockBitsEquiv (2 * n) u).2 i)) := by
    rw [blockDisplacement, map_sum]
    simp only [diagonalMap_directionVector, blockBitsEquiv]
    apply Prod.ext
    · exact Prod.fst_sum
    · exact Prod.snd_sum
  constructor
  · intro h
    rw [h, map_zero] at hdiag
    have h₁ : (∑ i, boolSign ((blockBitsEquiv (2 * n) u).1 i)) = 0 := by
      simpa using congrArg Prod.fst hdiag.symm
    have h₂ : (∑ i, boolSign ((blockBitsEquiv (2 * n) u).2 i)) = 0 := by
      simpa using congrArg Prod.snd hdiag.symm
    exact ⟨(sum_boolSign_eq_zero_iff _).mp h₁, (sum_boolSign_eq_zero_iff _).mp h₂⟩
  · intro h
    apply diagonalMap_injective
    rw [hdiag, map_zero]
    exact Prod.ext
      (by simpa using (sum_boolSign_eq_zero_iff _).mpr h.1)
      (by simpa using (sum_boolSign_eq_zero_iff _).mpr h.2)

/-! ## Counting balanced words -/

/-- Boolean words of length `2n` with exactly `n` positive signs. -/
def BalancedWords (n : ℕ) :=
  {f : Fin (2 * n) → Bool // (truePositions f).card = n}

noncomputable def boolWordEquivFinset (N : ℕ) :
    (Fin N → Bool) ≃ Finset (Fin N) where
  toFun := truePositions
  invFun s i := decide (i ∈ s)
  left_inv f := by
    funext i
    cases h : f i <;> simp [truePositions, h]
  right_inv s := by
    ext i
    simp [truePositions]

noncomputable def balancedWordsEquivPowerset (n : ℕ) :
    BalancedWords n ≃ {s : Finset (Fin (2 * n)) // s ∈ Finset.univ.powersetCard n} where
  toFun f := ⟨boolWordEquivFinset (2 * n) f.1, by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, f.property⟩⟩
  invFun s := ⟨(boolWordEquivFinset (2 * n)).symm s.1, by
    have hs := (Finset.mem_powersetCard.mp s.property).2
    change (truePositions ((boolWordEquivFinset (2 * n)).symm s.1)).card = n
    rw [show truePositions ((boolWordEquivFinset (2 * n)).symm s.1) = s.1 from
      (boolWordEquivFinset (2 * n)).apply_symm_apply s.1]
    exact hs⟩
  left_inv f := by
    apply Subtype.ext
    exact (boolWordEquivFinset (2 * n)).symm_apply_apply f.1
  right_inv s := by
    apply Subtype.ext
    exact (boolWordEquivFinset (2 * n)).apply_symm_apply s

noncomputable instance (n : ℕ) : Fintype (BalancedWords n) := by
  unfold BalancedWords
  infer_instance

lemma card_balancedWords (n : ℕ) : Fintype.card (BalancedWords n) = Nat.centralBinom n := by
  rw [Fintype.card_congr (balancedWordsEquivPowerset n)]
  simp [Nat.centralBinom]

/-- Returning direction words are pairs of balanced diagonal sign words. -/
noncomputable def returnBlocksEquiv (n : ℕ) :
    {u : Fin (2 * n) → Direction // blockDisplacement u = 0} ≃
      BalancedWords n × BalancedWords n where
  toFun u := by
    have hu := (blockDisplacement_eq_zero_iff (n := n) u.1).mp u.property
    exact ⟨⟨(blockBitsEquiv (2 * n) u.1).1, hu.1⟩,
      ⟨(blockBitsEquiv (2 * n) u.1).2, hu.2⟩⟩
  invFun p := by
    refine ⟨(blockBitsEquiv (2 * n)).symm (p.1.1, p.2.1), ?_⟩
    apply (blockDisplacement_eq_zero_iff (n := n) _).mpr
    simpa using And.intro p.1.2 p.2.2
  left_inv u := by
    apply Subtype.ext
    exact (blockBitsEquiv (2 * n)).symm_apply_apply u
  right_inv p := by
    rcases p with ⟨a, b⟩
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((blockBitsEquiv (2 * n)).apply_symm_apply (a.1, b.1))
    · exact congrArg Prod.snd ((blockBitsEquiv (2 * n)).apply_symm_apply (a.1, b.1))

lemma card_returning_blocks (n : ℕ) :
    Fintype.card {u : Fin (2 * n) → Direction // blockDisplacement u = 0} =
      Nat.centralBinom n ^ 2 := by
  rw [Fintype.card_congr (returnBlocksEquiv n), Fintype.card_prod, card_balancedWords]
  ring

/-! ## The product measure on a finite prefix -/

/-- The first `N` increments. -/
def returnStepPrefix (N : ℕ) (ω : StepPath) : Fin N → Direction := fun i ↦ ω i

/-- The fair product law on a finite block. -/
noncomputable def returnBlockLaw (N : ℕ) : Measure (Fin N → Direction) :=
  Measure.infinitePi fun _ : Fin N ↦ fairStep

noncomputable instance (N : ℕ) : IsProbabilityMeasure (returnBlockLaw N) := by
  unfold returnBlockLaw
  infer_instance

lemma measurable_returnStepPrefix (N : ℕ) : Measurable (returnStepPrefix N) := by
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : ℕ)

lemma fairSteps_map_returnStepPrefix (N : ℕ) :
    fairSteps.map (returnStepPrefix N) = returnBlockLaw N := by
  unfold fairSteps returnBlockLaw returnStepPrefix
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ fairStep) (f := fun i : Fin N ↦ (i : ℕ)) fun i j h ↦ Fin.ext h

lemma returnBlockLaw_eq_uniform (N : ℕ) :
    returnBlockLaw N = ProbabilityTheory.uniformOn (Set.univ : Set (Fin N → Direction)) := by
  rw [returnBlockLaw, Measure.infinitePi_eq_pi]
  symm
  simpa [fairStep] using
    (ProbabilityTheory.uniformOn_pi (f := fun _ : Fin N ↦ (Set.univ : Set Direction)))

lemma trajectory_eq_blockDisplacement_prefix (ω : StepPath) (N : ℕ) :
    trajectory ω N = blockDisplacement (returnStepPrefix N ω) := by
  rw [trajectory, blockDisplacement]
  simp only [returnStepPrefix]
  exact (Fin.sum_univ_eq_sum_range _ N).symm

/-! ## Exact probability and the harmonic lower bound -/

/-- The real-valued exact return probability formula. -/
noncomputable def planarReturnProbability (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) ^ 2 / 16 ^ n

theorem simpleRandomWalk_return_probability (n : ℕ) :
    simpleRandomWalk {s | s (2 * n) = (0, 0)} =
      ENNReal.ofReal (planarReturnProbability n) := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (measurableSet_eq_fun (measurable_pi_apply (2 * n)) measurable_const)]
  change fairSteps {ω | trajectory ω (2 * n) = (0, 0)} = _
  rw [show {ω | trajectory ω (2 * n) = (0, 0)} =
      returnStepPrefix (2 * n) ⁻¹' {u | blockDisplacement u = 0} by
        ext ω
        simp only [mem_ofPred_eq, mem_preimage]
        rw [trajectory_eq_blockDisplacement_prefix]
        change blockDisplacement (returnStepPrefix (2 * n) ω) = 0 ↔
          blockDisplacement (returnStepPrefix (2 * n) ω) = 0
        rfl]
  rw [← Measure.map_apply (measurable_returnStepPrefix (2 * n))
      (measurableSet_eq_fun (measurable_of_countable blockDisplacement) measurable_const),
    fairSteps_map_returnStepPrefix, returnBlockLaw_eq_uniform,
    ProbabilityTheory.uniformOn_univ]
  rw [show ({u | blockDisplacement u = 0} : Set (Fin (2 * n) → Direction)) =
      (Finset.univ.filter fun u ↦ blockDisplacement u = 0 :
        Finset (Fin (2 * n) → Direction)) by ext; simp]
  rw [MeasureTheory.Measure.count_apply_finset]
  rw [show (Finset.univ.filter fun u : Fin (2 * n) → Direction ↦
      blockDisplacement u = 0).card = Nat.centralBinom n ^ 2 by
        let e : ↥(Finset.univ.filter fun u : Fin (2 * n) → Direction ↦
            blockDisplacement u = 0) ≃
            {u : Fin (2 * n) → Direction // blockDisplacement u = 0} :=
          { toFun := fun u ↦ ⟨u.1, (Finset.mem_filter.mp u.2).2⟩
            invFun := fun u ↦ ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩⟩
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
        calc
          (Finset.univ.filter fun u : Fin (2 * n) → Direction ↦
              blockDisplacement u = 0).card =
              Fintype.card ↥(Finset.univ.filter fun u : Fin (2 * n) → Direction ↦
                blockDisplacement u = 0) := (Fintype.card_coe _).symm
          _ = Fintype.card {u : Fin (2 * n) → Direction // blockDisplacement u = 0} :=
            Fintype.card_congr e
          _ = Nat.centralBinom n ^ 2 := card_returning_blocks n]
  simp [planarReturnProbability, pow_mul, ENNReal.ofReal_div_of_pos]

lemma planarReturnProbability_pos (n : ℕ) : 0 < planarReturnProbability n := by
  unfold planarReturnProbability
  apply div_pos
  · exact sq_pos_of_pos (by exact_mod_cast Nat.centralBinom_pos n)
  · positivity

/-- A Wallis-strength lower bound, proved only from the recurrence for central
binomial coefficients. -/
theorem planarReturnProbability_lower_bound {n : ℕ} (hn : 0 < n) :
    1 / (4 * n : ℝ) ≤ planarReturnProbability n := by
  induction n using Nat.case_strong_induction_on with
  | hz => simp at hn
  | hi n ih =>
      by_cases hzero : n = 0
      · subst n
        norm_num [planarReturnProbability, Nat.centralBinom]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
        have hih := ih n (Nat.le_refl n) hnpos
        have hrec := Nat.succ_mul_centralBinom_succ n
        unfold planarReturnProbability at hih ⊢
        rw [pow_succ]
        have hrecR : ((n + 1 : ℕ) : ℝ) * Nat.centralBinom (n + 1) =
            2 * (2 * n + 1) * Nat.centralBinom n := by exact_mod_cast hrec
        have hc : (Nat.centralBinom (n + 1) : ℝ) =
            2 * (2 * n + 1) * Nat.centralBinom n / (n + 1) := by
          apply (eq_div_iff (by positivity : (n + 1 : ℝ) ≠ 0)).2
          norm_num only [Nat.cast_add, Nat.cast_one] at hrecR ⊢
          simpa [mul_comm] using hrecR
        have hprobRec :
            (Nat.centralBinom (n + 1) : ℝ) ^ 2 / 16 ^ (n + 1) =
              ((Nat.centralBinom n : ℝ) ^ 2 / 16 ^ n) *
                ((2 * n + 1 : ℝ) / (2 * (n + 1))) ^ 2 := by
          rw [hc, pow_succ]
          field_simp
          ring
        have hratio :
            1 / (4 * (n + 1 : ℕ) : ℝ) ≤
              (1 / (4 * n : ℝ)) * ((2 * n + 1 : ℝ) / (2 * (n + 1))) ^ 2 := by
          norm_num only [Nat.cast_add, Nat.cast_one]
          field_simp
          nlinarith
        calc
          1 / (4 * (n + 1 : ℕ) : ℝ) ≤
              (1 / (4 * n : ℝ)) * ((2 * n + 1 : ℝ) / (2 * (n + 1))) ^ 2 := hratio
          _ ≤ ((Nat.centralBinom n : ℝ) ^ 2 / 16 ^ n) *
                ((2 * n + 1 : ℝ) / (2 * (n + 1))) ^ 2 := by
              gcongr
          _ = (Nat.centralBinom (n + 1) : ℝ) ^ 2 / 16 ^ (n + 1) := hprobRec.symm

theorem simpleRandomWalk_return_probability_lower_bound {n : ℕ} (hn : 0 < n) :
    ENNReal.ofReal (1 / (4 * n : ℝ)) ≤
      simpleRandomWalk {s | s (2 * n) = (0, 0)} := by
  rw [simpleRandomWalk_return_probability]
  exact ENNReal.ofReal_le_ofReal (planarReturnProbability_lower_bound hn)

/-- The sum of the even-time return probabilities diverges.  This is the
quantitative input to the standard renewal/Markov proof of recurrence. -/
theorem not_summable_simpleRandomWalk_return_probabilities :
    ¬Summable (fun n : ℕ ↦
      (simpleRandomWalk {s | s (2 * (n + 1)) = (0, 0)}).toReal) := by
  intro hsum
  have hlower (n : ℕ) :
      1 / (4 * (n + 1) : ℝ) ≤
        (simpleRandomWalk {s | s (2 * (n + 1)) = (0, 0)}).toReal := by
    rw [simpleRandomWalk_return_probability, ENNReal.toReal_ofReal
      (planarReturnProbability_pos (n + 1)).le]
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
      planarReturnProbability_lower_bound (Nat.succ_pos n)
  have hsummable : Summable (fun n : ℕ ↦ 1 / (4 * (n + 1) : ℝ)) :=
    hsum.of_nonneg_of_le (fun _ ↦ by positivity) hlower
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  exact (hsummable.mul_left 4).congr fun n ↦ by
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp

/-- Consequently the complete sequence of return probabilities (including odd
times) is not summable. -/
theorem not_summable_all_simpleRandomWalk_return_probabilities :
    ¬Summable (fun n : ℕ ↦
      (simpleRandomWalk {s | s n = (0, 0)}).toReal) := by
  intro hsum
  apply not_summable_simpleRandomWalk_return_probabilities
  exact hsum.comp_injective fun a b h ↦ by omega

/-- Equivalently, the expected number of visits to the origin up to time `N`
tends to infinity. -/
theorem tendsto_sum_simpleRandomWalk_return_probabilities :
    Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
        (simpleRandomWalk {s | s n = (0, 0)}).toReal)
      atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg fun _ ↦ ENNReal.toReal_nonneg).mp
  exact not_summable_all_simpleRandomWalk_return_probabilities

end Erdos1165
