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
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Set.PowersetCard

/-!
# Return probabilities for planar simple random walk

This file computes the exact probability that the canonical walk from
`Erdos1165.Basic` is at the origin at an even time.  The proof uses the
standard diagonal-coordinate bijection: one planar step is the same as a pair
of independent signs.  Consequently the two diagonal coordinates are two
independent one-dimensional simple random walks.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165
namespace ReturnProbability

/-! ## Diagonal coordinates and balanced Boolean words -/

/-- A sign encoded by a Boolean. -/
def boolSign : Bool → ℤ
  | false => -1
  | true => 1

/-- The four planar directions, in diagonal coordinates, form all pairs of signs. -/
def directionDiagEquiv : Direction ≃ Bool × Bool where
  toFun d := match d with
    | ⟨0, _⟩ => (true, true)
    | ⟨1, _⟩ => (false, false)
    | ⟨2, _⟩ => (true, false)
    | ⟨3, _⟩ => (false, true)
  invFun p := match p with
    | (true, true) => 0
    | (false, false) => 1
    | (true, false) => 2
    | (false, true) => 3
  left_inv d := by fin_cases d <;> rfl
  right_inv p := by rcases p with ⟨b, c⟩; cases b <;> cases c <;> rfl

@[simp] lemma directionVector_diag_fst (d : Direction) :
    (directionVector d).1 + (directionVector d).2 =
      boolSign (directionDiagEquiv d).1 := by
  fin_cases d <;> rfl

@[simp] lemma directionVector_diag_snd (d : Direction) :
    (directionVector d).1 - (directionVector d).2 =
      boolSign (directionDiagEquiv d).2 := by
  fin_cases d <;> rfl

/-- Apply diagonal coordinates pointwise and split the resulting pair of words. -/
def blockDiagEquiv (m : ℕ) :
    (Fin m → Direction) ≃ (Fin m → Bool) × (Fin m → Bool) :=
  (Equiv.piCongrRight fun _ ↦ directionDiagEquiv).trans
    (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ ↦ Bool) (fun _ ↦ Bool))

@[simp] lemma blockDiagEquiv_fst_apply (m : ℕ) (u : Fin m → Direction) (i : Fin m) :
    (blockDiagEquiv m u).1 i = (directionDiagEquiv (u i)).1 := rfl

@[simp] lemma blockDiagEquiv_snd_apply (m : ℕ) (u : Fin m → Direction) (i : Fin m) :
    (blockDiagEquiv m u).2 i = (directionDiagEquiv (u i)).2 := rfl

/-- Number of `true` entries in a finite Boolean word. -/
def boolWeight {m : ℕ} (f : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i ↦ f i = true).card

lemma sum_boolSign_eq (f : Fin m → Bool) :
    ∑ i, boolSign (f i) = 2 * (boolWeight f : ℤ) - m := by
  classical
  have h : ∀ t : Finset (Fin m),
      ∑ i ∈ t, boolSign (f i) =
        2 * ((t.filter fun i ↦ f i = true).card : ℤ) - t.card := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
          Finset.filter_insert, ih]
        cases hfa : f a <;> simp [hfa, ha, boolSign] <;> ring
  simpa [boolWeight] using h Finset.univ

/-- A Boolean word of length `2n` is balanced when its sign sum is zero. -/
def BalancedWord (n : ℕ) :=
  {f : Fin (2 * n) → Bool // ∑ i, boolSign (f i) = 0}

lemma balanced_iff_weight (f : Fin (2 * n) → Bool) :
    (∑ i, boolSign (f i) = 0) ↔ boolWeight f = n := by
  rw [sum_boolSign_eq]
  norm_num
  omega

/-- A Boolean word is equivalent to the set of positions carrying `true`. -/
def boolWordEquivFinset (m : ℕ) : (Fin m → Bool) ≃ Finset (Fin m) where
  toFun f := Finset.univ.filter fun i ↦ f i = true
  invFun s i := decide (i ∈ s)
  left_inv f := by
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases f i <;> simp
  right_inv s := by
    ext i
    simp

@[simp] lemma boolWordEquivFinset_card (m : ℕ) (f : Fin m → Bool) :
    (boolWordEquivFinset m f).card = boolWeight f := rfl

/-- Balanced Boolean words are equivalent to `n`-subsets of their `2n` positions. -/
def balancedWordEquivPowersetCard (n : ℕ) :
    BalancedWord n ≃ Set.powersetCard (Fin (2 * n)) n :=
  Equiv.subtypeEquiv (boolWordEquivFinset (2 * n)) fun f ↦ by
    rw [Set.powersetCard.mem_iff, boolWordEquivFinset_card, balanced_iff_weight]

noncomputable instance (n : ℕ) : Fintype (BalancedWord n) :=
  Fintype.ofEquiv (Set.powersetCard (Fin (2 * n)) n)
    (balancedWordEquivPowersetCard n).symm

theorem card_balancedWord (n : ℕ) :
    Fintype.card (BalancedWord n) = (2 * n).choose n := by
  rw [Fintype.card_congr (balancedWordEquivPowersetCard n)]
  simpa using (Set.powersetCard.card (Fin (2 * n)) n)

/-! ## Returning blocks -/

/-- Displacement of a finite block of steps. -/
def blockDisplacement {m : ℕ} (u : Fin m → Direction) : Point :=
  ∑ i, directionVector (u i)

lemma blockDisplacement_eq_zero_iff_diag (u : Fin m → Direction) :
    blockDisplacement u = (0, 0) ↔
      (∑ i, boolSign ((blockDiagEquiv m u).1 i) = 0) ∧
      (∑ i, boolSign ((blockDiagEquiv m u).2 i) = 0) := by
  have hfst :
      (blockDisplacement u).1 + (blockDisplacement u).2 =
        ∑ i, boolSign ((blockDiagEquiv m u).1 i) := by
    rw [blockDisplacement, Prod.fst_sum, Prod.snd_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp
  have hsnd :
      (blockDisplacement u).1 - (blockDisplacement u).2 =
        ∑ i, boolSign ((blockDiagEquiv m u).2 i) := by
    rw [blockDisplacement, Prod.fst_sum, Prod.snd_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp
  constructor
  · intro h
    rw [h] at hfst hsnd
    simpa using And.intro hfst.symm hsnd.symm
  · rintro ⟨h₁, h₂⟩
    rw [← hfst] at h₁
    rw [← hsnd] at h₂
    apply Prod.ext <;> simp only
    · omega
    · omega

lemma even_length_of_blockDisplacement_eq_zero {m : ℕ} (u : Fin m → Direction)
    (hu : blockDisplacement u = (0, 0)) : Even m := by
  have hsum := (blockDisplacement_eq_zero_iff_diag u).mp hu |>.1
  rw [sum_boolSign_eq] at hsum
  refine ⟨boolWeight (blockDiagEquiv m u).1, ?_⟩
  omega

/-- Returning planar blocks of length `2n` are pairs of balanced Boolean words. -/
def returningBlockEquiv (n : ℕ) :
    {u : Fin (2 * n) → Direction // blockDisplacement u = (0, 0)} ≃
      BalancedWord n × BalancedWord n :=
  (Equiv.subtypeEquiv (blockDiagEquiv (2 * n))
    blockDisplacement_eq_zero_iff_diag).trans Equiv.subtypeProdEquivProd

theorem card_returning_blocks (n : ℕ) :
    Fintype.card {u : Fin (2 * n) → Direction // blockDisplacement u = (0, 0)} =
      ((2 * n).choose n) ^ 2 := by
  rw [Fintype.card_congr (returningBlockEquiv n), Fintype.card_prod,
    card_balancedWord]
  ring

/-! ## Exact probabilities -/

/-- The finite set of step blocks returning to the origin after `2n` steps. -/
def returningBlocks (n : ℕ) : Finset (Fin (2 * n) → Direction) :=
  Finset.univ.filter fun u ↦ blockDisplacement u = (0, 0)

@[simp] lemma mem_returningBlocks {n : ℕ} {u : Fin (2 * n) → Direction} :
    u ∈ returningBlocks n ↔ blockDisplacement u = (0, 0) := by
  simp [returningBlocks]

theorem card_returningBlocks (n : ℕ) :
    (returningBlocks n).card = ((2 * n).choose n) ^ 2 := by
  classical
  rw [← card_returning_blocks n, Fintype.card_subtype]
  rfl

/-- Product law of a finite block of fair increments. -/
noncomputable def initialBlockLaw (m : ℕ) : Measure (Fin m → Direction) :=
  Measure.infinitePi fun _ : Fin m ↦ fairStep

noncomputable instance (m : ℕ) : IsProbabilityMeasure (initialBlockLaw m) := by
  unfold initialBlockLaw
  infer_instance

theorem initialBlockLaw_singleton (m : ℕ) (u : Fin m → Direction) :
    initialBlockLaw m {u} = (1 / 4) ^ m := by
  rw [initialBlockLaw, Measure.infinitePi_singleton_of_fintype]
  simp only [fairStep_singleton, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Exact finite-block return probability. -/
theorem initialBlockLaw_return_probability (n : ℕ) :
    initialBlockLaw (2 * n) (returningBlocks n : Set (Fin (2 * n) → Direction)) =
      (((2 * n).choose n) ^ 2 : ℝ≥0∞) * (1 / 4) ^ (2 * n) := by
  rw [← MeasureTheory.sum_measure_singleton]
  simp only [initialBlockLaw_singleton, Finset.sum_const, nsmul_eq_mul,
    card_returningBlocks]
  norm_cast

/-- The first `m` increments have the finite product law `initialBlockLaw m`. -/
theorem fairSteps_map_initialBlock (m : ℕ) :
    fairSteps.map (fun ω : StepPath ↦ fun i : Fin m ↦ ω i) = initialBlockLaw m := by
  unfold fairSteps initialBlockLaw
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ fairStep) (f := fun i : Fin m ↦ (i : ℕ)) Fin.val_injective

lemma trajectory_eq_blockDisplacement_initialBlock (m : ℕ) (ω : StepPath) :
    trajectory ω m = blockDisplacement (fun i : Fin m ↦ ω i) := by
  exact (Fin.sum_univ_eq_sum_range (fun j ↦ directionVector (ω j)) m).symm

/-- Exact return probability on the IID increment space. -/
theorem fairSteps_return_probability (n : ℕ) :
    fairSteps {ω | trajectory ω (2 * n) = (0, 0)} =
      (((2 * n).choose n) ^ 2 : ℝ≥0∞) * (1 / 4) ^ (2 * n) := by
  let X : StepPath → (Fin (2 * n) → Direction) :=
    fun ω i ↦ ω i
  have hX : Measurable X := measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : ℕ)
  have hset : {ω | trajectory ω (2 * n) = (0, 0)} =
      X ⁻¹' (returningBlocks n : Set (Fin (2 * n) → Direction)) := by
    ext ω
    simp only [mem_ofPred_eq, Finset.mem_coe, mem_returningBlocks, mem_preimage]
    exact Iff.of_eq <| congrArg (fun z ↦ z = (0, 0))
      (trajectory_eq_blockDisplacement_initialBlock (2 * n) ω)
  rw [hset, ← Measure.map_apply hX (by measurability), fairSteps_map_initialBlock,
    initialBlockLaw_return_probability]

/-- Exact return probability for the path-space law used in Problem 1165. -/
theorem simpleRandomWalk_return_probability (n : ℕ) :
    simpleRandomWalk {s | s (2 * n) = (0, 0)} =
      (((2 * n).choose n) ^ 2 : ℝ≥0∞) * (1 / 4) ^ (2 * n) := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (measurableSet_eq_fun (measurable_pi_apply (2 * n)) measurable_const)]
  exact fairSteps_return_probability n

/-- The conventional division form of the even-time return formula. -/
theorem simpleRandomWalk_return_probability_div (n : ℕ) :
    simpleRandomWalk {s | s (2 * n) = (0, 0)} =
      (((2 * n).choose n) ^ 2 : ℝ≥0∞) / 16 ^ n := by
  rw [simpleRandomWalk_return_probability, div_eq_mul_inv]
  congr 1
  rw [pow_mul]
  calc
    ((1 / 4 : ℝ≥0∞) ^ 2) ^ n = (16 : ℝ≥0∞)⁻¹ ^ n := by
      congr 1
      rw [div_eq_mul_inv, one_mul, ← ENNReal.inv_pow]
      norm_num
    _ = (16 ^ n : ℝ≥0∞)⁻¹ := ENNReal.inv_pow.symm

/-- At odd times a nearest-neighbour walk cannot be back at the origin. -/
theorem simpleRandomWalk_odd_return_probability (n : ℕ) :
    simpleRandomWalk {s | s (2 * n + 1) = (0, 0)} = 0 := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (measurableSet_eq_fun (measurable_pi_apply (2 * n + 1)) measurable_const)]
  have hempty : trajectory ⁻¹' {s : WalkPath | s (2 * n + 1) = (0, 0)} = ∅ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro hreturn
    have hblock : blockDisplacement (fun i : Fin (2 * n + 1) ↦ ω i) = (0, 0) := by
      rw [← trajectory_eq_blockDisplacement_initialBlock]
      exact hreturn
    obtain ⟨k, hk⟩ := even_length_of_blockDisplacement_eq_zero _ hblock
    omega
  rw [hempty, measure_empty]

/-! ## A harmonic lower bound -/

/-- A square-form Wallis bound sufficient for recurrence. -/
theorem centralBinom_square_lower_bound :
    ∀ n : ℕ, 0 < n → 16 ^ n ≤ 4 * n * (Nat.centralBinom n) ^ 2
  | 0, hn => (Nat.not_lt_zero _ hn).elim
  | 1, _ => by norm_num [Nat.centralBinom, Nat.choose]
  | n + 2, _ => by
      have ih := centralBinom_square_lower_bound (n + 1) (by omega)
      have hrec := Nat.succ_mul_centralBinom_succ (n + 1)
      have hrec_sq := congrArg (fun z : ℕ ↦ z ^ 2) hrec
      have hquad : 4 * (n + 1) * (n + 2) ≤ (2 * (n + 1) + 1) ^ 2 := by
        nlinarith
      have hmul :
          16 ^ (n + 2) * (n + 2) ≤
            (4 * (n + 2) * Nat.centralBinom (n + 2) ^ 2) * (n + 2) := by
        calc
          16 ^ (n + 2) * (n + 2) =
              16 * 16 ^ (n + 1) * (n + 2) := by ring
          _ ≤ 16 * (4 * (n + 1) * Nat.centralBinom (n + 1) ^ 2) * (n + 2) := by
            gcongr
          _ ≤ 16 * (2 * (n + 1) + 1) ^ 2 * Nat.centralBinom (n + 1) ^ 2 := by
            nlinarith [Nat.centralBinom_pos (n + 1)]
          _ = (4 * (n + 2) * Nat.centralBinom (n + 2) ^ 2) * (n + 2) := by
            nlinarith [hrec_sq]
      exact Nat.le_of_mul_le_mul_right hmul (by omega)

/-- The real-valued formula corresponding to the even-time return probability. -/
noncomputable def evenReturnProbability (n : ℕ) : ℝ :=
  ((Nat.centralBinom n : ℝ) ^ 2) / 16 ^ n

theorem evenReturnProbability_eq (n : ℕ) :
    evenReturnProbability n = ((2 * n).choose n : ℝ) ^ 2 / 16 ^ n := rfl

/-- The real formula is exactly the real part of the path-space probability. -/
theorem simpleRandomWalk_return_probability_toReal (n : ℕ) :
    (simpleRandomWalk {s | s (2 * n) = (0, 0)}).toReal =
      evenReturnProbability n := by
  rw [simpleRandomWalk_return_probability]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_ofNat]
  rw [evenReturnProbability, Nat.centralBinom_eq_two_mul_choose]
  norm_num
  congr 1
  rw [pow_mul, ← inv_pow]
  norm_num

theorem evenReturnProbability_lower_bound {n : ℕ} (hn : 0 < n) :
    1 / (4 * n : ℝ) ≤ evenReturnProbability n := by
  rw [evenReturnProbability]
  have hnat := centralBinom_square_lower_bound n hn
  have h16 : (0 : ℝ) < 16 ^ n := by positivity
  have h4n : (0 : ℝ) < 4 * n := by positivity
  rw [div_le_div_iff₀ h4n h16]
  norm_num
  exact_mod_cast (by simpa [mul_assoc, mul_comm, mul_left_comm] using hnat)

theorem evenReturnProbability_not_summable :
    ¬ Summable evenReturnProbability := by
  intro hs
  have hs_shift : Summable (fun n ↦ evenReturnProbability (n + 1)) :=
    (summable_nat_add_iff 1).2 hs
  have hsmall : Summable (fun n : ℕ ↦ 1 / (4 * (n + 1) : ℝ)) :=
    hs_shift.of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦
      by simpa [Nat.cast_add, Nat.cast_one] using
        evenReturnProbability_lower_bound (n := n + 1) (Nat.zero_lt_succ n)
  have hharm_shift : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) := by
    refine (hsmall.mul_left 4).congr fun n ↦ ?_
    push_cast
    field_simp
  have hharm : Summable (fun n : ℕ ↦ 1 / (n : ℝ)) :=
    (summable_nat_add_iff 1).1 hharm_shift
  exact Real.not_summable_one_div_natCast hharm

/-- The sum of the even-time return probabilities diverges.  This is the
analytic input to the standard renewal proof of recurrence. -/
theorem simpleRandomWalk_even_return_tsum_eq_top :
    ∑' n : ℕ, simpleRandomWalk {s | s (2 * n) = (0, 0)} = ∞ := by
  let q : ℕ → NNReal := fun n ↦
    (simpleRandomWalk {s | s (2 * n) = (0, 0)}).toNNReal
  have hcoe (n : ℕ) :
      (q n : ℝ≥0∞) = simpleRandomWalk {s | s (2 * n) = (0, 0)} := by
    exact ENNReal.coe_toNNReal (measure_ne_top simpleRandomWalk _)
  have hqreal (n : ℕ) : (q n : ℝ) = evenReturnProbability n := by
    change (simpleRandomWalk {s | s (2 * n) = (0, 0)}).toReal = _
    exact simpleRandomWalk_return_probability_toReal n
  calc
    ∑' n : ℕ, simpleRandomWalk {s | s (2 * n) = (0, 0)} =
        ∑' n : ℕ, (q n : ℝ≥0∞) := by
      congr 1
      funext n
      exact (hcoe n).symm
    _ = ∞ := ENNReal.tsum_coe_eq_top_iff_not_summable_coe.mpr <| by
      intro hsum
      exact evenReturnProbability_not_summable (hsum.congr hqreal)

end ReturnProbability
end Erdos1165
