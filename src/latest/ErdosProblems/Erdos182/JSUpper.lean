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

import ErdosProblems.Erdos182.Roof
import ErdosProblems.Erdos182.Asymptotics
import ErdosProblems.Erdos182.Probability
import ErdosProblems.Erdos182.JSGlobalParameters
import ErdosProblems.Erdos182.JSKFreeBridge
import ErdosProblems.Erdos182.Iteration
import ErdosProblems.Erdos182.AlmostRegularExtraction
import ErdosProblems.Erdos182.JSCodegreeCleaning
import ErdosProblems.Erdos182.JSCleaningPower
import ErdosProblems.Erdos182.JSPRSCompletion
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Log

/-!
# The global degree-bucket step in the Janzer--Sudakov proof

This file contains the finite, rounding-safe combinatorial core of
Janzer--Sudakov Theorem 5.3.  The graph is represented as a two-sorted
`BipartiteGraph`: vertices in the displayed right part have already been
trimmed to one common degree.  A low-degree class and finitely many higher
degree buckets cover the left neighbours of every active right vertex.

The principal theorem `degreeBucket_dichotomy` proves, without suppressed
division, the dichotomy used in the paper.  Either at least half of the
right vertices have many neighbours in the low class, or one high bucket
has at least `|B| / (2 * numberOfBuckets)` right vertices retaining the
required degree.  The companion theorem
`exists_almostBiregular_of_large_goodRightJS` performs the exact independent
edge trimming and verifies all cross-multiplied density estimates needed by
the iteration lemmas.
-/

namespace Erdos182

open Finset
open scoped BigOperators NNReal

noncomputable section

section BernoulliThirdLowerTail

variable {α : Type*} [Fintype α] [DecidableEq α]

private lemma coe_weightedExpectationJS {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ≥0) (Z : Ω → ℝ≥0) :
    ((weightedExpectation weight Z : ℝ≥0) : ℝ) =
      realWeightedExpectation weight (fun ω ↦ (Z ω : ℝ)) := by
  simp [weightedExpectation, realWeightedExpectation]

private lemma coe_weightedProbabilityJS {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ≥0) (P : Ω → Prop) [DecidablePred P] :
    ((weightedProbability weight P : ℝ≥0) : ℝ) =
      realWeightedExpectation weight (fun ω ↦ if P ω then 1 else 0) := by
  unfold weightedProbability realWeightedExpectation
  rw [NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : P ω <;> simp [hω]

private lemma weightedProbability_mul_le_realWeightedExpectationJS
    {Ω : Type*} [Fintype Ω] (weight : Ω → ℝ≥0) (P : Ω → Prop)
    (Z : Ω → ℝ) (a : ℝ) (hZ : ∀ ω, 0 ≤ Z ω)
    (hPa : ∀ ω, P ω → a ≤ Z ω) :
    (weightedProbability weight P : ℝ) * a ≤
      realWeightedExpectation weight Z := by
  classical
  unfold weightedProbability realWeightedExpectation
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hPω : P ω
  · simp only [hPω, if_true]
    exact mul_le_mul_of_nonneg_left (hPa ω hPω) (NNReal.coe_nonneg _)
  · simp only [hPω, if_false, NNReal.coe_zero, zero_mul]
    exact mul_nonneg (NNReal.coe_nonneg _) (hZ ω)

private lemma bernoulli_inter_card_centered_sq_realJS
    (p : ℝ≥0) (hp : p ≤ 1) (T : Finset α) (hT : T.Nonempty) :
    realWeightedExpectation (bernoulliWeight p)
        (fun S : Finset α ↦
          (((T ∩ S).card : ℝ) - (p : ℝ) * (T.card : ℝ)) ^ 2) =
      (p : ℝ) * (T.card : ℝ) * (1 - (p : ℝ)) := by
  classical
  let Y : Finset α → ℝ := fun S ↦ ((T ∩ S).card : ℝ)
  let mu : ℝ := (p : ℝ) * (T.card : ℝ)
  have hmassNN : ∑ S : Finset α, bernoulliWeight p S = 1 :=
    sum_bernoulliWeight p hp
  have hmass : ∑ S : Finset α, (bernoulliWeight p S : ℝ) = 1 := by
    exact_mod_cast hmassNN
  have hfirstNN := bernoulli_expect_inter_card p hp T
  change weightedExpectation (bernoulliWeight p)
      (fun S : Finset α ↦ ((T ∩ S).card : ℝ≥0)) = _ at hfirstNN
  have hfirst : realWeightedExpectation (bernoulliWeight p) Y = mu := by
    dsimp [mu]
    change realWeightedExpectation (bernoulliWeight p)
      (fun S : Finset α ↦ (((T ∩ S).card : ℝ≥0) : ℝ)) = _
    rw [← coe_weightedExpectationJS]
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
      congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hfirstNN
  have hsecondNN := bernoulli_expect_inter_card_sq p hp T
  change weightedExpectation (bernoulliWeight p)
      (fun S : Finset α ↦ ((T ∩ S).card : ℝ≥0) ^ 2) = _ at hsecondNN
  have hsecond :
      realWeightedExpectation (bernoulliWeight p) (fun S ↦ (Y S) ^ 2) =
        (p : ℝ) * (T.card : ℝ) +
          (p : ℝ) ^ 2 * (T.card : ℝ) *
            ((((T.card : ℝ≥0) - 1 : ℝ≥0)) : ℝ) := by
    change realWeightedExpectation (bernoulliWeight p)
      (fun S : Finset α ↦ ((((T ∩ S).card : ℝ≥0) ^ 2 : ℝ≥0) : ℝ)) = _
    rw [← coe_weightedExpectationJS]
    simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow,
      NNReal.coe_natCast] using congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hsecondNN
  have hexpand :
      realWeightedExpectation (bernoulliWeight p) (fun S ↦ (Y S - mu) ^ 2) =
        realWeightedExpectation (bernoulliWeight p) (fun S ↦ (Y S) ^ 2) -
          2 * mu * realWeightedExpectation (bernoulliWeight p) Y +
          mu ^ 2 * ∑ S : Finset α, (bernoulliWeight p S : ℝ) := by
    unfold realWeightedExpectation
    calc
      ∑ S : Finset α, (bernoulliWeight p S : ℝ) * (Y S - mu) ^ 2 =
          ∑ S : Finset α,
            ((bernoulliWeight p S : ℝ) * (Y S) ^ 2 -
              2 * mu * ((bernoulliWeight p S : ℝ) * Y S) +
              mu ^ 2 * (bernoulliWeight p S : ℝ)) := by
        apply Finset.sum_congr rfl
        intro S _
        ring
      _ = (∑ S : Finset α, (bernoulliWeight p S : ℝ) * (Y S) ^ 2) -
          2 * mu * (∑ S : Finset α, (bernoulliWeight p S : ℝ) * Y S) +
          mu ^ 2 * ∑ S : Finset α, (bernoulliWeight p S : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [← Finset.mul_sum]
  rw [show (fun S : Finset α ↦
      (((T ∩ S).card : ℝ) - (p : ℝ) * (T.card : ℝ)) ^ 2) =
      (fun S ↦ (Y S - mu) ^ 2) by rfl]
  rw [hexpand, hfirst, hsecond, hmass]
  dsimp [mu]
  have hcardNN : (1 : ℝ≥0) ≤ (T.card : ℝ≥0) := by
    exact_mod_cast Finset.one_le_card.mpr hT
  have hcard_cast : ((((T.card : ℝ≥0) - 1 : ℝ≥0)) : ℝ) =
      (T.card : ℝ) - 1 := by
    rw [NNReal.coe_sub hcardNN]
    norm_num
  rw [hcard_cast]
  ring


/-- A one-third Bernoulli sample contains fewer than `D` points of `T` with
probability at most `1/12`, provided `T` has at least 96 points and `D` is at
most one tenth of its size. -/
theorem bernoulli_inter_card_lower_tail_third (T : Finset α) (D : ℕ)
    (hT : 96 ≤ T.card) (hD : 10 * D ≤ T.card) :
    weightedProbability (bernoulliWeight (1 / 3))
        (fun S : Finset α ↦ (T ∩ S).card < D) ≤ 1 / 12 := by
  classical
  let n : ℝ := T.card
  have hn96 : (96 : ℝ) ≤ n := by
    have hc : (96 : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hT
    simpa [n] using hc
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn96
  have hnonempty : T.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hmarkov :
      (weightedProbability (bernoulliWeight (1 / 3))
          (fun S : Finset α ↦ (T ∩ S).card < D) : ℝ) * (n / 6) ^ 2 ≤
        realWeightedExpectation (bernoulliWeight (1 / 3))
          (fun S : Finset α ↦
            (((T ∩ S).card : ℝ) -
              ((1 / 3 : ℝ≥0) : ℝ) * (T.card : ℝ)) ^ 2) := by
    apply weightedProbability_mul_le_realWeightedExpectationJS
    · intro S
      positivity
    · intro S hS
      have hnat : 10 * (T ∩ S).card < T.card := by omega
      have hreal : 10 * ((T ∩ S).card : ℝ) < n := by
        have hc : ((10 * (T ∩ S).card : ℕ) : ℝ) < (T.card : ℝ) := by
          exact_mod_cast hnat
        simpa [n] using hc
      have hsixth : 0 ≤ n / 6 := by positivity
      have hdiff : n / 6 ≤
          ((1 / 3 : ℝ≥0) : ℝ) * (T.card : ℝ) -
            ((T ∩ S).card : ℝ) := by
        norm_num
        dsimp [n] at hreal ⊢
        linarith
      have hsquares := mul_self_le_mul_self hsixth hdiff
      nlinarith
  have hcenter := bernoulli_inter_card_centered_sq_realJS
    (1 / 3) (by
      exact (div_le_one (by norm_num : (0 : ℝ≥0) < 3)).2 (by norm_num))
    T hnonempty
  have hvar :
      realWeightedExpectation (bernoulliWeight (1 / 3))
          (fun S : Finset α ↦
            (((T ∩ S).card : ℝ) -
              ((1 / 3 : ℝ≥0) : ℝ) * (T.card : ℝ)) ^ 2) =
        2 * n / 9 := by
    rw [hcenter]
    norm_num
    dsimp [n]
    ring
  have hnum : 2 * n / 9 ≤ (1 / 12 : ℝ) * (n / 6) ^ 2 := by
    have hprod : 0 ≤ n * (n - 96) :=
      mul_nonneg (le_of_lt hnpos) (sub_nonneg.mpr hn96)
    nlinarith
  have hmul :
      (weightedProbability (bernoulliWeight (1 / 3))
          (fun S : Finset α ↦ (T ∩ S).card < D) : ℝ) * (n / 6) ^ 2 ≤
        (1 / 12 : ℝ) * (n / 6) ^ 2 := by
    exact hmarkov.trans (hvar.le.trans hnum)
  have hsquarepos : 0 < (n / 6) ^ 2 := sq_pos_of_pos (by positivity)
  have hreal :
      (weightedProbability (bernoulliWeight (1 / 3))
          (fun S : Finset α ↦ (T ∩ S).card < D) : ℝ) ≤ (1 / 12 : ℝ) := by
    nlinarith
  exact_mod_cast hreal


/-- If every set in a finite family has the one-third Bernoulli lower-tail
bound and the ambient set is not too large, some subset is no larger than
the number of family members in which it retains at least D points. -/
theorem exists_subset_card_le_good_of_third
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Bgood : Finset β) (T : β → Finset α) (D : ℕ)
    (hsub : ∀ b ∈ Bgood, T b ⊆ X)
    (hlarge : ∀ b ∈ Bgood, 96 ≤ (T b).card)
    (hdegree : ∀ b ∈ Bgood, 10 * D ≤ (T b).card)
    (hBgood : Bgood.Nonempty)
    (hbalance : X.card ≤ 2 * Bgood.card) :
    ∃ S ⊆ X,
      S.card < (Bgood.filter fun b ↦ D ≤ (T b ∩ S).card).card := by
  classical
  let w : Finset α → ℝ≥0 := bernoulliWeight (1 / 3)
  let failures : Finset α → Finset β := fun R ↦
    Bgood.filter fun b ↦ (T b ∩ R).card < D
  have hmassNN : ∑ R : Finset α, w R = 1 := by
    dsimp [w]
    apply sum_bernoulliWeight
    exact (div_le_one (by norm_num : (0 : ℝ≥0) < 3)).2 (by norm_num)
  have hmass : ∑ R : Finset α, (w R : ℝ) = 1 := by
    exact_mod_cast hmassNN
  have hfailExp :
      realWeightedExpectation w (fun R ↦ ((failures R).card : ℝ)) =
        ∑ b ∈ Bgood,
          (weightedProbability w (fun R ↦ (T b ∩ R).card < D) : ℝ) := by
    unfold realWeightedExpectation
    calc
      (∑ R : Finset α, (w R : ℝ) * ((failures R).card : ℝ)) =
          ∑ R : Finset α, (w R : ℝ) *
            (∑ b ∈ Bgood, if (T b ∩ R).card < D then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro R _
        congr 1
        dsimp [failures]
        norm_cast
        rw [Finset.card_filter]
      _ = ∑ b ∈ Bgood, ∑ R : Finset α,
            (w R : ℝ) * if (T b ∩ R).card < D then 1 else 0 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ b ∈ Bgood,
          (weightedProbability w (fun R ↦ (T b ∩ R).card < D) : ℝ) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [coe_weightedProbabilityJS]
        rfl
  have hfailBound :
      realWeightedExpectation w (fun R ↦ ((failures R).card : ℝ)) ≤
        (Bgood.card : ℝ) / 12 := by
    rw [hfailExp]
    calc
      (∑ b ∈ Bgood,
          (weightedProbability w (fun R ↦ (T b ∩ R).card < D) : ℝ)) ≤
          ∑ _b ∈ Bgood, (1 / 12 : ℝ) := by
        apply Finset.sum_le_sum
        intro b hb
        have ht := bernoulli_inter_card_lower_tail_third
          (T b) D (hlarge b hb) (hdegree b hb)
        change weightedProbability w (fun R ↦ (T b ∩ R).card < D) ≤ 1 / 12 at ht
        exact_mod_cast ht
      _ = (Bgood.card : ℝ) / 12 := by simp; ring
  have hsizeNN := bernoulli_expect_inter_card (1 / 3)
    ((div_le_one (by norm_num : (0 : ℝ≥0) < 3)).2 (by norm_num)) X
  change weightedExpectation w
      (fun R : Finset α ↦ ((X ∩ R).card : ℝ≥0)) = _ at hsizeNN
  have hsize :
      realWeightedExpectation w (fun R ↦ ((X ∩ R).card : ℝ)) =
        (X.card : ℝ) / 3 := by
    calc
      _ = ((weightedExpectation w
          (fun R : Finset α ↦ ((X ∩ R).card : ℝ≥0)) : ℝ≥0) : ℝ) :=
        (coe_weightedExpectationJS w _).symm
      _ = (X.card : ℝ) / 3 := by rw [hsizeNN]; norm_num; ring
  let score : Finset α → ℝ := fun R ↦
    (Bgood.card : ℝ) - ((failures R).card : ℝ) - ((X ∩ R).card : ℝ)
  have hscoreExp :
      realWeightedExpectation w score =
        (Bgood.card : ℝ) -
          realWeightedExpectation w (fun R ↦ ((failures R).card : ℝ)) -
          realWeightedExpectation w (fun R ↦ ((X ∩ R).card : ℝ)) := by
    unfold realWeightedExpectation
    calc
      (∑ R : Finset α, (w R : ℝ) * score R) =
          ∑ R : Finset α,
            ((Bgood.card : ℝ) * (w R : ℝ) -
              (w R : ℝ) * ((failures R).card : ℝ) -
              (w R : ℝ) * ((X ∩ R).card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro R _
        dsimp [score]
        ring
      _ = (Bgood.card : ℝ) * ∑ R : Finset α, (w R : ℝ) -
          (∑ R : Finset α, (w R : ℝ) * ((failures R).card : ℝ)) -
          ∑ R : Finset α, (w R : ℝ) * ((X ∩ R).card : ℝ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        simp only [← Finset.mul_sum]
      _ = (Bgood.card : ℝ) -
          (∑ R : Finset α, (w R : ℝ) * ((failures R).card : ℝ)) -
          ∑ R : Finset α, (w R : ℝ) * ((X ∩ R).card : ℝ) := by rw [hmass, mul_one]
  have hbalanceR : (X.card : ℝ) ≤ 2 * (Bgood.card : ℝ) := by
    exact_mod_cast hbalance
  have hBgoodPos : 0 < (Bgood.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hBgood
  have hscorePos : 0 < realWeightedExpectation w score := by
    rw [hscoreExp, hsize]
    linarith
  obtain ⟨R, hR⟩ := exists_realWeightedExpectation_le w hmassNN score
  have hscoreR : 0 < score R := hscorePos.trans_le hR
  let S := X ∩ R
  have hnat : S.card + (failures R).card < Bgood.card := by
    have hreal : (S.card : ℝ) + ((failures R).card : ℝ) < (Bgood.card : ℝ) := by
      dsimp [score, S] at hscoreR
      linarith
    exact_mod_cast hreal
  have hinter (b : β) (hb : b ∈ Bgood) : T b ∩ S = T b ∩ R := by
    ext a
    dsimp [S]
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨haT, _haX, haR⟩
      exact ⟨haT, haR⟩
    · rintro ⟨haT, haR⟩
      exact ⟨haT, hsub b hb haT, haR⟩
  have hsuccess :
      (Bgood.filter fun b ↦ D ≤ (T b ∩ S).card) =
        Bgood.filter fun b ↦ D ≤ (T b ∩ R).card := by
    ext b
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hb, hdeg⟩
      exact ⟨hb, by simpa [hinter b hb] using hdeg⟩
    · rintro ⟨hb, hdeg⟩
      exact ⟨hb, by simpa [hinter b hb] using hdeg⟩
  have hpartition :
      (failures R).card +
          (Bgood.filter fun b ↦ D ≤ (T b ∩ R).card).card = Bgood.card := by
    dsimp [failures]
    simpa only [not_lt] using
      (Finset.card_filter_add_card_filter_not (s := Bgood)
        (fun b ↦ (T b ∩ R).card < D))
  refine ⟨S, Finset.inter_subset_left, ?_⟩
  rw [hsuccess]
  omega


end BernoulliThirdLowerTail

namespace BipartiteGraph

variable {A B I : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Right vertices in `B₀` which retain at least `r` neighbours in `X`.
This local definition keeps the global argument independent of the later
probabilistic ratio-amplification module. -/
def goodRightJS (G : BipartiteGraph A B) (X : Finset A)
    (B₀ : Finset B) (r : ℕ) : Finset B :=
  B₀.filter fun b ↦ r ≤ (G.leftNeighbors b ∩ X).card

@[simp]
theorem mem_goodRightJS (G : BipartiteGraph A B) (X : Finset A)
    (B₀ : Finset B) (r : ℕ) (b : B) :
    b ∈ G.goodRightJS X B₀ r ↔
      b ∈ B₀ ∧ r ≤ (G.leftNeighbors b ∩ X).card := by
  simp [goodRightJS]

/-- Independently trim the star at every good right vertex. -/
theorem exists_halfRegularSubgraphOf_goodRightJS
    (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B) (r : ℕ)
    (hne : (G.goodRightJS X B₀ r).Nonempty) :
    ∃ H : BipartiteGraph A B,
      H.IsHalfRegularSubgraphOf G X (G.goodRightJS X B₀ r) r := by
  classical
  let B₁ := G.goodRightJS X B₀ r
  have hdeg : ∀ b ∈ B₁, r ≤ (G.leftNeighbors b ∩ X).card := by
    intro b hb
    exact (G.mem_goodRightJS X B₀ r b).1 hb |>.2
  let N : B → Finset A := fun b ↦
    if hb : b ∈ B₁ then (Finset.exists_subset_card_eq (hdeg b hb)).choose else ∅
  have hNsub (b : B) (hb : b ∈ B₁) : N b ⊆ G.leftNeighbors b ∩ X := by
    simp only [N, dif_pos hb]
    exact (Finset.exists_subset_card_eq (hdeg b hb)).choose_spec.1
  have hNcard (b : B) (hb : b ∈ B₁) : (N b).card = r := by
    simp only [N, dif_pos hb]
    exact (Finset.exists_subset_card_eq (hdeg b hb)).choose_spec.2
  let H : BipartiteGraph A B := ⟨fun a b ↦ b ∈ B₁ ∧ a ∈ N b⟩
  refine ⟨H, ?_, ?_, hne, ?_⟩
  · intro a b hab
    exact G.mem_leftNeighbors a b |>.1
      (Finset.mem_inter.1 ((hNsub b hab.1) hab.2)).1
  · intro a b hab
    exact ⟨(Finset.mem_inter.1 ((hNsub b hab.1) hab.2)).2, hab.1⟩
  · intro b hb
    have hb' : b ∈ B₁ := by simpa [B₁] using hb
    have hleft : H.leftNeighbors b = N b := by
      ext a
      simp [H, hb']
    rw [rightDegree, hleft, hNcard b hb']

/-- The right vertices in `B₀` which see fewer than `d` vertices of `X`.
This is the literal complement, inside `B₀`, of `goodRightJS`. -/
def lowRight (G : BipartiteGraph A B) (X : Finset A)
    (B₀ : Finset B) (d : ℕ) : Finset B :=
  B₀.filter fun b ↦ (G.leftNeighbors b ∩ X).card < d

@[simp]
theorem mem_lowRight (G : BipartiteGraph A B) (X : Finset A)
    (B₀ : Finset B) (d : ℕ) (b : B) :
    b ∈ G.lowRight X B₀ d ↔
      b ∈ B₀ ∧ (G.leftNeighbors b ∩ X).card < d := by
  simp [lowRight]

theorem goodRightJS_card_add_lowRight_card (G : BipartiteGraph A B)
    (X : Finset A) (B₀ : Finset B) (d : ℕ) :
    (G.goodRightJS X B₀ d).card + (G.lowRight X B₀ d).card = B₀.card := by
  classical
  simpa only [goodRightJS, lowRight, not_le] using
    (Finset.card_filter_add_card_filter_not (s := B₀)
      (fun b ↦ d ≤ (G.leftNeighbors b ∩ X).card))

/-- If the low route contains fewer than half of `B₀`, its literal
complement contains at least half.  This cross-multiplied form is immune to
all floor/ceiling choices. -/
theorem card_le_twice_lowRight_of_not_card_le_twice_goodRightJS
    (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B) (d : ℕ)
    (h : ¬ B₀.card ≤ 2 * (G.goodRightJS X B₀ d).card) :
    B₀.card ≤ 2 * (G.lowRight X B₀ d).card := by
  have hpartition := goodRightJS_card_add_lowRight_card G X B₀ d
  omega

/-- A finite pigeonhole lemma in exactly the form used for the degree
buckets.  Every vertex of `B₁` chooses a bucket in which it is good.
Consequently one bucket contains at least `|B₁| / |J|` such vertices;
the prefactor `c` is carried without division. -/
theorem exists_index_large_goodRightJS [DecidableEq I]
    (G : BipartiteGraph A B) (J : Finset I) (hJ : J.Nonempty)
    (bucket : I → Finset A) (B₀ B₁ : Finset B) (r c : ℕ)
    (hB₁ : B₁ ⊆ B₀) (hcard : B₀.card ≤ c * B₁.card)
    (hgood : ∀ b ∈ B₁, ∃ i ∈ J,
      r ≤ (G.leftNeighbors b ∩ bucket i).card) :
    ∃ i ∈ J,
      B₀.card ≤ c * J.card * (G.goodRightJS (bucket i) B₀ r).card := by
  classical
  obtain ⟨i, hiJ, himax⟩ := Finset.exists_max_image J
    (fun j ↦ (G.goodRightJS (bucket j) B₀ r).card) hJ
  refine ⟨i, hiJ, ?_⟩
  have hsubset : B₁ ⊆ J.biUnion fun j ↦ G.goodRightJS (bucket j) B₀ r := by
    intro b hb
    obtain ⟨j, hjJ, hjgood⟩ := hgood b hb
    simp only [Finset.mem_biUnion]
    exact ⟨j, hjJ, (G.mem_goodRightJS (bucket j) B₀ r b).2
      ⟨hB₁ hb, hjgood⟩⟩
  calc
    B₀.card ≤ c * B₁.card := hcard
    _ ≤ c * (J.biUnion fun j ↦ G.goodRightJS (bucket j) B₀ r).card :=
      Nat.mul_le_mul_left c (Finset.card_le_card hsubset)
    _ ≤ c * ∑ j ∈ J, (G.goodRightJS (bucket j) B₀ r).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ ≤ c * (J.card * (G.goodRightJS (bucket i) B₀ r).card) := by
      apply Nat.mul_le_mul_left
      simpa using Finset.sum_le_card_nsmul J
        (fun j ↦ (G.goodRightJS (bucket j) B₀ r).card)
        ((G.goodRightJS (bucket i) B₀ r).card)
        (fun j hj ↦ himax j hj)
    _ = c * J.card * (G.goodRightJS (bucket i) B₀ r).card := by
      simp [mul_assoc]

/-- If the neighbours of `b` are covered by the low class and the high
buckets, a low-class degree below `dLow` forces degree at least `r` in some
high bucket as soon as `dLow + |J| r` is at most the total degree.

The proof is a literal finite union bound.  In particular it remains valid
when buckets overlap, which makes the result convenient for later changes
of endpoint conventions. -/
theorem exists_good_bucket_of_lowDegree_lt [DecidableEq I]
    (G : BipartiteGraph A B) (J : Finset I) (hJ : J.Nonempty)
    (low : Finset A) (bucket : I → Finset A) (b : B)
    (d dLow r : ℕ)
    (hdegree : G.rightDegree b = d)
    (hcover : G.leftNeighbors b ⊆ low ∪ J.biUnion bucket)
    (hlow : (G.leftNeighbors b ∩ low).card < dLow)
    (hparameters : dLow + J.card * r ≤ d) :
    ∃ i ∈ J, r ≤ (G.leftNeighbors b ∩ bucket i).card := by
  classical
  by_contra hnone
  push_neg at hnone
  let N := G.leftNeighbors b
  have hNsubset : N ⊆ (N ∩ low) ∪
      J.biUnion (fun i ↦ N ∩ bucket i) := by
    intro a haN
    rcases Finset.mem_union.1 (hcover haN) with halow | hahigh
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨haN, halow⟩)
    · simp only [Finset.mem_biUnion] at hahigh
      obtain ⟨i, hiJ, hai⟩ := hahigh
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.2 ⟨i, hiJ, Finset.mem_inter.2 ⟨haN, hai⟩⟩
  have hcardN : N.card ≤ (N ∩ low).card +
      ∑ i ∈ J, (N ∩ bucket i).card := by
    calc
      N.card ≤ ((N ∩ low) ∪
          J.biUnion (fun i ↦ N ∩ bucket i)).card :=
        Finset.card_le_card hNsubset
      _ ≤ (N ∩ low).card +
          (J.biUnion fun i ↦ N ∩ bucket i).card :=
        Finset.card_union_le _ _
      _ ≤ (N ∩ low).card +
          ∑ i ∈ J, (N ∩ bucket i).card := by
        gcongr
        exact Finset.card_biUnion_le
  have hsumPlus :
      (∑ i ∈ J, (N ∩ bucket i).card) + J.card ≤ J.card * r := by
    calc
      (∑ i ∈ J, (N ∩ bucket i).card) + J.card =
          ∑ i ∈ J, ((N ∩ bucket i).card + 1) := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ ∑ _i ∈ J, r := by
        apply Finset.sum_le_sum
        intro i hi
        exact hnone i hi
      _ = J.card * r := by simp
  have hJcard : 0 < J.card := Finset.card_pos.2 hJ
  have hsumlt : (∑ i ∈ J, (N ∩ bucket i).card) < J.card * r := by
    omega
  have hNlt : N.card < dLow + J.card * r := by
    exact lt_of_le_of_lt hcardN (Nat.add_lt_add hlow hsumlt)
  have hNcard : N.card = d := by
    simpa [N, rightDegree] using hdegree
  omega

/-- **The degree-bucket dichotomy (JS Theorem 5.3, finite core).**

`low` and `bucket i` cover every neighbour of every active right vertex.
All such vertices have degree `d`, and `dLow + |J| r ≤ d`.  Then either
the low class works for at least half the right vertices, or one high class
works for at least a `1 / (2|J|)` fraction.  Every denominator from the
paper has been cleared. -/
theorem degreeBucket_dichotomy [DecidableEq I]
    (G : BipartiteGraph A B) (J : Finset I) (hJ : J.Nonempty)
    (low : Finset A) (bucket : I → Finset A) (B₀ : Finset B)
    (d dLow r : ℕ)
    (hregular : ∀ b ∈ B₀, G.rightDegree b = d)
    (hcover : ∀ b ∈ B₀,
      G.leftNeighbors b ⊆ low ∪ J.biUnion bucket)
    (hparameters : dLow + J.card * r ≤ d) :
    B₀.card ≤ 2 * (G.goodRightJS low B₀ dLow).card ∨
      ∃ i ∈ J,
        B₀.card ≤ 2 * J.card * (G.goodRightJS (bucket i) B₀ r).card := by
  classical
  by_cases hlow : B₀.card ≤ 2 * (G.goodRightJS low B₀ dLow).card
  · exact Or.inl hlow
  · right
    let B₁ := G.lowRight low B₀ dLow
    apply exists_index_large_goodRightJS G J hJ bucket B₀ B₁ r 2
    · intro b hb
      exact (G.mem_lowRight low B₀ dLow b).1 hb |>.1
    · exact card_le_twice_lowRight_of_not_card_le_twice_goodRightJS
        G low B₀ dLow hlow
    · intro b hb
      have hb' := (G.mem_lowRight low B₀ dLow b).1 hb
      exact exists_good_bucket_of_lowDegree_lt G J hJ low bucket b d dLow r
        (hregular b hb'.1) (hcover b hb'.1) hb'.2 hparameters

/-- The low-degree class in the exact global parameter schedule. -/
def globalLowClass (G : BipartiteGraph A B) (r Delta : ℕ) : Finset A :=
  Finset.univ.filter fun a ↦
    G.leftDegree a ≤ 2 ^ (JSGlobalParameters.slots r * JSGlobalParameters.ell Delta)

/-- A degree bucket in the exact global parameter schedule. -/
def globalDegreeBucket (G : BipartiteGraph A B) (r Delta : ℕ)
    (z : ℕ × ℕ) : Finset A :=
  Finset.univ.filter fun a ↦
    2 ^ JSGlobalParameters.lowerExponent r Delta z.1 z.2 < G.leftDegree a ∧
      G.leftDegree a ≤ 2 ^ JSGlobalParameters.upperExponent r Delta z.1 z.2

/-- The global, rounding-safe specialization of `degreeBucket_dichotomy`.

The only numerical input is that the trimmed right degree dominates
`coreDegree`.  The exact identity
`lowDegree + |indices| * r = coreDegree` supplies the pigeonhole budget,
while `degree_covered` proves that the displayed classes cover every
left vertex whose degree is at most `Delta`. -/
theorem global_degreeBucket_dichotomy
    (G : BipartiteGraph A B) (r Delta delta : ℕ) (hr : 0 < r)
    (hregular : ∀ b : B, G.rightDegree b = delta)
    (hmax : ∀ a : A, G.leftDegree a ≤ Delta)
    (hcore : JSGlobalParameters.coreDegree r Delta ≤ delta) :
    Fintype.card B ≤
        2 * (G.goodRightJS (G.globalLowClass r Delta) Finset.univ
          (JSGlobalParameters.lowDegree r Delta)).card ∨
      ∃ z ∈ JSGlobalParameters.indices r Delta,
        Fintype.card B ≤ 2 * (JSGlobalParameters.indices r Delta).card *
          (G.goodRightJS (G.globalDegreeBucket r Delta z) Finset.univ r).card := by
  classical
  let J := JSGlobalParameters.indices r Delta
  have hJ : J.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [J, JSGlobalParameters.indices, JSGlobalParameters.ell_pos,
      JSGlobalParameters.slots_pos hr]
  have hcover : ∀ b ∈ (Finset.univ : Finset B),
      G.leftNeighbors b ⊆ G.globalLowClass r Delta ∪
        J.biUnion (G.globalDegreeBucket r Delta) := by
    intro b _ a ha
    by_cases haLow : G.leftDegree a ≤
        2 ^ (JSGlobalParameters.slots r * JSGlobalParameters.ell Delta)
    · apply Finset.mem_union_left
      simp [globalLowClass, haLow]
    · apply Finset.mem_union_right
      obtain ⟨z, hzJ, hzlow, hzhigh⟩ :=
        JSGlobalParameters.degree_covered hr (hmax a) (Nat.lt_of_not_ge haLow)
      apply Finset.mem_biUnion.2
      refine ⟨z, by simpa [J] using hzJ, ?_⟩
      simp [globalDegreeBucket, hzlow, hzhigh]
  have hparameters :
      JSGlobalParameters.lowDegree r Delta + J.card * r ≤ delta := by
    rw [JSGlobalParameters.lowDegree_add_bucket_budget]
    exact hcore
  simpa [J] using
    (degreeBucket_dichotomy G J hJ (G.globalLowClass r Delta)
      (G.globalDegreeBucket r Delta) (Finset.univ : Finset B) delta
      (JSGlobalParameters.lowDegree r Delta) r
      (fun b _ ↦ hregular b) hcover hparameters)

/-- Route-elimination form of `degreeBucket_dichotomy`.  This is the exact
assembly interface for JS Theorem 5.3: the probabilistic low route and the
iterative high route can be proved in separate modules, while this theorem
performs the exhaustive case split. -/
theorem of_degreeBucket_routes [DecidableEq I]
    (G : BipartiteGraph A B) (J : Finset I) (hJ : J.Nonempty)
    (low : Finset A) (bucket : I → Finset A) (B₀ : Finset B)
    (d dLow r : ℕ)
    (hregular : ∀ b ∈ B₀, G.rightDegree b = d)
    (hcover : ∀ b ∈ B₀,
      G.leftNeighbors b ⊆ low ∪ J.biUnion bucket)
    (hparameters : dLow + J.card * r ≤ d)
    (P : Prop)
    (lowRoute : B₀.card ≤ 2 * (G.goodRightJS low B₀ dLow).card → P)
    (highRoute : ∀ i ∈ J,
      B₀.card ≤ 2 * J.card * (G.goodRightJS (bucket i) B₀ r).card → P) :
    P := by
  rcases degreeBucket_dichotomy G J hJ low bucket B₀ d dLow r
      hregular hcover hparameters with hlow | ⟨i, hi, hhigh⟩
  · exact lowRoute hlow
  · exact highRoute i hi hhigh

/-- Left degrees are monotone under passage to a bipartite subgraph. -/
theorem leftDegree_mono_of_le {G H : BipartiteGraph A B} (hHG : H ≤ G)
    (a : A) : H.leftDegree a ≤ G.leftDegree a := by
  classical
  apply Finset.card_le_card
  intro b hb
  exact G.mem_rightNeighbors a b |>.2
    (hHG (H.mem_rightNeighbors a b |>.1 hb))

/-- A half-regular graph with an explicit density lower bound and explicit
left maximum-degree bound satisfies the normalized almost-biregular
predicate used by JS Lemmas 3.5 and 5.2. -/
theorem IsHalfRegularSubgraphOf.isAlmostBiregularOn
    {G H : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B}
    {d L : ℕ} (hH : H.IsHalfRegularSubgraphOf G A₀ B₀ d)
    (hA₀ : A₀.Nonempty) (hdensity : d * A₀.card ≤ H.edgeCount)
    (hleft : ∀ a ∈ A₀,
      H.leftDegree a * A₀.card ≤ L * H.edgeCount) :
    H.IsAlmostBiregularOn A₀ B₀ L d := by
  refine ⟨hH.2.1, hA₀, hH.2.2.1, hH.2.2.2, ?_, ?_⟩
  · exact hdensity
  · exact hleft

/-- The exact trimming-and-density package for a large high-degree bucket.

The hypotheses `hlarge` and `hscale` are the two double-counting estimates
in Case 2 of JS Theorem 5.3.  The conclusion is an actual subgraph, regular
of degree `r` on its active right side, satisfying the normalized
`(L,D)`-almost-biregularity inequalities. -/
theorem exists_almostBiregular_of_large_goodRightJS
    (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B)
    (r c L : ℕ) (hc : 0 < c) (hX : X.Nonempty) (hB₀ : B₀.Nonempty)
    (hlarge : B₀.card ≤ c * (G.goodRightJS X B₀ r).card)
    (hscale : c * (r * X.card) ≤ B₀.card * r)
    (hleft : ∀ a ∈ X,
      c * (G.leftDegree a * X.card) ≤ L * (B₀.card * r)) :
    ∃ H : BipartiteGraph A B,
      H.IsHalfRegularSubgraphOf G X (G.goodRightJS X B₀ r) r ∧
      H.IsAlmostBiregularOn X (G.goodRightJS X B₀ r) L r := by
  classical
  have hgoodne : (G.goodRightJS X B₀ r).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hBzero : B₀.card = 0 := by simpa [hempty] using hlarge
    exact (Finset.card_pos.2 hB₀).ne' hBzero
  obtain ⟨H, hH⟩ := G.exists_halfRegularSubgraphOf_goodRightJS X B₀ r hgoodne
  have hedge : H.edgeCount = (G.goodRightJS X B₀ r).card * r :=
    edgeCount_eq_card_mul_of_rightRegularOn hH.2.1 hH.2.2.2
  refine ⟨H, hH, hH.isAlmostBiregularOn hX ?_ ?_⟩
  · have hscaled : c * (r * X.card) ≤ c * H.edgeCount := by
      calc
        c * (r * X.card) ≤ B₀.card * r := hscale
        _ ≤ (c * (G.goodRightJS X B₀ r).card) * r := by
          gcongr
        _ = c * H.edgeCount := by rw [hedge]; simp [mul_assoc]
    exact Nat.le_of_mul_le_mul_left hscaled hc
  · intro a ha
    have hscaled : c * (H.leftDegree a * X.card) ≤
        c * (L * H.edgeCount) := by
      calc
        c * (H.leftDegree a * X.card) ≤
            c * (G.leftDegree a * X.card) := by
          gcongr
          exact leftDegree_mono_of_le hH.1 a
        _ ≤ L * (B₀.card * r) := hleft a ha
        _ ≤ L * ((c * (G.goodRightJS X B₀ r).card) * r) := by
          gcongr
        _ = c * (L * H.edgeCount) := by rw [hedge]; simp [mul_assoc, mul_comm, mul_left_comm]
    exact Nat.le_of_mul_le_mul_left hscaled hc

/-- The one-third sampling/alteration step in the low-degree branch of
Janzer--Sudakov Theorem 5.3.  A positive-score Bernoulli outcome leaves a
left set strictly smaller than the surviving right set.  Independent star
trimming then gives an exactly `D`-regular right part and all the integral
cross-multiplied estimates in `IsAlmostBiregularOn`. -/
theorem exists_lowRoute_almostBiregular
    (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B)
    (dLow D L : ℕ)
    (hB₀ : B₀.Nonempty)
    (hXB : X.card ≤ B₀.card)
    (hlarge : B₀.card ≤ 2 * (G.goodRightJS X B₀ dLow).card)
    (hdLow : 120 ≤ dLow) (hDscale : 10 * D ≤ dLow) (hD : 0 < D)
    (hleft : ∀ a ∈ X, G.leftDegree a ≤ L) :
    ∃ A₁ : Finset A, ∃ B₁ : Finset B, ∃ H : BipartiteGraph A B,
      A₁ ⊆ X ∧ B₁ ⊆ G.goodRightJS X B₀ dLow ∧
        H.IsHalfRegularSubgraphOf G A₁ B₁ D ∧
        H.IsAlmostBiregularOn A₁ B₁ L D := by
  classical
  let Bstar := G.goodRightJS X B₀ dLow
  have hBstar : Bstar.Nonempty := by
    apply Finset.card_pos.mp
    change B₀.card ≤ 2 * Bstar.card at hlarge
    have hB₀pos : 0 < B₀.card := hB₀.card_pos
    omega
  have hbalance : X.card ≤ 2 * Bstar.card := hXB.trans hlarge
  obtain ⟨A₁, hA₁X, hratioRaw⟩ := exists_subset_card_le_good_of_third
    X Bstar (fun b ↦ G.leftNeighbors b ∩ X) D
    (fun _b _hb ↦ Finset.inter_subset_right)
    (fun b hb ↦ by
      have hb' : b ∈ G.goodRightJS X B₀ dLow := by simpa [Bstar] using hb
      have hdeg := (G.mem_goodRightJS X B₀ dLow b).1 hb' |>.2
      omega)
    (fun b hb ↦ by
      have hb' : b ∈ G.goodRightJS X B₀ dLow := by simpa [Bstar] using hb
      have hdeg := (G.mem_goodRightJS X B₀ dLow b).1 hb' |>.2
      omega)
    hBstar hbalance
  let B₁ := G.goodRightJS A₁ Bstar D
  have hinter (b : B) : (G.leftNeighbors b ∩ X) ∩ A₁ =
      G.leftNeighbors b ∩ A₁ := by
    rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hA₁X]
  have hratio : A₁.card < B₁.card := by
    change A₁.card < (Bstar.filter fun b ↦
      D ≤ (G.leftNeighbors b ∩ A₁).card).card
    simpa only [hinter] using hratioRaw
  have hB₁ : B₁.Nonempty :=
    Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hratio)
  have hA₁ : A₁.Nonempty := by
    obtain ⟨b, hb⟩ := hB₁
    have hdeg : D ≤ (G.leftNeighbors b ∩ A₁).card :=
      (G.mem_goodRightJS A₁ Bstar D b).1 (by simpa [B₁] using hb) |>.2
    have hpos : 0 < (G.leftNeighbors b ∩ A₁).card := hD.trans_le hdeg
    exact (Finset.card_pos.mp hpos).mono Finset.inter_subset_right
  obtain ⟨H, hH⟩ := G.exists_halfRegularSubgraphOf_goodRightJS A₁ Bstar D (by
    simpa [B₁] using hB₁)
  have hedge : H.edgeCount = B₁.card * D := by
    simpa [B₁] using
      (edgeCount_eq_card_mul_of_rightRegularOn hH.2.1 hH.2.2.2)
  have hdensity : D * A₁.card ≤ H.edgeCount := by
    rw [hedge]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right D hratio.le
  have hleftH : ∀ a ∈ A₁,
      H.leftDegree a * A₁.card ≤ L * H.edgeCount := by
    intro a ha
    have haX : a ∈ X := hA₁X ha
    have hdegHL : H.leftDegree a ≤ L :=
      (G.leftDegree_mono_of_le hH.1 a).trans (hleft a haX)
    rw [hedge]
    calc
      H.leftDegree a * A₁.card ≤ L * A₁.card :=
        Nat.mul_le_mul_right A₁.card hdegHL
      _ ≤ L * B₁.card := Nat.mul_le_mul_left L hratio.le
      _ = (L * B₁.card) * 1 := by simp
      _ ≤ (L * B₁.card) * D := Nat.mul_le_mul_left (L * B₁.card) hD
      _ = L * (B₁.card * D) := by simp [Nat.mul_assoc]
  refine ⟨A₁, B₁, H, hA₁X, ?_, hH, ?_⟩
  · intro b hb
    exact (G.mem_goodRightJS A₁ Bstar D b).1 (by simpa [B₁] using hb) |>.1
  · exact hH.isAlmostBiregularOn hA₁ hdensity hleftH

/-- The low branch specialized to the exact global bucket schedule.  All
sampling cutoffs and rounding inequalities are discharged here. -/
theorem exists_globalLowRoute_almostBiregular
    (G : BipartiteGraph A B) (r Delta : ℕ) (hr : 4 ≤ r)
    (hcard : Fintype.card A ≤ Fintype.card B)
    (hB : Nonempty B)
    (hlarge : Fintype.card B ≤
      2 * (G.goodRightJS (G.globalLowClass r Delta) Finset.univ
        (JSGlobalParameters.lowDegree r Delta)).card) :
    ∃ A₁ : Finset A, ∃ B₁ : Finset B, ∃ H : BipartiteGraph A B,
      A₁ ⊆ G.globalLowClass r Delta ∧
        B₁ ⊆ G.goodRightJS (G.globalLowClass r Delta) Finset.univ
          (JSGlobalParameters.lowDegree r Delta) ∧
        H.IsHalfRegularSubgraphOf G A₁ B₁
          (r ^ 2 * JSGlobalParameters.ell Delta) ∧
        H.IsAlmostBiregularOn A₁ B₁
          (2 ^ (JSGlobalParameters.slots r * JSGlobalParameters.ell Delta))
          (r ^ 2 * JSGlobalParameters.ell Delta) := by
  classical
  let : Nonempty B := hB
  let X := G.globalLowClass r Delta
  have hBne : (Finset.univ : Finset B).Nonempty := Finset.univ_nonempty
  have hXB : X.card ≤ (Finset.univ : Finset B).card := by
    calc
      X.card ≤ Fintype.card A := Finset.card_le_univ X
      _ ≤ Fintype.card B := hcard
      _ = (Finset.univ : Finset B).card := by simp
  have hdLow : 120 ≤ JSGlobalParameters.lowDegree r Delta := by
    have hell := JSGlobalParameters.ell_pos Delta
    simp only [JSGlobalParameters.lowDegree]
    nlinarith
  have hscale :
      10 * (r ^ 2 * JSGlobalParameters.ell Delta) ≤
        JSGlobalParameters.lowDegree r Delta := by
    simp [JSGlobalParameters.lowDegree, Nat.mul_assoc]
  have hD : 0 < r ^ 2 * JSGlobalParameters.ell Delta := by
    exact Nat.mul_pos (pow_pos (by omega) _) (JSGlobalParameters.ell_pos Delta)
  have hleft : ∀ a ∈ X,
      G.leftDegree a ≤
        2 ^ (JSGlobalParameters.slots r * JSGlobalParameters.ell Delta) := by
    intro a ha
    simpa [X, globalLowClass] using (Finset.mem_filter.1 ha).2
  simpa [X] using
    (G.exists_lowRoute_almostBiregular X (Finset.univ : Finset B)
      (JSGlobalParameters.lowDegree r Delta)
      (r ^ 2 * JSGlobalParameters.ell Delta)
      (2 ^ (JSGlobalParameters.slots r * JSGlobalParameters.ell Delta))
      hBne hXB hlarge hdLow hscale hD hleft)

/-- The complete low branch, composed with JS Lemma 3.5.  Besides the
`64`-almost-regular conclusion, the last conjunct records the exact
cross-multiplied average-degree loss used by the global edge count. -/
theorem exists_lowRoute_almostRegular
    (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B)
    (dLow D L : ℕ)
    (hB₀ : B₀.Nonempty)
    (hXB : X.card ≤ B₀.card)
    (hlarge : B₀.card ≤ 2 * (G.goodRightJS X B₀ dLow).card)
    (hdLow : 120 ≤ dLow) (hDscale : 10 * D ≤ dLow)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (hDL : D ≤ L)
    (hleft : ∀ a ∈ X, G.leftDegree a ≤ L) :
    ∃ H : BipartiteGraph A B,
      H ≤ G ∧ H.IsAlmostRegular 64 ∧
        D * H.supportCard ≤ 32 * (Nat.log2 L + 1) * H.edgeCount := by
  obtain ⟨A₁, B₁, F, _hA₁, _hB₁, hFG, hF⟩ :=
    G.exists_lowRoute_almostBiregular X B₀ dLow D L
      hB₀ hXB hlarge hdLow hDscale hD hleft
  obtain ⟨H, hHF, hHregular, hHaverage⟩ :=
    exists_almostRegular_subgraph hF hDtwo hDL
  exact ⟨H, hHF.trans hFG.1, hHregular, hHaverage⟩

/-- The completed global low branch.  The logarithm of its almost-
biregularity parameter is exactly `10 * r * ell`; after cancelling the
positive factor `r * ell`, JS Lemma 3.5 loses only the absolute constant
`352`. -/
theorem exists_globalLowRoute_almostRegular
    (G : BipartiteGraph A B) (r Delta : ℕ) (hr : 4 ≤ r)
    (hcard : Fintype.card A ≤ Fintype.card B)
    (hB : Nonempty B)
    (hlarge : Fintype.card B ≤
      2 * (G.goodRightJS (G.globalLowClass r Delta) Finset.univ
        (JSGlobalParameters.lowDegree r Delta)).card) :
    ∃ H : BipartiteGraph A B,
      H ≤ G ∧ H.IsAlmostRegular 64 ∧
        r * H.supportCard ≤ 352 * H.edgeCount := by
  classical
  let ell := JSGlobalParameters.ell Delta
  let D := r ^ 2 * ell
  let L := 2 ^ (JSGlobalParameters.slots r * ell)
  have hell : 0 < ell := JSGlobalParameters.ell_pos Delta
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hDtwo : 2 ≤ D := by
    dsimp [D]
    nlinarith
  have hrSq : r ^ 2 ≤ 2 ^ (2 * r) := by
    nlinarith [Nat.two_mul_sq_add_one_le_two_pow_two_mul r]
  have hellPow : ell ≤ 2 ^ (2 * ell) := by
    nlinarith [Nat.two_mul_sq_add_one_le_two_pow_two_mul ell]
  have hexponents : 2 * r + 2 * ell ≤ JSGlobalParameters.slots r * ell := by
    simp only [JSGlobalParameters.slots]
    nlinarith
  have hDL : D ≤ L := by
    dsimp [D, L]
    calc
      r ^ 2 * ell ≤ 2 ^ (2 * r) * 2 ^ (2 * ell) :=
        Nat.mul_le_mul hrSq hellPow
      _ = 2 ^ (2 * r + 2 * ell) := by rw [pow_add]
      _ ≤ 2 ^ (JSGlobalParameters.slots r * ell) :=
        Nat.pow_le_pow_right (by omega) hexponents
  have hBne : (Finset.univ : Finset B).Nonempty := by
    let : Nonempty B := hB
    exact Finset.univ_nonempty
  have hXB : (G.globalLowClass r Delta).card ≤
      (Finset.univ : Finset B).card := by
    calc
      (G.globalLowClass r Delta).card ≤ Fintype.card A := Finset.card_le_univ _
      _ ≤ Fintype.card B := hcard
      _ = (Finset.univ : Finset B).card := by simp
  have hdLow : 120 ≤ JSGlobalParameters.lowDegree r Delta := by
    simp only [JSGlobalParameters.lowDegree]
    nlinarith
  have hDscale : 10 * D ≤ JSGlobalParameters.lowDegree r Delta := by
    simp [D, ell, JSGlobalParameters.lowDegree, Nat.mul_assoc]
  have hleft : ∀ a ∈ G.globalLowClass r Delta, G.leftDegree a ≤ L := by
    intro a ha
    simpa [globalLowClass, L, ell] using (Finset.mem_filter.1 ha).2
  obtain ⟨H, hHG, hHregular, hHavg⟩ :=
    G.exists_lowRoute_almostRegular (G.globalLowClass r Delta)
      (Finset.univ : Finset B) (JSGlobalParameters.lowDegree r Delta) D L
      hBne hXB hlarge hdLow hDscale hD hDtwo hDL hleft
  have hHavg' :
      D * H.supportCard ≤
        32 * (JSGlobalParameters.slots r * ell + 1) * H.edgeCount := by
    simpa [L, Nat.log2_eq_log_two, Nat.log_pow (by omega : 1 < 2)] using hHavg
  have hcoefficient :
      32 * (JSGlobalParameters.slots r * ell + 1) ≤ 352 * (r * ell) := by
    simp only [JSGlobalParameters.slots]
    nlinarith
  have hscaled :
      (r * ell) * (r * H.supportCard) ≤
        (r * ell) * (352 * H.edgeCount) := by
    calc
      (r * ell) * (r * H.supportCard) = D * H.supportCard := by
        simp [D, pow_two]
        ring
      _ ≤ 32 * (JSGlobalParameters.slots r * ell + 1) * H.edgeCount := hHavg'
      _ ≤ (352 * (r * ell)) * H.edgeCount := by gcongr
      _ = (r * ell) * (352 * H.edgeCount) := by ring
  exact ⟨H, hHG, hHregular,
    Nat.le_of_mul_le_mul_left hscaled (Nat.mul_pos (by omega) hell)⟩

section HighBucketRoute

open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

/-- Exact arithmetic data needed to invoke the active key-restriction step
at every nonterminal dyadic state.  Keeping this as a named predicate makes
the rounding obligations of JS Lemma 4.2 visible at the high-bucket call
site. -/
def HasExactActiveIterationData (G : BipartiteGraph A B) (r cutoff : ℕ) : Prop :=
  ∀ (K : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
    (y : DyadicState), K ≤ G → IsDyadicallyBiregularOn K A₁ B₁ r y →
      cutoff < y.gap →
      0 < y.s ∧ y.s < y.t ∧
      (∀ u ∈ A₁, ∀ w ∈ A₁, u ≠ w →
        bipCodegree K.Adj u w ≤
          2 ^ (r * y.s - (r - 1) * y.t)) ∧
      10 * y.gap * r ≤ 2 ^ (r * y.s - (r - 1) * y.t) ∧
      Nat.clog 2 (40 * y.gap * r ^ 2) + 1 < y.gap ∧
      y.invariant r + (Nat.clog 2 (10 * y.gap * r) : ℤ) +
          (2 * (r : ℤ) - 1) *
            (Nat.clog 2 (40 * y.gap * r ^ 2) + 1 : ℕ) ≤
        (r * y.s - (r - 1) * y.t : ℕ)

/-- The exact active restriction hypotheses produce the graph-valued step
expected by `js_lemma_5_1_to_almostBiregular`. -/
theorem activeIterationStep_of_exactData
    (G : BipartiteGraph A B) (r cutoff : ℕ) (hr : 1 ≤ r)
    (hdata : G.HasExactActiveIterationData r cutoff) :
    ∀ (K : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState), K ≤ G → IsDyadicallyBiregularOn K A₁ B₁ r y →
      cutoff < y.gap →
      ∃ (L : BipartiteGraph A B) (A₂ : Finset A) (B₂ : Finset B)
        (z : DyadicState),
        L ≤ K ∧ IsDyadicallyBiregularOn L A₂ B₂ r z ∧
          IsDyadicImprovement r y z := by
  intro K A₁ B₁ y hKG hy hgap
  obtain ⟨hys, hyst, hcodeg, hQD, hgapSlack, hinvariantSlack⟩ :=
    hdata K A₁ B₁ y hKG hy hgap
  obtain ⟨L, A₂, B₂, z, _hA₂, _hB₂, hLK, hz, himprove⟩ :=
    exists_dyadicImprovement_active K A₁ B₁ r y hr hys hyst hy
      hcodeg hQD hgapSlack hinvariantSlack
  exact ⟨L, A₂, B₂, z, hLK, hz, himprove⟩

/-- The purely numerical obligations in the uniform-codegree form of the
iteration.  The current state is known to have invariant at least that of
the initial state, so a single exponent bound `E` suffices throughout. -/
def HasExactIterationArithmetic (x : DyadicState)
    (r cutoff E : ℕ) : Prop :=
  ∀ y : DyadicState, x.invariant r ≤ y.invariant r → y.s ≤ y.t →
    cutoff < y.gap →
      (E : ℤ) ≤ (r * y.s - (r - 1) * y.t : ℕ) ∧
      10 * y.gap * r ≤ 2 ^ (r * y.s - (r - 1) * y.t) ∧
      Nat.clog 2 (40 * y.gap * r ^ 2) + 1 < y.gap ∧
      y.invariant r + (Nat.clog 2 (10 * y.gap * r) : ℤ) +
          (2 * (r : ℤ) - 1) *
            (Nat.clog 2 (40 * y.gap * r ^ 2) + 1 : ℕ) ≤
        (r * y.s - (r - 1) * y.t : ℕ)

private theorem eight_mul_add_seven_le_pow_two_JS {m : ℕ} (hm : 8 ≤ m) :
    8 * m + 7 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm hpow =>
      rw [pow_succ]
      omega

/-- Above 64, the binary ceiling logarithm is at most one eighth of its
argument.  This explicit integer estimate supplies the slack in the active
restriction iteration. -/
theorem clog_two_le_div_eight_JS {n : ℕ} (hn : 64 ≤ n) :
    Nat.clog 2 n ≤ n / 8 := by
  apply Nat.clog_le_of_le_pow
  have hm : 8 ≤ n / 8 := by omega
  calc
    n = 8 * (n / 8) + n % 8 := by omega
    _ ≤ 8 * (n / 8) + 7 := by omega
    _ ≤ 2 ^ (n / 8) := eight_mul_add_seven_le_pow_two_JS hm

/-- Subadditivity of the binary ceiling logarithm, in the exact natural
number form used by the JS iteration. -/
theorem clog_mul_le_add_JS (a b : ℕ) :
    Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  apply Nat.clog_le_of_le_pow
  calc
    a * b ≤ 2 ^ Nat.clog 2 a * 2 ^ Nat.clog 2 b := by
      gcongr <;> exact Nat.le_pow_clog (by omega) _
    _ = 2 ^ (Nat.clog 2 a + Nat.clog 2 b) := (pow_add _ _ _).symm

private theorem clog_40_mul_mul_sq_le_JS (g r : ℕ) :
    Nat.clog 2 (40 * g * r ^ 2) ≤
      6 + Nat.clog 2 g + 2 * Nat.clog 2 r := by
  calc
    Nat.clog 2 (40 * g * r ^ 2) ≤
        Nat.clog 2 (40 * g) + Nat.clog 2 (r ^ 2) :=
      clog_mul_le_add_JS (40 * g) (r ^ 2)
    _ ≤ (Nat.clog 2 40 + Nat.clog 2 g) +
        (Nat.clog 2 r + Nat.clog 2 r) := by
      gcongr
      · exact clog_mul_le_add_JS 40 g
      · simpa [pow_two] using clog_mul_le_add_JS r r
    _ = 6 + Nat.clog 2 g + 2 * Nat.clog 2 r := by
      have h40 : Nat.clog 2 40 = 6 := by norm_num
      rw [h40]
      omega

private theorem clog_10_mul_mul_le_JS (g r : ℕ) :
    Nat.clog 2 (10 * g * r) ≤
      4 + Nat.clog 2 g + Nat.clog 2 r := by
  calc
    Nat.clog 2 (10 * g * r) ≤
        Nat.clog 2 (10 * g) + Nat.clog 2 r :=
      clog_mul_le_add_JS (10 * g) r
    _ ≤ (Nat.clog 2 10 + Nat.clog 2 g) + Nat.clog 2 r := by
      gcongr
      exact clog_mul_le_add_JS 10 g
    _ = 4 + Nat.clog 2 g + Nat.clog 2 r := by
      have h10 : Nat.clog 2 10 = 4 := by norm_num
      rw [h10]

private theorem ten_mul_le_two_pow_JS : ∀ n : ℕ, 7 ≤ n →
    10 * n ≤ 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      omega

/-- The numerical obligations for the active JS iteration follow uniformly
from one shifted-invariant bound once the terminal cutoff is enlarged to
`64 * (clog₂ r + 1)`.  Thus callers do not need to assume the iteration
arithmetic separately. -/
theorem exactIterationArithmetic_of_largeCutoff
    (x : DyadicState) (r E : ℕ) (hr : 1 ≤ r)
    (hshift : (E : ℤ) + (r : ℤ) ≤ x.invariant r) :
    HasExactIterationArithmetic x r (64 * (Nat.clog 2 r + 1)) E := by
  intro y hxy hyst hgap
  let g := y.gap
  let key := r * y.s - (r - 1) * y.t
  have hg64 : 64 ≤ g := by dsimp [g]; omega
  have hinv : (E : ℤ) + (r : ℤ) ≤ y.invariant r :=
    hshift.trans hxy
  have hinv0 : 0 ≤ y.invariant r := by
    exact (by positivity : (0 : ℤ) ≤ (E : ℤ) + (r : ℤ)).trans hinv
  have hinvGap := DyadicState.invariant_eq_t_sub_twice_mul_gap r y hr hyst
  have hrgZ : (r : ℤ) * (g : ℤ) ≤ (y.t : ℤ) := by
    dsimp [g] at hinvGap ⊢
    linarith
  have hrg : r * g ≤ y.t := by exact_mod_cast hrgZ
  have hsub : (r - 1) * y.t ≤ r * y.s := by
    have hgapEq : y.s + g = y.t := by
      dsimp [g, DyadicState.gap]
      omega
    have hrEq : r - 1 + 1 = r := Nat.sub_add_cancel hr
    nlinarith
  have hkey : (key : ℤ) = y.invariant r + (r : ℤ) * (g : ℤ) := by
    dsimp [key]
    rw [Nat.cast_sub hsub, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hr, hinvGap]
    dsimp [g, DyadicState.gap]
    rw [Nat.cast_sub hyst]
    ring
  have hE : (E : ℤ) ≤ (key : ℤ) := by
    have hrg0 : 0 ≤ (r : ℤ) * (g : ℤ) := by positivity
    linarith
  have hkeyrg : r * g ≤ key := by
    exact_mod_cast (show (r : ℤ) * (g : ℤ) ≤ (key : ℤ) by
      rw [hkey]
      exact le_add_of_nonneg_left hinv0)
  have hlogg : Nat.clog 2 g ≤ g / 8 := clog_two_le_div_eight_JS hg64
  have hlogr : Nat.clog 2 r ≤ g / 64 := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    change 64 * (Nat.clog 2 r + 1) < g at hgap
    omega
  have hCraw := clog_40_mul_mul_sq_le_JS g r
  have hC : Nat.clog 2 (40 * g * r ^ 2) + 1 ≤ g / 2 := by
    omega
  have hDraw := clog_10_mul_mul_le_JS g r
  have hD : Nat.clog 2 (10 * g * r) ≤ g / 4 := by
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [key] using hE
  · calc
      10 * y.gap * r = 10 * (r * g) := by simp [g]; ring
      _ ≤ 2 ^ (r * g) := ten_mul_le_two_pow_JS _ (by nlinarith)
      _ ≤ 2 ^ key := Nat.pow_le_pow_right (by omega) hkeyrg
  · dsimp [g] at hC ⊢
    omega
  · have hhalf : 2 * (g / 2) ≤ g := by
      simpa [mul_comm] using Nat.mul_div_le g 2
    have hquarterhalf : g / 4 ≤ g / 2 := by omega
    have hloss : Nat.clog 2 (10 * g * r) +
        (2 * r - 1) * (Nat.clog 2 (40 * g * r ^ 2) + 1) ≤ r * g := by
      calc
        Nat.clog 2 (10 * g * r) +
            (2 * r - 1) * (Nat.clog 2 (40 * g * r ^ 2) + 1) ≤
            g / 4 + (2 * r - 1) * (g / 2) := by gcongr
        _ ≤ g / 2 + (2 * r - 1) * (g / 2) := by gcongr
        _ = 2 * r * (g / 2) := by
          calc
            g / 2 + (2 * r - 1) * (g / 2) =
                1 * (g / 2) + (2 * r - 1) * (g / 2) := by simp
            _ = (1 + (2 * r - 1)) * (g / 2) := by ring
            _ = 2 * r * (g / 2) := by
              congr 1
              omega
        _ ≤ r * g := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            Nat.mul_le_mul_left r hhalf
    have hlossZ :
        (Nat.clog 2 (10 * g * r) : ℤ) +
          (2 * (r : ℤ) - 1) *
            (Nat.clog 2 (40 * g * r ^ 2) + 1 : ℕ) ≤
          (r : ℤ) * (g : ℤ) := by
      have hcoeffcast : ((2 * r - 1 : ℕ) : ℤ) = 2 * (r : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
        push_cast
        rfl
      rw [← hcoeffcast]
      exact_mod_cast hloss
    change y.invariant r + (Nat.clog 2 (10 * g * r) : ℤ) +
        (2 * (r : ℤ) - 1) *
          (Nat.clog 2 (40 * g * r ^ 2) + 1 : ℕ) ≤ (key : ℤ)
    rw [hkey]
    linarith

/-- Codegrees decrease when edges are deleted. -/
theorem bipCodegree_adj_mono {G K : BipartiteGraph A B} (hKG : K ≤ G)
    (u w : A) : bipCodegree K.Adj u w ≤ bipCodegree G.Adj u w := by
  classical
  apply Finset.card_le_card
  intro b hb
  simp only [bipCodegree, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  exact ⟨hKG hb.1, hKG hb.2⟩

/-- JS Lemma 5.1 driven by one uniform codegree bound on the initial graph.
The well-founded predicate retains the cumulative invariant inequality, so
the active key-restriction hypotheses are reconstructed at every step. -/
theorem js_lemma_5_1_uniformCodegree
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (r cutoff E : ℕ) (x : DyadicState)
    (hr : 1 ≤ r) (hx : IsDyadicallyBiregularOn G A₀ B₀ r x)
    (hshift : 0 ≤ x.invariant r - (r : ℤ))
    (hcodeg : ∀ u w : A, u ≠ w →
      bipCodegree G.Adj u w ≤ 2 ^ E)
    (harith : HasExactIterationArithmetic x r cutoff E) :
    ∃ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState),
      H ≤ G ∧ H.IsAlmostBiregularOn A₁ B₁ (2 ^ y.gap) r ∧
        y.gap ≤ cutoff ∧ r ≤ y.s := by
  let P : DyadicState → Prop := fun y ↦
    ∃ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B),
      H ≤ G ∧ IsDyadicallyBiregularOn H A₁ B₁ r y ∧
        x.invariant r ≤ y.invariant r
  have hxP : P x := ⟨G, A₀, B₀, le_rfl, hx, le_rfl⟩
  have hstep : ∀ y, P y → cutoff < y.gap →
      ∃ z, P z ∧ IsDyadicImprovement r y z := by
    intro y hy hgap
    obtain ⟨K, A₁, B₁, hKG, hyK, hxy⟩ := hy
    have hyst : y.s < y.t := by
      simpa [DyadicState.gap, Nat.sub_pos_iff_lt] using
        (lt_of_le_of_lt (Nat.zero_le cutoff) hgap)
    have hys : 0 < y.s := by
      have hry : r ≤ y.s := js_lemma_5_1_levels hr hyK.2.2.2.2.2.2
        hshift hxy
      exact lt_of_lt_of_le (by omega) hry
    obtain ⟨hE, hQD, hgapSlack, hinvariantSlack⟩ :=
      harith y hxy hyK.2.2.2.2.2.2 hgap
    have hcodegK : ∀ u ∈ A₁, ∀ w ∈ A₁, u ≠ w →
        bipCodegree K.Adj u w ≤
          2 ^ (r * y.s - (r - 1) * y.t) := by
      intro u _hu w _hw huw
      calc
        bipCodegree K.Adj u w ≤ bipCodegree G.Adj u w :=
          bipCodegree_adj_mono hKG u w
        _ ≤ 2 ^ E := hcodeg u w huw
        _ ≤ 2 ^ (r * y.s - (r - 1) * y.t) := by
          apply Nat.pow_le_pow_right (by omega)
          exact_mod_cast hE
    obtain ⟨L, A₂, B₂, z, _hA₂, _hB₂, hLK, hzL, hyz⟩ :=
      exists_dyadicImprovement_active K A₁ B₁ r y hr hys hyst hyK
        hcodegK hQD hgapSlack hinvariantSlack
    refine ⟨z, ⟨L, A₂, B₂, hLK.trans hKG, hzL, ?_⟩, hyz⟩
    exact hxy.trans hyz.2
  obtain ⟨y, ⟨H, A₁, B₁, hHG, hyH, hxy⟩, hygap, _⟩ :=
    js_lemma_4_2_iteration r cutoff P x hxP hstep
  have hry : r ≤ y.s := js_lemma_5_1_levels hr hyH.2.2.2.2.2.2
    hshift hxy
  exact ⟨H, A₁, B₁, y, hHG,
    hyH.isAlmostBiregularOn hr hry, hygap, hry⟩

/-- High-bucket assembly with every finite and integer step exposed.

The bucket is independently trimmed to right degree `r`.  It is then used as
the initial dyadically biregular graph, iterated via the active form of the
key-restriction lemma, converted to an almost-biregular terminal graph, and
finally passed through the exact cross-multiplied form of Lemma 3.5.

The extractor conclusion is the exact integer form exported by JS Lemma 3.5.
We enlarge the terminal almost-biregularity constant from `2^y.gap` to
`2^cutoff`; its logarithm is exactly `cutoff`, including the extra rounding
unit in the formal Lemma 3.5 denominator. -/
theorem exists_almostRegular_highBucket_of_exactData
    (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B)
    (r c L s t cutoff E : ℕ)
    (hc : 0 < c) (hr : 2 ≤ r) (hX : X.Nonempty) (hB₀ : B₀.Nonempty)
    (hlarge : B₀.card ≤ c * (G.goodRightJS X B₀ r).card)
    (hscale : c * (r * X.card) ≤ B₀.card * r)
    (hleft : ∀ a ∈ X,
      c * (G.leftDegree a * X.card) ≤ L * (B₀.card * r))
    (hdensity : c * (2 ^ s * X.card) ≤ B₀.card * r)
    (hmax : ∀ a ∈ X, G.leftDegree a ≤ 2 ^ t)
    (hst : s ≤ t)
    (hshift : 0 ≤ (DyadicState.invariant r ⟨s, t⟩) - (r : ℤ))
    (hrcutoff : r ≤ 2 ^ cutoff)
    (hcodeg : ∀ u w : A, u ≠ w →
      bipCodegree G.Adj u w ≤ 2 ^ E)
    (harith : HasExactIterationArithmetic ⟨s, t⟩ r cutoff E) :
    ∃ Q : BipartiteGraph A B, Q ≤ G ∧ Q.IsAlmostRegular 64 ∧
      r * Q.supportCard ≤ 32 * (cutoff + 1) * Q.edgeCount := by
  classical
  obtain ⟨H, hhalf, _halmost⟩ :=
    G.exists_almostBiregular_of_large_goodRightJS X B₀ r c L hc hX hB₀
      hlarge hscale hleft
  let B₁ := G.goodRightJS X B₀ r
  have hedge : H.edgeCount = B₁.card * r := by
    exact edgeCount_eq_card_mul_of_rightRegularOn hhalf.2.1 hhalf.2.2.2
  have hdensityH : 2 ^ s * X.card ≤ H.edgeCount := by
    have hscaled : c * (2 ^ s * X.card) ≤ c * H.edgeCount := by
      calc
        c * (2 ^ s * X.card) ≤ B₀.card * r := hdensity
        _ ≤ (c * B₁.card) * r := by gcongr
        _ = c * H.edgeCount := by rw [hedge]; ring
    exact Nat.le_of_mul_le_mul_left hscaled hc
  have hmaxH : ∀ a ∈ X, H.leftDegree a ≤ 2 ^ t := by
    intro a ha
    exact (leftDegree_mono hhalf.1 a).trans (hmax a ha)
  have hdyadic : IsDyadicallyBiregularOn H X B₁ r ⟨s, t⟩ := by
    exact ⟨hhalf.2.1, hX, hhalf.2.2.1, hhalf.2.2.2,
      hdensityH, hmaxH, hst⟩
  have hcodegH : ∀ u w : A, u ≠ w →
      bipCodegree H.Adj u w ≤ 2 ^ E := by
    intro u w huw
    exact (bipCodegree_adj_mono hhalf.1 u w).trans (hcodeg u w huw)
  obtain ⟨F, A₁, B₂, y, hFH, hFalmost, hygap, _hrys⟩ :=
    js_lemma_5_1_uniformCodegree H X B₁ r cutoff E ⟨s, t⟩
      (by omega) hdyadic hshift hcodegH harith
  have hFalmost' :
      F.IsAlmostBiregularOn A₁ B₂ (2 ^ cutoff) r := by
    refine ⟨hFalmost.1, hFalmost.2.1, hFalmost.2.2.1,
      hFalmost.2.2.2.1, hFalmost.2.2.2.2.1, ?_⟩
    intro a ha
    calc
      F.leftDegree a * A₁.card ≤ 2 ^ y.gap * F.edgeCount :=
        hFalmost.2.2.2.2.2 a ha
      _ ≤ 2 ^ cutoff * F.edgeCount := by
        exact Nat.mul_le_mul_right F.edgeCount
          (Nat.pow_le_pow_right (by omega) hygap)
  obtain ⟨Q, hQF, hQalmost, hQavg⟩ :=
    F.exists_almostRegular_subgraph hFalmost' hr hrcutoff
  refine ⟨Q, hQF.trans (hFH.trans hhalf.1), hQalmost, ?_⟩
  simpa [Nat.log2_eq_log_two, Nat.log_pow (by omega : 1 < 2)] using hQavg

/-- The denominator conversion used by JS Lemma 5.2.  With cutoff
`5 * clog₂(r')`, the high-bucket output has exactly the hypothesis needed
by `js_lemma_5_2_average_transfer`. -/
theorem exists_almostRegular_highBucket_averageTransfer
    (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B)
    (k r₀ r' c L s t E : ℕ)
    (hk : 1 ≤ k) (hr₀ : 2 * k ≤ r₀)
    (hr' : r' = jsTrimmedDegree r₀ k)
    (hc : 0 < c) (hr'pos : 2 ≤ r') (hX : X.Nonempty)
    (hB₀ : B₀.Nonempty)
    (hlarge : B₀.card ≤ c * (G.goodRightJS X B₀ r').card)
    (hscale : c * (r' * X.card) ≤ B₀.card * r')
    (hleft : ∀ a ∈ X,
      c * (G.leftDegree a * X.card) ≤ L * (B₀.card * r'))
    (hdensity : c * (2 ^ s * X.card) ≤ B₀.card * r')
    (hmax : ∀ a ∈ X, G.leftDegree a ≤ 2 ^ t)
    (hst : s ≤ t)
    (hshift : 0 ≤ (DyadicState.invariant r' ⟨s, t⟩) - (r' : ℤ))
    (hr'cutoff : r' ≤ 2 ^ (5 * Nat.clog 2 r'))
    (hcodeg : ∀ u w : A, u ≠ w →
      bipCodegree G.Adj u w ≤ 2 ^ E)
    (harith : HasExactIterationArithmetic ⟨s, t⟩ r'
      (5 * Nat.clog 2 r') E) :
    ∃ Q : BipartiteGraph A B, Q ≤ G ∧ Q.IsAlmostRegular 64 ∧
      r₀ * Q.supportCard ≤
        384 * (k + 1) * Nat.clog 2 r₀ * Q.edgeCount := by
  obtain ⟨Q, hQG, hQalmost, hQavg⟩ :=
    exists_almostRegular_highBucket_of_exactData G X B₀ r' c L s t
      (5 * Nat.clog 2 r') E hc hr'pos hX hB₀ hlarge hscale hleft hdensity
      hmax hst hshift hr'cutoff hcodeg harith
  refine ⟨Q, hQG, hQalmost, ?_⟩
  have hcover : r₀ ≤ 2 * (k + 1) * r' := by
    rw [hr']
    exact le_mul_jsTrimmedDegree r₀ k
  have hr'le : r' ≤ r₀ := by
    rw [hr']
    exact (jsTrimmedDegree_le_div hk hr₀).trans (Nat.div_le_self _ _)
  have hlog : Nat.clog 2 r' ≤ Nat.clog 2 r₀ :=
    Nat.clog_mono_right 2 hr'le
  have hlogpos : 1 ≤ Nat.clog 2 r₀ := by
    have : 2 ≤ r₀ := by omega
    exact Nat.clog_pos Nat.one_lt_two (by omega)
  have hfactor :
      32 * (5 * Nat.clog 2 r' + 1) ≤
        192 * Nat.clog 2 r₀ := by
    omega
  calc
    r₀ * Q.supportCard ≤ (2 * (k + 1) * r') * Q.supportCard := by gcongr
    _ = 2 * (k + 1) * (r' * Q.supportCard) := by ring
    _ ≤ 2 * (k + 1) *
        (32 * (5 * Nat.clog 2 r' + 1) * Q.edgeCount) := by gcongr
    _ ≤ 2 * (k + 1) *
        (192 * Nat.clog 2 r₀ * Q.edgeCount) := by
      apply Nat.mul_le_mul_left
      exact Nat.mul_le_mul_right Q.edgeCount hfactor
    _ = 384 * (k + 1) * Nat.clog 2 r₀ * Q.edgeCount := by ring

/-- Cleaning retains enough edges that many right vertices still have the
JS 5.2 trimmed degree. -/
theorem card_le_twice_mul_goodRight_after_cleaning
    (F C : BipartiteGraph A B) (X : Finset A) (B₁ : Finset B)
    (r k : ℕ) (hr : 0 < r)
    (hFsupp : F.SupportedOn X B₁) (hFreg : F.IsRightRegularOn B₁ r)
    (hCF : C ≤ F) (hCsupp : C.SupportedOn X B₁)
    (hretain : F.edgeCount ≤ (k + 1) * C.edgeCount) :
    B₁.card ≤ 2 * (k + 1) *
      (C.goodRightJS X B₁ (jsTrimmedDegree r k)).card := by
  classical
  let d := jsTrimmedDegree r k
  let Good := C.goodRightJS X B₁ d
  have hd : 0 < d := by
    have hcover := le_mul_jsTrimmedDegree r k
    dsimp [d]
    nlinarith
  have htrim : 2 * (k + 1) * (d - 1) < r := by
    have hceil := mul_jsTrimmedDegree_lt_add r k
    have heq : 2 * (k + 1) * (d - 1) + 2 * (k + 1) =
        2 * (k + 1) * d := by
      calc
        2 * (k + 1) * (d - 1) + 2 * (k + 1) =
            2 * (k + 1) * ((d - 1) + 1) := by ring
        _ = 2 * (k + 1) * d := by rw [Nat.sub_add_cancel hd]
    change 2 * (k + 1) * d < r + 2 * (k + 1) at hceil
    omega
  have hGoodSub : Good ⊆ B₁ := by
    intro b hb
    exact (C.mem_goodRightJS X B₁ d b).1 (by simpa [Good] using hb) |>.1
  have hout : ∀ b ∈ (Finset.univ : Finset B), b ∉ B₁ → C.rightDegree b = 0 := by
    intro b _hb hbB
    rw [rightDegree, Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨a, ha⟩
    exact hbB (hCsupp ((C.mem_leftNeighbors a b).mp ha)).2
  have hdegree : ∀ b ∈ B₁,
      C.rightDegree b ≤ (if b ∈ Good then r else 0) + (d - 1) := by
    intro b hb
    by_cases hbGood : b ∈ Good
    · have hmono : C.rightDegree b ≤ r :=
        (rightDegree_mono hCF b).trans_eq (hFreg b hb)
      simpa [hbGood] using hmono.trans (Nat.le_add_right r (d - 1))
    · have hinter : C.leftNeighbors b ∩ X = C.leftNeighbors b := by
        apply Finset.inter_eq_left.mpr
        intro a ha
        exact (hCsupp ((C.mem_leftNeighbors a b).mp ha)).1
      have hlt : C.rightDegree b < d := by
        have hn := hbGood
        rw [show Good = C.goodRightJS X B₁ d by rfl,
          C.mem_goodRightJS X B₁ d b] at hn
        push Not at hn
        simpa only [rightDegree, hinter] using hn hb
      simp [hbGood]
      omega
  have hCedge : C.edgeCount ≤ Good.card * r + B₁.card * (d - 1) := by
    calc
      C.edgeCount = ∑ b ∈ B₁, C.rightDegree b := by
        rw [edgeCount]
        exact (Finset.sum_subset (Finset.subset_univ B₁) hout).symm
      _ ≤ ∑ b ∈ B₁, ((if b ∈ Good then r else 0) + (d - 1)) := by
        exact Finset.sum_le_sum fun b hb ↦ hdegree b hb
      _ = (∑ b ∈ B₁, (if b ∈ Good then r else 0)) +
          ∑ _b ∈ B₁, (d - 1) := by rw [Finset.sum_add_distrib]
      _ = Good.card * r + B₁.card * (d - 1) := by
        simp [Finset.inter_eq_right.mpr hGoodSub]
  have hFedge : F.edgeCount = B₁.card * r :=
    edgeCount_eq_card_mul_of_rightRegularOn hFsupp hFreg
  have hmain : B₁.card * r ≤
      (k + 1) * (Good.card * r + B₁.card * (d - 1)) := by
    rw [← hFedge]
    exact hretain.trans (Nat.mul_le_mul_left _ hCedge)
  have hbad : 2 * (k + 1) * (B₁.card * (d - 1)) ≤ B₁.card * r := by
    calc
      2 * (k + 1) * (B₁.card * (d - 1)) =
          B₁.card * (2 * (k + 1) * (d - 1)) := by ring
      _ ≤ B₁.card * r := by gcongr
  have hmul : B₁.card * r ≤ (2 * (k + 1) * Good.card) * r := by
    nlinarith
  have hcard : B₁.card ≤ 2 * (k + 1) * Good.card :=
    Nat.le_of_mul_le_mul_right hmul hr
  simpa [Good, d] using hcard

/-- The complete high-bucket route after KST cleaning.  All numerical
inputs are exact natural-number inequalities; the density hypothesis includes
the `2*(k+1)` cleaning and low-right-degree loss. -/
theorem exists_almostRegular_highBucket_cleaned
    (G : BipartiteGraph A B) (X : Finset A) (B₀ : Finset B)
    (k r c s t : ℕ)
    (hk : 1 ≤ k) (hrLarge : 4 * (k + 1) ≤ r) (hc : 0 < c)
    (hX : X.Nonempty) (hB₀ : B₀.Nonempty)
    (hlarge : B₀.card ≤ c * (G.goodRightJS X B₀ r).card)
    (hdensity : (2 * (k + 1) * c) * (2 ^ s * X.card) ≤
      B₀.card * jsTrimmedDegree r k)
    (hmax : ∀ a ∈ X, G.leftDegree a ≤ 2 ^ t)
    (hst : s < t) (hclose : 6 * r * (t - s) ≤ t)
    (hfree : IsBipartiteKFree G.Adj k)
    (hpow : k ^ (k + 1) * (2 ^ t) ^ (k - 1) ≤
      (2 ^ (t - t / (2 * k)) + 1) ^ k) :
    ∃ Q : BipartiteGraph A B, Q ≤ G ∧ Q.IsAlmostRegular 64 ∧
      r * Q.supportCard ≤
        4160 * (k + 1) * (Nat.clog 2 r + 1) * Q.edgeCount := by
  classical
  let B₁ := G.goodRightJS X B₀ r
  let r' := jsTrimmedDegree r k
  let E := t - t / (2 * k)
  let cutoff := 64 * (Nat.clog 2 r' + 1)
  have hr : 0 < r := by omega
  have hrTwoK : 2 * k ≤ r := by omega
  have hr' : 2 ≤ r' := by
    have hcover := le_mul_jsTrimmedDegree r k
    dsimp [r']
    nlinarith
  have hB₁ : B₁.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hzero : B₀.card = 0 := by
      simpa [B₁, hempty] using hlarge
    exact (Finset.card_pos.mpr hB₀).ne' hzero
  obtain ⟨F, hF⟩ := G.exists_halfRegularSubgraphOf_goodRightJS X B₀ r
    (by simpa [B₁] using hB₁)
  have hfreeF : IsBipartiteKFree F.Adj k :=
    hfree.mono fun a b hab ↦ hF.1 hab
  have hmaxF : ∀ a ∈ X, F.leftDegree a ≤ 2 ^ t := by
    intro a ha
    exact (leftDegree_mono hF.1 a).trans (hmax a ha)
  obtain ⟨C, hCF, hCsupp, hretain, hcodegC⟩ :=
    F.exists_codegreeCleaning_active_of_pow X B₁ (2 ^ E) k (2 ^ t)
      (by omega) (by simpa [B₁] using hF.2.1) hfreeF hmaxF
      (by simpa [E] using hpow)
  let B₂ := C.goodRightJS X B₁ r'
  have hB₁B₂ : B₁.card ≤ 2 * (k + 1) * B₂.card := by
    simpa [B₁, B₂, r'] using
      card_le_twice_mul_goodRight_after_cleaning F C X B₁ r k hr
        (by simpa [B₁] using hF.2.1) (by simpa [B₁] using hF.2.2.2)
        hCF hCsupp hretain
  have hlarge₂ : B₀.card ≤ (2 * (k + 1) * c) * B₂.card := by
    calc
      B₀.card ≤ c * B₁.card := by simpa [B₁] using hlarge
      _ ≤ c * (2 * (k + 1) * B₂.card) := by gcongr
      _ = (2 * (k + 1) * c) * B₂.card := by ring
  have hB₂ : B₂.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hzero : B₀.card = 0 := by simpa [hempty] using hlarge₂
    exact (Finset.card_pos.mpr hB₀).ne' hzero
  obtain ⟨H, hH⟩ := C.exists_halfRegularSubgraphOf_goodRightJS X B₁ r'
    (by simpa [B₂] using hB₂)
  have hedgeH : H.edgeCount = B₂.card * r' := by
    simpa [B₂] using
      (edgeCount_eq_card_mul_of_rightRegularOn hH.2.1 hH.2.2.2)
  have hdensityH : 2 ^ s * X.card ≤ H.edgeCount := by
    have hscaled : (2 * (k + 1) * c) * (2 ^ s * X.card) ≤
        (2 * (k + 1) * c) * H.edgeCount := by
      calc
        (2 * (k + 1) * c) * (2 ^ s * X.card) ≤ B₀.card * r' :=
          by simpa [r'] using hdensity
        _ ≤ ((2 * (k + 1) * c) * B₂.card) * r' := by gcongr
        _ = (2 * (k + 1) * c) * H.edgeCount := by rw [hedgeH]; ring
    exact Nat.le_of_mul_le_mul_left hscaled (by positivity)
  have hmaxH : ∀ a ∈ X, H.leftDegree a ≤ 2 ^ t := by
    intro a ha
    exact (leftDegree_mono (hH.1.trans hCF) a).trans (hmaxF a ha)
  have hdyadic : IsDyadicallyBiregularOn H X B₂ r' ⟨s, t⟩ := by
    exact ⟨by simpa [B₂] using hH.2.1, hX,
      by simpa [B₂] using hH.2.2.1, by simpa [B₂] using hH.2.2.2,
      hdensityH, hmaxH, hst.le⟩
  have hcodegH : ∀ u w : A, u ≠ w → bipCodegree H.Adj u w ≤ 2 ^ E := by
    intro u w huw
    calc
      bipCodegree H.Adj u w ≤ bipCodegree C.Adj u w :=
        bipCodegree_adj_mono hH.1 u w
      _ ≤ 2 ^ E := by
        simpa only [bipCodegree] using hcodegC u w huw
  have hexp := js_lemma_5_2_trimmed_exponent hk hrTwoK hst hclose
  have hshiftStrong : (E : ℤ) + (r' : ℤ) ≤
      (DyadicState.invariant r' ⟨s, t⟩) := by
    dsimp [E, r'] at hexp ⊢
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * jsTrimmedDegree r k),
      Nat.cast_mul 2 (jsTrimmedDegree r k)] at hexp
    norm_num only [Nat.cast_ofNat, Nat.cast_one] at hexp
    linarith
  have hshift : 0 ≤ (DyadicState.invariant r' ⟨s, t⟩) - (r' : ℤ) := by
    have hEzero : (0 : ℤ) ≤ (E : ℤ) := by positivity
    linarith
  have harith : HasExactIterationArithmetic ⟨s, t⟩ r' cutoff E := by
    simpa [cutoff] using exactIterationArithmetic_of_largeCutoff
      (x := (⟨s, t⟩ : DyadicState)) r' E (by omega) hshiftStrong
  obtain ⟨J, A₁, B₃, y, hJH, hJalmost, hygap, _⟩ :=
    js_lemma_5_1_uniformCodegree H X B₂ r' cutoff E ⟨s, t⟩
      (by omega) hdyadic hshift hcodegH harith
  have hr'cutoff : r' ≤ 2 ^ cutoff := by
    calc
      r' ≤ 2 ^ Nat.clog 2 r' := Nat.le_pow_clog (by omega) r'
      _ ≤ 2 ^ cutoff := by
        apply Nat.pow_le_pow_right (by omega)
        dsimp [cutoff]
        omega
  have hJalmost' : J.IsAlmostBiregularOn A₁ B₃ (2 ^ cutoff) r' := by
    refine hJalmost.mono_loss ?_
    exact Nat.pow_le_pow_right (by omega) hygap
  obtain ⟨Q, hQJ, hQalmost, hQavg⟩ :=
    J.exists_almostRegular_subgraph hJalmost' hr' hr'cutoff
  refine ⟨Q, hQJ.trans (hJH.trans (hH.1.trans (hCF.trans hF.1))), hQalmost, ?_⟩
  have hcover : r ≤ 2 * (k + 1) * r' := by
    simpa [r'] using le_mul_jsTrimmedDegree r k
  have hr'le : r' ≤ r := by
    dsimp [r']
    exact (jsTrimmedDegree_le_div hk hrTwoK).trans (Nat.div_le_self _ _)
  have hlog : Nat.clog 2 r' ≤ Nat.clog 2 r := Nat.clog_mono_right 2 hr'le
  have hfactor : 64 * (cutoff + 1) ≤ 4160 * (Nat.clog 2 r + 1) := by
    dsimp [cutoff]
    omega
  have hQavg' : r' * Q.supportCard ≤ 32 * (cutoff + 1) * Q.edgeCount := by
    simpa [Nat.log2_eq_log_two, Nat.log_pow (by omega : 1 < 2)] using hQavg
  calc
    r * Q.supportCard ≤ (2 * (k + 1) * r') * Q.supportCard := by gcongr
    _ = 2 * (k + 1) * (r' * Q.supportCard) := by ring
    _ ≤ 2 * (k + 1) * (32 * (cutoff + 1) * Q.edgeCount) := by gcongr
    _ = (k + 1) * (64 * (cutoff + 1)) * Q.edgeCount := by ring
    _ ≤ (k + 1) * (4160 * (Nat.clog 2 r + 1)) * Q.edgeCount := by gcongr
    _ = 4160 * (k + 1) * (Nat.clog 2 r + 1) * Q.edgeCount := by ring

/-- Global-parameter specialization of the cleaned high-bucket route. -/
theorem exists_globalHighRoute_almostRegular
    (G : BipartiteGraph A B) (k r Delta i q : ℕ)
    (hk : 1 ≤ k) (hrLarge : 4 * (k + 1) ≤ r)
    (hB : (Finset.univ : Finset B).Nonempty)
    (hregular : ∀ b : B,
      G.rightDegree b = JSGlobalParameters.coreDegree r Delta)
    (hhigh : Fintype.card B ≤
      2 * (JSGlobalParameters.indices r Delta).card *
        (G.goodRightJS (G.globalDegreeBucket r Delta (i, q))
          Finset.univ r).card)
    (hfree : IsBipartiteKFree G.Adj k)
    (hloss : JSGlobalParameters.incidenceLoss k r Delta ≤
      JSGlobalParameters.ell Delta / 2)
    (hclean : Nat.clog 2 (k ^ (k + 1)) ≤ 5 * r) :
    ∃ Q : BipartiteGraph A B, Q ≤ G ∧ Q.IsAlmostRegular 64 ∧
      r * Q.supportCard ≤
        4160 * (k + 1) * (Nat.clog 2 r + 1) * Q.edgeCount := by
  classical
  let X := G.globalDegreeBucket r Delta (i, q)
  let P := JSGlobalParameters.lowerExponent r Delta i q
  let S := JSGlobalParameters.iterationExponent r Delta i q
  let T := JSGlobalParameters.upperExponent r Delta i q
  let r' := jsTrimmedDegree r k
  let c := 2 * (JSGlobalParameters.indices r Delta).card
  have hr : 0 < r := by omega
  have hgood : (G.goodRightJS X Finset.univ r).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hz : Fintype.card B = 0 := by
      simpa [X, hempty] using hhigh
    have hpos : 0 < Fintype.card B := by simpa using Finset.card_pos.mpr hB
    omega
  have hX : X.Nonempty := by
    obtain ⟨b, hb⟩ := hgood
    have hb' := (G.mem_goodRightJS X Finset.univ r b).1 hb
    have hinter : (G.leftNeighbors b ∩ X).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have : (G.leftNeighbors b ∩ X).card = 0 := by simp [hempty]
      omega
    exact hinter.mono Finset.inter_subset_right
  have hbucket : 2 ^ P * X.card ≤
      Fintype.card B * JSGlobalParameters.coreDegree r Delta := by
    have hlow : ∀ a ∈ X, 2 ^ P ≤ G.leftDegree a := by
      intro a ha
      have ha' := ha
      simp only [X, globalDegreeBucket, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha'
      dsimp [P]
      omega
    have hsupp : G.SupportedOn (Finset.univ : Finset A)
        (Finset.univ : Finset B) := by
      intro a b hab
      simp
    have hedge : G.edgeCount =
        Fintype.card B * JSGlobalParameters.coreDegree r Delta := by
      simpa using edgeCount_eq_card_mul_of_rightRegularOn hsupp
        (fun b _hb ↦ hregular b)
    calc
      2 ^ P * X.card = ∑ _a ∈ X, 2 ^ P := by simp [mul_comm]
      _ ≤ ∑ a ∈ X, G.leftDegree a := Finset.sum_le_sum hlow
      _ = ∑ a ∈ (Finset.univ : Finset A),
          if a ∈ X then G.leftDegree a else 0 := by simp
      _ ≤ ∑ a ∈ (Finset.univ : Finset A), G.leftDegree a := by
        exact Finset.sum_le_sum fun a _ha ↦ by
          by_cases ha : a ∈ X <;> simp [ha]
      _ = G.edgeCount := G.edgeCount_eq_sum_leftDegree.symm
      _ = Fintype.card B * JSGlobalParameters.coreDegree r Delta := hedge
  have hcover : r ≤ 2 * (k + 1) * r' := by
    simpa [r'] using le_mul_jsTrimmedDegree r k
  have hcoefficient :
      (2 * (k + 1) * c) * JSGlobalParameters.coreDegree r Delta ≤
        (400 * (4 * (k + 1) ^ 2) * r ^ 2 *
          (JSGlobalParameters.ell Delta) ^ 2) * r' := by
    let M := 800 * (k + 1) * r ^ 2 * (JSGlobalParameters.ell Delta) ^ 2
    calc
      (2 * (k + 1) * c) * JSGlobalParameters.coreDegree r Delta = M * r := by
        simp [M, c, JSGlobalParameters.card_indices, JSGlobalParameters.slots,
          JSGlobalParameters.coreDegree]
        ring
      _ ≤ M * (2 * (k + 1) * r') := by gcongr
      _ = (400 * (4 * (k + 1) ^ 2) * r ^ 2 *
          (JSGlobalParameters.ell Delta) ^ 2) * r' := by
        simp [M]
        ring
  have hcase := JSGlobalParameters.case2_density_power
    (i := i) (q := q) hr hloss
  have hcoefficientPower :
      (2 * (k + 1) * c) * JSGlobalParameters.coreDegree r Delta * 2 ^ S ≤
        r' * 2 ^ P := by
    calc
      (2 * (k + 1) * c) * JSGlobalParameters.coreDegree r Delta * 2 ^ S ≤
          ((400 * (4 * (k + 1) ^ 2) * r ^ 2 *
            (JSGlobalParameters.ell Delta) ^ 2) * r') * 2 ^ S := by gcongr
      _ = (400 * (4 * (k + 1) ^ 2) * r ^ 2 *
          (JSGlobalParameters.ell Delta) ^ 2 * 2 ^ S) * r' := by ring
      _ ≤ 2 ^ P * r' := by
        dsimp [S, P]
        gcongr
      _ = r' * 2 ^ P := by ring
  have hcorepos : 0 < JSGlobalParameters.coreDegree r Delta := by
    simp [JSGlobalParameters.coreDegree, hr, JSGlobalParameters.ell_pos]
  have hdensity : (2 * (k + 1) * c) * (2 ^ S * X.card) ≤
      Fintype.card B * r' := by
    have hmul : ((2 * (k + 1) * c) * (2 ^ S * X.card)) *
        JSGlobalParameters.coreDegree r Delta ≤
        (Fintype.card B * r') * JSGlobalParameters.coreDegree r Delta := by
      calc
        ((2 * (k + 1) * c) * (2 ^ S * X.card)) *
            JSGlobalParameters.coreDegree r Delta =
          ((2 * (k + 1) * c) * JSGlobalParameters.coreDegree r Delta *
            2 ^ S) * X.card := by ring
        _ ≤ (r' * 2 ^ P) * X.card := by gcongr
        _ = r' * (2 ^ P * X.card) := by ring
        _ ≤ r' * (Fintype.card B * JSGlobalParameters.coreDegree r Delta) := by
          gcongr
        _ = (Fintype.card B * r') *
            JSGlobalParameters.coreDegree r Delta := by ring
    exact Nat.le_of_mul_le_mul_right hmul hcorepos
  have hmax : ∀ a ∈ X, G.leftDegree a ≤ 2 ^ T := by
    intro a ha
    have ha' := ha
    simp only [X, globalDegreeBucket, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha'
    simpa [T] using ha'.2
  have hst : S < T := by
    simpa [S, T] using
      (JSGlobalParameters.iterationExponent_lt_upper (Delta := Delta)
        (i := i) (q := q) hr)
  have hclose : 6 * r * (T - S) ≤ T := by
    simpa [S, T] using
      (JSGlobalParameters.iteration_gap (Delta := Delta) (i := i) (q := q) hr).1
  have hpow := JSGlobalParameters.cleaning_power_upperExponent_of_clog_le_five_mul
    (k := k) (r := r) (Delta := Delta) (i := i) (q := q) (by omega) hclean
  exact exists_almostRegular_highBucket_cleaned G X Finset.univ k r c S T
    hk hrLarge (by
      simp [c, JSGlobalParameters.card_indices, JSGlobalParameters.slots,
        hr, JSGlobalParameters.ell_pos]) hX hB
    (by simpa [X, c] using hhigh) (by simpa [r'] using hdensity)
    hmax hst hclose hfree (by simpa [T] using hpow)

end HighBucketRoute

end BipartiteGraph

/-- The PRS entry reduction, specialized to the exact degree needed by the
global JS bucket schedule.  The factor `80` absorbs the factor-four loss in
the entry reduction and leaves precisely `coreDegree` for the dichotomy. -/
theorem exists_globalCore_degreeBucket_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r Delta : ℕ) (hr : 0 < r)
    (havg : (80 * r ^ 2 * JSGlobalParameters.ell Delta) *
        Fintype.card V ≤ 2 * G.edgeFinset.card)
    (hmax : G.maxDegree ≤ Delta) :
    ∃ A B : Finset V,
      A.Nonempty ∧ B.Nonempty ∧ A.card ≤ B.card ∧
      Disjoint (A : Set V) (B : Set V) ∧
      ∃ H : BipartiteGraph A B, ∃ delta : ℕ,
        H.IsHalfRegularSubgraphOf (PRSEntry.fromSimpleGraph G A B)
          (Finset.univ : Finset A) (Finset.univ : Finset B) delta ∧
        delta = JSGlobalParameters.coreDegree r Delta ∧
        (∀ a : A, H.leftDegree a ≤ Delta) ∧
        (Fintype.card B ≤
            2 * (H.goodRightJS (H.globalLowClass r Delta) Finset.univ
              (JSGlobalParameters.lowDegree r Delta)).card ∨
          ∃ z ∈ JSGlobalParameters.indices r Delta,
            Fintype.card B ≤
              2 * (JSGlobalParameters.indices r Delta).card *
                (H.goodRightJS (H.globalDegreeBucket r Delta z)
                  Finset.univ r).card) := by
  classical
  let d := 80 * r ^ 2 * JSGlobalParameters.ell Delta
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos hr _))
      (JSGlobalParameters.ell_pos Delta)
  obtain ⟨A, B, hA, hB, hcard, hAB, H, delta, hH, hdeltaEq,
      hdDelta, _hdeltaD, _hdeltaMax, _hdeltaPos, hleft, _hedge, _hdensity⟩ :=
    PRSEntry.exists_initial_halfRegular_core_of_maxDegree G d Delta hd
      (by simpa [d] using havg) hmax
  have hdEq : d = 4 * JSGlobalParameters.coreDegree r Delta := by
    simp [d, JSGlobalParameters.coreDegree]
    ring
  have hdeltaCore : delta = JSGlobalParameters.coreDegree r Delta := by
    rw [hdeltaEq, hdEq]
    simpa [nsmul_eq_mul] using
      (smul_ceilDiv (a := (4 : ℕ))
        (b := JSGlobalParameters.coreDegree r Delta) (by omega))
  have hregular : ∀ b : B, H.rightDegree b = delta := by
    intro b
    exact hH.2.2.2 b (by simp)
  have hdich := H.global_degreeBucket_dichotomy r Delta delta hr
    hregular hleft (by rw [hdeltaCore])
  exact ⟨A, B, hA, hB, hcard, hAB, H, delta, hH, hdeltaCore, hleft, hdich⟩

open scoped Classical in
/-- A maximum-degree version of the Janzer--Sudakov forcing statement,
expressed entirely in natural-number arithmetic. -/
def MaxDegreeLogLogForcing (k C : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) (Δ : ℕ),
    4 ≤ Δ → G.maxDegree ≤ Δ →
      C * Nat.log2 (Nat.log2 Δ) * Fintype.card V ≤
        2 * G.edgeFinset.card →
      ContainsRegularSubgraph G k

open scoped Classical in
/-- A convenient per-maximum-degree form of the complete global extraction. -/
def GlobalScaleForcing (k r Delta : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V),
    G.maxDegree ≤ Delta →
      (80 * r ^ 2 * JSGlobalParameters.ell Delta) * Fintype.card V ≤
        2 * G.edgeFinset.card →
      ContainsRegularSubgraph G k

/-- The complete finite JS extraction at one maximum-degree scale. -/
theorem globalScaleForcing_of_exact_parameters
    (k r Cprs Delta : ℕ) (hk : 0 < k)
    (hrLarge : 4 * (k + 1) ≤ r)
    (hMlow : 176 * 2 ^ (256 * Cprs + 2) ≤ r)
    (hMhigh :
      (2080 * (k + 1) * (Nat.clog 2 r + 1)) *
          2 ^ (256 * Cprs + 2) ≤ r)
    (hloss : JSGlobalParameters.incidenceLoss k r Delta ≤
      JSGlobalParameters.ell Delta / 2)
    (hclean : Nat.clog 2 (k ^ (k + 1)) ≤ 5 * r)
    (hcomplete : ∀ {W : Type} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) (A B : Finset W),
      Disjoint (A : Set W) (B : Set W) →
      ∀ (H : BipartiteGraph A B),
        (∀ {a : A} {b : B}, H.Adj a b → G.Adj a.1 b.1) →
        H.IsAlmostRegular 64 →
        2 ^ (256 * Cprs + 2) * H.supportCard ≤ 2 * H.edgeCount →
        ContainsRegularSubgraph G k) :
    GlobalScaleForcing k r Delta := by
  intro V _instV _instNonemptyV G hmax havg
  classical
  have hr : 0 < r := by omega
  obtain ⟨A, B, hA, hB, hcard, hAB, H, delta, hH, hdelta,
      hleft, hdich⟩ :=
    exists_globalCore_degreeBucket_dichotomy G r Delta hr havg hmax
  rcases H.isBipartiteKFree_or_containsRegularSubgraph hAB hH.1 k hk with
    hfree | hdone
  · rcases hdich with hlow | ⟨z, hz, hhigh⟩
    · obtain ⟨Q, hQH, hQreg, hQavg⟩ :=
        H.exists_globalLowRoute_almostRegular r Delta (by omega)
          (by simpa using hcard) hB.to_subtype hlow
      apply hcomplete (W := V) G A B hAB Q (fun h ↦ hH.1 (hQH h)) hQreg
      let M := 2 ^ (256 * Cprs + 2)
      have hscaled : 176 * (M * Q.supportCard) ≤
          176 * (2 * Q.edgeCount) := by
        calc
          176 * (M * Q.supportCard) = (176 * M) * Q.supportCard := by ring
          _ ≤ r * Q.supportCard := by gcongr
          _ ≤ 352 * Q.edgeCount := hQavg
          _ = 176 * (2 * Q.edgeCount) := by ring
      exact Nat.le_of_mul_le_mul_left hscaled (by omega)
    · have hBuniv : (Finset.univ : Finset B).Nonempty := by
        let : Nonempty B := hB.to_subtype
        exact Finset.univ_nonempty
      have hregular : ∀ b : B,
          H.rightDegree b = JSGlobalParameters.coreDegree r Delta := by
        intro b
        rw [← hdelta]
        exact hH.2.2.2 b (by simp)
      obtain ⟨Q, hQH, hQreg, hQavg⟩ :=
        H.exists_globalHighRoute_almostRegular k r Delta z.1 z.2
          (by omega) hrLarge hBuniv hregular (by simpa using hhigh)
          hfree hloss hclean
      apply hcomplete (W := V) G A B hAB Q (fun h ↦ hH.1 (hQH h)) hQreg
      let M := 2 ^ (256 * Cprs + 2)
      let a := 2080 * (k + 1) * (Nat.clog 2 r + 1)
      have ha : 0 < a := by dsimp [a]; positivity
      have hscaled : a * (M * Q.supportCard) ≤ a * (2 * Q.edgeCount) := by
        calc
          a * (M * Q.supportCard) = (a * M) * Q.supportCard := by ring
          _ ≤ r * Q.supportCard := by
            exact Nat.mul_le_mul_right Q.supportCard (by
              simpa [a, M] using hMhigh)
          _ ≤ 4160 * (k + 1) * (Nat.clog 2 r + 1) * Q.edgeCount := hQavg
          _ = a * (2 * Q.edgeCount) := by simp [a]; ring
      exact Nat.le_of_mul_le_mul_left hscaled ha
  · exact hdone

open scoped Classical in
/-- An eventual proof at the exact global scale gives the uniform
maximum-degree statement, including the finitely many smaller values of the
degree parameter. -/
theorem exists_maxDegree_forcing_of_eventually_globalScaleForcing
    {k r : ℕ} (_hr : 0 < r)
    (hglobal : ∀ᶠ Delta : ℕ in Filter.atTop,
      GlobalScaleForcing k r Delta) :
    ∃ C : ℕ, 0 < C ∧ MaxDegreeLogLogForcing k C := by
  rw [Filter.eventually_atTop] at hglobal
  obtain ⟨N, hN⟩ := hglobal
  let C := max (160 * r ^ 2) (N + 1)
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro V _instV _instNonemptyV G Delta hDelta hmax hEdges
  classical
  let LL := Nat.log2 (Nat.log2 Delta)
  change C * LL * Fintype.card V ≤ 2 * G.edgeFinset.card at hEdges
  have hLL : 0 < LL := by
    dsimp [LL]
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    apply Nat.log_pos (by omega)
    exact (Nat.le_log_iff_pow_le (by omega) (by omega : Delta ≠ 0)).2 (by
      simpa using hDelta)
  by_cases hlarge : N ≤ Delta
  · apply hN Delta hlarge G hmax
    have hell : JSGlobalParameters.ell Delta ≤ 2 * LL := by
      simp only [JSGlobalParameters.ell, LL, Nat.log2_eq_log_two]
      simp only [LL, Nat.log2_eq_log_two] at hLL
      omega
    calc
      (80 * r ^ 2 * JSGlobalParameters.ell Delta) * Fintype.card V ≤
          (160 * r ^ 2 * LL) * Fintype.card V := by
        apply Nat.mul_le_mul_right
        calc
          80 * r ^ 2 * JSGlobalParameters.ell Delta ≤
              80 * r ^ 2 * (2 * LL) := Nat.mul_le_mul_left _ hell
          _ = 160 * r ^ 2 * LL := by ring
      _ ≤ (C * LL) * Fintype.card V := by
        gcongr
        exact le_max_left _ _
      _ ≤ 2 * G.edgeFinset.card := hEdges
  · have hDeltaN : Delta < N := by omega
    have hDeltaC : Delta < C := by
      dsimp [C]
      exact hDeltaN.trans_le (Nat.le_add_right N 1 |>.trans (le_max_right _ _))
    have hcard : 0 < Fintype.card V := Fintype.card_pos
    have htwice : 2 * G.edgeFinset.card ≤ Delta * Fintype.card V := by
      rw [← G.sum_degrees_eq_twice_card_edges]
      calc
        ∑ v : V, G.degree v ≤ ∑ _v : V, Delta := by
          exact Finset.sum_le_sum fun v _ ↦ (G.degree_le_maxDegree v).trans hmax
        _ = Fintype.card V * Delta := by simp
        _ = Delta * Fintype.card V := Nat.mul_comm _ _
    have hstrict : Delta * Fintype.card V <
        C * LL * Fintype.card V := by
      apply Nat.mul_lt_mul_of_pos_right _ hcard
      calc
        Delta < C := hDeltaC
        _ = C * 1 := by omega
        _ ≤ C * LL := Nat.mul_le_mul_left C hLL
    exact False.elim ((Nat.not_lt_of_ge (hEdges.trans htwice)) hstrict)

/-- The unconditional maximum-degree form of the Janzer--Sudakov theorem.
All constants are explicit natural numbers chosen after the PRS constant. -/
theorem janzer_sudakov_maxDegree_logLog_forcing
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ MaxDegreeLogLogForcing k C := by
  obtain ⟨Cprs, hCprs, hcomplete⟩ :=
    PRSCompletion.exists_prsConstant_sixtyFourAlmostRegular_subgraph k (by omega)
  let M := 2 ^ (256 * Cprs + 2)
  let A := max (4160 * M * (k + 1)) (Nat.clog 2 (k ^ (k + 1)))
  let r := 2 ^ (2 * A + 2)
  have hM : 0 < M := by dsimp [M]; positivity
  have hAbase : 4160 * M * (k + 1) ≤ A := le_max_left _ _
  have hAclean : Nat.clog 2 (k ^ (k + 1)) ≤ A := le_max_right _ _
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hAbase
  have hr : 0 < r := by dsimp [r]; positivity
  have hAr : A * Nat.log2 r ≤ r := by
    apply PRSCompletion.coeff_log2_le_self_of_pow_threshold A r hA
    exact le_rfl
  have hlogr : 0 < Nat.log2 r := by
    dsimp [r]
    rw [Nat.log2_eq_log_two, Nat.log_pow (by omega : 1 < 2)]
    omega
  have hA_le_r : A ≤ r := by
    calc
      A = A * 1 := by omega
      _ ≤ A * Nat.log2 r := Nat.mul_le_mul_left A hlogr
      _ ≤ r := hAr
  have hrLarge : 4 * (k + 1) ≤ r := by
    apply (show 4 * (k + 1) ≤ A by
      calc
        4 * (k + 1) ≤ 4160 * M * (k + 1) := by
          have : 1 ≤ M := by omega
          nlinarith
        _ ≤ A := hAbase) |>.trans hA_le_r
  have hMlow : 176 * M ≤ r := by
    apply (show 176 * M ≤ A by
      calc
        176 * M ≤ 4160 * M * (k + 1) := by
          have : 1 ≤ k + 1 := by omega
          nlinarith
        _ ≤ A := hAbase) |>.trans hA_le_r
  have hclogR : Nat.clog 2 r = Nat.log2 r := by
    dsimp [r]
    rw [Nat.clog_pow 2 (2 * A + 2) (by omega), Nat.log2_eq_log_two,
      Nat.log_pow (by omega : 1 < 2)]
  have hMhigh :
      (2080 * (k + 1) * (Nat.clog 2 r + 1)) * M ≤ r := by
    have hlogadd : Nat.clog 2 r + 1 ≤ 2 * Nat.log2 r := by
      rw [hclogR]
      omega
    calc
      (2080 * (k + 1) * (Nat.clog 2 r + 1)) * M ≤
          (2080 * (k + 1) * (2 * Nat.log2 r)) * M := by gcongr
      _ = (4160 * M * (k + 1)) * Nat.log2 r := by ring
      _ ≤ A * Nat.log2 r := Nat.mul_le_mul_right _ hAbase
      _ ≤ r := hAr
  have hclean : Nat.clog 2 (k ^ (k + 1)) ≤ 5 * r := by
    calc
      Nat.clog 2 (k ^ (k + 1)) ≤ A := hAclean
      _ ≤ r := hA_le_r
      _ ≤ 5 * r := by omega
  apply exists_maxDegree_forcing_of_eventually_globalScaleForcing hr
  filter_upwards [JSGlobalParameters.eventually_incidenceLoss_le_half k r]
    with Delta hloss
  exact globalScaleForcing_of_exact_parameters k r Cprs Delta (by omega)
    hrLarge (by simpa [M] using hMlow) (by simpa [M] using hMhigh)
    hloss hclean hcomplete

open scoped Classical in
/-- A maximum-degree forcing theorem implies its usual `n`-vertex form.
The coefficient is increased by one only to rule out graphs of maximum
degree at most two; no asymptotic or real-number rounding is used. -/
theorem nVertex_forcing_of_maxDegree_forcing {k C : ℕ} (hC : 0 < C)
    (hforce : MaxDegreeLogLogForcing k C) :
    ∃ C' : ℕ, 0 < C' ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n),
        C' * Nat.log2 (Nat.log2 n) * n ≤ G.edgeFinset.card →
          ContainsRegularSubgraph G k := by
  refine ⟨C + 1, by omega, 4, ?_⟩
  intro n hn G hEdges
  classical
  have hnpos : 0 < n := by omega
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  have hmax_le_n : G.maxDegree ≤ n := by
    simpa only [Fintype.card_fin] using
      (G.maxDegree_lt_card_verts (V := Fin n)).le
  have hlog_mono : Nat.log2 (Nat.log2 G.maxDegree) ≤
      Nat.log2 (Nat.log2 n) := by
    simpa only [Nat.log2_eq_log_two] using
      Nat.log_mono_right (Nat.log_mono_right hmax_le_n)
  by_cases hmax : 4 ≤ G.maxDegree
  · apply hforce (V := Fin n) G G.maxDegree hmax le_rfl
    calc
      C * Nat.log2 (Nat.log2 G.maxDegree) * Fintype.card (Fin n)
          ≤ C * Nat.log2 (Nat.log2 n) * n := by
              simpa only [Fintype.card_fin] using
                Nat.mul_le_mul_right n (Nat.mul_le_mul_left C hlog_mono)
      _ ≤ (C + 1) * Nat.log2 (Nat.log2 n) * n := by
        exact Nat.mul_le_mul_right n
          (Nat.mul_le_mul_right (Nat.log2 (Nat.log2 n)) (Nat.le_add_right C 1))
      _ ≤ 2 * G.edgeFinset.card := hEdges.trans (by omega)
  · have hmax_le_three : G.maxDegree ≤ 3 := by omega
    have htwice_le : 2 * G.edgeFinset.card ≤ 3 * n := by
      rw [← G.sum_degrees_eq_twice_card_edges]
      calc
        ∑ v : Fin n, G.degree v ≤ ∑ _v : Fin n, 3 := by
          exact Finset.sum_le_sum fun v _ ↦ (G.degree_le_maxDegree v).trans hmax_le_three
        _ = n * 3 := by simp
        _ = 3 * n := Nat.mul_comm _ _
    have hlog_pos : 0 < Nat.log2 (Nat.log2 n) := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      apply Nat.log_pos (by omega)
      exact (Nat.le_log_iff_pow_le (by omega) (Nat.ne_of_gt hnpos)).2 (by
        simpa using hn)
    have hthree_n_lt_twice_edges : 3 * n < 2 * G.edgeFinset.card := by
      have : 3 * n < 2 * ((C + 1) * Nat.log2 (Nat.log2 n) * n) := by
        have hcoefficient : 1 < (C + 1) * Nat.log2 (Nat.log2 n) := by
          calc
            1 < C + 1 := by omega
            _ = (C + 1) * 1 := by omega
            _ ≤ (C + 1) * Nat.log2 (Nat.log2 n) :=
              Nat.mul_le_mul_left _ (by omega)
        have hcoefficient_two : 3 < 2 * ((C + 1) * Nat.log2 (Nat.log2 n)) := by
          omega
        simpa only [mul_assoc] using
          Nat.mul_lt_mul_of_pos_right hcoefficient_two hnpos
      exact this.trans_le (Nat.mul_le_mul_left 2 hEdges)
    omega

open scoped Classical in
/-- Existentially quantified interface matching the usual statement of the
maximum-degree theorem. -/
theorem exists_nVertex_forcing_of_exists_maxDegree_forcing {k : ℕ}
    (hforce : ∃ C : ℕ, 0 < C ∧ MaxDegreeLogLogForcing k C) :
    ∃ C' : ℕ, 0 < C' ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n),
        C' * Nat.log2 (Nat.log2 n) * n ≤ G.edgeFinset.card →
          ContainsRegularSubgraph G k := by
  obtain ⟨C, hC, hforce⟩ := hforce
  exact nVertex_forcing_of_maxDegree_forcing hC hforce

open scoped Classical in
/-- Once the graph-level Janzer--Sudakov forcing statement has been proved,
the same constant bounds the literal finite extremal number.  Keeping this
short bridge next to the global extraction prevents a later integration
step from confusing a forcing threshold with the maximum itself. -/
theorem regularExtremalNumber_upper_of_graph_forcing
    (k : ℕ) (hk : 0 < k) {C : ℝ}
    (hforcing : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ G : SimpleGraph (Fin n),
        C * ((n : ℝ) * logLog2 n) ≤ (G.edgeFinset.card : ℝ) →
          ContainsRegularSubgraph G k) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (regularExtremalNumber n k : ℝ) ≤ C * ((n : ℝ) * logLog2 n) := by
  filter_upwards [hforcing] with n hforce
  rw [← regularExtremalGraph_card_edgeFinset n k hk]
  exact le_of_not_ge fun hthreshold ↦
    regularExtremalGraph_isRegularSubgraphFree n k hk (hforce _ hthreshold)

end

end Erdos182
