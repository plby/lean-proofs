/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Algebra.Order.Chebyshev
import ErdosProblems.Erdos207.NormalizedBipartiteMixing

/-!
# A finite second-moment mixing lemma for bipartite relations

This is the Cauchy--Schwarz step behind KSSS equation (5.6).  Degree lower
bounds give the total number of pairs from `S`; a uniform second-moment bound
controls how many of those pairs can concentrate in the complement of `U`.
All numerical slack is exposed as a finite natural-number inequality.
-/

namespace Erdos207

open Finset

/-- The total relation degree of each left vertex lies in `[d, D]`, and the
sum of squared `S`-degrees on the right has the usual degree/codegree upper
bound. -/
def HasBipartiteDegreeSecondMomentBounds
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (d D codegree : ℕ) : Prop :=
  (∀ a, d ≤ (relationNeighborsIn r univ a).card ∧
    (relationNeighborsIn r univ a).card ≤ D) ∧
  ∀ S : Finset A,
    (∑ b : B, (relationPreneighborsIn r S b).card ^ 2) ≤
      D * S.card + codegree * S.card * (S.card - 1)

lemma relationPairsBetween_univ_eq_union_complement
    {A B : Type*} [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (S : Finset A) (U : Finset B) :
    relationPairsBetween r S univ =
      relationPairsBetween r S U ∪
        relationPairsBetween r S (univ \ U) := by
  ext ab
  rcases ab with ⟨a, b⟩
  simp only [mem_relationPairsBetween_iff, mem_univ, true_and, mem_union,
    mem_sdiff]
  tauto

lemma disjoint_relationPairsBetween_complement
    {A B : Type*} [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (S : Finset A) (U : Finset B) :
    Disjoint (relationPairsBetween r S U)
      (relationPairsBetween r S (univ \ U)) := by
  rw [Finset.disjoint_left]
  intro ab habU habC
  exact (mem_sdiff.mp
    (mem_relationPairsBetween_iff r |>.mp habC).2.1).2
      (mem_relationPairsBetween_iff r |>.mp habU).2.1

/-- Exact partition of the total `S`-edge count into `U` and its
complement. -/
lemma card_relationPairsBetween_univ_eq_add_complement
    {A B : Type*} [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (S : Finset A) (U : Finset B) :
    (relationPairsBetween r S univ).card =
      (relationPairsBetween r S U).card +
        (relationPairsBetween r S (univ \ U)).card := by
  rw [relationPairsBetween_univ_eq_union_complement,
    card_union_of_disjoint (disjoint_relationPairsBetween_complement
      r S U)]

/-- Cauchy--Schwarz controls the number of relation-pairs from `S` entering
an arbitrary right set by the global second moment. -/
theorem card_relationPairsBetween_sq_le_secondMoment
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (S : Finset A) (U : Finset B) :
    (relationPairsBetween r S U).card ^ 2 ≤
      U.card * ∑ b : B, (relationPreneighborsIn r S b).card ^ 2 := by
  rw [card_relationPairsBetween_eq_sum_right]
  calc
    (∑ b ∈ U, (relationPreneighborsIn r S b).card) ^ 2 ≤
        U.card * ∑ b ∈ U,
          (relationPreneighborsIn r S b).card ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ U.card * ∑ b : B,
        (relationPreneighborsIn r S b).card ^ 2 := by
      exact Nat.mul_le_mul_left U.card <|
        sum_le_sum_of_subset_of_nonneg (subset_univ U)
          (fun _ _ _ ↦ Nat.zero_le _)

/-- Degree plus second-moment bounds imply normalized rectangle mixing once
the displayed scalar inequality is verified for every tested rectangle.
The inequality is exactly the squared contradiction obtained after applying
Cauchy--Schwarz to the complement of `U`. -/
theorem normalizedLowerMixing_of_degree_secondMoment
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (d D codegree density cutoff : ℕ)
    (hbounds : HasBipartiteDegreeSecondMomentBounds r d D codegree)
    (hscalar : ∀ S : Finset A, ∀ U : Finset B, cutoff < S.card →
      Fintype.card B ^ 2 * (Fintype.card B - U.card) *
          (D * S.card + codegree * S.card * (S.card - 1)) <
        (Fintype.card B * d * S.card -
          density * S.card * U.card) ^ 2) :
    HasNormalizedBipartiteLowerMixing r density cutoff := by
  intro S U hScut
  classical
  let total := (relationPairsBetween r S univ).card
  let inside := (relationPairsBetween r S U).card
  let outside := (relationPairsBetween r S (univ \ U)).card
  have hpartition : total = inside + outside := by
    exact card_relationPairsBetween_univ_eq_add_complement r S U
  have htotal : d * S.card ≤ total := by
    dsimp only [total]
    rw [card_relationPairsBetween_eq_sum_left]
    calc
      d * S.card = ∑ _a ∈ S, d := by simp [mul_comm]
      _ ≤ ∑ a ∈ S, (relationNeighborsIn r univ a).card := by
        apply sum_le_sum
        intro a ha
        exact (hbounds.1 a).1
  have houtsideSq : outside ^ 2 ≤
      (Fintype.card B - U.card) *
        (D * S.card + codegree * S.card * (S.card - 1)) := by
    have hUcard : U.card ≤ Fintype.card B := by
      simpa using U.card_le_univ
    have hcs := card_relationPairsBetween_sq_le_secondMoment
      r S (univ \ U)
    dsimp only [outside]
    calc
      (relationPairsBetween r S (univ \ U)).card ^ 2 ≤
          (univ \ U).card *
            ∑ b : B, (relationPreneighborsIn r S b).card ^ 2 := hcs
      _ ≤ (Fintype.card B - U.card) *
          (D * S.card + codegree * S.card * (S.card - 1)) := by
        rw [card_sdiff_of_subset (subset_univ U)]
        exact Nat.mul_le_mul_left _ (hbounds.2 S)
  by_contra hmix
  have hinsufficient : Fintype.card B * inside <
      density * S.card * U.card := by
    dsimp only [inside]
    omega
  have hgap : Fintype.card B * d * S.card -
      density * S.card * U.card ≤ Fintype.card B * outside := by
    have hscaledTotal : Fintype.card B * d * S.card ≤
        Fintype.card B * total := by
      nlinarith
    apply Nat.sub_le_iff_le_add.mpr
    calc
      Fintype.card B * d * S.card ≤ Fintype.card B * total :=
        hscaledTotal
      _ = Fintype.card B * inside + Fintype.card B * outside := by
        rw [hpartition]
        ring
      _ ≤ density * S.card * U.card +
          Fintype.card B * outside :=
        Nat.add_le_add_right (Nat.le_of_lt hinsufficient) _
      _ = Fintype.card B * outside +
          density * S.card * U.card := by omega
  have hgapSq :
      (Fintype.card B * d * S.card -
        density * S.card * U.card) ^ 2 ≤
      (Fintype.card B * outside) ^ 2 := by
    exact Nat.pow_le_pow_left hgap 2
  have hupper : (Fintype.card B * outside) ^ 2 ≤
      Fintype.card B ^ 2 * (Fintype.card B - U.card) *
        (D * S.card + codegree * S.card * (S.card - 1)) := by
    calc
      (Fintype.card B * outside) ^ 2 =
          Fintype.card B ^ 2 * outside ^ 2 := by ring
      _ ≤ Fintype.card B ^ 2 *
          ((Fintype.card B - U.card) *
            (D * S.card + codegree * S.card * (S.card - 1))) := by
        gcongr
      _ = _ := by ring
  exact (not_lt_of_ge (hgapSq.trans hupper)) (hscalar S U hScut)

end Erdos207
