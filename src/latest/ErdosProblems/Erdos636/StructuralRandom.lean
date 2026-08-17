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

import ErdosProblems.Erdos636.AntiConcentration
import ErdosProblems.Erdos636.CollisionCounting
import ErdosProblems.Erdos636.SetDiversity
import ErdosProblems.Erdos636.Structural
import ErdosProblems.Erdos636.SlicePersistence
import ErdosProblems.Erdos636.StructuralEndpoint

/-!
# The random degree-separation slice

This file isolates the finite first-exposure argument in Claim 4.7 of
Kwan--Sudakov.  The output is a single fixed-cardinality sample for which
all prescribed bounded-set incidence supports persist and whose degree
collision graph has few edges.  A deterministic pruning then retains a
large set on which every collision degree is small.

The simultaneous-selection theorem is deliberately stated for an arbitrary
finite probability space.  Its numerical hypothesis is exact: persistence
failures are charged `edgeBudget + 1`, so a cost strictly below that number
forces zero failures while retaining the desired collision-edge bound.
-/

open scoped BigOperators

namespace Erdos636.StructuralRandom

open Classical Finset SimpleGraph
open Erdos88.Concentration
open Erdos636.CollisionCounting

universe u v w

noncomputable section

section FiniteSelection

variable {Omega : Type u} [Fintype Omega] [Nonempty Omega]
variable {P : Type v} {I : Type w} [LinearOrder I]

/-- The collision graph of a family of finite-valued random variables. -/
def collisionGraph (I0 : Finset I) {A : Type*} [DecidableEq A]
    (X : I → Omega → A) (omega : Omega) : SimpleGraph {i // i ∈ I0} :=
  SimpleGraph.mk
    (fun i j ↦ i ≠ j ∧ X i omega = X j omega)
    (symm := ⟨by rintro i j ⟨hij, hX⟩; exact ⟨hij.symm, hX.symm⟩⟩)
    (loopless := ⟨by intro i hi; exact hi.1 rfl⟩)

@[simp] lemma collisionGraph_adj (I0 : Finset I) {A : Type*} [DecidableEq A]
    (X : I → Omega → A) (omega : Omega) (i j : {i // i ∈ I0}) :
    (collisionGraph I0 X omega).Adj i j ↔
      i ≠ j ∧ X i omega = X j omega := Iff.rfl

/-- Increasingly oriented collision pairs count the same edges as the
ordinary `SimpleGraph.edgeFinset`. -/
lemma card_edgeFinset_collisionGraph_eq {A : Type*} [DecidableEq A]
    (I0 : Finset I) (X : I → Omega → A) (omega : Omega) :
    (collisionGraph I0 X omega).edgeFinset.card =
      (collisionEdges I0 X omega).card := by
  classical
  let H := collisionGraph I0 X omega
  symm
  apply Finset.card_bij
    (fun p hp ↦ s(⟨p.1, (mem_collisionEdges.mp hp).1⟩,
      ⟨p.2, (mem_collisionEdges.mp hp).2.1⟩))
  · intro p hp
    rw [SimpleGraph.mem_edgeFinset]
    exact H.mem_edgeSet.mpr ⟨by
      intro h
      exact (mem_collisionEdges.mp hp).2.2.1 (congrArg Subtype.val h),
      (mem_collisionEdges.mp hp).2.2.2.2⟩
  · intro p hp q hq heq
    rcases Sym2.eq_iff.mp heq with hsame | hswap
    · apply Prod.ext
      · exact congrArg Subtype.val hsame.1
      · exact congrArg Subtype.val hsame.2
    · have hpLt := (mem_collisionEdges.mp hp).2.2.2.1
      have hqLt := (mem_collisionEdges.mp hq).2.2.2.1
      have hpq : p.1 = q.2 := congrArg Subtype.val hswap.1
      have hqp : p.2 = q.1 := congrArg Subtype.val hswap.2
      have hreverse : q.2 < q.1 := by simpa [hpq, hqp] using hpLt
      exact (lt_asymm hqLt hreverse).elim
  · intro e he
    induction e using Sym2.inductionOn with
    | _ i j =>
        have hij : H.Adj i j := H.mem_edgeSet.mp
          (SimpleGraph.mem_edgeFinset.mp he)
        by_cases hlt : i.1 < j.1
        · refine ⟨(i.1, j.1), mem_collisionEdges.mpr
            ⟨i.2, j.2, fun h ↦ hij.1 (Subtype.ext h), hlt, hij.2⟩, ?_⟩
          rfl
        · have hji : j.1 < i.1 := lt_of_le_of_ne (le_of_not_gt hlt)
            (fun h ↦ hij.1 (Subtype.ext h.symm))
          refine ⟨(j.1, i.1), mem_collisionEdges.mpr
            ⟨j.2, i.2, fun h ↦ hij.1 (Subtype.ext h.symm), hji, hij.2.symm⟩, ?_⟩
          exact Sym2.eq_swap

/-- The retained vertices after pruning all collision degrees above `D`. -/
def lowCollisionSubtype (I0 : Finset I) {A : Type*} [DecidableEq A]
    (X : I → Omega → A) (omega : Omega) (D : ℕ) :
    Finset {i // i ∈ I0} :=
  Finset.univ.filter fun i ↦ (collisionGraph I0 X omega).degree i ≤ D

@[simp] lemma mem_lowCollisionSubtype {I0 : Finset I}
    {A : Type*} [DecidableEq A] {X : I → Omega → A} {omega : Omega}
    {D : ℕ} {i : {i // i ∈ I0}} :
    i ∈ lowCollisionSubtype I0 X omega D ↔
      (collisionGraph I0 X omega).degree i ≤ D := by
  simp [lowCollisionSubtype]

/-- The degree-sum identity shows that pruning above `D` loses at most
`2E/(D+1)` vertices when there are at most `E` collision edges. -/
theorem card_le_lowCollisionSubtype_add_of_edges
    {A : Type*} [DecidableEq A]
    (I0 : Finset I) (X : I → Omega → A) (omega : Omega) (D E : ℕ)
    (hedges : (collisionEdges I0 X omega).card ≤ E) :
    I0.card ≤ (lowCollisionSubtype I0 X omega D).card +
      (2 * E) / (D + 1) := by
  classical
  let H := collisionGraph I0 X omega
  let good : Finset {i // i ∈ I0} := Finset.univ.filter fun i ↦ H.degree i ≤ D
  let bad : Finset {i // i ∈ I0} := Finset.univ.filter fun i ↦ D < H.degree i
  have hbadDegree : bad.card * (D + 1) ≤ ∑ i ∈ bad, H.degree i := by
    calc
      bad.card * (D + 1) = ∑ _i ∈ bad, (D + 1) := by simp
      _ ≤ ∑ i ∈ bad, H.degree i := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.succ_le_iff.mpr (mem_filter.mp hi).2
  have hsum : ∑ i ∈ bad, H.degree i ≤ 2 * E := by
    calc
      ∑ i ∈ bad, H.degree i ≤ ∑ i, H.degree i :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
      _ = 2 * (collisionEdges I0 X omega).card := by
        rw [card_edgeFinset_collisionGraph_eq]
      _ ≤ 2 * E := Nat.mul_le_mul_left 2 hedges
  have hbad : bad.card ≤ (2 * E) / (D + 1) := by
    exact (Nat.le_div_iff_mul_le (by omega)).2 (hbadDegree.trans hsum)
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro i hiG hiB
    exact (not_lt_of_ge (mem_filter.mp hiG).2) (mem_filter.mp hiB).2
  have hunion : good ∪ bad = Finset.univ := by
    ext i
    simp only [good, bad, mem_union, mem_filter, mem_univ, true_and]
    exact iff_true_intro (le_or_gt (H.degree i) D)
  have hpartition : I0.card = good.card + bad.card := by
    calc
      I0.card = Fintype.card {i // i ∈ I0} := by simp
      _ = (Finset.univ : Finset {i // i ∈ I0}).card := by simp
      _ = (good ∪ bad).card := by rw [hunion]
      _ = good.card + bad.card := Finset.card_union_of_disjoint hdisj
  change I0.card ≤ good.card + (2 * E) / (D + 1)
  omega

/-- A collision-degree bound gives the corresponding bound on every value
fibre inside the retained set.  The extra one is the chosen vertex itself. -/
theorem card_filter_value_le_degree_add_one
    {A : Type*} [DecidableEq A]
    (I0 : Finset I) (X : I → Omega → A) (omega : Omega)
    (W : Finset {i // i ∈ I0}) (D : ℕ)
    (hdegree : ∀ i ∈ W,
      (collisionGraph I0 X omega).degree i ≤ D) (z : A) :
    (W.filter fun i : {i // i ∈ I0} ↦ X i.1 omega = z).card ≤ D + 1 := by
  classical
  let Wz : Finset {i // i ∈ I0} :=
    W.filter fun i : {i // i ∈ I0} ↦ X i.1 omega = z
  by_cases hzero : Wz = ∅
  · simp [Wz, hzero]
  · have hnonempty : Wz.Nonempty := Finset.nonempty_iff_ne_empty.mpr hzero
    obtain ⟨i, hi⟩ := hnonempty
    have hiW : i ∈ W := (Finset.mem_filter.mp hi).1
    have hiValue : X i.1 omega = z := (Finset.mem_filter.mp hi).2
    have heraseSubset : Wz.erase i ⊆
        (collisionGraph I0 X omega).neighborFinset i := by
      intro j hj
      rw [SimpleGraph.mem_neighborFinset]
      have hjWz := Finset.mem_of_mem_erase hj
      have hjValue : X j.1 omega = z := (Finset.mem_filter.mp hjWz).2
      refine ⟨?_, ?_⟩
      · exact fun hji ↦ (Finset.ne_of_mem_erase hj) hji.symm
      · rw [hiValue, hjValue]
    calc
      Wz.card = (Wz.erase i).card + 1 :=
        (Finset.card_erase_add_one hi).symm
      _ ≤ (collisionGraph I0 X omega).degree i + 1 := by
        gcongr
        exact Finset.card_le_card heraseSubset
      _ ≤ D + 1 := Nat.add_le_add_right (hdegree i hiW) 1

/-- Exact simultaneous random choice.  `exceptionalPairs` are collision
pairs which are paid for deterministically; every other pair has collision
probability at most `pColl`. -/
theorem exists_noFailure_and_collisionEdges_le
    {A : Type*} [DecidableEq A]
    (tests : Finset P) (fails : P → Omega → Prop)
    (I0 : Finset I) (X : I → Omega → A)
    (exceptionalPairs : Finset (I × I))
    (pPersist pColl : ℝ) (edgeBudget : ℕ)
    (hpColl : 0 ≤ pColl)
    (hfail : ∀ p ∈ tests, uniformProbability (fails p) ≤ pPersist)
    (hexceptional : exceptionalPairs ⊆ possibleEdges I0)
    (hcoll : ∀ i ∈ I0, ∀ j ∈ I0, i ≠ j → i < j →
      (i, j) ∉ exceptionalPairs →
      uniformProbability (fun omega ↦ X i omega = X j omega) ≤ pColl)
    (hbudget :
      (edgeBudget + 1 : ℝ) * tests.card * pPersist +
          exceptionalPairs.card + I0.card.choose 2 * pColl <
        edgeBudget + 1) :
    ∃ omega,
      (∀ p ∈ tests, ¬ fails p omega) ∧
      (collisionEdges I0 X omega).card ≤ edgeBudget := by
  classical
  let cost : Omega → ℝ := fun omega ↦
    (edgeBudget + 1) * eventCount tests fails omega +
      (collisionEdges I0 X omega).card
  have hcollMean : uniformExpectation
      (fun omega ↦ ((collisionEdges I0 X omega).card : ℝ)) ≤
      exceptionalPairs.card + I0.card.choose 2 * pColl := by
    simp_rw [card_collisionEdges_eq_eventCount]
    rw [uniformExpectation_eventCount]
    let goodPairs := (possibleEdges I0) \ exceptionalPairs
    calc
      (∑ ij ∈ possibleEdges I0,
          uniformProbability (fun omega ↦ X ij.1 omega = X ij.2 omega)) =
          (∑ ij ∈ exceptionalPairs,
            uniformProbability (fun omega ↦ X ij.1 omega = X ij.2 omega)) +
          ∑ ij ∈ goodPairs,
            uniformProbability (fun omega ↦ X ij.1 omega = X ij.2 omega) := by
              rw [← Finset.sum_union]
              · congr 1
                exact (Finset.union_sdiff_of_subset hexceptional).symm
              · exact Finset.sdiff_disjoint.symm
      _ ≤ (∑ _ij ∈ exceptionalPairs, (1 : ℝ)) +
          ∑ _ij ∈ goodPairs, pColl := by
            apply add_le_add
            · apply Finset.sum_le_sum
              intro ij hij
              exact uniformProbability_le_one _
            · apply Finset.sum_le_sum
              intro ij hij
              have hp := mem_sdiff.mp hij
              have hm := hp.1
              simp only [possibleEdges, mem_filter, mem_offDiag] at hm
              exact hcoll ij.1 hm.1.1 ij.2 hm.1.2.1 hm.1.2.2 hm.2 hp.2
      _ = (exceptionalPairs.card : ℝ) + goodPairs.card * pColl := by simp
      _ ≤ exceptionalPairs.card + I0.card.choose 2 * pColl := by
            apply add_le_add le_rfl
            apply mul_le_mul_of_nonneg_right _ hpColl
            have hgoodCard : goodPairs.card ≤ (possibleEdges I0).card :=
              Finset.card_le_card Finset.sdiff_subset
            rw [card_possibleEdges] at hgoodCard
            exact_mod_cast hgoodCard
  have hcostMean : uniformExpectation cost ≤
      (edgeBudget + 1 : ℝ) * tests.card * pPersist +
        exceptionalPairs.card + I0.card.choose 2 * pColl := by
    rw [show uniformExpectation cost =
        (edgeBudget + 1) * uniformExpectation
            (fun omega ↦ (eventCount tests fails omega : ℝ)) +
          uniformExpectation
            (fun omega ↦ ((collisionEdges I0 X omega).card : ℝ)) by
      simp only [cost]
      rw [uniformExpectation_add]
      congr 1
      unfold uniformExpectation
      rw [← Finset.mul_sum]
      ring]
    have hf := uniformExpectation_eventCount_le tests fails pPersist hfail
    nlinarith
  have hexistsCost : ∃ omega, cost omega ≤ uniformExpectation cost := by
    have hcard : (0 : ℝ) < Fintype.card Omega := by
      exact_mod_cast Fintype.card_pos
    have hmean : uniformExpectation cost ≤ uniformExpectation cost := le_rfl
    rw [uniformExpectation] at hmean
    have hsum : ∑ omega, cost omega ≤
        ∑ _omega : Omega, uniformExpectation cost := by
      simpa [uniformExpectation, nsmul_eq_mul, mul_comm] using
        (div_le_iff₀ hcard).1 hmean
    obtain ⟨omega, _homega, hle⟩ := Finset.exists_le_of_sum_le
      (s := (Finset.univ : Finset Omega)) (by simp) hsum
    exact ⟨omega, hle⟩
  obtain ⟨omega, hcost⟩ := hexistsCost
  have hcostLt : cost omega < edgeBudget + 1 :=
    hcost.trans_lt (hcostMean.trans_lt hbudget)
  have hfailZero : eventCount tests fails omega = 0 := by
    by_contra hne
    have hone : 1 ≤ eventCount tests fails omega := Nat.one_le_iff_ne_zero.mpr hne
    have hcollNonneg : 0 ≤ ((collisionEdges I0 X omega).card : ℝ) := by positivity
    have : (edgeBudget + 1 : ℝ) ≤ cost omega := by
      dsimp only [cost]
      calc
        (edgeBudget + 1 : ℝ) ≤
            (edgeBudget + 1 : ℝ) * eventCount tests fails omega := by
          apply le_mul_of_one_le_right
          · positivity
          · exact_mod_cast hone
        _ ≤ (edgeBudget + 1 : ℝ) * eventCount tests fails omega +
            (collisionEdges I0 X omega).card := le_add_of_nonneg_right hcollNonneg
    linarith
  have hnofail : ∀ p ∈ tests, ¬ fails p omega := by
    intro p hp hbad
    have : p ∈ tests.filter fun p ↦ fails p omega := mem_filter.mpr ⟨hp, hbad⟩
    have : 0 < eventCount tests fails omega :=
      Finset.card_pos.mpr ⟨p, by simpa [eventCount] using this⟩
    omega
  have hedge : (collisionEdges I0 X omega).card ≤ edgeBudget := by
    have : ((collisionEdges I0 X omega).card : ℝ) < edgeBudget + 1 := by
      dsimp only [cost] at hcostLt
      have hnonneg : 0 ≤ (edgeBudget + 1 : ℝ) * eventCount tests fails omega := by
        positivity
      linarith
    have hnat : (collisionEdges I0 X omega).card < edgeBudget + 1 := by
      exact_mod_cast this
    omega
  exact ⟨omega, hnofail, hedge⟩

/-- Claim-4.7 selection followed by deterministic degree pruning.  The
retained subtype is explicit, every one of its collision degrees is at most
`degreeBudget`, and the exact loss is at most `2 * edgeBudget /
(degreeBudget + 1)`. -/
theorem exists_noFailure_and_many_lowCollision
    {A : Type*} [DecidableEq A]
    (tests : Finset P) (fails : P → Omega → Prop)
    (I0 : Finset I) (X : I → Omega → A)
    (exceptionalPairs : Finset (I × I))
    (pPersist pColl : ℝ) (edgeBudget degreeBudget : ℕ)
    (hpColl : 0 ≤ pColl)
    (hfail : ∀ p ∈ tests, uniformProbability (fails p) ≤ pPersist)
    (hexceptional : exceptionalPairs ⊆ possibleEdges I0)
    (hcoll : ∀ i ∈ I0, ∀ j ∈ I0, i ≠ j → i < j →
      (i, j) ∉ exceptionalPairs →
      uniformProbability (fun omega ↦ X i omega = X j omega) ≤ pColl)
    (hbudget :
      (edgeBudget + 1 : ℝ) * tests.card * pPersist +
          exceptionalPairs.card + I0.card.choose 2 * pColl <
        edgeBudget + 1) :
    ∃ omega, ∃ W : Finset {i // i ∈ I0},
      (∀ p ∈ tests, ¬ fails p omega) ∧
      W = lowCollisionSubtype I0 X omega degreeBudget ∧
      I0.card ≤ W.card + (2 * edgeBudget) / (degreeBudget + 1) ∧
      ∀ i ∈ W, (collisionGraph I0 X omega).degree i ≤ degreeBudget := by
  obtain ⟨omega, hnofail, hedges⟩ :=
    exists_noFailure_and_collisionEdges_le tests fails I0 X exceptionalPairs
      pPersist pColl edgeBudget hpColl hfail hexceptional hcoll hbudget
  let W := lowCollisionSubtype I0 X omega degreeBudget
  refine ⟨omega, W, hnofail, rfl,
    card_le_lowCollisionSubtype_add_of_edges I0 X omega degreeBudget
      edgeBudget hedges, ?_⟩
  intro i hi
  exact mem_lowCollisionSubtype.mp hi

end FiniteSelection

section FixedSliceCollision

open Erdos88.Fourier

variable {J : Type u} [Fintype J] [DecidableEq J]
variable {I : Type v} [LinearOrder I]
variable {P : Type w}

/-- Scalar variance bound for a population taking values in `{-1,0,1}`.
Here `A` and `B` are the multiplicities of `+1` and `-1`, respectively.
If neither signed class can occupy more than a `(1 - eps)` fraction and
their union has density at least `theta`, the centered variance has density
at least `eps * theta`.

Indeed, after multiplying by `m`, the centered sum of squares is
`A (m-A) + B (m-B) + 2AB`. -/
theorem two_signed_classes_variance_density
    {A B m eps theta : ℝ}
    (hm : 0 < m) (heps : 0 ≤ eps) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAmax : A ≤ (1 - eps) * m)
    (hBmax : B ≤ (1 - eps) * m)
    (hsupport : theta * m ≤ A + B) :
    eps * theta * m ≤ A + B - (A - B) ^ 2 / m := by
  have hAm : eps * m ≤ m - A := by linarith
  have hBm : eps * m ≤ m - B := by linarith
  have hAprod : A * (eps * m) ≤ A * (m - A) :=
    mul_le_mul_of_nonneg_left hAm hA
  have hBprod : B * (eps * m) ≤ B * (m - B) :=
    mul_le_mul_of_nonneg_left hBm hB
  have hscale : 0 ≤ eps * m := mul_nonneg heps hm.le
  have hsupportScaled := mul_le_mul_of_nonneg_left hsupport hscale
  have hscaled :
      (eps * theta * m) * m ≤ (A + B) * m - (A - B) ^ 2 := by
    calc
      (eps * theta * m) * m = (eps * m) * (theta * m) := by ring
      _ ≤ (eps * m) * (A + B) := hsupportScaled
      _ = A * (eps * m) + B * (eps * m) := by ring
      _ ≤ A * (m - A) + B * (m - B) := add_le_add hAprod hBprod
      _ ≤ A * (m - A) + B * (m - B) + 2 * A * B := by
        exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hA) hB)
      _ = (A + B) * m - (A - B) ^ 2 := by ring
  rw [show A + B - (A - B) ^ 2 / m =
      ((A + B) * m - (A - B) ^ 2) / m by
        field_simp [ne_of_gt hm] <;> ring]
  exact (le_div_iff₀ hm).2 hscaled

/-- Finite-population form of `two_signed_classes_variance_density`.
The two moment equalities are exactly what one gets from a population with
`A` entries equal to `1`, `B` entries equal to `-1`, and all remaining
entries equal to `0`.  Besides the variance estimate, this packages the
centering identity required by the anti-concentration theorem. -/
theorem signed_class_centered_sum_and_variance
    (a : J → ℤ) (A B eps theta : ℝ)
    (hJ : 0 < (Fintype.card J : ℝ))
    (heps : 0 ≤ eps) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAmax : A ≤ (1 - eps) * (Fintype.card J : ℝ))
    (hBmax : B ≤ (1 - eps) * (Fintype.card J : ℝ))
    (hsupport : theta * (Fintype.card J : ℝ) ≤ A + B)
    (hsum : ∑ u, (a u : ℝ) = A - B)
    (hsq : ∑ u, (a u : ℝ) ^ 2 = A + B) :
    (∑ u, ((a u : ℝ) - (A - B) / Fintype.card J)) = 0 ∧
      eps * theta * (Fintype.card J : ℝ) ≤
        ∑ u, ((a u : ℝ) - (A - B) / Fintype.card J) ^ 2 := by
  let m : ℝ := Fintype.card J
  let mu : ℝ := (A - B) / m
  have hm : 0 < m := by simpa [m] using hJ
  have hmu : mu = (A - B) / m := rfl
  have hcenter : (∑ u, ((a u : ℝ) - mu)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [nsmul_eq_mul]
    change A - B - m * mu = 0
    rw [hmu]
    field_simp [ne_of_gt hm]
    ring
  have hcross : (∑ u, 2 * (a u : ℝ) * mu) = 2 * (A - B) * mu := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]
  have hvarianceIdentity :
      (∑ u, ((a u : ℝ) - mu) ^ 2) = A + B - (A - B) ^ 2 / m := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsq, hcross]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [nsmul_eq_mul, hmu]
    field_simp [ne_of_gt hm]
    ring
  constructor
  · simpa [m, mu] using hcenter
  · rw [show (∑ u, ((a u : ℝ) - (A - B) / Fintype.card J) ^ 2) =
        A + B - (A - B) ^ 2 / (Fintype.card J : ℝ) by
          simpa [m, mu] using hvarianceIdentity]
    exact two_signed_classes_variance_density hJ heps hA hB hAmax hBmax hsupport

section GraphVariance

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The ambient finset encoded by a Boolean-slice point. -/
def sliceFinset (s : ℕ) (omega : BoolSlice V s) : Finset V :=
  boolFunEquivFinset V omega.1

@[simp] lemma card_sliceFinset (s : ℕ) (omega : BoolSlice V s) :
    (sliceFinset s omega).card = s := omega.2

/-- The integer adjacency indicator used for graph degree slices. -/
def adjacencyCoefficient (G : SimpleGraph V) (x u : V) : ℤ :=
  if G.Adj x u then 1 else 0

/-- The adjacency-indicator slice statistic is the ordinary graph degree
into the encoded sample. -/
lemma sliceLinear_adjacencyCoefficient_eq (G : SimpleGraph V) (x : V)
    (s : ℕ) (omega : BoolSlice V s) :
    AntiConcentration.sliceLinear s
        (fun u ↦ (adjacencyCoefficient G x u : ℝ)) omega =
      (Erdos88.neighborsIn G x (sliceFinset s omega)).card := by
  rw [AntiConcentration.sliceLinear, Erdos88.neighborsIn,
    Finset.card_filter]
  rw [Nat.cast_sum]
  push_cast
  symm
  calc
    (∑ u ∈ sliceFinset s omega, (if G.Adj x u then 1 else 0 : ℝ)) =
        ∑ u ∈ sliceFinset s omega,
          (adjacencyCoefficient G x u : ℝ) *
            if omega.1 u then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have homega : omega.1 u = true := by
        simpa [sliceFinset, boolFunEquivFinset] using hu
      by_cases hx : G.Adj x u <;> simp [adjacencyCoefficient, hx, homega]
    _ = ∑ u ∈ (Finset.univ : Finset V),
          (adjacencyCoefficient G x u : ℝ) *
            if omega.1 u then 1 else 0 := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro u _hu huNot
      have homega : omega.1 u = false := by
        cases h : omega.1 u
        · rfl
        · exact (huNot (by
            simpa [sliceFinset, boolFunEquivFinset, h])).elim
      simp [homega]
    _ = ∑ u, (adjacencyCoefficient G x u : ℝ) *
          if omega.1 u then 1 else 0 := by simp

/-- Coordinates contributing `+1` to the difference of two adjacency
indicators. -/
def positiveAdjacencyDiff (G : SimpleGraph V) (x y : V) : Finset V :=
  Finset.univ.filter fun u ↦ G.Adj x u ∧ ¬ G.Adj y u

/-- Coordinates contributing `-1` to the difference of two adjacency
indicators. -/
def negativeAdjacencyDiff (G : SimpleGraph V) (x y : V) : Finset V :=
  Finset.univ.filter fun u ↦ ¬ G.Adj x u ∧ G.Adj y u

lemma adjacencyDiff_sum (G : SimpleGraph V) (x y : V) :
    (∑ u, ((adjacencyCoefficient G x u -
        adjacencyCoefficient G y u : ℤ) : ℝ)) =
      (positiveAdjacencyDiff G x y).card -
        (negativeAdjacencyDiff G x y).card := by
  rw [show (∑ u, ((adjacencyCoefficient G x u -
      adjacencyCoefficient G y u : ℤ) : ℝ)) =
      ∑ u, ((if G.Adj x u ∧ ¬ G.Adj y u then 1 else 0) -
        (if ¬ G.Adj x u ∧ G.Adj y u then 1 else 0) : ℝ) by
    apply Finset.sum_congr rfl
    intro u _hu
    by_cases hx : G.Adj x u <;> by_cases hy : G.Adj y u <;>
      simp [adjacencyCoefficient, hx, hy]]
  rw [Finset.sum_sub_distrib]
  simp [positiveAdjacencyDiff, negativeAdjacencyDiff]

lemma incidence_singleton (G : SimpleGraph V) (x u : V) :
    Erdos636.incidence G {x} u = if G.Adj x u then 1 else 0 := by
  rw [Erdos636.incidence, show
    ({x} : Finset V).filter (fun v ↦ G.Adj v u) =
        if G.Adj x u then {x} else (∅ : Finset V) by
      ext v
      by_cases h : G.Adj x u
      · simp only [h, if_true, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · exact fun hv ↦ hv.1
        · intro hv
          subst v
          exact ⟨rfl, h⟩
      · simp only [h, if_false, Finset.mem_filter, Finset.mem_singleton,
          Finset.notMem_empty, iff_false]
        rintro ⟨rfl, hv⟩
        exact h hv]
  split <;> simp

/-- The squared adjacency-difference coefficients count exactly the
singleton support difference. -/
lemma adjacencyDiff_sq_sum (G : SimpleGraph V) (x y : V) :
    (∑ u, ((adjacencyCoefficient G x u -
        adjacencyCoefficient G y u : ℤ) : ℝ) ^ 2) =
      Erdos636.supportDiffCard G Finset.univ {x} {y} := by
  rw [Erdos636.supportDiffCard, Erdos636.supportDiff]
  simp only [Finset.card_filter, incidence_singleton, Nat.cast_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases hx : G.Adj x u <;> by_cases hy : G.Adj y u <;>
    simp [adjacencyCoefficient, hx, hy]

lemma card_pos_add_neg_eq_support (G : SimpleGraph V) (x y : V) :
    ((positiveAdjacencyDiff G x y).card : ℝ) +
        (negativeAdjacencyDiff G x y).card =
      Erdos636.supportDiffCard G Finset.univ {x} {y} := by
  rw [Erdos636.supportDiffCard, Erdos636.supportDiff]
  simp only [Finset.card_filter, incidence_singleton]
  simp only [positiveAdjacencyDiff, negativeAdjacencyDiff,
    Finset.card_filter]
  rw [Nat.cast_sum, Nat.cast_sum, Nat.cast_sum]
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases hx : G.Adj x u <;> by_cases hy : G.Adj y u <;>
    simp [hx, hy]

lemma positiveAdjacencyDiff_card_le_complement
    (G : SimpleGraph V) (x y : V) :
    (positiveAdjacencyDiff G x y).card ≤
      (Finset.univ \ Erdos88.neighborsIn G y Finset.univ).card := by
  apply Finset.card_le_card
  intro u hu
  rw [Finset.mem_sdiff, Erdos88.mem_neighborsIn]
  exact ⟨Finset.mem_univ u, fun h ↦
    (Finset.mem_filter.mp hu).2.2 h.2⟩

lemma negativeAdjacencyDiff_card_le_complement
    (G : SimpleGraph V) (x y : V) :
    (negativeAdjacencyDiff G x y).card ≤
      (Finset.univ \ Erdos88.neighborsIn G x Finset.univ).card := by
  apply Finset.card_le_card
  intro u hu
  rw [Finset.mem_sdiff, Erdos88.mem_neighborsIn]
  exact ⟨Finset.mem_univ u, fun h ↦
    (Finset.mem_filter.mp hu).2.1 h.2⟩

lemma positiveAdjacencyDiff_card_le_one_sub
    (G : SimpleGraph V) (x y : V) (eps : ℝ)
    (hy : eps * Fintype.card V ≤
      (Erdos88.neighborsIn G y Finset.univ).card) :
    ((positiveAdjacencyDiff G x y).card : ℝ) ≤
      (1 - eps) * Fintype.card V := by
  have hsub := positiveAdjacencyDiff_card_le_complement G x y
  have hcardEq :
      (Finset.univ \ Erdos88.neighborsIn G y Finset.univ).card =
        Fintype.card V -
          (Erdos88.neighborsIn G y Finset.univ).card := by
    rw [Finset.card_sdiff]
    simp
  have hsubReal : ((positiveAdjacencyDiff G x y).card : ℝ) ≤
      (Fintype.card V : ℝ) -
        (Erdos88.neighborsIn G y Finset.univ).card := by
    calc
      ((positiveAdjacencyDiff G x y).card : ℝ) ≤
          ((Finset.univ \
            Erdos88.neighborsIn G y Finset.univ).card : ℕ) := by
        exact_mod_cast hsub
      _ = (Fintype.card V : ℝ) -
          (Erdos88.neighborsIn G y Finset.univ).card := by
        rw [hcardEq, Nat.cast_sub]
        exact Finset.card_le_univ _
  nlinarith

lemma negativeAdjacencyDiff_card_le_one_sub
    (G : SimpleGraph V) (x y : V) (eps : ℝ)
    (hx : eps * Fintype.card V ≤
      (Erdos88.neighborsIn G x Finset.univ).card) :
    ((negativeAdjacencyDiff G x y).card : ℝ) ≤
      (1 - eps) * Fintype.card V := by
  have hsub := negativeAdjacencyDiff_card_le_complement G x y
  have hcardEq :
      (Finset.univ \ Erdos88.neighborsIn G x Finset.univ).card =
        Fintype.card V -
          (Erdos88.neighborsIn G x Finset.univ).card := by
    rw [Finset.card_sdiff]
    simp
  have hsubReal : ((negativeAdjacencyDiff G x y).card : ℝ) ≤
      (Fintype.card V : ℝ) -
        (Erdos88.neighborsIn G x Finset.univ).card := by
    calc
      ((negativeAdjacencyDiff G x y).card : ℝ) ≤
          ((Finset.univ \
            Erdos88.neighborsIn G x Finset.univ).card : ℕ) := by
        exact_mod_cast hsub
      _ = (Fintype.card V : ℝ) -
          (Erdos88.neighborsIn G x Finset.univ).card := by
        rw [hcardEq, Nat.cast_sub]
        exact Finset.card_le_univ _
  nlinarith

/-- Graph-facing centered-variance bridge.  A support lower bound and
nonexceptional endpoint degrees imply the exact hypotheses required by
balanced-slice anti-concentration, with variance density `eps * theta`. -/
theorem adjacencyDiff_centered_sum_and_variance
    (G : SimpleGraph V) (x y : V) (eps theta : ℝ)
    (hV : 0 < (Fintype.card V : ℝ)) (heps : 0 ≤ eps)
    (hx : eps * Fintype.card V ≤
      (Erdos88.neighborsIn G x Finset.univ).card)
    (hy : eps * Fintype.card V ≤
      (Erdos88.neighborsIn G y Finset.univ).card)
    (hsupport : theta * Fintype.card V ≤
      Erdos636.supportDiffCard G Finset.univ {x} {y}) :
    let mu :=
      (((positiveAdjacencyDiff G x y).card : ℝ) -
        (negativeAdjacencyDiff G x y).card) / Fintype.card V
    (∑ u, (((adjacencyCoefficient G x u -
        adjacencyCoefficient G y u : ℤ) : ℝ) - mu)) = 0 ∧
      eps * theta * (Fintype.card V : ℝ) ≤
        ∑ u, (((adjacencyCoefficient G x u -
          adjacencyCoefficient G y u : ℤ) : ℝ) - mu) ^ 2 := by
  dsimp only
  apply signed_class_centered_sum_and_variance
    (fun u ↦ adjacencyCoefficient G x u - adjacencyCoefficient G y u)
    ((positiveAdjacencyDiff G x y).card : ℝ)
    ((negativeAdjacencyDiff G x y).card : ℝ) eps theta hV heps
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (positiveAdjacencyDiff_card_le_one_sub G x y eps hy)
    (negativeAdjacencyDiff_card_le_one_sub G x y eps hx)
  · simpa [card_pos_add_neg_eq_support G x y] using hsupport
  · exact adjacencyDiff_sum G x y
  · calc
      (∑ u, ((adjacencyCoefficient G x u -
          adjacencyCoefficient G y u : ℤ) : ℝ) ^ 2) =
          Erdos636.supportDiffCard G Finset.univ {x} {y} :=
        adjacencyDiff_sq_sum G x y
      _ = ((positiveAdjacencyDiff G x y).card : ℝ) +
          (negativeAdjacencyDiff G x y).card :=
        (card_pos_add_neg_eq_support G x y).symm

section RichGraphPairs

variable [LinearOrder V] [Nonempty V]

/-- Vertices which are neither sparse nor dense into the whole rich graph. -/
def richCore (G : SimpleGraph V) (eps : ℝ) : Finset V :=
  Finset.univ \ Erdos636.strictExceptionalVertices G Finset.univ eps

@[simp] lemma mem_richCore {G : SimpleGraph V} {eps : ℝ} {x : V} :
    x ∈ richCore G eps ↔
      eps * Fintype.card V ≤
          (Erdos88.neighborsIn G x Finset.univ).card ∧
        eps * Fintype.card V ≤
          (Finset.univ \ Erdos88.neighborsIn G x Finset.univ).card := by
  simp only [richCore, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Erdos636.mem_strictExceptionalVertices, not_or, not_lt]
  rfl

/-- The low-support neighbours of one rich-core vertex. -/
def lowSupportNeighbors (G : SimpleGraph V) (I0 : Finset V)
    (x : V) (theta : ℝ) : Finset V :=
  I0.filter fun y ↦ x ≠ y ∧
    (Erdos636.supportDiffCard G Finset.univ {x} {y} : ℝ) <
      theta * Fintype.card V

lemma singleton_subset_commonNeighbors (G : SimpleGraph V) (x : V) :
    Erdos88.neighborsIn G x Finset.univ ⊆
      Erdos88.commonNeighborFinset G {x} := by
  intro u hu
  rw [Erdos88.mem_neighborsIn] at hu
  rw [Erdos88.mem_commonNeighborFinset]
  intro v hv
  simp only [Finset.mem_singleton] at hv
  subst v
  exact hu.2

lemma supportDiffCard_mono_univ (G : SimpleGraph V)
    (A x y : Finset V) :
    Erdos636.supportDiffCard G A x y ≤
      Erdos636.supportDiffCard G Finset.univ x y := by
  apply Finset.card_le_card
  intro u hu
  rw [Erdos636.mem_supportDiff] at hu ⊢
  exact ⟨Finset.mem_univ u, hu.2⟩

/-- For a rich-core vertex, set diversity bounds all other core vertices
whose singleton neighbourhood support is below `theta |V|`. -/
theorem card_lowSupportNeighbors_le
    (G : SimpleGraph V) (delta eps theta : ℝ)
    (hdelta : 0 < delta) (heps : 0 < eps)
    (hdeltaeps : delta ≤ eps)
    (hrich : Erdos636.KwanSudakovRich G delta eps)
    (htheta : theta ≤ eps ^ 2 / 2)
    (x : V) (hx : x ∈ richCore G eps) :
    (lowSupportNeighbors G (richCore G eps) x theta).card ≤
      ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ := by
  let Y := (lowSupportNeighbors G (richCore G eps) x theta).image
    fun y ↦ ({y} : Finset V)
  have hYcard : Y.card =
      (lowSupportNeighbors G (richCore G eps) x theta).card := by
    rw [Finset.card_image_of_injective]
    intro a b h
    simpa using h
  rw [← hYcard]
  apply Erdos636.setDiversity_support
    (Erdos636.correctedRichWithBound_of_kwanSudakovRich
      hdelta heps hrich)
    (W := Erdos88.neighborsIn G x Finset.univ) (x := {x}) (k := 1)
  · calc
      delta * (Fintype.card V : ℝ) ≤ eps * Fintype.card V := by gcongr
      _ ≤ (Erdos88.neighborsIn G x Finset.univ).card :=
        (mem_richCore.mp hx).1
  · omega
  · exact singleton_subset_commonNeighbors G x
  · simp
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    simp
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hvne : x ≠ v := (Finset.mem_filter.mp hv).2.1
    rw [Finset.disjoint_left]
    intro z hzx hzv
    simp only [Finset.mem_singleton] at hzx hzv
    subst z
    subst v
    exact hvne rfl
  · intro y hy z hz hyz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    change Disjoint ({v} : Finset V) {w}
    rw [Finset.disjoint_left]
    intro z hzv hzw
    simp only [Finset.mem_singleton] at hzv hzw
    subst z
    subst w
    exact hyz rfl
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hvlow := (Finset.mem_filter.mp hv).2.2
    have hmono := supportDiffCard_mono_univ G
      (Erdos88.neighborsIn G x Finset.univ) {x} {v}
    have hmonoReal :
        (Erdos636.supportDiffCard G
          (Erdos88.neighborsIn G x Finset.univ) {x} {v} : ℝ) ≤
            Erdos636.supportDiffCard G Finset.univ {x} {v} := by
      exact_mod_cast hmono
    calc
      (Erdos636.supportDiffCard G
          (Erdos88.neighborsIn G x Finset.univ) {x} {v} : ℝ) ≤
          Erdos636.supportDiffCard G Finset.univ {x} {v} := hmonoReal
      _ < theta * Fintype.card V := hvlow
      _ ≤ (eps / 2) *
          (Erdos88.neighborsIn G x Finset.univ).card := by
        have hxdeg := (mem_richCore.mp hx).1
        calc
          theta * (Fintype.card V : ℝ) ≤
              (eps ^ 2 / 2) * Fintype.card V := by gcongr
          _ = (eps / 2) * (eps * Fintype.card V) := by ring
          _ ≤ (eps / 2) *
              (Erdos88.neighborsIn G x Finset.univ).card := by gcongr

/-- Increasingly oriented rich-core pairs which must be paid for because
their singleton support is too small. -/
def richExceptionalPairs (G : SimpleGraph V) (eps theta : ℝ) :
    Finset (V × V) :=
  (richCore G eps).biUnion fun x ↦
    ((lowSupportNeighbors G (richCore G eps) x theta).filter
      fun y ↦ x < y).image fun y ↦ (x, y)

lemma richExceptionalPairs_subset_possibleEdges
    (G : SimpleGraph V) (eps theta : ℝ) :
    richExceptionalPairs G eps theta ⊆ possibleEdges (richCore G eps) := by
  intro p hp
  simp only [richExceptionalPairs, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter] at hp
  obtain ⟨x, hx, y, ⟨hy, hxy⟩, rfl⟩ := hp
  simp only [possibleEdges, Finset.mem_filter, Finset.mem_offDiag]
  exact ⟨⟨hx, (Finset.mem_filter.mp hy).1, ne_of_lt hxy⟩, hxy⟩

lemma not_mem_richExceptionalPairs_support_ge
    (G : SimpleGraph V) (eps theta : ℝ)
    {x y : V} (hx : x ∈ richCore G eps) (hy : y ∈ richCore G eps)
    (hxy : x < y) (hnot : (x, y) ∉ richExceptionalPairs G eps theta) :
    theta * Fintype.card V ≤
      Erdos636.supportDiffCard G Finset.univ {x} {y} := by
  by_contra hlt
  have hylow : y ∈ lowSupportNeighbors G (richCore G eps) x theta := by
    rw [lowSupportNeighbors, Finset.mem_filter]
    exact ⟨hy, ne_of_lt hxy, lt_of_not_ge hlt⟩
  apply hnot
  simp only [richExceptionalPairs, Finset.mem_biUnion]
  refine ⟨x, hx, ?_⟩
  simp only [Finset.mem_image, Finset.mem_filter]
  exact ⟨y, ⟨hylow, hxy⟩, rfl⟩

theorem card_richExceptionalPairs_le
    (G : SimpleGraph V) (delta eps theta : ℝ)
    (hdelta : 0 < delta) (heps : 0 < eps) (hdeltaeps : delta ≤ eps)
    (hrich : Erdos636.KwanSudakovRich G delta eps)
    (htheta : theta ≤ eps ^ 2 / 2) :
    (richExceptionalPairs G eps theta).card ≤
      (richCore G eps).card *
        ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ := by
  let b : ℕ := ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊
  calc
    (richExceptionalPairs G eps theta).card ≤
        ∑ x ∈ richCore G eps,
          ((((lowSupportNeighbors G (richCore G eps) x theta).filter
            fun y ↦ x < y).image fun y ↦ (x, y)).card) :=
      Finset.card_biUnion_le
    _ = ∑ x ∈ richCore G eps,
          ((lowSupportNeighbors G (richCore G eps) x theta).filter
            fun y ↦ x < y).card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.card_image_of_injective]
      intro y z h
      exact congrArg Prod.snd h
    _ ≤ ∑ _x ∈ richCore G eps, b := by
      apply Finset.sum_le_sum
      intro x hx
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (card_lowSupportNeighbors_le G delta eps theta hdelta heps
          hdeltaeps hrich htheta x hx)
    _ = (richCore G eps).card * b := by simp

/-- Richness leaves all but at most the explicit fifth-power exceptional
bound in the rich core. -/
theorem card_le_richCore_add
    (G : SimpleGraph V) (delta eps : ℝ)
    (hrich : Erdos636.KwanSudakovRich G delta eps) (hdelta : delta ≤ 1) :
    Fintype.card V ≤ (richCore G eps).card +
      ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ := by
  have hbadReal := hrich Finset.univ (by
    simpa using mul_le_mul_of_nonneg_right hdelta
      (Nat.cast_nonneg (Fintype.card V)))
  have hbadNat : (Erdos636.strictExceptionalVertices
      G Finset.univ eps).card ≤
      ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ := by
    exact_mod_cast hbadReal.trans (Nat.le_ceil _)
  have hpartition :
      (richCore G eps).card +
          (Erdos636.strictExceptionalVertices G Finset.univ eps).card =
        Fintype.card V := by
    exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  omega

end RichGraphPairs

end GraphVariance

/-- Fixed-slice specialization of the random selection/pruning theorem.
The coefficient population `a i` is the degree-incidence vector attached to
vertex `i`.  For every nonexceptional pair, a centered variance lower bound
feeds directly into the checked Fourier--Esseen estimate.

Persistence tests remain completely general here.  In Claim 4.7 they are
the bounded set-pairs, and `fails p` says that their incidence-difference
support inside the chosen slice fell below its prescribed threshold. -/
theorem exists_fixedSlice_noFailure_and_many_lowCollision_of_variance
    (s : ℕ) [Nonempty (BoolSlice J s)]
    (tests : Finset P) (fails : P → BoolSlice J s → Prop)
    (I0 : Finset I) (a : I → J → ℤ) (mu : I → I → ℝ)
    (exceptionalPairs : Finset (I × I))
    (pPersist c eta : ℝ) (B edgeBudget degreeBudget : ℕ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (heta : 0 < eta)
    (hB : 1 ≤ B) (hJ : 0 < Fintype.card J)
    (hsel : c * Fintype.card J ≤ s)
    (hunsel : c * Fintype.card J ≤ Fintype.card J - s)
    (hfail : ∀ p ∈ tests, uniformProbability (fails p) ≤ pPersist)
    (hexceptional : exceptionalPairs ⊆ possibleEdges I0)
    (hbounded : ∀ i ∈ I0, ∀ j ∈ I0, i ≠ j → i < j →
      (i, j) ∉ exceptionalPairs → ∀ u, |a i u - a j u| ≤ (B : ℤ))
    (hcentered : ∀ i ∈ I0, ∀ j ∈ I0, i ≠ j → i < j →
      (i, j) ∉ exceptionalPairs →
      ∑ u, (((a i u - a j u : ℤ) : ℝ) - mu i j) = 0)
    (hvariance : ∀ i ∈ I0, ∀ j ∈ I0, i ≠ j → i < j →
      (i, j) ∉ exceptionalPairs →
      eta * (Fintype.card J : ℝ) ≤
        ∑ u, (((a i u - a j u : ℤ) : ℝ) - mu i j) ^ 2)
    (hbudget :
      (edgeBudget + 1 : ℝ) * tests.card * pPersist +
          exceptionalPairs.card + I0.card.choose 2 *
            (AntiConcentration.variancePointMassConstant c eta B /
              Real.sqrt (Fintype.card J : ℝ)) <
        edgeBudget + 1) :
    ∃ omega, ∃ W : Finset {i // i ∈ I0},
      (∀ p ∈ tests, ¬ fails p omega) ∧
      W = lowCollisionSubtype I0
        (fun i omega ↦ AntiConcentration.sliceLinear s
          (fun u ↦ (a i u : ℝ)) omega) omega degreeBudget ∧
      I0.card ≤ W.card + (2 * edgeBudget) / (degreeBudget + 1) ∧
      ∀ i ∈ W,
        (collisionGraph I0
          (fun i omega ↦ AntiConcentration.sliceLinear s
            (fun u ↦ (a i u : ℝ)) omega) omega).degree i ≤ degreeBudget := by
  classical
  let X : I → BoolSlice J s → ℝ := fun i omega ↦
    AntiConcentration.sliceLinear s (fun u ↦ (a i u : ℝ)) omega
  let pColl : ℝ := AntiConcentration.variancePointMassConstant c eta B /
    Real.sqrt (Fintype.card J : ℝ)
  have hpColl : 0 ≤ pColl := by
    dsimp only [pColl]
    exact div_nonneg
      (AntiConcentration.variancePointMassConstant_pos hc0 heta (by omega)).le
      (Real.sqrt_nonneg _)
  have hcoll : ∀ i ∈ I0, ∀ j ∈ I0, i ≠ j → i < j →
      (i, j) ∉ exceptionalPairs →
      uniformProbability (fun omega ↦ X i omega = X j omega) ≤ pColl := by
    intro i hi j hj hij hlt hnot
    have hevent : (fun omega ↦ X i omega = X j omega) =
        (fun omega ↦ AntiConcentration.sliceLinear s
          (fun u ↦ ((a i u - a j u : ℤ) : ℝ)) omega = 0) := by
      funext omega
      apply propext
      change
        AntiConcentration.sliceLinear s (fun u ↦ (a i u : ℝ)) omega =
          AntiConcentration.sliceLinear s (fun u ↦ (a j u : ℝ)) omega ↔ _
      have hlinear :
          AntiConcentration.sliceLinear s (fun u ↦ (a i u : ℝ)) omega -
              AntiConcentration.sliceLinear s (fun u ↦ (a j u : ℝ)) omega =
            AntiConcentration.sliceLinear s
              (fun u ↦ ((a i u - a j u : ℤ) : ℝ)) omega := by
        simp only [AntiConcentration.sliceLinear]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro u _hu
        push_cast
        ring
      rw [← sub_eq_zero, hlinear]
    rw [hevent]
    change finProbability (BoolSlice J s)
        (fun omega ↦ AntiConcentration.sliceLinear s
          (fun u ↦ ((a i u - a j u : ℤ) : ℝ)) omega = 0) ≤ pColl
    exact AntiConcentration.slice_point_probability_le_of_integer_variance
      (fun u ↦ a i u - a j u) (mu i j) c eta B s hc0 hc1 heta hB hJ
      (hbounded i hi j hj hij hlt hnot)
      (hcentered i hi j hj hij hlt hnot)
      (hvariance i hi j hj hij hlt hnot) hsel hunsel 0
  simpa only [X, pColl] using
    exists_noFailure_and_many_lowCollision tests fails I0 X exceptionalPairs
      pPersist pColl edgeBudget degreeBudget hpColl hfail hexceptional hcoll hbudget

section GraphFixedSlice

variable {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Graph-facing random-slice selection.  The coefficients are literal
adjacency indicators, so the selected linear statistic is the vertex degree
into `U1 = sliceFinset s omega`.  Off the explicitly paid exceptional pairs,
nonexceptional endpoint degrees and singleton support diversity give variance
density `eps * theta` automatically.

The last conclusion is the ambient degree-fibre bound consumed by the
structural endpoint: every degree value occurs at most `degreeBudget + 1`
times on the retained vertex set. -/
theorem exists_graphSlice_noFailure_and_many_lowCollision
    (G : SimpleGraph V) (s : ℕ) [Nonempty (BoolSlice V s)]
    (tests : Finset P) (fails : P → BoolSlice V s → Prop)
    (I0 : Finset V) (exceptionalPairs : Finset (V × V))
    (pPersist c eps theta : ℝ) (edgeBudget degreeBudget : ℕ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (heps : 0 < eps) (htheta : 0 < theta)
    (hV : 0 < Fintype.card V)
    (hsel : c * Fintype.card V ≤ s)
    (hunsel : c * Fintype.card V ≤ Fintype.card V - s)
    (hfail : ∀ p ∈ tests, uniformProbability (fails p) ≤ pPersist)
    (hexceptional : exceptionalPairs ⊆ possibleEdges I0)
    (hdegree : ∀ i ∈ I0,
      eps * Fintype.card V ≤
        (Erdos88.neighborsIn G i Finset.univ).card)
    (hsupport : ∀ i ∈ I0, ∀ j ∈ I0, i ≠ j → i < j →
      (i, j) ∉ exceptionalPairs →
      theta * Fintype.card V ≤
        Erdos636.supportDiffCard G Finset.univ {i} {j})
    (hbudget :
      (edgeBudget + 1 : ℝ) * tests.card * pPersist +
          exceptionalPairs.card + I0.card.choose 2 *
            (AntiConcentration.variancePointMassConstant
                c (eps * theta) 1 /
              Real.sqrt (Fintype.card V : ℝ)) <
        edgeBudget + 1) :
    ∃ omega : BoolSlice V s, ∃ W : Finset {i // i ∈ I0},
      let U1 := sliceFinset s omega
      let retained := W.image Subtype.val
      let Wambient := retained \ U1
      U1.card = s ∧
      (∀ p ∈ tests, ¬ fails p omega) ∧
      I0.card ≤ W.card + (2 * edgeBudget) / (degreeBudget + 1) ∧
      I0.card ≤ Wambient.card + s +
        (2 * edgeBudget) / (degreeBudget + 1) ∧
      (∀ i ∈ W,
        (collisionGraph I0
          (fun i omega ↦ ((Erdos88.neighborsIn G i
            (sliceFinset s omega)).card : ℝ)) omega).degree i ≤ degreeBudget) ∧
      Wambient ⊆ I0 ∧
      Disjoint Wambient U1 ∧
      (∀ z : ℕ,
        (Wambient.filter fun x ↦
          (Erdos88.neighborsIn G x U1).card = z).card ≤
            degreeBudget + 1) := by
  classical
  let mu : V → V → ℝ := fun i j ↦
    (((positiveAdjacencyDiff G i j).card : ℝ) -
      (negativeAdjacencyDiff G i j).card) / Fintype.card V
  let X : V → BoolSlice V s → ℝ := fun i omega ↦
    AntiConcentration.sliceLinear s
      (fun u ↦ (adjacencyCoefficient G i u : ℝ)) omega
  have hVreal : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hV
  have hbounded : ∀ i ∈ I0, ∀ j ∈ I0, i ≠ j → i < j →
      (i, j) ∉ exceptionalPairs → ∀ u,
      |adjacencyCoefficient G i u - adjacencyCoefficient G j u| ≤ (1 : ℤ) := by
    intro i _hi j _hj _hij _hlt _hnot u
    by_cases hiu : G.Adj i u <;> by_cases hju : G.Adj j u <;>
      simp [adjacencyCoefficient, hiu, hju]
  have hcentered : ∀ i ∈ I0, ∀ j ∈ I0, i ≠ j → i < j →
      (i, j) ∉ exceptionalPairs →
      ∑ u, (((adjacencyCoefficient G i u -
        adjacencyCoefficient G j u : ℤ) : ℝ) - mu i j) = 0 := by
    intro i hi j hj hij hlt hnot
    have hmoment := adjacencyDiff_centered_sum_and_variance
      G i j eps theta hVreal heps.le (hdegree i hi) (hdegree j hj)
      (hsupport i hi j hj hij hlt hnot)
    exact hmoment.1
  have hvariance : ∀ i ∈ I0, ∀ j ∈ I0, i ≠ j → i < j →
      (i, j) ∉ exceptionalPairs →
      eps * theta * (Fintype.card V : ℝ) ≤
        ∑ u, (((adjacencyCoefficient G i u -
          adjacencyCoefficient G j u : ℤ) : ℝ) - mu i j) ^ 2 := by
    intro i hi j hj hij hlt hnot
    have hmoment := adjacencyDiff_centered_sum_and_variance
      G i j eps theta hVreal heps.le (hdegree i hi) (hdegree j hj)
      (hsupport i hi j hj hij hlt hnot)
    exact hmoment.2
  obtain ⟨omega, W, hnofail, _hWdef, hWcard, hWdegree⟩ :=
    exists_fixedSlice_noFailure_and_many_lowCollision_of_variance
      s tests fails I0 (adjacencyCoefficient G) mu exceptionalPairs
      pPersist c (eps * theta) 1 edgeBudget degreeBudget hc0 hc1
      (mul_pos heps htheta) (by norm_num) hV hsel hunsel hfail
      hexceptional hbounded hcentered hvariance hbudget
  have hstatistic :
      (fun i omega ↦ AntiConcentration.sliceLinear s
        (fun u ↦ (adjacencyCoefficient G i u : ℝ)) omega) =
      (fun i omega ↦ ((Erdos88.neighborsIn G i
        (sliceFinset s omega)).card : ℝ)) := by
    funext i omega
    exact sliceLinear_adjacencyCoefficient_eq G i s omega
  rw [hstatistic] at hWdegree
  have hretainedCard : (W.image Subtype.val).card = W.card := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
  have hretainedSplit : (W.image Subtype.val).card ≤
      ((W.image Subtype.val) \ sliceFinset s omega).card +
        (sliceFinset s omega).card := by
    calc
      (W.image Subtype.val).card ≤
          (((W.image Subtype.val) \ sliceFinset s omega) ∪
            sliceFinset s omega).card := by
        apply Finset.card_le_card
        intro x hx
        by_cases hxu : x ∈ sliceFinset s omega
        · exact Finset.mem_union_right _ hxu
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxu⟩)
      _ ≤ ((W.image Subtype.val) \ sliceFinset s omega).card +
          (sliceFinset s omega).card := Finset.card_union_le _ _
  have houtsideCard : I0.card ≤
      ((W.image Subtype.val) \ sliceFinset s omega).card + s +
        (2 * edgeBudget) / (degreeBudget + 1) := by
    rw [card_sliceFinset] at hretainedSplit
    omega
  refine ⟨omega, W, card_sliceFinset s omega, hnofail, hWcard,
    houtsideCard, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact hWdegree i hi
  · intro x hx
    obtain ⟨i, hiW, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hx).1
    exact i.2
  · exact disjoint_sdiff_self_left
  · intro z
    have hfiberSubtype :
        (W.filter fun i ↦
          (Erdos88.neighborsIn G i.1 (sliceFinset s omega)).card = z).card ≤
            degreeBudget + 1 := by
      let Xdegree : V → BoolSlice V s → ℝ := fun i omega ↦
        ((Erdos88.neighborsIn G i (sliceFinset s omega)).card : ℝ)
      have hdegree' : ∀ i ∈ W,
          (collisionGraph I0 Xdegree omega).degree i ≤ degreeBudget := by
        intro i hi
        exact hWdegree i hi
      have hreal := card_filter_value_le_degree_add_one
        I0 Xdegree omega W degreeBudget hdegree' (z : ℝ)
      have heq : (W.filter fun i : {i // i ∈ I0} ↦
          (Erdos88.neighborsIn G i.1 (sliceFinset s omega)).card = z) =
          W.filter fun i : {i // i ∈ I0} ↦
            Xdegree i.1 omega = (z : ℝ) := by
        ext i
        simp only [Finset.mem_filter]
        constructor
        · intro h
          refine ⟨h.1, ?_⟩
          dsimp only [Xdegree]
          exact_mod_cast h.2
        · intro h
          refine ⟨h.1, ?_⟩
          dsimp only [Xdegree] at h
          exact_mod_cast h.2
      rw [heq]
      exact hreal
    have himageFilter :
        (W.image Subtype.val).filter (fun x ↦
          (Erdos88.neighborsIn G x (sliceFinset s omega)).card = z) =
        (W.filter fun i ↦
          (Erdos88.neighborsIn G i.1 (sliceFinset s omega)).card = z).image
            Subtype.val := by
      ext x
      simp
    have hfullFiber :
        ((W.image Subtype.val).filter fun x ↦
          (Erdos88.neighborsIn G x (sliceFinset s omega)).card = z).card ≤
            degreeBudget + 1 := by
      rw [himageFilter, Finset.card_image_of_injective _ Subtype.val_injective]
      exact hfiberSubtype
    apply (Finset.card_le_card ?_).trans hfullFiber
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨(Finset.mem_sdiff.mp hx.1).1, hx.2⟩

/-- Finite Kwan--Sudakov-rich specialization of the random slice claim.
All bounded support tests are instantiated with the checked hypergeometric
failure predicate, while the only exceptional collision pairs are the
richness-controlled low-support pairs.  The budget charges their coarse
`|core| * ceil(|V|^(1/5))` upper bound.

The output reservoir is disjoint from the retained ambient vertex set,
persists every bounded support test in the exact endpoint interface, and has
all degree fibres bounded by `degreeBudget + 1`. -/
theorem exists_rich_graphSlice_supportPersistent_lowCollision
    [Nonempty V]
    (G : SimpleGraph V) (delta eps theta : ℝ)
    (s K : ℕ) [Nonempty (BoolSlice V s)]
    (global localThreshold c : ℝ) (edgeBudget degreeBudget : ℕ)
    (hdelta : 0 < delta) (heps : 0 < eps)
    (hdeltaeps : delta ≤ eps) (hdelta1 : delta ≤ 1)
    (htheta0 : 0 < theta) (htheta : theta ≤ eps ^ 2 / 2)
    (hrich : Erdos636.KwanSudakovRich G delta eps)
    (hV : 0 < Fintype.card V)
    (hell : s ≤ Fintype.card V) (hspos : 0 < s)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hsel : c * Fintype.card V ≤ s)
    (hunsel : c * Fintype.card V ≤ Fintype.card V - s)
    (hlocal : 0 ≤ localThreshold)
    (hmargin : ∀ p ∈ Erdos636.supportPersistenceTests G K global,
      2 * localThreshold ≤ (s : ℝ) / Fintype.card V *
        Erdos636.supportDiffCard G Finset.univ p.1 p.2)
    (hbudget :
      (edgeBudget + 1 : ℝ) *
          (Erdos636.supportPersistenceTests G K global).card *
            (2 * Real.exp (-localThreshold ^ 2 / (8 * s))) +
        (richCore G eps).card *
          ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ +
        (richCore G eps).card.choose 2 *
          (AntiConcentration.variancePointMassConstant
              c (eps * theta) 1 /
            Real.sqrt (Fintype.card V : ℝ)) <
        edgeBudget + 1) :
    ∃ omega : BoolSlice V s,
      ∃ W : Finset {i // i ∈ richCore G eps},
        let U1 := sliceFinset s omega
        let retained := W.image Subtype.val
        let Wambient := retained \ U1
        U1.card = s ∧
        Erdos636.StructuralEndpoint.SupportPersists
          G U1 K global localThreshold ∧
        (∀ p ∈ Erdos636.supportPersistenceTests G K global,
          ¬ Erdos636.SlicePersistence.intersectionCount
            (Erdos636.supportDiff G Finset.univ p.1 p.2) s omega <
              localThreshold) ∧
        (richCore G eps).card ≤ W.card +
          (2 * edgeBudget) / (degreeBudget + 1) ∧
        (richCore G eps).card ≤ Wambient.card + s +
          (2 * edgeBudget) / (degreeBudget + 1) ∧
        Fintype.card V ≤ Wambient.card + s +
          (2 * edgeBudget) / (degreeBudget + 1) +
          ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ ∧
        Wambient ⊆ richCore G eps ∧
        Disjoint Wambient U1 ∧
        (∀ z : ℕ,
          (Wambient.filter fun x ↦
            (Erdos88.neighborsIn G x U1).card = z).card ≤
              degreeBudget + 1) := by
  classical
  let tests := Erdos636.supportPersistenceTests G K global
  let fails : (Finset V × Finset V) → BoolSlice V s → Prop :=
    fun p omega ↦ Erdos636.SlicePersistence.intersectionCount
      (Erdos636.supportDiff G Finset.univ p.1 p.2) s omega < localThreshold
  let exceptionalPairs := richExceptionalPairs G eps theta
  let pPersist : ℝ := 2 * Real.exp (-localThreshold ^ 2 / (8 * s))
  have hfail : ∀ p ∈ tests,
      uniformProbability (fails p) ≤ pPersist := by
    intro p hp
    let D := Erdos636.supportDiff G Finset.univ p.1 p.2
    dsimp only [fails, pPersist]
    apply Erdos636.SlicePersistence.support_persistence_failure_probability_le
      D s hell hspos localThreshold hlocal
    rw [Erdos636.SlicePersistence.uniformExpectation_intersectionCount
      D s hell hV]
    simpa [D, Erdos636.supportDiffCard] using hmargin p hp
  have hexceptional : exceptionalPairs ⊆ possibleEdges (richCore G eps) :=
    richExceptionalPairs_subset_possibleEdges G eps theta
  have hdegree : ∀ i ∈ richCore G eps,
      eps * Fintype.card V ≤
        (Erdos88.neighborsIn G i Finset.univ).card := by
    intro i hi
    exact (mem_richCore.mp hi).1
  have hsupport : ∀ i ∈ richCore G eps, ∀ j ∈ richCore G eps,
      i ≠ j → i < j → (i, j) ∉ exceptionalPairs →
      theta * Fintype.card V ≤
        Erdos636.supportDiffCard G Finset.univ {i} {j} := by
    intro i hi j hj _hij hlt hnot
    exact not_mem_richExceptionalPairs_support_ge
      G eps theta hi hj hlt hnot
  have hexceptionalCard : exceptionalPairs.card ≤
      (richCore G eps).card *
        ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ :=
    card_richExceptionalPairs_le G delta eps theta hdelta heps
      hdeltaeps hrich htheta
  have hbudgetExact :
      (edgeBudget + 1 : ℝ) * tests.card * pPersist +
          exceptionalPairs.card + (richCore G eps).card.choose 2 *
            (AntiConcentration.variancePointMassConstant
                c (eps * theta) 1 /
              Real.sqrt (Fintype.card V : ℝ)) <
        edgeBudget + 1 := by
    apply lt_of_le_of_lt _ hbudget
    dsimp only [tests, pPersist]
    gcongr
    exact_mod_cast hexceptionalCard
  obtain ⟨omega, W, hUcard, hnofail, hWcard, houtsideCard,
      _hdegree, hWsub, hdisjoint, hfiber⟩ :=
    exists_graphSlice_noFailure_and_many_lowCollision
      G s tests fails (richCore G eps) exceptionalPairs pPersist c eps theta
      edgeBudget degreeBudget hc0 hc1 heps htheta0 hV hsel hunsel hfail
      hexceptional hdegree hsupport hbudgetExact
  have hpersist : Erdos636.StructuralEndpoint.SupportPersists
      G (sliceFinset s omega) K global localThreshold := by
    intro X Y hX hY hglobal
    have hp : (X, Y) ∈ tests := by
      exact Erdos636.mem_supportPersistenceTests.mpr ⟨hX, hY, hglobal⟩
    have h := hnofail (X, Y) hp
    have hsupport : localThreshold ≤
        (Erdos636.supportDiffCard G (sliceFinset s omega) X Y : ℝ) := by
      have hinter : Erdos636.SlicePersistence.intersectionCount
          (Erdos636.supportDiff G Finset.univ X Y) s omega =
          (Erdos636.supportDiffCard G (sliceFinset s omega) X Y : ℝ) := by
        simp [Erdos636.SlicePersistence.intersectionCount,
          Erdos636.SlicePersistence.sampleFinset, sliceFinset,
          Erdos636.supportDiffCard, Erdos636.supportDiff,
          Finset.inter_filter]
      simpa [fails, not_lt, hinter] using h
    exact hsupport.trans (by
      exact_mod_cast Erdos636.supportDiffCard_le_incidenceDiffMass
        G (sliceFinset s omega) X Y)
  have hcore : Fintype.card V ≤ (richCore G eps).card +
      ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ :=
    card_le_richCore_add G delta eps hrich hdelta1
  have hambientCard : Fintype.card V ≤
      ((W.image Subtype.val) \ sliceFinset s omega).card + s +
        (2 * edgeBudget) / (degreeBudget + 1) +
        ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ := by
    omega
  exact ⟨omega, W, hUcard, hpersist, hnofail, hWcard, houtsideCard,
    hambientCard, hWsub, hdisjoint, hfiber⟩

end GraphFixedSlice

end FixedSliceCollision

end

end Erdos636.StructuralRandom
