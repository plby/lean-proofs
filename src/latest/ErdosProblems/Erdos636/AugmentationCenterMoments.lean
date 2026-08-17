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

import ErdosProblems.Erdos636.Augmentation
import ErdosProblems.Erdos636.AugmentationCenterMotion
import ErdosProblems.Erdos636.AugmentationGraphFullIdentity
import ErdosProblems.Erdos636.AugmentationGraphPartial
import ErdosProblems.Erdos636.HalfSample
import ErdosProblems.Erdos636.SliceMoments
import ErdosProblems.Erdos636.SlicePersistence

/-!
# First moments for the canonical augmentation centre

The centre used after the inner exposure contains the literal edge count of
`W ∪ (U₀ \ D)`.  Its part depending only on `U₀ \ D` is common to every
outer switching time.  After this common term is removed, the error in one
raw switch is a linear statistic on the uniform deletion slice.  A raw
switch removes and inserts one vertex, so its coefficient is bounded by one.

This file proves the exact mean identity, a general fixed-slice second moment
bound, the resulting `L¹` estimate for one switch, and the summed raw-path
variation estimate.  The estimates are deliberately stated with an explicit
coefficient bound: an absolute selected-time centre estimate with constant
coefficients would be false for a state containing linearly many vertices.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace AugmentationCenterMoments

open Erdos88.Concentration
open Erdos88.Fourier

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## The state-free canonical centre -/

/-- The deletion-only centre shared by the large and bounded augmentation
branches.  It is independent of the intermediate set `D₁` and of the inner
switching state. -/
def canonicalAugmentationCenter (G : SimpleGraph V) (W U₀ D : Finset V)
    (nZ : ℕ) (wCenter d₀ outerCenter : ℝ) : ℝ :=
  (Erdos88.inducedEdges G (W ∪ (U₀ \ D)) : ℝ) +
    nZ * (wCenter + d₀ - outerCenter / 2)

/-- The part of `canonicalAugmentationCenter` which varies with the outer
state after the common term `e(U₀ \ D)` is removed and expectation is taken.
The final summand is the deterministic contribution of the `nZ` cells. -/
def canonicalAugmentationIdeal (G : SimpleGraph V) (alpha : ℝ)
    (U₀ W : Finset V) (nZ : ℕ) (wCenter d₀ : ℝ) : ℝ :=
  weightedScore G alpha U₀ W + nZ * wCenter + nZ * alpha * d₀

/-- Coefficient of a reservoir vertex in the crossing-edge change from
`W₀` to `W₁`. -/
def crossingIncrementCoeff (G : SimpleGraph V) (W₀ W₁ : Finset V)
    (u : V) : ℝ :=
  ((Erdos88.neighborsIn G u W₁).card : ℝ) -
    (Erdos88.neighborsIn G u W₀).card

/-- The centered deletion statistic attached to a raw outer switch. -/
def rawSwitchError (G : SimpleGraph V) (U₀ W₀ W₁ D : Finset V)
    (d : ℕ) : ℝ :=
  (degreeInto G W₁ D : ℝ) - degreeInto G W₀ D -
    (d : ℝ) / U₀.card *
      ((degreeInto G W₁ U₀ : ℝ) - degreeInto G W₀ U₀)

/-- Removing and inserting at most one vertex makes every crossing
coefficient at most one in absolute value. -/
lemma abs_crossingIncrementCoeff_le_one_of_exchange
    (G : SimpleGraph V) (W₀ W₁ : Finset V)
    (h₀₁ : (W₀ \ W₁).card ≤ 1) (h₁₀ : (W₁ \ W₀).card ≤ 1)
    (u : V) : |crossingIncrementCoeff G W₀ W₁ u| ≤ 1 := by
  let N₀ := Erdos88.neighborsIn G u W₀
  let N₁ := Erdos88.neighborsIn G u W₁
  have hsub₁ : N₁ ⊆ N₀ ∪ (W₁ \ W₀) := by
    intro v hv
    have hv' := Erdos88.mem_neighborsIn.mp hv
    by_cases hv₀ : v ∈ W₀
    · exact Finset.mem_union_left _ (Erdos88.mem_neighborsIn.mpr ⟨hv₀, hv'.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv'.1, hv₀⟩)
  have hsub₀ : N₀ ⊆ N₁ ∪ (W₀ \ W₁) := by
    intro v hv
    have hv' := Erdos88.mem_neighborsIn.mp hv
    by_cases hv₁ : v ∈ W₁
    · exact Finset.mem_union_left _ (Erdos88.mem_neighborsIn.mpr ⟨hv₁, hv'.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv'.1, hv₁⟩)
  have hcard₁ : N₁.card ≤ N₀.card + 1 := by
    calc
      N₁.card ≤ (N₀ ∪ (W₁ \ W₀)).card := Finset.card_le_card hsub₁
      _ ≤ N₀.card + (W₁ \ W₀).card :=
        Finset.card_union_le N₀ (W₁ \ W₀)
      _ ≤ N₀.card + 1 := Nat.add_le_add_left h₁₀ _
  have hcard₀ : N₀.card ≤ N₁.card + 1 := by
    calc
      N₀.card ≤ (N₁ ∪ (W₀ \ W₁)).card := Finset.card_le_card hsub₀
      _ ≤ N₁.card + (W₀ \ W₁).card :=
        Finset.card_union_le N₁ (W₀ \ W₁)
      _ ≤ N₁.card + 1 := Nat.add_le_add_left h₀₁ _
  have hcard₁' : (N₁.card : ℝ) ≤ N₀.card + 1 := by exact_mod_cast hcard₁
  have hcard₀' : (N₀.card : ℝ) ≤ N₁.card + 1 := by exact_mod_cast hcard₀
  rw [crossingIncrementCoeff, abs_le]
  constructor <;> dsimp only [N₀, N₁] at hcard₀' hcard₁' ⊢ <;> linarith

/-- The coefficient sum over a set is exactly the corresponding change in
the graph-theoretic incidence count. -/
lemma sum_crossingIncrementCoeff (G : SimpleGraph V) (W₀ W₁ D : Finset V) :
    (∑ u ∈ D, crossingIncrementCoeff G W₀ W₁ u) =
      (degreeInto G W₁ D : ℝ) - degreeInto G W₀ D := by
  simp only [crossingIncrementCoeff, degreeInto, Nat.cast_sum,
    Finset.sum_sub_distrib]

/-- Crossing the undeleted reservoir is crossing the full reservoir minus
crossing the deletion. -/
lemma crossEdges_sdiff_eq_sub (G : SimpleGraph V)
    (U₀ D W : Finset V) (hDU : D ⊆ U₀) :
    (crossEdges G (U₀ \ D) W : ℝ) =
      crossEdges G U₀ W - crossEdges G D W := by
  have hnat := degreeInto_sdiff_add G W hDU
  simp only [crossEdges] at hnat ⊢
  have hreal : (degreeInto G W (U₀ \ D) : ℝ) + degreeInto G W D =
      degreeInto G W U₀ := by exact_mod_cast hnat
  linarith

/-- Expansion of the canonical centre into its common deletion term, its
outer-state terms, and its cell term. -/
lemma canonicalAugmentationCenter_eq
    (G : SimpleGraph V) (W U₀ D : Finset V) (nZ : ℕ)
    (wCenter d₀ outerCenter : ℝ) (hDU : D ⊆ U₀)
    (hWU : Disjoint W U₀) :
    canonicalAugmentationCenter G W U₀ D nZ wCenter d₀ outerCenter =
      (Erdos88.inducedEdges G (U₀ \ D) : ℝ) +
      Erdos88.inducedEdges G W + crossEdges G U₀ W - crossEdges G D W +
      nZ * (wCenter + d₀ - outerCenter / 2) := by
  have hdisj : Disjoint W (U₀ \ D) := hWU.mono_right Finset.sdiff_subset
  have hedge := inducedEdges_union_of_disjoint G hdisj
  have hinter : (G.interedges W (U₀ \ D)).card =
      crossEdges G (U₀ \ D) W := by
    rw [crossEdges, AugmentationGraphFullIdentity.degreeInto_comm,
      degreeInto_eq_card_interedges]
  rw [canonicalAugmentationCenter, hedge, hinter]
  push_cast
  rw [crossEdges_sdiff_eq_sub G U₀ D W hDU]
  ring

/-- Exact increment comparison between the canonical deletion-dependent
centre and its deterministic ideal.  The common term `e(U₀ \ D)` and all
time-independent cell terms cancel. -/
lemma canonicalIncrement_sub_idealIncrement
    (G : SimpleGraph V) (U₀ D W₀ W₁ : Finset V)
    (nZ d : ℕ) (wCenter₀ wCenter₁ d₀ outerCenter alpha : ℝ)
    (hDU : D ⊆ U₀) (hW₀U : Disjoint W₀ U₀)
    (hW₁U : Disjoint W₁ U₀)
    (halpha : alpha = 1 - (d : ℝ) / U₀.card) :
    (canonicalAugmentationCenter G W₁ U₀ D nZ wCenter₁ d₀ outerCenter -
        canonicalAugmentationCenter G W₀ U₀ D nZ wCenter₀ d₀ outerCenter) -
      (canonicalAugmentationIdeal G alpha U₀ W₁ nZ wCenter₁ d₀ -
        canonicalAugmentationIdeal G alpha U₀ W₀ nZ wCenter₀ d₀) =
      -rawSwitchError G U₀ W₀ W₁ D d := by
  rw [canonicalAugmentationCenter_eq G W₁ U₀ D nZ wCenter₁ d₀ outerCenter
      hDU hW₁U,
    canonicalAugmentationCenter_eq G W₀ U₀ D nZ wCenter₀ d₀ outerCenter
      hDU hW₀U]
  simp only [canonicalAugmentationIdeal, weightedScore, rawSwitchError, crossEdges]
  rw [halpha]
  ring

/-- The same identity in the exact convention of
`OuterSwitchingPath.rawIncrementError`. -/
lemma rawIncrementError_canonical_eq_neg_rawSwitchError
    (G : SimpleGraph V) (U₀ D : Finset V) (W : ℕ → Finset V)
    (nZ d i : ℕ) (wCenter : ℕ → ℝ) (d₀ outerCenter alpha : ℝ)
    (hDU : D ⊆ U₀)
    (hWU : ∀ j, Disjoint (W j) U₀)
    (halpha : alpha = 1 - (d : ℝ) / U₀.card) :
    OuterSwitchingPath.rawIncrementError
        (fun j ↦ canonicalAugmentationCenter G (W j) U₀ D nZ
          (wCenter j) d₀ outerCenter)
        (fun j ↦ canonicalAugmentationIdeal G alpha U₀ (W j) nZ
          (wCenter j) d₀) i =
      -rawSwitchError G U₀ (W (i - 1)) (W i) D d := by
  rw [OuterSwitchingPath.rawIncrementError]
  exact canonicalIncrement_sub_idealIncrement G U₀ D (W (i - 1)) (W i)
    nZ d (wCenter (i - 1)) (wCenter i) d₀ outerCenter alpha hDU
      (hWU (i - 1)) (hWU i) halpha

/-! ## A fixed-slice second moment -/

private lemma card_filter_slice_subset {I : Type*} [Fintype I]
    [DecidableEq I] {s : ℕ} (T : Finset I) (hTs : T.card ≤ s) :
    ((Finset.univ.filter fun S : HalfSample.Slice I s ↦ T ⊆ S.1).card) =
      (Fintype.card I - T.card).choose (s - T.card) := by
  let A := Finset.univ.filter fun S : HalfSample.Slice I s ↦ T ⊆ S.1
  let B := ((Finset.univ : Finset I).powersetCard s).filter (T ⊆ ·)
  have hAB : A.card = B.card := by
    apply Finset.card_bij (fun S _ ↦ S.1)
    · intro S hS
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      simp only [B, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      exact ⟨S.2, hS⟩
    · intro S₁ hS₁ S₂ hS₂ h
      exact Subtype.ext h
    · intro S hS
      simp only [B, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and] at hS
      refine ⟨⟨S, hS.1⟩, ?_, rfl⟩
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hS.2
  rw [hAB]
  simpa using Finset.card_filter_powersetCard_subset T
    (Finset.univ : Finset I) s (Finset.subset_univ T) hTs

private lemma sum_indicator_pair {I : Type*} [Fintype I] [DecidableEq I]
    {s : ℕ} (i j : I) (hpair : ({i, j} : Finset I).card ≤ s) :
    (∑ S : HalfSample.Slice I s,
        if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0) =
      ((Fintype.card I - ({i, j} : Finset I).card).choose
        (s - ({i, j} : Finset I).card) : ℝ) := by
  calc
    (∑ S : HalfSample.Slice I s,
        if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0) =
      ∑ S : HalfSample.Slice I s,
        if ({i, j} : Finset I) ⊆ S.1 then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro S _
          congr 1
          apply propext
          constructor
          · rintro ⟨hi, hj⟩ x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hi
            · exact hj
          · intro h
            exact ⟨h (by simp), h (by simp)⟩
    _ = _ := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      exact_mod_cast card_filter_slice_subset ({i, j} : Finset I) hpair

/-- Exact unnormalised second moment for a coefficient population of sum
zero on a general fixed-cardinality slice. -/
private lemma sum_sliceSum_sq_exact {I : Type*} [Fintype I] [DecidableEq I]
    {s : ℕ} (hs : 2 ≤ s) (a : I → ℝ) (hsum : ∑ i, a i = 0) :
    (∑ S : HalfSample.Slice I s, (HalfSample.sliceSum a S) ^ 2) =
      (((Fintype.card I - 1).choose (s - 1) : ℝ) -
        ((Fintype.card I - 2).choose (s - 2) : ℝ)) *
          ∑ i, (a i) ^ 2 := by
  have hpair (i j : I) : ({i, j} : Finset I).card ≤ s := by
    rcases Finset.card_pair_eq_one_or_two (a := i) (b := j) with h | h <;> omega
  have hcount (i j : I) :
      (∑ S : HalfSample.Slice I s,
          if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0) =
        if i = j then ((Fintype.card I - 1).choose (s - 1) : ℝ)
        else ((Fintype.card I - 2).choose (s - 2) : ℝ) := by
    rw [sum_indicator_pair i j (hpair i j)]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  calc
    (∑ S : HalfSample.Slice I s, (HalfSample.sliceSum a S) ^ 2) =
        ∑ S : HalfSample.Slice I s, ∑ i, ∑ j,
          a i * a j * if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      simp only [HalfSample.sliceSum, pow_two]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      calc
        (∑ i ∈ S.1, ∑ j ∈ S.1, a i * a j) =
            ∑ i ∈ S.1, ∑ j,
              a i * a j * if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ S.1)
          · intro j hj
            have hjS : j ∉ S.1 := (Finset.mem_sdiff.mp hj).2
            simp [hjS]
          · intro j hj
            simp [hi, hj]
        _ = ∑ i, ∑ j,
              a i * a j * if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0 := by
          apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ S.1)
          · intro i hi
            have hiS : i ∉ S.1 := (Finset.mem_sdiff.mp hi).2
            simp [hiS]
          · intro i hi
            rfl
    _ = ∑ i, ∑ j, ∑ S : HalfSample.Slice I s,
          a i * a j * if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, a i * a j *
          (∑ S : HalfSample.Slice I s,
            if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, a i * a j *
        (if i = j then ((Fintype.card I - 1).choose (s - 1) : ℝ)
         else ((Fintype.card I - 2).choose (s - 2) : ℝ)) := by
      simp_rw [hcount]
    _ = (((Fintype.card I - 1).choose (s - 1) : ℝ) -
        ((Fintype.card I - 2).choose (s - 2) : ℝ)) *
          ∑ i, (a i) ^ 2 := by
      let c₁ : ℝ := (Fintype.card I - 1).choose (s - 1)
      let c₂ : ℝ := (Fintype.card I - 2).choose (s - 2)
      have hoff : (∑ i, ∑ j, if i = j then (0 : ℝ) else a i * a j) =
          -(∑ i, (a i) ^ 2) := by
        have htotal : (∑ i, ∑ j, a i * a j) = 0 := by
          calc
            (∑ i, ∑ j, a i * a j) = (∑ i, a i) * (∑ j, a j) := by
              rw [Finset.sum_mul_sum]
            _ = 0 := by rw [hsum]; ring
        have hdiag : (∑ i, ∑ j, if i = j then a i * a j else 0) =
            ∑ i, (a i) ^ 2 := by simp [pow_two]
        have hsplit : (∑ i, ∑ j, a i * a j) =
            (∑ i, (a i) ^ 2) +
              ∑ i, ∑ j, if i = j then (0 : ℝ) else a i * a j := by
          rw [← hdiag, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          by_cases hij : i = j <;> simp [hij]
        linarith
      change (∑ i, ∑ j, a i * a j * (if i = j then c₁ else c₂)) = _
      have hdecomp :
          (∑ i, ∑ j, a i * a j * (if i = j then c₁ else c₂)) =
            c₁ * (∑ i, (a i)^2) + c₂ *
              (∑ i, ∑ j, if i = j then 0 else a i * a j) := by
        calc
          _ = ∑ i, ∑ j,
              ((if i = j then a i * a j else 0) * c₁ +
               (if i = j then 0 else a i * a j) * c₂) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            by_cases hij : i = j <;> simp [hij]
          _ = c₁ * (∑ i, (a i)^2) + c₂ *
              (∑ i, ∑ j, if i = j then 0 else a i * a j) := by
            simp_rw [Finset.sum_add_distrib]
            have hdiag' : (∑ i, ∑ j,
                (if i = j then a i * a j else 0) * c₁) =
                c₁ * ∑ i, (a i)^2 := by
              simp [pow_two, mul_comm]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
            rw [hdiag']
            simp_rw [← Finset.sum_mul]
            ring
      rw [hdecomp, hoff]
      dsimp [c₁, c₂]
      ring

/-- The fixed-cardinality slice exists throughout its natural range. -/
private lemma nonempty_slice {I : Type*} [Fintype I] [DecidableEq I]
    {s : ℕ} (hs : s ≤ Fintype.card I) : Nonempty (HalfSample.Slice I s) := by
  have hs' : s ≤ (Finset.univ : Finset I).card := by simpa using hs
  obtain ⟨S, _hS, hcard⟩ := Finset.exists_subset_card_eq hs'
  exact ⟨⟨S, hcard⟩⟩

/-- A zero-sum coefficient population bounded by `K` has fixed-slice second
moment at most `s K²`.  This is valid for every sampling density. -/
theorem uniformExpectation_sliceSum_sq_le
    {I : Type*} [Fintype I] [DecidableEq I] {s : ℕ}
    (hs : s ≤ Fintype.card I) (a : I → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, |a i| ≤ K) (hsum : ∑ i, a i = 0) :
    letI : Nonempty (HalfSample.Slice I s) := nonempty_slice hs
    uniformExpectation (fun S : HalfSample.Slice I s ↦
      (HalfSample.sliceSum a S) ^ 2) ≤ (s : ℝ) * K ^ 2 := by
  letI : Nonempty (HalfSample.Slice I s) := nonempty_slice hs
  by_cases hs0 : s = 0
  · subst s
    have hzero (S : HalfSample.Slice I 0) : HalfSample.sliceSum a S = 0 := by
      have hcard : S.1.card = 0 := S.2
      rw [HalfSample.sliceSum, Finset.card_eq_zero.mp hcard]
      simp
    simp only [Nat.cast_zero, zero_mul]
    have hfun : (fun S : HalfSample.Slice I 0 ↦
        HalfSample.sliceSum a S ^ 2) = fun _ ↦ 0 := by
      funext S
      rw [hzero S]
      norm_num
    rw [hfun, uniformExpectation_const]
  by_cases hs1 : s = 1
  · subst s
    rw [uniformExpectation]
    have hpoint (S : HalfSample.Slice I 1) :
        (HalfSample.sliceSum a S) ^ 2 ≤ K ^ 2 := by
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp S.2
      simp only [HalfSample.sliceSum, hi, Finset.sum_singleton]
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (a i)) hK).2 (ha i)
    have hsumle := Finset.sum_le_sum
      (fun S (_ : S ∈ (Finset.univ : Finset (HalfSample.Slice I 1))) ↦
        hpoint S)
    have hcardPos : (0 : ℝ) < Fintype.card (HalfSample.Slice I 1) := by
      exact_mod_cast Fintype.card_pos
    rw [div_le_iff₀ hcardPos]
    simpa [mul_comm] using hsumle
  have hs2 : 2 ≤ s := by omega
  rw [uniformExpectation, sum_sliceSum_sq_exact hs2 a hsum]
  rw [Fintype.card_finset_len]
  have hchoosePos : 0 < (Fintype.card I).choose s := Nat.choose_pos hs
  have hc2nonneg :
      (0 : ℝ) ≤ ((Fintype.card I - 2).choose (s - 2) : ℝ) := by positivity
  have hsquares : (∑ i, (a i)^2) ≤ (Fintype.card I : ℝ) * K^2 := by
    calc
      (∑ i, (a i)^2) ≤ ∑ _i : I, K^2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (a i)) hK).2 (ha i)
      _ = (Fintype.card I : ℝ) * K^2 := by simp
  have hcardPos : 0 < Fintype.card I := lt_of_lt_of_le (by omega) hs
  have hc1ratio :
      (((Fintype.card I - 1).choose (s - 1) : ℝ) /
        ((Fintype.card I).choose s : ℝ)) =
        (s : ℝ) / Fintype.card I := by
    have hchoose := Nat.choose_mul (n := Fintype.card I) (k := s) (s := 1)
      (show 0 < s by omega)
    norm_num at hchoose
    have hreal : ((Fintype.card I).choose s : ℝ) * s =
        (Fintype.card I : ℝ) *
          ((Fintype.card I - 1).choose (s - 1) : ℝ) := by
      exact_mod_cast hchoose
    field_simp [Nat.ne_of_gt hchoosePos, Nat.ne_of_gt hcardPos]
    nlinarith
  calc
    ((((Fintype.card I - 1).choose (s - 1) : ℝ) -
        ((Fintype.card I - 2).choose (s - 2) : ℝ)) * ∑ i, (a i)^2) /
        ((Fintype.card I).choose s : ℝ) ≤
      (((Fintype.card I - 1).choose (s - 1) : ℝ) * ∑ i, (a i)^2) /
        ((Fintype.card I).choose s : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (sub_le_self _ hc2nonneg)
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    _ = ((s : ℝ) / Fintype.card I) * ∑ i, (a i)^2 := by
      rw [mul_div_assoc]
      calc
        ((Fintype.card I - 1).choose (s - 1) : ℝ) *
            ((∑ i, a i ^ 2) / ((Fintype.card I).choose s : ℝ)) =
            (((Fintype.card I - 1).choose (s - 1) : ℝ) /
              ((Fintype.card I).choose s : ℝ)) * (∑ i, a i^2) := by ring
        _ = _ := by rw [hc1ratio]
    _ ≤ ((s : ℝ) / Fintype.card I) *
        ((Fintype.card I : ℝ) * K^2) := by
      gcongr
    _ = (s : ℝ) * K^2 := by
      field_simp [Nat.ne_of_gt hcardPos]

/-- Finite Cauchy--Schwarz: an `L²` bound implies the corresponding `L¹`
bound for normalized counting measure. -/
theorem uniformExpectation_abs_le_sqrt_of_sq
    {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (X : Omega → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hsecond : uniformExpectation (fun omega ↦ X omega ^ 2) ≤ v) :
    uniformExpectation (fun omega ↦ |X omega|) ≤ Real.sqrt v := by
  rw [uniformExpectation] at hsecond ⊢
  let N : ℝ := Fintype.card Omega
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Omega)
    (fun _ ↦ (1 : ℝ)) (fun omega ↦ |X omega|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hcs
  have hsquareEq : (∑ omega : Omega, |X omega| ^ 2) =
      ∑ omega : Omega, X omega ^ 2 := by
    apply Finset.sum_congr rfl
    intro omega _
    exact sq_abs (X omega)
  rw [hsquareEq] at hcs
  have hsumSecond : (∑ omega : Omega, X omega ^ 2) ≤ v * N := by
    rw [div_le_iff₀ hN] at hsecond
    simpa [N] using hsecond
  have hsumAbsSq : (∑ omega : Omega, |X omega|) ^ 2 ≤ v * N ^ 2 := by
    calc
      (∑ omega : Omega, |X omega|) ^ 2 ≤
          N * ∑ omega : Omega, X omega ^ 2 := by simpa [N] using hcs
      _ ≤ N * (v * N) := mul_le_mul_of_nonneg_left hsumSecond hN.le
      _ = v * N ^ 2 := by ring
  have hmeanSq : ((∑ omega : Omega, |X omega|) / N) ^ 2 ≤ v := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hN)).2
    simpa [pow_two] using hsumAbsSq
  have hmeanNonneg : 0 ≤ (∑ omega : Omega, |X omega|) / N := by positivity
  exact (sq_le_sq₀ hmeanNonneg (Real.sqrt_nonneg v)).1 (by
    rw [Real.sq_sqrt hv]
    exact hmeanSq)

/-- A coefficient population bounded by `K` has centered fixed-slice first
absolute moment at most `2 K sqrt s`. -/
theorem uniformExpectation_centered_sliceSum_abs_le
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (s : ℕ) (hs : s ≤ Fintype.card I) (a : I → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, |a i| ≤ K) :
    letI : Nonempty (BoolSlice I s) :=
      (Erdos88.Fourier.boolSliceEquivFinsetLen I s).nonempty_congr.mpr
        (nonempty_slice hs)
    uniformExpectation (fun omega : BoolSlice I s ↦
      |AugmentationGraphPartial.sliceSum s a omega -
        (s : ℝ) / Fintype.card I * ∑ i, a i|) ≤
      2 * K * Real.sqrt s := by
  let E := Erdos88.Fourier.boolSliceEquivFinsetLen I s
  letI : Nonempty (HalfSample.Slice I s) := nonempty_slice hs
  letI : Nonempty (BoolSlice I s) := E.nonempty_congr.mpr inferInstance
  let mu : ℝ := (∑ i, a i) / Fintype.card I
  let b : I → ℝ := fun i ↦ a i - mu
  have hcardPos : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hmu : (Fintype.card I : ℝ) * mu = ∑ i, a i := by
    dsimp [mu]
    field_simp
  have hmusmall : |mu| ≤ K := by
    have habsSum : |∑ i, a i| ≤ (Fintype.card I : ℝ) * K := by
      calc
        |∑ i, a i| ≤ ∑ i, |a i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : I, K := Finset.sum_le_sum fun i _ ↦ ha i
        _ = (Fintype.card I : ℝ) * K := by simp
    rw [show mu = (∑ i, a i) / Fintype.card I by rfl,
      abs_div, abs_of_pos hcardPos]
    exact (div_le_iff₀ hcardPos).2 (by simpa [mul_comm] using habsSum)
  have hb : ∀ i, |b i| ≤ 2 * K := by
    intro i
    calc
      |b i| = |a i - mu| := rfl
      _ ≤ |a i| + |mu| := abs_sub _ _
      _ ≤ K + K := add_le_add (ha i) hmusmall
      _ = 2 * K := by ring
  have hbsum : ∑ i, b i = 0 := by
    simp only [b, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ]
    rw [hmu]
    ring
  have hslice (S : HalfSample.Slice I s) :
      HalfSample.sliceSum b S =
        HalfSample.sliceSum a S - (s : ℝ) / Fintype.card I * ∑ i, a i := by
    simp only [HalfSample.sliceSum, b, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, S.2]
    rw [← hmu]
    field_simp
  have hsecond := uniformExpectation_sliceSum_sq_le hs b (2 * K)
    (by positivity) hb hbsum
  have hlone : uniformExpectation
      (fun S : HalfSample.Slice I s ↦ |HalfSample.sliceSum b S|) ≤
      Real.sqrt ((s : ℝ) * (2 * K) ^ 2) :=
    uniformExpectation_abs_le_sqrt_of_sq _ _ (by positivity) hsecond
  have hsqrt : Real.sqrt ((s : ℝ) * (2 * K) ^ 2) =
      2 * K * Real.sqrt s := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity)]
    ring
  rw [hsqrt] at hlone
  have htransport : uniformExpectation (fun omega : BoolSlice I s ↦
      |AugmentationGraphPartial.sliceSum s a omega -
        (s : ℝ) / Fintype.card I * ∑ i, a i|) =
      uniformExpectation
        (fun S : HalfSample.Slice I s ↦ |HalfSample.sliceSum b S|) := by
    let f : HalfSample.Slice I s → ℝ :=
      fun S ↦ |HalfSample.sliceSum b S|
    have hfun : (fun omega : BoolSlice I s ↦
        |AugmentationGraphPartial.sliceSum s a omega -
          (s : ℝ) / Fintype.card I * ∑ i, a i|) = fun omega ↦ f (E omega) := by
      funext omega
      change |HalfSample.sliceSum a (E omega) -
        (s : ℝ) / Fintype.card I * ∑ i, a i| = _
      exact congrArg abs (hslice (E omega)).symm
    rw [hfun]
    exact SlicePersistence.uniformExpectation_equiv E f
  rw [htransport]
  exact hlone

/-! ## One raw switch and its summed variation -/

/-- Exact coefficient representation of the raw switch error. -/
lemma rawSwitchError_eq_sum_coeff
    (G : SimpleGraph V) (U₀ W₀ W₁ D : Finset V) (d : ℕ) :
    rawSwitchError G U₀ W₀ W₁ D d =
      (∑ u ∈ D, crossingIncrementCoeff G W₀ W₁ u) -
        (d : ℝ) / U₀.card *
          ∑ u ∈ U₀, crossingIncrementCoeff G W₀ W₁ u := by
  rw [sum_crossingIncrementCoeff, sum_crossingIncrementCoeff]
  rfl

/-- One raw switch has `L¹` error at most `2 K sqrt d` whenever its
per-reservoir-vertex crossing coefficient is bounded by `K`. -/
theorem uniformExpectation_abs_rawSwitchError_le
    (G : SimpleGraph V) (U₀ W₀ W₁ : Finset V) (d : ℕ)
    (hd : d ≤ U₀.card) (K : ℝ) (hK : 0 ≤ K)
    (hcoeff : ∀ u ∈ U₀, |crossingIncrementCoeff G W₀ W₁ u| ≤ K) :
    letI : Nonempty (BoolSlice U₀ d) :=
      (Erdos88.Fourier.boolSliceEquivFinsetLen U₀ d).nonempty_congr.mpr
        (nonempty_slice (by simpa using hd))
    uniformExpectation (fun omega : BoolSlice U₀ d ↦
      |rawSwitchError G U₀ W₀ W₁
        (Augmentation.boolSliceDeletion U₀ d omega) d|) ≤
      2 * K * Real.sqrt d := by
  letI : Nonempty (BoolSlice U₀ d) :=
    (Erdos88.Fourier.boolSliceEquivFinsetLen U₀ d).nonempty_congr.mpr
      (nonempty_slice (by simpa using hd))
  by_cases hU : U₀.Nonempty
  swap
  · have hUempty : U₀ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U₀
    have hd0 : d = 0 := by simpa using hd
    subst d
    have hfun : (fun omega : BoolSlice (∅ : Finset V) 0 ↦
        |rawSwitchError G ∅ W₀ W₁
          (Augmentation.boolSliceDeletion ∅ 0 omega) 0|) = fun _ ↦ 0 := by
      funext omega
      have hmem := Augmentation.boolSliceDeletion_mem_layer
        (∅ : Finset V) 0 omega
      have hD : Augmentation.boolSliceDeletion ∅ 0 omega = ∅ := by
        simpa [NestedUniform.layer] using hmem
      rw [hD]
      simp [rawSwitchError, degreeInto]
    rw [hfun, uniformExpectation_const]
    positivity
  letI : Nonempty U₀ := by
    obtain ⟨u, hu⟩ := hU
    exact ⟨⟨u, hu⟩⟩
  let a : U₀ → ℝ := fun u ↦ crossingIncrementCoeff G W₀ W₁ u.1
  have ha : ∀ u : U₀, |a u| ≤ K := fun u ↦ hcoeff u u.2
  have hmoment := uniformExpectation_centered_sliceSum_abs_le
    d (by simpa using hd) a K hK ha
  have hpoint (omega : BoolSlice U₀ d) :
      rawSwitchError G U₀ W₀ W₁
          (Augmentation.boolSliceDeletion U₀ d omega) d =
        AugmentationGraphPartial.sliceSum d a omega -
          (d : ℝ) / Fintype.card U₀ * ∑ u, a u := by
    rw [rawSwitchError_eq_sum_coeff]
    have hsample :
        (∑ u ∈ Augmentation.boolSliceDeletion U₀ d omega,
          crossingIncrementCoeff G W₀ W₁ u) =
        ∑ u ∈ SlicePersistence.sampleFinset d omega,
          crossingIncrementCoeff G W₀ W₁ u.1 := by
      change (∑ u ∈ Augmentation.mapSubtypeFinset U₀
          (SlicePersistence.sampleFinset d omega),
          crossingIncrementCoeff G W₀ W₁ u) = _
      rw [Augmentation.mapSubtypeFinset, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro u _
      rfl
    have htotal :
        (∑ u ∈ U₀, crossingIncrementCoeff G W₀ W₁ u) =
          ∑ u : U₀, crossingIncrementCoeff G W₀ W₁ u.1 := by
      exact (Finset.sum_attach U₀
        (fun u ↦ crossingIncrementCoeff G W₀ W₁ u)).symm
    rw [hsample, htotal, Fintype.card_coe]
    rfl
  simpa only [hpoint] using hmoment

/-- One genuine one-vertex exchange has the uniform bound `2 sqrt d`. -/
theorem uniformExpectation_abs_rawSwitchError_le_two_sqrt
    (G : SimpleGraph V) (U₀ W₀ W₁ : Finset V) (d : ℕ)
    (hd : d ≤ U₀.card)
    (h₀₁ : (W₀ \ W₁).card ≤ 1) (h₁₀ : (W₁ \ W₀).card ≤ 1) :
    letI : Nonempty (BoolSlice U₀ d) :=
      (Erdos88.Fourier.boolSliceEquivFinsetLen U₀ d).nonempty_congr.mpr
        (nonempty_slice (by simpa using hd))
    uniformExpectation (fun omega : BoolSlice U₀ d ↦
      |rawSwitchError G U₀ W₀ W₁
        (Augmentation.boolSliceDeletion U₀ d omega) d|) ≤
      2 * Real.sqrt d := by
  simpa using uniformExpectation_abs_rawSwitchError_le
    G U₀ W₀ W₁ d hd 1 (by norm_num)
      (fun u _ ↦ abs_crossingIncrementCoeff_le_one_of_exchange
        G W₀ W₁ h₀₁ h₁₀ u)

/-- Total absolute raw-switch error. -/
def rawVariationError (G : SimpleGraph V) (U₀ : Finset V)
    (W : ℕ → Finset V) (d last : ℕ) (omega : BoolSlice U₀ d) : ℝ :=
  ∑ i ∈ Finset.range last,
    |rawSwitchError G U₀ (W i) (W (i + 1))
      (Augmentation.boolSliceDeletion U₀ d omega) d|

lemma rawVariationError_nonneg (G : SimpleGraph V) (U₀ : Finset V)
    (W : ℕ → Finset V) (d last : ℕ) (omega : BoolSlice U₀ d) :
    0 ≤ rawVariationError G U₀ W d last omega := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Summing the one-switch moment bound gives the exact expectation budget
used by the common-deletion selector. -/
theorem uniformExpectation_rawVariationError_le
    (G : SimpleGraph V) (U₀ : Finset V) (W : ℕ → Finset V)
    (d last : ℕ) (hd : d ≤ U₀.card) (K : ℝ) (hK : 0 ≤ K)
    (hcoeff : ∀ i < last, ∀ u ∈ U₀,
      |crossingIncrementCoeff G (W i) (W (i + 1)) u| ≤ K) :
    letI : Nonempty (BoolSlice U₀ d) :=
      (Erdos88.Fourier.boolSliceEquivFinsetLen U₀ d).nonempty_congr.mpr
        (nonempty_slice (by simpa using hd))
    uniformExpectation (rawVariationError G U₀ W d last) ≤
      last * (2 * K * Real.sqrt d) := by
  letI : Nonempty (BoolSlice U₀ d) :=
    (Erdos88.Fourier.boolSliceEquivFinsetLen U₀ d).nonempty_congr.mpr
      (nonempty_slice (by simpa using hd))
  change uniformExpectation (fun omega ↦
      ∑ i ∈ Finset.range last,
        |rawSwitchError G U₀ (W i) (W (i + 1))
          (Augmentation.boolSliceDeletion U₀ d omega) d|) ≤ _
  rw [AugmentationFull.uniformExpectation_sum]
  calc
    (∑ i ∈ Finset.range last,
      uniformExpectation (fun omega : BoolSlice U₀ d ↦
        |rawSwitchError G U₀ (W i) (W (i + 1))
          (Augmentation.boolSliceDeletion U₀ d omega) d|)) ≤
        ∑ _i ∈ Finset.range last, 2 * K * Real.sqrt d := by
      apply Finset.sum_le_sum
      intro i hi
      exact uniformExpectation_abs_rawSwitchError_le
        G U₀ (W i) (W (i + 1)) d hd K hK
          (hcoeff i (Finset.mem_range.mp hi))
    _ = last * (2 * K * Real.sqrt d) := by simp

/-- The raw path exchanges at most one vertex in each direction, so the
total raw variation has expectation at most `2 last sqrt d`. -/
theorem uniformExpectation_rawVariationError_le_two_mul_sqrt
    (G : SimpleGraph V) (U₀ : Finset V) (W : ℕ → Finset V)
    (d last : ℕ) (hd : d ≤ U₀.card)
    (hexchange : ∀ i < last,
      ((W i \ W (i + 1)).card ≤ 1) ∧
        ((W (i + 1) \ W i).card ≤ 1)) :
    letI : Nonempty (BoolSlice U₀ d) :=
      (Erdos88.Fourier.boolSliceEquivFinsetLen U₀ d).nonempty_congr.mpr
        (nonempty_slice (by simpa using hd))
    uniformExpectation (rawVariationError G U₀ W d last) ≤
      last * (2 * Real.sqrt d) := by
  simpa using uniformExpectation_rawVariationError_le
    G U₀ W d last hd 1 (by norm_num)
      (fun i hi u _ ↦ abs_crossingIncrementCoeff_le_one_of_exchange
        G (W i) (W (i + 1)) (hexchange i hi).1 (hexchange i hi).2 u)

/-- Canonical-centre form of the complete raw `Icc 1 last` error budget.
This is the exact expression consumed by the separated-interval motion
lemmas. -/
theorem uniformExpectation_sum_abs_rawIncrementError_canonical_le
    (G : SimpleGraph V) (U₀ : Finset V) (W : ℕ → Finset V)
    (nZ d last : ℕ) (wCenter : ℕ → ℝ) (d₀ outerCenter alpha : ℝ)
    (hd : d ≤ U₀.card) (hWU : ∀ i, Disjoint (W i) U₀)
    (halpha : alpha = 1 - (d : ℝ) / U₀.card)
    (hexchange : ∀ i < last,
      ((W i \ W (i + 1)).card ≤ 1) ∧
        ((W (i + 1) \ W i).card ≤ 1)) :
    letI : Nonempty (BoolSlice U₀ d) :=
      (Erdos88.Fourier.boolSliceEquivFinsetLen U₀ d).nonempty_congr.mpr
        (nonempty_slice (by simpa using hd))
    uniformExpectation (fun omega : BoolSlice U₀ d ↦
      ∑ i ∈ Finset.Icc 1 last,
        |OuterSwitchingPath.rawIncrementError
          (fun j ↦ canonicalAugmentationCenter G (W j) U₀
            (Augmentation.boolSliceDeletion U₀ d omega) nZ
            (wCenter j) d₀ outerCenter)
          (fun j ↦ canonicalAugmentationIdeal G alpha U₀ (W j) nZ
            (wCenter j) d₀) i|) ≤
      last * (2 * Real.sqrt d) := by
  letI : Nonempty (BoolSlice U₀ d) :=
    (Erdos88.Fourier.boolSliceEquivFinsetLen U₀ d).nonempty_congr.mpr
      (nonempty_slice (by simpa using hd))
  rw [AugmentationFull.uniformExpectation_sum]
  calc
    (∑ i ∈ Finset.Icc 1 last,
      uniformExpectation (fun omega : BoolSlice U₀ d ↦
        |OuterSwitchingPath.rawIncrementError
          (fun j ↦ canonicalAugmentationCenter G (W j) U₀
            (Augmentation.boolSliceDeletion U₀ d omega) nZ
            (wCenter j) d₀ outerCenter)
          (fun j ↦ canonicalAugmentationIdeal G alpha U₀ (W j) nZ
            (wCenter j) d₀) i|)) ≤
        ∑ _i ∈ Finset.Icc 1 last, 2 * Real.sqrt d := by
      apply Finset.sum_le_sum
      intro i hi
      have hiIcc := Finset.mem_Icc.mp hi
      have hpred : i - 1 < last := by omega
      have hpoint (omega : BoolSlice U₀ d) :
          |OuterSwitchingPath.rawIncrementError
            (fun j ↦ canonicalAugmentationCenter G (W j) U₀
              (Augmentation.boolSliceDeletion U₀ d omega) nZ
              (wCenter j) d₀ outerCenter)
            (fun j ↦ canonicalAugmentationIdeal G alpha U₀ (W j) nZ
              (wCenter j) d₀) i| =
            |rawSwitchError G U₀ (W (i - 1)) (W i)
              (Augmentation.boolSliceDeletion U₀ d omega) d| := by
        have hDU : Augmentation.boolSliceDeletion U₀ d omega ⊆ U₀ :=
          (NestedUniform.mem_layer.mp
            (Augmentation.boolSliceDeletion_mem_layer U₀ d omega)).1
        rw [rawIncrementError_canonical_eq_neg_rawSwitchError
          G U₀ (Augmentation.boolSliceDeletion U₀ d omega) W nZ d i
            wCenter d₀ outerCenter alpha
            hDU hWU halpha, abs_neg]
      rw [show (fun omega : BoolSlice U₀ d ↦
          |OuterSwitchingPath.rawIncrementError
            (fun j ↦ canonicalAugmentationCenter G (W j) U₀
              (Augmentation.boolSliceDeletion U₀ d omega) nZ
              (wCenter j) d₀ outerCenter)
            (fun j ↦ canonicalAugmentationIdeal G alpha U₀ (W j) nZ
              (wCenter j) d₀) i|) =
          (fun omega ↦ |rawSwitchError G U₀ (W (i - 1)) (W i)
            (Augmentation.boolSliceDeletion U₀ d omega) d|) by
            funext omega
            exact hpoint omega]
      have hsucc : i - 1 + 1 = i := by omega
      have hex := hexchange (i - 1) hpred
      have hforward : (W (i - 1) \ W i).card ≤ 1 := by
        simpa only [hsucc] using hex.1
      have hbackward : (W i \ W (i - 1)).card ≤ 1 := by
        simpa only [hsucc] using hex.2
      simpa only [hsucc] using
        uniformExpectation_abs_rawSwitchError_le_two_sqrt
          G U₀ (W (i - 1)) (W i) d hd
            hforward hbackward
    _ = last * (2 * Real.sqrt d) := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp

end

end AugmentationCenterMoments
end Erdos636
