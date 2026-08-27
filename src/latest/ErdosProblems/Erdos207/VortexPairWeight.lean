/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairSharingCount
import ErdosProblems.Erdos207.VortexWeight

/-!
# Pair-star weights in a vortex

At a fixed vortex level, triples containing a prescribed pair inject into
the vertices of that level.  The factor `1 / |U_i|` in the vortex weight
therefore cancels this choice.  Summing over levels and over the three pairs
of a triangle gives the bound needed for order-four rooted threats.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The unique element of a one-element finset. -/
def pairSingletonElement {V : Type*} (s : SingletonOn V) : V :=
  (card_eq_one.mp s.2).choose

@[simp]
lemma singleton_eq_pairSingletonElement {V : Type*} (s : SingletonOn V) :
    s.1 = {pairSingletonElement s} :=
  (card_eq_one.mp s.2).choose_spec

/-- Triples containing `P` whose deepest vortex level is exactly `i`. -/
abbrev VortexPairLevelTriple
    (V : Type*) [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (P : Finset V) (i : Fin (ell + 1)) :=
  {T : TripleOn V // T ∈
    (universeTriplesContainingPair P).filter fun T ↦ W.level T = i}

/-- The third vertex embeds a fixed-pair, fixed-level triple into `U_i`. -/
def vortexPairLevelThirdVertex
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (P : Finset V) (hP : P.card = 2)
    (i : Fin (ell + 1)) (T : VortexPairLevelTriple V W P i) :
    {x : V // x ∈ W.U i} := by
  have hT := mem_filter.mp T.2
  let T' : universeTriplesContainingPair P := ⟨T.1, hT.1⟩
  let x := pairSingletonElement (eraseContainingPair P hP T')
  have hxDiff : x ∈ T.1.1 \ P := by
    have heq := singleton_eq_pairSingletonElement
      (eraseContainingPair P hP T')
    change x ∈ (eraseContainingPair P hP T').1
    rw [heq]
    simp [x]
  refine ⟨x, ?_⟩
  rw [← hT.2]
  exact W.subset_at_level T.1 (mem_sdiff.mp hxDiff).1

lemma vortexPairLevelThirdVertex_injective
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (P : Finset V) (hP : P.card = 2)
    (i : Fin (ell + 1)) :
    Function.Injective (vortexPairLevelThirdVertex W P hP i) := by
  intro T U hTU
  let T' : universeTriplesContainingPair P :=
    ⟨T.1, (mem_filter.mp T.2).1⟩
  let U' : universeTriplesContainingPair P :=
    ⟨U.1, (mem_filter.mp U.2).1⟩
  have hval : pairSingletonElement (eraseContainingPair P hP T') =
      pairSingletonElement (eraseContainingPair P hP U') :=
    congrArg Subtype.val hTU
  have herase : eraseContainingPair P hP T' =
      eraseContainingPair P hP U' := by
    apply Subtype.ext
    rw [singleton_eq_pairSingletonElement,
      singleton_eq_pairSingletonElement, hval]
  have hT'U' := eraseContainingPair_injective P hP herase
  apply Subtype.ext
  exact congrArg (fun X : universeTriplesContainingPair P ↦ X.1) hT'U'

/-- At one level, at most `|U_i|` triples contain a prescribed pair. -/
theorem card_vortexPairLevelTriple_le
    (V : Type*) [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (P : Finset V) (hP : P.card = 2)
    (i : Fin (ell + 1)) :
    Fintype.card (VortexPairLevelTriple V W P i) ≤ (W.U i).card := by
  calc
    Fintype.card (VortexPairLevelTriple V W P i) ≤
        Fintype.card {x : V // x ∈ W.U i} :=
      Fintype.card_le_of_injective (vortexPairLevelThirdVertex W P hP i)
        (vortexPairLevelThirdVertex_injective W P hP i)
    _ = (W.U i).card := Fintype.card_coe _

/-- The vortex weight of a fixed-pair star at one level is at most `c`. -/
theorem sum_vortexTripleWeight_containingPair_level_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (c : ℝ≥0) (P : Finset V) (hP : P.card = 2)
    (i : Fin (ell + 1)) :
    ∑ T ∈ universeTriplesContainingPair P with W.level T = i,
        vortexTripleWeight W c T ≤ c := by
  let S := (universeTriplesContainingPair P).filter fun T ↦ W.level T = i
  by_cases hUi : (W.U i).card = 0
  · have hS : S = ∅ := by
      apply card_eq_zero.mp
      have hcard : S.card ≤ (W.U i).card := by
        simpa only [S, Fintype.card_coe] using
          card_vortexPairLevelTriple_le V W P hP i
      omega
    simp [S, hS]
  · have hcard : (S.card : ℝ≥0) ≤ ((W.U i).card : ℝ≥0) := by
      exact_mod_cast (by
        simpa only [S, Fintype.card_coe] using
          card_vortexPairLevelTriple_le V W P hP i)
    calc
      ∑ T ∈ universeTriplesContainingPair P with W.level T = i,
          vortexTripleWeight W c T =
          (S.card : ℝ≥0) * (c / (W.U i).card) := by
        change ∑ T ∈ S, vortexTripleWeight W c T = _
        calc
          ∑ T ∈ S, vortexTripleWeight W c T =
              ∑ _T ∈ S, c / (W.U i).card := by
            apply sum_congr rfl
            intro T hT
            have hlevel : W.level T = i := (mem_filter.mp hT).2
            simp only [vortexTripleWeight, hlevel]
          _ = (S.card : ℝ≥0) * (c / (W.U i).card) := by
            rw [sum_const]
            simp only [nsmul_eq_mul]
      _ ≤ ((W.U i).card : ℝ≥0) * (c / (W.U i).card) := by
        gcongr
      _ = c := by
        rw [mul_comm, div_mul_cancel₀]
        exact_mod_cast hUi

/-- The full fixed-pair star has vortex weight at most one `c` per level. -/
theorem sum_vortexTripleWeight_containingPair_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (c : ℝ≥0) (P : Finset V) (hP : P.card = 2) :
    ∑ T ∈ universeTriplesContainingPair P, vortexTripleWeight W c T ≤
      (ell + 1 : ℕ) * c := by
  calc
    ∑ T ∈ universeTriplesContainingPair P, vortexTripleWeight W c T =
        ∑ T ∈ universeTriplesContainingPair P,
          ∑ i : Fin (ell + 1),
            if W.level T = i then vortexTripleWeight W c T else 0 := by
      apply sum_congr rfl
      intro T hT
      simp
    _ = ∑ i : Fin (ell + 1),
        ∑ T ∈ universeTriplesContainingPair P,
          if W.level T = i then vortexTripleWeight W c T else 0 := by
      rw [sum_comm]
    _ = ∑ i : Fin (ell + 1),
        ∑ T ∈ universeTriplesContainingPair P with W.level T = i,
          vortexTripleWeight W c T := by
      apply sum_congr rfl
      intro i hi
      rw [sum_filter]
    _ ≤ ∑ _i : Fin (ell + 1), c := by
      apply sum_le_sum
      intro i hi
      exact sum_vortexTripleWeight_containingPair_level_le W c P hP i
    _ = (ell + 1 : ℕ) * c := by simp

/-- A weighted finite union is bounded by the sum of the weights of its
members, without any disjointness hypothesis. -/
lemma sum_biUnion_le_sum_sum
    {I X : Type*} [DecidableEq I] [DecidableEq X]
    (s : Finset I) (t : I → Finset X) (f : X → ℝ≥0) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [biUnion_insert, sum_insert ha]
      have hunion : ∑ x ∈ t a ∪ s.biUnion t, f x ≤
          (∑ x ∈ t a, f x) + ∑ x ∈ s.biUnion t, f x := by
        rw [show t a ∪ s.biUnion t =
            t a ∪ (s.biUnion t \ t a) by
              ext x
              simp only [mem_union, mem_sdiff]
              tauto]
        have hd : Disjoint (t a) (s.biUnion t \ t a) := by
          apply disjoint_left.mpr
          intro x hxa hx
          exact (mem_sdiff.mp hx).2 hxa
        rw [sum_union hd]
        gcongr
        exact sdiff_subset
      exact hunion.trans (add_le_add (le_refl _) ih)

/-- All triples sharing a pair with `T` have total vortex weight at most
three times the number of levels times `c`. -/
theorem sum_vortexTripleWeight_triplesSharingPair_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (c : ℝ≥0) (T : TripleOn V) :
    ∑ U ∈ triplesSharingPair T, vortexTripleWeight W c U ≤
      3 * ((ell + 1 : ℕ) * c) := by
  calc
    ∑ U ∈ triplesSharingPair T, vortexTripleWeight W c U ≤
        ∑ U ∈ (T.1.powersetCard 2).biUnion
          (fun P ↦ universeTriplesContainingPair P),
          vortexTripleWeight W c U := by
      apply sum_le_sum_of_subset_of_nonneg
        (triplesSharingPair_subset_pair_union T)
      simp
    _ ≤ ∑ P ∈ T.1.powersetCard 2,
        ∑ U ∈ universeTriplesContainingPair P,
          vortexTripleWeight W c U :=
      sum_biUnion_le_sum_sum _ _ _
    _ ≤ ∑ _P ∈ T.1.powersetCard 2, ((ell + 1 : ℕ) * c) := by
      apply sum_le_sum
      intro P hP
      exact sum_vortexTripleWeight_containingPair_le W c P
        (mem_powersetCard.mp hP).2
    _ = 3 * ((ell + 1 : ℕ) * c) := by
      rw [sum_const, nsmul_eq_mul, card_powersetCard, T.2]
      norm_num

end

end Erdos207
