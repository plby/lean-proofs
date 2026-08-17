/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.Avoidance
import ErdosProblems.Erdos63.BoundedExpansions
import ErdosProblems.Erdos63.ExpanderDefs
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The lower-degree-set obstruction in the Liu--Montgomery argument

This file formalizes the finite counting core of Liu--Montgomery Lemma 3.5.
The point of that lemma is that an expander cannot contain a large disjoint
family of moderately sized sets which all have very small neighborhoods after
one common set of vertices is deleted.

The proof has two parts.  Large members of the family are sampled directly.
For the small members, weighted pigeonhole first makes their cardinalities
equal, and ordinary pigeonhole then makes their neighborhoods inside the
deleted set equal.  The union of the resulting subfamily has too small an
external neighborhood, contradicting the exact Komlós--Szemerédi expansion
property `IsLMExpander`.

All estimates suppressed by the phrase "sufficiently large" in the paper are
arguments of `liuMontgomery_lemma3_5_finite`.  They are pointwise numerical
inequalities, rather than graph-theoretic existence assumptions.  This makes
the combinatorial content reusable while leaving the eventual real estimates
to the parameter layer.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u v

variable {V : Type u} {I : Type v}
variable {G : SimpleGraph V}

/-! ## Neighborhoods of a disjoint union after deletion -/

/-- Every external neighbor of a union either lies in the deleted set, or is
an available external neighbor of one of the members of the union. -/
theorem externalNeighborhood_biUnion_subset_deleted_union_available
    [Fintype V] [DecidableEq I] (G : SimpleGraph V) (U : Finset V)
    (J : Finset I) (S : I → Finset V) :
    externalNeighborhood G (J.biUnion S) ⊆
      U ∪ J.biUnion (fun i ↦ availableExternalNeighborhood G (U : Set V) (S i)) := by
  classical
  intro y hy
  have hy' := externalNeighborhood_biUnion_subset G J S hy
  obtain ⟨i, hiJ, hyi⟩ := Finset.mem_biUnion.1 hy'
  by_cases hyU : y ∈ U
  · exact Finset.mem_union_left _ hyU
  · exact Finset.mem_union_right _ <| Finset.mem_biUnion.2
      ⟨i, hiJ, (mem_availableExternalNeighborhood G (U : Set V) (S i) y).2
        ⟨hyi, hyU⟩⟩

/-- Cardinal version of
`externalNeighborhood_biUnion_subset_deleted_union_available`. -/
theorem card_externalNeighborhood_biUnion_le_deleted_add_available
    [Fintype V] [DecidableEq I] (G : SimpleGraph V) (U : Finset V)
    (J : Finset I) (S : I → Finset V) :
    (externalNeighborhood G (J.biUnion S)).card ≤
      U.card + ∑ i ∈ J,
        (availableExternalNeighborhood G (U : Set V) (S i)).card := by
  classical
  have hsub := Finset.card_le_card
    (externalNeighborhood_biUnion_subset_deleted_union_available G U J S)
  have hunion := Finset.card_union_le U
    (J.biUnion (fun i ↦ availableExternalNeighborhood G (U : Set V) (S i)))
  have hbi := Finset.card_biUnion_le
    (s := J) (t := fun i ↦ availableExternalNeighborhood G (U : Set V) (S i))
  omega

/-- If every selected set has the same neighborhood inside the deleted set,
that common neighborhood replaces the whole deleted set in the preceding
bound.  This is the decisive second pigeonhole step in Lemma 3.5. -/
theorem externalNeighborhood_biUnion_subset_common_blocked
    [Fintype V] [DecidableEq I] (G : SimpleGraph V) (U Z : Finset V)
    (J : Finset I) (S : I → Finset V)
    (hblocked : ∀ i ∈ J,
      blockedExternalNeighborhood G (U : Set V) (S i) = Z) :
    externalNeighborhood G (J.biUnion S) ⊆
      Z ∪ J.biUnion (fun i ↦ availableExternalNeighborhood G (U : Set V) (S i)) := by
  classical
  intro y hy
  have hy' := externalNeighborhood_biUnion_subset G J S hy
  obtain ⟨i, hiJ, hyi⟩ := Finset.mem_biUnion.1 hy'
  by_cases hyU : y ∈ U
  · apply Finset.mem_union_left
    rw [← hblocked i hiJ, mem_blockedExternalNeighborhood]
    exact ⟨hyi, hyU⟩
  · exact Finset.mem_union_right _ <| Finset.mem_biUnion.2
      ⟨i, hiJ, (mem_availableExternalNeighborhood G (U : Set V) (S i) y).2
        ⟨hyi, hyU⟩⟩

/-- Cardinal version of the common-blocked-neighborhood bound. -/
theorem card_externalNeighborhood_biUnion_le_common_blocked_add_available
    [Fintype V] [DecidableEq I] (G : SimpleGraph V) (U Z : Finset V)
    (J : Finset I) (S : I → Finset V)
    (hblocked : ∀ i ∈ J,
      blockedExternalNeighborhood G (U : Set V) (S i) = Z) :
    (externalNeighborhood G (J.biUnion S)).card ≤
      Z.card + ∑ i ∈ J,
        (availableExternalNeighborhood G (U : Set V) (S i)).card := by
  classical
  have hsub := Finset.card_le_card
    (externalNeighborhood_biUnion_subset_common_blocked G U Z J S hblocked)
  have hunion := Finset.card_union_le Z
    (J.biUnion (fun i ↦ availableExternalNeighborhood G (U : Set V) (S i)))
  have hbi := Finset.card_biUnion_le
    (s := J) (t := fun i ↦ availableExternalNeighborhood G (U : Set V) (S i))
  omega

/-! ## Two exact expander obstructions -/

/-- A selected disjoint family with small neighborhoods after deleting `U`
contradicts the Komlós--Szemerédi expansion inequality once its union lies in
the expansion range. -/
theorem no_selected_family_of_deleted_neighborhood_bound
    [Fintype V] [DecidableEq I]
    (G : SimpleGraph V) (epsilon k : ℝ) (hexp : IsLMExpander G epsilon k)
    (U : Finset V) (S : I → Finset V) (J : Finset I) (B : ℕ)
    (hlower : k / 2 ≤ ((J.biUnion S).card : ℝ))
    (hupper : ((J.biUnion S).card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hsmall : ∀ i ∈ J,
      (availableExternalNeighborhood G (U : Set V) (S i)).card ≤ B)
    (hnumeric : ((U.card + J.card * B : ℕ) : ℝ) <
      expansionEpsilon epsilon k (J.biUnion S).card * ((J.biUnion S).card : ℝ)) :
    False := by
  have hN := card_externalNeighborhood_biUnion_le_deleted_add_available G U J S
  have hsum : ∑ i ∈ J,
      (availableExternalNeighborhood G (U : Set V) (S i)).card ≤ J.card * B := by
    calc
      ∑ i ∈ J, (availableExternalNeighborhood G (U : Set V) (S i)).card
          ≤ ∑ _i ∈ J, B := Finset.sum_le_sum fun i hi ↦ hsmall i hi
      _ = J.card * B := by simp
  have hN' : (externalNeighborhood G (J.biUnion S)).card ≤ U.card + J.card * B := by
    omega
  have he := hexp.expands hlower hupper
  change expansionEpsilon epsilon k (J.biUnion S).card *
      ((J.biUnion S).card : ℝ) ≤
        ((externalNeighborhood G (J.biUnion S)).card : ℝ) at he
  exact (not_lt_of_ge (he.trans (by exact_mod_cast hN'))) hnumeric

/-- Size-correlated version of the deleted-neighborhood obstruction.  It
keeps the sum of the individual budgets instead of replacing it by a uniform
worst-case bound. -/
theorem no_selected_family_of_deleted_neighborhood_sum_bound
    [Fintype V] [DecidableEq I]
    (G : SimpleGraph V) (epsilon k : ℝ) (hexp : IsLMExpander G epsilon k)
    (U : Finset V) (S : I → Finset V) (J : Finset I) (budget : I → ℕ)
    (hlower : k / 2 ≤ ((J.biUnion S).card : ℝ))
    (hupper : ((J.biUnion S).card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hsmall : ∀ i ∈ J,
      (availableExternalNeighborhood G (U : Set V) (S i)).card ≤ budget i)
    (hnumeric : ((U.card + ∑ i ∈ J, budget i : ℕ) : ℝ) <
      expansionEpsilon epsilon k (J.biUnion S).card * ((J.biUnion S).card : ℝ)) :
    False := by
  have hN := card_externalNeighborhood_biUnion_le_deleted_add_available G U J S
  have hsum : ∑ i ∈ J,
      (availableExternalNeighborhood G (U : Set V) (S i)).card ≤
        ∑ i ∈ J, budget i :=
    Finset.sum_le_sum fun i hi ↦ hsmall i hi
  have hN' : (externalNeighborhood G (J.biUnion S)).card ≤
      U.card + ∑ i ∈ J, budget i := by
    omega
  have he := hexp.expands hlower hupper
  change expansionEpsilon epsilon k (J.biUnion S).card *
      ((J.biUnion S).card : ℝ) ≤
        ((externalNeighborhood G (J.biUnion S)).card : ℝ) at he
  exact (not_lt_of_ge (he.trans (by exact_mod_cast hN'))) hnumeric

/-- Common blocked neighborhoods give the sharper obstruction used for the
small-set case of Liu--Montgomery Lemma 3.5. -/
theorem no_selected_family_of_common_blocked_neighborhood
    [Fintype V] [DecidableEq I]
    (G : SimpleGraph V) (epsilon k : ℝ) (hexp : IsLMExpander G epsilon k)
    (U Z : Finset V) (S : I → Finset V) (J : Finset I) (B C : ℕ)
    (hlower : k / 2 ≤ ((J.biUnion S).card : ℝ))
    (hupper : ((J.biUnion S).card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hblocked : ∀ i ∈ J,
      blockedExternalNeighborhood G (U : Set V) (S i) = Z)
    (hZ : Z.card ≤ C)
    (hsmall : ∀ i ∈ J,
      (availableExternalNeighborhood G (U : Set V) (S i)).card ≤ B)
    (hnumeric : ((C + J.card * B : ℕ) : ℝ) <
      expansionEpsilon epsilon k (J.biUnion S).card * ((J.biUnion S).card : ℝ)) :
    False := by
  have hN := card_externalNeighborhood_biUnion_le_common_blocked_add_available
    G U Z J S hblocked
  have hsum : ∑ i ∈ J,
      (availableExternalNeighborhood G (U : Set V) (S i)).card ≤ J.card * B := by
    calc
      ∑ i ∈ J, (availableExternalNeighborhood G (U : Set V) (S i)).card
          ≤ ∑ _i ∈ J, B := Finset.sum_le_sum fun i hi ↦ hsmall i hi
      _ = J.card * B := by simp
  have hN' : (externalNeighborhood G (J.biUnion S)).card ≤ C + J.card * B := by
    omega
  have he := hexp.expands hlower hupper
  change expansionEpsilon epsilon k (J.biUnion S).card *
      ((J.biUnion S).card : ℝ) ≤
        ((externalNeighborhood G (J.biUnion S)).card : ℝ) at he
  exact (not_lt_of_ge (he.trans (by exact_mod_cast hN'))) hnumeric

theorem blockedExternalNeighborhood_subset_deleted [Fintype V]
    (G : SimpleGraph V) (U S : Finset V) :
    blockedExternalNeighborhood G (U : Set V) S ⊆ U := by
  classical
  intro x hx
  exact (mem_blockedExternalNeighborhood G (U : Set V) S x).1 hx |>.2

/-! ## Limited contact after a fixed deletion -/

/-- `A` has `contact`-limited contact with `C` after `deleted` is removed.
The ball itself avoids both `deleted` and `C`; among its external neighbors,
at most `contact * (r+1)` lie in `C` at radius `r`.  This is the literal
finite-set version of Liu--Montgomery's limited-contact condition. -/
def HasLimitedContactAfterDeletion [Fintype V] (G : SimpleGraph V)
    (A deleted C : Finset V) (contact : ℕ) : Prop :=
  ∀ r : ℕ,
    (blockedExternalNeighborhood G (C : Set V)
      (ballAvoidingFrom G ((deleted : Set V) ∪ (C : Set V)) A r)).card ≤
        contact * (r + 1)

/-- A path which is no longer than any deleted-set-avoiding path from `A` to
`T` has limited contact with an avoiding ball grown from `A`.  The path itself
need not start in `A`; this is the form used when the path starts in the other
end of an adjuster.  The factor `2` is stronger than the factor `4` recorded
in Liu--Montgomery Lemma 3.7.

The disjointness of `A` from `deleted` is essential: every initial vertex is
present in `ballAvoidingFrom` even if it belongs to the forbidden set. -/
theorem hasLimitedContactAfterDeletion_of_path_shortest_from_set
    [Fintype V] (G : SimpleGraph V) (A T deleted : Finset V)
    {s t : V} (ht : t ∈ T) (p : G.Walk s t)
    (hp : p.IsPath) (hpdeleted : p.Avoids (deleted : Set V) ∅)
    (hAdeleted : Disjoint A deleted)
    (hshortest : ∀ a' ∈ A, ∀ t' ∈ T, ∀ q : G.Walk a' t',
      q.IsPath → q.Avoids (deleted : Set V) ∅ → p.length ≤ q.length) :
    HasLimitedContactAfterDeletion G A deleted p.support.toFinset 2 := by
  classical
  intro r
  let C : Finset V := p.support.toFinset
  let current := ballAvoidingFrom G ((deleted : Set V) ∪ (C : Set V)) A r
  have hcontactSubset :
      blockedExternalNeighborhood G (C : Set V) current ⊆
        (p.support.take (r + 2)).toFinset := by
    intro y hy
    obtain ⟨hyN, hyC⟩ :=
      (mem_blockedExternalNeighborhood G (C : Set V) current y).1 hy
    have hyp : y ∈ p.support := by
      simpa [C] using hyC
    obtain ⟨_, x, hxcurrent, hxy⟩ :=
      (mem_externalNeighborhood G current y).1 hyN
    obtain ⟨a', ha'A, q, hq, hqlen⟩ :=
      (mem_ballAvoidingFrom G
        ((deleted : Set V) ∪ (C : Set V)) A r x).1 hxcurrent
    have hqdeleted : q.Avoids (deleted : Set V) ∅ := by
      intro z hzq hzdeleted
      have hza' := hq.2 z hzq (Or.inl hzdeleted)
      have hzeq : z = a' := by simpa using hza'
      subst z
      exact (Finset.disjoint_left.1 hAdeleted ha'A hzdeleted).elim
    let edge : G.Walk x y := Walk.cons hxy Walk.nil
    have hedgedeleted : edge.Avoids (deleted : Set V) ∅ := by
      intro z hzedge hzdeleted
      have hzedge' : z = x ∨ z = y := by
        simpa [edge] using hzedge
      rcases hzedge' with hzx | hzy
      · subst z
        exact (hqdeleted _ q.end_mem_support hzdeleted).elim
      · subst z
        exact (hpdeleted _ hyp hzdeleted).elim
    have hdropdeleted :
        (p.dropUntil y hyp).Avoids (deleted : Set V) ∅ :=
      hpdeleted.of_support_subset (p.support_dropUntil_subset_support hyp)
    let w : G.Walk a' t :=
      (q.append edge).append (p.dropUntil y hyp)
    have hwdeleted : w.Avoids (deleted : Set V) ∅ := by
      intro z hzw hzdeleted
      change z ∈ ((q.append edge).append (p.dropUntil y hyp)).support at hzw
      rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff] at hzw
      rcases hzw with (hzq | hzedge) | hzdrop
      · exact hqdeleted z hzq hzdeleted
      · exact hedgedeleted z hzedge hzdeleted
      · exact hdropdeleted z hzdrop hzdeleted
    have htake : (p.takeUntil y hyp).length ≤ r + 1 := by
      by_contra hnot
      have htakeLong : r + 1 < (p.takeUntil y hyp).length :=
        Nat.lt_of_not_ge hnot
      have hsplit : (p.takeUntil y hyp).length +
          (p.dropUntil y hyp).length = p.length := by
        calc
          (p.takeUntil y hyp).length + (p.dropUntil y hyp).length =
              ((p.takeUntil y hyp).append (p.dropUntil y hyp)).length := by
                rw [Walk.length_append]
          _ = p.length := congrArg Walk.length (p.take_spec hyp)
      have hwlength : w.length < p.length := by
        dsimp [w, edge]
        simp only [Walk.length_append, Walk.length_cons, Walk.length_nil]
        omega
      have hshort := hshortest a' ha'A t ht w.bypass w.bypass_isPath
        (hwdeleted.of_support_subset w.support_bypass_subset_support)
      exact (Nat.not_lt_of_ge (hshort.trans w.length_bypass_le_length)) hwlength
    rw [List.mem_toFinset]
    apply (List.mem_take_iff_idxOf_lt hyp).2
    rw [← p.length_takeUntil hyp]
    omega
  have hcard := Finset.card_le_card hcontactSubset
  have htoFinset := List.toFinset_card_le (p.support.take (r + 2))
  have htakeLength : (p.support.take (r + 2)).length ≤ r + 2 := by
    simp
  dsimp [current, C] at hcard
  omega

/-- The common special case in which the globally shortest path starts in
the set whose avoiding ball is grown. -/
theorem hasLimitedContactAfterDeletion_of_shortest_path
    [Fintype V] (G : SimpleGraph V) (A T deleted : Finset V)
    {a t : V} (ha : a ∈ A) (ht : t ∈ T) (p : G.Walk a t)
    (hp : p.IsPath) (hpdeleted : p.Avoids (deleted : Set V) ∅)
    (hAdeleted : Disjoint A deleted)
    (hshortest : ∀ a' ∈ A, ∀ t' ∈ T, ∀ q : G.Walk a' t',
      q.IsPath → q.Avoids (deleted : Set V) ∅ → p.length ≤ q.length) :
    HasLimitedContactAfterDeletion G A deleted p.support.toFinset 2 := by
  exact hasLimitedContactAfterDeletion_of_path_shortest_from_set
    G A T deleted ht p hp hpdeleted hAdeleted hshortest

/-- Restoring `B` and `C` after deleting `U ∪ B ∪ C` costs only all of `B`
and those vertices of `C` which are actual external neighbors. -/
theorem availableExternalNeighborhood_subset_restore_blocked
    [Fintype V] (G : SimpleGraph V) (U B C S : Finset V) :
    availableExternalNeighborhood G (U : Set V) S ⊆
      (availableExternalNeighborhood G
        ((U : Set V) ∪ (B : Set V) ∪ (C : Set V)) S ∪ B) ∪
          blockedExternalNeighborhood G (C : Set V) S := by
  classical
  intro y hy
  obtain ⟨hyN, hyU⟩ := (mem_availableExternalNeighborhood G (U : Set V) S y).1 hy
  by_cases hyC : y ∈ C
  · exact Finset.mem_union_right _ <|
      (mem_blockedExternalNeighborhood G (C : Set V) S y).2 ⟨hyN, hyC⟩
  by_cases hyB : y ∈ B
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hyB)
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [mem_availableExternalNeighborhood]
    exact ⟨hyN, by simp [hyU, hyB, hyC]⟩

theorem card_availableExternalNeighborhood_restore_blocked_le
    [Fintype V] (G : SimpleGraph V) (U B C S : Finset V) :
    (availableExternalNeighborhood G (U : Set V) S).card ≤
      (availableExternalNeighborhood G
        ((U : Set V) ∪ (B : Set V) ∪ (C : Set V)) S).card +
          B.card + (blockedExternalNeighborhood G (C : Set V) S).card := by
  classical
  have hsub := Finset.card_le_card
    (availableExternalNeighborhood_subset_restore_blocked G U B C S)
  have h₁ := Finset.card_union_le
    (availableExternalNeighborhood G
      ((U : Set V) ∪ (B : Set V) ∪ (C : Set V)) S) B
  have h₂ := Finset.card_union_le
    (availableExternalNeighborhood G
      ((U : Set V) ∪ (B : Set V) ∪ (C : Set V)) S ∪ B)
    (blockedExternalNeighborhood G (C : Set V) S)
  omega

/-- A minimum-degree-into-`U` estimate for a blocked external neighborhood.
This is the exact finite counting step used to verify condition B3 of
Liu--Montgomery Lemma 3.5. -/
theorem card_blockedExternalNeighborhood_le_card_mul_of_degree_into
    [Fintype V] (G : SimpleGraph V) (U S : Finset V) (d : ℕ)
    (hdegree : ∀ v ∈ S, (G.neighborFinset v ∩ U).card ≤ d) :
    (blockedExternalNeighborhood G (U : Set V) S).card ≤ S.card * d := by
  classical
  have hsub : blockedExternalNeighborhood G (U : Set V) S ⊆
      S.biUnion fun v ↦ G.neighborFinset v ∩ U := by
    intro y hy
    obtain ⟨hyN, hyU⟩ :=
      (mem_blockedExternalNeighborhood G (U : Set V) S y).1 hy
    obtain ⟨-, v, hvS, hvy⟩ := (mem_externalNeighborhood G S y).1 hyN
    rw [Finset.mem_biUnion]
    have hyU' : y ∈ U := by
      change y ∈ U at hyU
      exact hyU
    exact ⟨v, hvS, by simp [hyU', hvy]⟩
  calc
    (blockedExternalNeighborhood G (U : Set V) S).card
        ≤ (S.biUnion fun v ↦ G.neighborFinset v ∩ U).card :=
          Finset.card_le_card hsub
    _ ≤ ∑ v ∈ S, (G.neighborFinset v ∩ U).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ S, d := Finset.sum_le_sum fun v hv ↦ hdegree v hv
    _ = S.card * d := by simp

/-- A first radius at which a ball lies below a prescribed numerical growth
curve.  The preceding radius is strictly above the curve. -/
theorem exists_first_slow_ball [Fintype V] (G : SimpleGraph V)
    (X : Set V) (A : Finset V) (radius : ℕ) (growth : ℕ → ℕ)
    (hstart : growth 0 < A.card)
    (hfinal : (ballAvoidingFrom G X A radius).card ≤ growth radius) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ radius ∧
      (ballAvoidingFrom G X A ell).card ≤ growth ell ∧
      growth (ell - 1) < (ballAvoidingFrom G X A (ell - 1)).card := by
  classical
  let P : ℕ → Prop := fun ell ↦ ell ≤ radius ∧
    (ballAvoidingFrom G X A ell).card ≤ growth ell
  have hex : ∃ ell : ℕ, P ell := ⟨radius, le_rfl, hfinal⟩
  let ell := Nat.find hex
  have hell := Nat.find_spec hex
  have hellpos : 0 < ell := by
    by_contra h
    have hellzero : ell = 0 := Nat.eq_zero_of_not_pos h
    have := hell.2
    change (ballAvoidingFrom G X A ell).card ≤ growth ell at this
    rw [hellzero, ballAvoidingFrom_zero] at this
    exact (Nat.not_le_of_gt hstart) this
  have hprevNot : ¬ P (ell - 1) := by
    apply Nat.find_min hex
    omega
  refine ⟨ell, hellpos, hell.1, hell.2, ?_⟩
  have hprevLe : ell - 1 ≤ radius := by omega
  exact Nat.lt_of_not_ge fun h ↦ hprevNot ⟨hprevLe, h⟩

/-- Claim 3.8's set-theoretic and discrete core.  At the first slow radius,
the available neighborhood after restoring `B` and `C` is bounded by the
jump in the comparison curve, the size of `B`, and the limited contact with
`C`. -/
theorem card_available_first_slow_ball_le
    [Fintype V] (G : SimpleGraph V) (U B C A : Finset V)
    (contact ell stepLoss : ℕ) (growth : ℕ → ℕ)
    (hellpos : 0 < ell)
    (hslow : (ballAvoidingFrom G
      ((U : Set V) ∪ (B : Set V) ∪ (C : Set V)) A ell).card ≤ growth ell)
    (hprevious : growth (ell - 1) <
      (ballAvoidingFrom G
        ((U : Set V) ∪ (B : Set V) ∪ (C : Set V)) A (ell - 1)).card)
    (hjump : growth ell ≤ growth (ell - 1) + 1 + stepLoss)
    (hcontact : HasLimitedContactAfterDeletion G A (U ∪ B) C contact) :
    (availableExternalNeighborhood G (U : Set V)
      (ballAvoidingFrom G
        ((U : Set V) ∪ (B : Set V) ∪ (C : Set V)) A (ell - 1))).card ≤
      stepLoss + B.card + contact * ell := by
  let X : Set V := (U : Set V) ∪ (B : Set V) ∪ (C : Set V)
  let current := ballAvoidingFrom G X A (ell - 1)
  have hellPred : ell - 1 + 1 = ell := by omega
  have havailable : current.card +
      (availableExternalNeighborhood G X current).card ≤
        (ballAvoidingFrom G X A ell).card := by
    simpa [current, X, hellPred] using
      card_ballAvoidingFrom_add_card_available_le G X A (ell - 1)
  have havailableBound :
      (availableExternalNeighborhood G X current).card ≤ stepLoss := by
    dsimp [current, X] at havailable ⊢
    omega
  have hcontactAt :
      (blockedExternalNeighborhood G (C : Set V) current).card ≤
        contact * ell := by
    have := hcontact (ell - 1)
    simpa [HasLimitedContactAfterDeletion, current, X, hellPred,
      Finset.coe_union, Set.union_assoc] using this
  have hrestore := card_availableExternalNeighborhood_restore_blocked_le
    G U B C current
  dsimp [current, X] at havailableBound hcontactAt hrestore ⊢
  omega

/-! ## Direct expander growth and connection -/

/-- Additive growth of a ball after deleting `W`, derived directly from the
Liu--Montgomery expansion inequality.  Growth stops only after the ball has
strictly more than half of all vertices. -/
theorem min_card_ballAvoidingFrom_of_lmExpander_growth
    [Fintype V] (G : SimpleGraph V) (epsilon k : ℝ)
    (hexp : IsLMExpander G epsilon k) (W A : Finset V) (q radius : ℕ)
    (hlower : k / 2 ≤ (A.card : ℝ))
    (hrate : ∀ s : ℕ, A.card ≤ s → s ≤ Fintype.card V / 2 →
      (((W.card + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ))) :
    min (A.card + radius * q) (Fintype.card V / 2 + 1) ≤
      (ballAvoidingFrom G (W : Set V) A radius).card := by
  classical
  induction radius with
  | zero =>
      simp
  | succ radius ih =>
      let current := ballAvoidingFrom G (W : Set V) A radius
      let cap := Fintype.card V / 2 + 1
      by_cases hcap : cap ≤ current.card
      · have hmono := Finset.card_le_card <|
          ballAvoidingFrom_radius_mono G (W : Set V) A
            (Nat.le_succ radius)
        exact (min_le_right _ cap).trans (hcap.trans hmono)
      · have hcurrentUpper : current.card ≤ Fintype.card V / 2 := by
          dsimp [cap] at hcap
          omega
        have hAcurrent : A.card ≤ current.card :=
          Finset.card_le_card (subset_ballAvoidingFrom G (W : Set V) A radius)
        have hcurrentLower : k / 2 ≤ (current.card : ℝ) :=
          hlower.trans (by exact_mod_cast hAcurrent)
        have hcurrentUpperReal : (current.card : ℝ) ≤
            (Fintype.card V : ℝ) / 2 := by
          calc
            (current.card : ℝ) ≤ ((Fintype.card V / 2 : ℕ) : ℝ) := by
              exact_mod_cast hcurrentUpper
            _ ≤ (Fintype.card V : ℝ) / 2 := by
              simpa using (Nat.cast_div_le (α := ℝ)
                (m := Fintype.card V) (n := 2))
        have he := hexp.expands hcurrentLower hcurrentUpperReal
        change expansionEpsilon epsilon k current.card * (current.card : ℝ) ≤
          ((externalNeighborhood G current).card : ℝ) at he
        have hNat : W.card + q ≤ (externalNeighborhood G current).card := by
          exact_mod_cast (hrate current.card hAcurrent hcurrentUpper).trans he
        have hblocked :
            (blockedExternalNeighborhood G (W : Set V) current).card ≤ W.card :=
          Finset.card_le_card (blockedExternalNeighborhood_subset_deleted G W current)
        have hstep : current.card + q ≤
            (ballAvoidingFrom G (W : Set V) A (radius + 1)).card := by
          apply card_ballAvoidingFrom_add_le_succ_of_external G (W : Set V) A radius q
          calc
            q + (blockedExternalNeighborhood G (W : Set V) current).card
                ≤ q + W.card := Nat.add_le_add_left hblocked q
            _ = W.card + q := Nat.add_comm _ _
            _ ≤ (externalNeighborhood G current).card := hNat
        have hsmall : A.card + radius * q < cap := by
          by_contra h
          have hreach : cap ≤ A.card + radius * q := Nat.le_of_not_gt h
          have hreachCurrent : cap ≤ current.card := by
            simpa [current, cap, min_eq_right hreach] using ih
          exact hcap hreachCurrent
        have hbase : A.card + radius * q ≤ current.card := by
          simpa [current, cap, min_eq_left (Nat.le_of_lt hsmall)] using ih
        have hnext : A.card + Nat.succ radius * q ≤ current.card + q := by
          calc
            A.card + Nat.succ radius * q = (A.card + radius * q) + q := by
              simp [Nat.succ_mul, Nat.add_assoc]
            _ ≤ current.card + q := Nat.add_le_add_right hbase q
        have hmin : min (A.card + Nat.succ radius * q) cap ≤ current.card + q :=
          (min_le_left _ _).trans hnext
        dsimp [current, cap] at hstep hmin
        simpa [Nat.succ_eq_add_one] using hmin.trans hstep

/-- Additive ball growth when one forbidden set is paid for globally and a
second forbidden set has limited contact with the growing ball.  This is the
direct half-order growth API used when the paper retains large end sets
instead of charging their whole cardinality to the deletion budget. -/
theorem min_card_ballAvoidingFrom_of_lmExpander_limitedContact
    [Fintype V] (G : SimpleGraph V) (epsilon k : ℝ)
    (hexp : IsLMExpander G epsilon k) (A deleted C : Finset V)
    (contact q radius : ℕ)
    (hlower : k / 2 ≤ (A.card : ℝ))
    (hcontact : HasLimitedContactAfterDeletion G A deleted C contact)
    (hrate : ∀ step : ℕ, step < radius → ∀ s : ℕ,
      A.card ≤ s → s ≤ Fintype.card V / 2 →
      (((q + deleted.card + contact * (step + 1) : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ))) :
    min (A.card + radius * q) (Fintype.card V / 2 + 1) ≤
      (ballAvoidingFrom G
        ((deleted : Set V) ∪ (C : Set V)) A radius).card := by
  classical
  have aux : ∀ r : ℕ, r ≤ radius →
      min (A.card + r * q) (Fintype.card V / 2 + 1) ≤
        (ballAvoidingFrom G ((deleted : Set V) ∪ (C : Set V)) A r).card := by
    intro r
    induction r with
    | zero =>
        intro _
        simp
    | succ r ih =>
      intro hrs
      let X : Set V := (deleted : Set V) ∪ (C : Set V)
      let current := ballAvoidingFrom G X A r
      let cap := Fintype.card V / 2 + 1
      have hir : min (A.card + r * q) cap ≤ current.card := by
        have hrle : r ≤ radius := (Nat.le_succ r).trans hrs
        simpa [current, X, cap] using ih hrle
      by_cases hcap : cap ≤ current.card
      · have hmono := Finset.card_le_card <|
          ballAvoidingFrom_radius_mono G X A (Nat.le_succ r)
        exact (min_le_right _ cap).trans (hcap.trans hmono)
      · have hcurrentUpper : current.card ≤ Fintype.card V / 2 := by
          dsimp [cap] at hcap
          omega
        have hAcurrent : A.card ≤ current.card :=
          Finset.card_le_card (subset_ballAvoidingFrom G X A r)
        have hcurrentLower : k / 2 ≤ (current.card : ℝ) :=
          hlower.trans (by exact_mod_cast hAcurrent)
        have hcurrentUpperReal : (current.card : ℝ) ≤
            (Fintype.card V : ℝ) / 2 := by
          calc
            (current.card : ℝ) ≤ ((Fintype.card V / 2 : ℕ) : ℝ) := by
              exact_mod_cast hcurrentUpper
            _ ≤ (Fintype.card V : ℝ) / 2 := by
              simpa using (Nat.cast_div_le (α := ℝ)
                (m := Fintype.card V) (n := 2))
        have hcontactAt :
            (blockedExternalNeighborhood G (C : Set V) current).card ≤
              contact * (r + 1) := by
          simpa [HasLimitedContactAfterDeletion, current, X] using hcontact r
        have hstep : current.card + q ≤
            (ballAvoidingFrom G X A (r + 1)).card := by
          have hlowerThree : k / 2 ≤
              (ballAvoidingFrom G
                ((deleted : Set V) ∪ ((∅ : Finset V) : Set V) ∪ (C : Set V))
                  A r).card := by
            simpa [current, X] using hcurrentLower
          have hupperThree :
              ((ballAvoidingFrom G
                ((deleted : Set V) ∪ ((∅ : Finset V) : Set V) ∪ (C : Set V))
                  A r).card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
            simpa [current, X] using hcurrentUpperReal
          have hcontactThree :
              (blockedExternalNeighborhood G (C : Set V)
                (ballAvoidingFrom G
                  ((deleted : Set V) ∪ ((∅ : Finset V) : Set V) ∪ (C : Set V))
                    A r)).card ≤ contact * (r + 1) := by
            simpa [current, X] using hcontactAt
          have hbudgetThree :
              (((q + deleted.card + (∅ : Finset V).card + contact * (r + 1) : ℕ) : ℝ) ≤
                expansionEpsilon epsilon k
                    (ballAvoidingFrom G
                      ((deleted : Set V) ∪ ((∅ : Finset V) : Set V) ∪ (C : Set V))
                        A r).card *
                  (ballAvoidingFrom G
                    ((deleted : Set V) ∪ ((∅ : Finset V) : Set V) ∪ (C : Set V))
                      A r).card) := by
            simpa [current, X] using
              (hrate r (Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hrs)
                current.card hAcurrent hcurrentUpper)
          have h := hexp.card_ballAvoidingFrom_union_three_add_le_succ
            A deleted ∅ C r q (contact * (r + 1))
            hlowerThree hupperThree hcontactThree hbudgetThree
          simpa [current, X] using h
        have hsmall : A.card + r * q < cap := by
          by_contra h
          have hreach : cap ≤ A.card + r * q := Nat.le_of_not_gt h
          have hreachCurrent : cap ≤ current.card := by
            simpa [min_eq_right hreach] using hir
          exact hcap hreachCurrent
        have hbase : A.card + r * q ≤ current.card := by
          simpa [min_eq_left (Nat.le_of_lt hsmall)] using hir
        have hnext : A.card + Nat.succ r * q ≤ current.card + q := by
          calc
            A.card + Nat.succ r * q = (A.card + r * q) + q := by
              simp [Nat.succ_mul, Nat.add_assoc]
            _ ≤ current.card + q := Nat.add_le_add_right hbase q
        have hmin : min (A.card + Nat.succ r * q) cap ≤ current.card + q :=
          (min_le_left _ _).trans hnext
        dsimp [current, cap, X] at hstep hmin
        simpa [Nat.succ_eq_add_one] using hmin.trans hstep
  exact aux radius le_rfl

/-- The limited-contact form of Liu--Montgomery Lemma 3.4.  Both end sets are
grown while avoiding the same fixed deletion `deleted ∪ C`; only `deleted` is
paid for in full, while contact with `C` is charged radius by radius.  Once
both balls have more than half the vertices, their intersection gives the
required short avoiding path. -/
theorem exists_avoiding_path_between_of_lmExpander_limitedContact
    [Fintype V] (G : SimpleGraph V) (epsilon k : ℝ)
    (hexp : IsLMExpander G epsilon k) (deleted C A B : Finset V)
    (contactA contactB q radius : ℕ)
    (hAlower : k / 2 ≤ (A.card : ℝ))
    (hBlower : k / 2 ≤ (B.card : ℝ))
    (hAcontact : HasLimitedContactAfterDeletion G A deleted C contactA)
    (hBcontact : HasLimitedContactAfterDeletion G B deleted C contactB)
    (hArate : ∀ step : ℕ, step < radius → ∀ s : ℕ,
      A.card ≤ s → s ≤ Fintype.card V / 2 →
      (((q + deleted.card + contactA * (step + 1) : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ)))
    (hBrate : ∀ step : ℕ, step < radius → ∀ s : ℕ,
      B.card ≤ s → s ≤ Fintype.card V / 2 →
      (((q + deleted.card + contactB * (step + 1) : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ)))
    (hAsteps : Fintype.card V / 2 + 1 ≤ A.card + radius * q)
    (hBsteps : Fintype.card V / 2 + 1 ≤ B.card + radius * q) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath (((deleted : Set V) ∪ (C : Set V))) ({a, b} : Set V) ∧
        p.length ≤ 2 * radius := by
  have hAball := min_card_ballAvoidingFrom_of_lmExpander_limitedContact
    G epsilon k hexp A deleted C contactA q radius hAlower hAcontact hArate
  have hBball := min_card_ballAvoidingFrom_of_lmExpander_limitedContact
    G epsilon k hexp B deleted C contactB q radius hBlower hBcontact hBrate
  have hAhalf : Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G ((deleted : Set V) ∪ (C : Set V)) A radius).card := by
    simpa [min_eq_right hAsteps] using hAball
  have hBhalf : Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G ((deleted : Set V) ∪ (C : Set V)) B radius).card := by
    simpa [min_eq_right hBsteps] using hBball
  have hcard : Fintype.card V <
      (ballAvoidingFrom G ((deleted : Set V) ∪ (C : Set V)) A radius).card +
        (ballAvoidingFrom G ((deleted : Set V) ∪ (C : Set V)) B radius).card := by
    omega
  simpa [two_mul] using
    (exists_avoiding_path_between_of_large_balls G
      ((deleted : Set V) ∪ (C : Set V)) A B radius radius hcard)

/-- Concrete Liu--Montgomery Lemma 3.4 in the range where the two initial
sets already satisfy the expander's lower cutoff.  The rate assumptions are
literal inequalities for the exact expansion profile, so the conclusion has
no abstract ball-growth premise. -/
theorem exists_avoiding_path_between_of_lmExpander_growth
    [Fintype V] (G : SimpleGraph V) (epsilon k : ℝ)
    (hexp : IsLMExpander G epsilon k) (W A B : Finset V) (q radius : ℕ)
    (hAlower : k / 2 ≤ (A.card : ℝ))
    (hBlower : k / 2 ≤ (B.card : ℝ))
    (hArate : ∀ s : ℕ, A.card ≤ s → s ≤ Fintype.card V / 2 →
      (((W.card + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ)))
    (hBrate : ∀ s : ℕ, B.card ≤ s → s ≤ Fintype.card V / 2 →
      (((W.card + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ)))
    (hAsteps : Fintype.card V / 2 + 1 ≤ A.card + radius * q)
    (hBsteps : Fintype.card V / 2 + 1 ≤ B.card + radius * q) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath (W : Set V) ({a, b} : Set V) ∧
        p.length ≤ 2 * radius := by
  have hAball := min_card_ballAvoidingFrom_of_lmExpander_growth
    G epsilon k hexp W A q radius hAlower hArate
  have hBball := min_card_ballAvoidingFrom_of_lmExpander_growth
    G epsilon k hexp W B q radius hBlower hBrate
  have hAhalf : Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G (W : Set V) A radius).card := by
    simpa [min_eq_right hAsteps] using hAball
  have hBhalf : Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G (W : Set V) B radius).card := by
    simpa [min_eq_right hBsteps] using hBball
  have hcard : Fintype.card V <
      (ballAvoidingFrom G (W : Set V) A radius).card +
        (ballAvoidingFrom G (W : Set V) B radius).card := by
    omega
  simpa [two_mul] using
    (exists_avoiding_path_between_of_large_balls
      G (W : Set V) A B radius radius hcard)

/-! ## The radius-one bootstrap for prescribed expansions -/

/-- A one-step avoiding ball around an expansion inherits the standard
minimum-degree lower bound from its root.  This foundational version belongs
below all adjuster and long-path modules. -/
theorem VertexExpansion.minDegree_sub_budget_le_card_ballAvoidingFrom_one
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {x : V} {D m d budget : ℕ} (E : VertexExpansion G x D m)
    (W : Finset V) (hdegree : d - 1 ≤ G.degree x)
    (hW : W.card ≤ budget) :
    d - 1 - budget ≤ (ballAvoidingFrom G (W : Set V) E.verts 1).card := by
  classical
  have hneighborSubset : G.neighborFinset x \ W ⊆
      ballAvoidingFrom G (W : Set V) E.verts 1 := by
    intro y hy
    obtain ⟨hyN, hyW⟩ := Finset.mem_sdiff.1 hy
    have hxy : G.Adj x y := (G.mem_neighborFinset x y).1 hyN
    let p : G.Walk x y := Walk.cons hxy Walk.nil
    rw [mem_ballAvoidingFrom]
    refine ⟨x, E.root_mem, p, ?_, by simp [p]⟩
    refine ⟨?_, ?_⟩
    · simp [p, Walk.cons_isPath_iff, G.ne_of_adj hxy]
    · intro z hz hzW
      simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · simp
      · exact (hyW hzW).elim
  have hsub := Finset.card_le_card hneighborSubset
  have hinter : (W ∩ G.neighborFinset x).card ≤ W.card :=
    Finset.card_le_card Finset.inter_subset_left
  rw [Finset.card_sdiff, G.card_neighborFinset_eq_degree] at hsub
  calc
    d - 1 - budget ≤ G.degree x - budget :=
      Nat.sub_le_sub_right hdegree budget
    _ ≤ G.degree x - (W ∩ G.neighborFinset x).card :=
      Nat.sub_le_sub_left (hinter.trans hW) _
    _ ≤ (ballAvoidingFrom G (W : Set V) E.verts 1).card := hsub

/-- Full Liu--Montgomery Lemma 3.4 bootstrap for two prescribed expansions.
The orders of the expansions may lie below the expander cutoff: one
radius-one layer, supplied by minimum degree after paying for `W`, is used as
the seed for the expander growth. -/
theorem exists_expansion_root_connector_of_lmExpander_bootstrap [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} {D₁ D₂ m₁ m₂ d budget : ℕ}
    (E : VertexExpansion G x D₁ m₁)
    (F : VertexExpansion G y D₂ m₂)
    (W : Finset V) (hEW : Disjoint E.verts W) (hFW : Disjoint F.verts W)
    (hExDegree : d - 1 ≤ G.degree x) (hFyDegree : d - 1 ≤ G.degree y)
    (hW : W.card ≤ budget)
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (q radius : ℕ)
    (hlower : kappa / 2 ≤ ((d - 1 - budget : ℕ) : ℝ))
    (hrate : ∀ s : ℕ, d - 1 - budget ≤ s →
      s ≤ Fintype.card V / 2 →
      (((budget + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon kappa s * (s : ℝ)))
    (hsteps : Fintype.card V / 2 + 1 ≤
      d - 1 - budget + radius * q) :
    ∃ P : G.Walk x y,
      P.IsPath ∧ P.Avoids (W : Set V) ∅ ∧
        P.length ≤ m₁ + 2 * radius + m₂ + 2 := by
  classical
  let seedE := ballAvoidingFrom G (W : Set V) E.verts 1
  let seedF := ballAvoidingFrom G (W : Set V) F.verts 1
  have hseedE : d - 1 - budget ≤ seedE.card := by
    simpa [seedE] using
      E.minDegree_sub_budget_le_card_ballAvoidingFrom_one G W hExDegree hW
  have hseedF : d - 1 - budget ≤ seedF.card := by
    simpa [seedF] using
      F.minDegree_sub_budget_le_card_ballAvoidingFrom_one G W hFyDegree hW
  have hbudget : W.card + q ≤ budget + q := Nat.add_le_add_right hW q
  have hbudgetReal : ((W.card + q : ℕ) : ℝ) ≤ (budget + q : ℕ) := by
    exact_mod_cast hbudget
  have hseedEReal : ((d - 1 - budget : ℕ) : ℝ) ≤ (seedE.card : ℝ) := by
    exact_mod_cast hseedE
  have hseedFReal : ((d - 1 - budget : ℕ) : ℝ) ≤ (seedF.card : ℝ) := by
    exact_mod_cast hseedF
  have hEball := min_card_ballAvoidingFrom_of_lmExpander_growth
    G epsilon kappa hexp W seedE q radius
      (hlower.trans hseedEReal)
      (fun s hs hsN ↦ hbudgetReal.trans (hrate s (hseedE.trans hs) hsN))
  have hFball := min_card_ballAvoidingFrom_of_lmExpander_growth
    G epsilon kappa hexp W seedF q radius
      (hlower.trans hseedFReal)
      (fun s hs hsN ↦ hbudgetReal.trans (hrate s (hseedF.trans hs) hsN))
  have hEsteps : Fintype.card V / 2 + 1 ≤ seedE.card + radius * q :=
    hsteps.trans (Nat.add_le_add_right hseedE (radius * q))
  have hFsteps : Fintype.card V / 2 + 1 ≤ seedF.card + radius * q :=
    hsteps.trans (Nat.add_le_add_right hseedF (radius * q))
  have hEhalf : Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G (W : Set V) seedE radius).card := by
    simpa [min_eq_right hEsteps] using hEball
  have hFhalf : Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G (W : Set V) seedF radius).card := by
    simpa [min_eq_right hFsteps] using hFball
  have hEnotW : ∀ a ∈ E.verts, a ∉ (W : Set V) := by
    intro a ha haW
    exact (Finset.disjoint_left.1 hEW ha haW).elim
  have hFnotW : ∀ a ∈ F.verts, a ∉ (W : Set V) := by
    intro a ha haW
    exact (Finset.disjoint_left.1 hFW ha haW).elim
  have hEsub : ballAvoidingFrom G (W : Set V) seedE radius ⊆
      ballAvoidingFrom G (W : Set V) E.verts (1 + radius) := by
    simpa [seedE] using
      ballAvoidingFrom_ballAvoidingFrom_subset
        G (W : Set V) E.verts 1 radius hEnotW
  have hFsub : ballAvoidingFrom G (W : Set V) seedF radius ⊆
      ballAvoidingFrom G (W : Set V) F.verts (1 + radius) := by
    simpa [seedF] using
      ballAvoidingFrom_ballAvoidingFrom_subset
        G (W : Set V) F.verts 1 radius hFnotW
  have hElarge : Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G (W : Set V) E.verts (1 + radius)).card :=
    hEhalf.trans (Finset.card_le_card hEsub)
  have hFlarge : Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G (W : Set V) F.verts (1 + radius)).card :=
    hFhalf.trans (Finset.card_le_card hFsub)
  have hlarge : Fintype.card V <
      (ballAvoidingFrom G (W : Set V) E.verts (1 + radius)).card +
        (ballAvoidingFrom G (W : Set V) F.verts (1 + radius)).card := by
    omega
  obtain ⟨P, hP, hPlength, hPmiss⟩ :=
    VertexExpansion.exists_path_between_roots_of_large_balls
      E F W hEW.symm hFW.symm hlarge
  refine ⟨P, hP, ?_, by omega⟩
  intro z hz hzW
  exact (hPmiss z hz hzW).elim

/-! ## Bounded labels and the finite Lemma 3.5 engine -/

/-- All subsets of `U` having cardinality at most `C`.  This is the literal
finite set of labels used in the second pigeonhole argument. -/
noncomputable def boundedSubsets (U : Finset V) (C : ℕ) : Finset (Finset V) := by
  classical
  exact U.powerset.filter fun Z ↦ Z.card ≤ C

@[simp] theorem mem_boundedSubsets (U Z : Finset V) (C : ℕ) :
    Z ∈ boundedSubsets U C ↔ Z ⊆ U ∧ Z.card ≤ C := by
  classical
  simp [boundedSubsets]

theorem blockedExternalNeighborhood_mem_boundedSubsets [Fintype V]
    (G : SimpleGraph V) (U S : Finset V) {C : ℕ}
    (hcard : (blockedExternalNeighborhood G (U : Set V) S).card ≤ C) :
    blockedExternalNeighborhood G (U : Set V) S ∈ boundedSubsets U C := by
  rw [mem_boundedSubsets]
  exact ⟨blockedExternalNeighborhood_subset_deleted G U S, hcard⟩

/-- Source-faithful count for the contact traces used in the small-set case
of Lemma 3.5.  The paper counts only subsets of `U` of size at most `C`, not
all `2 ^ |U|` subsets. -/
theorem card_boundedSubsets_le_sum_choose (U : Finset V) (C : ℕ) :
    (boundedSubsets U C).card ≤
      ∑ r ∈ Finset.range (C + 1), Nat.choose U.card r := by
  classical
  have hsub : boundedSubsets U C ⊆
      (Finset.range (C + 1)).biUnion (fun r ↦ U.powersetCard r) := by
    intro Z hZ
    have hZU : Z ⊆ U := (mem_boundedSubsets U Z C).1 hZ |>.1
    have hZcard : Z.card ≤ C := (mem_boundedSubsets U Z C).1 hZ |>.2
    rw [Finset.mem_biUnion]
    exact ⟨Z.card, by simp [hZcard], Finset.mem_powersetCard.2 ⟨hZU, rfl⟩⟩
  calc
    (boundedSubsets U C).card ≤
        ((Finset.range (C + 1)).biUnion (fun r ↦ U.powersetCard r)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ r ∈ Finset.range (C + 1), (U.powersetCard r).card :=
      Finset.card_biUnion_le
    _ = ∑ r ∈ Finset.range (C + 1), Nat.choose U.card r := by
      simp [Finset.card_powersetCard]

/-- Polynomial contact-trace bound used in the source proof of Lemma 3.5:
there are at most `(C+1) max(1,|U|)^C` subsets of `U` of size at most `C`.
Unlike the coarse powerset bound, this remains useful when `U` is
polylogarithmic but `C` is a much smaller power of `log n`. -/
theorem card_boundedSubsets_le_mul_pow (U : Finset V) (C : ℕ) :
    (boundedSubsets U C).card ≤
      (C + 1) * (max 1 U.card) ^ C := by
  calc
    (boundedSubsets U C).card ≤
        ∑ r ∈ Finset.range (C + 1), Nat.choose U.card r :=
      card_boundedSubsets_le_sum_choose U C
    _ ≤ ∑ _r ∈ Finset.range (C + 1), (max 1 U.card) ^ C := by
      apply Finset.sum_le_sum
      intro r hr
      have hrlt : r < C + 1 := Finset.mem_range.1 hr
      have hrC : r ≤ C := by omega
      calc
        Nat.choose U.card r ≤ U.card ^ r := Nat.choose_le_pow U.card r
        _ ≤ (max 1 U.card) ^ r := Nat.pow_le_pow_left (by omega) r
        _ ≤ (max 1 U.card) ^ C := Nat.pow_le_pow_right (by omega) hrC
    _ = (C + 1) * (max 1 U.card) ^ C := by simp [Finset.card_range]

/-- The exact finite two-regime form of Liu--Montgomery Lemma 3.5.

`L` is the cutoff between the two cases in the paper, `D` is the maximum
member size, and `T` is the forbidden lower bound for the union.  `qLarge`
and `qSmall` are the sample sizes.  The four real-valued assumptions are
precisely the expansion-range and expansion-rate comparisons for those two
samples; the remaining arithmetic assumptions are the two pigeonhole
comparisons. -/
private theorem liuMontgomery_lemma3_5_uniform
    [Fintype V] [Fintype I]
    (G : SimpleGraph V) (epsilon k : ℝ) (hexp : IsLMExpander G epsilon k)
    (U : Finset V) (S : I → Finset V)
    (L D T qLarge qSmall Blarge Bsmall C : ℕ)
    (hpair : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint S)
    (hnonempty : ∀ i : I, (S i).Nonempty)
    (hmax : ∀ i : I, (S i).card ≤ D)
    (hlargeN : ∀ i : I, L ≤ (S i).card →
      (availableExternalNeighborhood G (U : Set V) (S i)).card ≤ Blarge)
    (hsmallN : ∀ i : I, (S i).card < L →
      (availableExternalNeighborhood G (U : Set V) (S i)).card ≤ Bsmall)
    (hsmallU : ∀ i : I, (S i).card < L →
      (blockedExternalNeighborhood G (U : Set V) (S i)).card ≤ C)
    (hLpos : 0 < L) (hDpos : 0 < D) (hqSmallPos : 0 < qSmall)
    (hlargeSample : qLarge * D ≤ (T + 1) / 2)
    (hsmallSample :
      L * ((boundedSubsets U C).card * qSmall * L) ≤ (T + 1) / 2)
    (hlargeLower : k / 2 ≤ ((qLarge * L : ℕ) : ℝ))
    (hlargeUpper : ((qLarge * D : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hlargeRate : ∀ s : ℕ, qLarge * L ≤ s → s ≤ qLarge * D →
      (((U.card + qLarge * Blarge : ℕ) : ℝ) <
        expansionEpsilon epsilon k s * (s : ℝ)))
    (hsmallLower : ∀ r : ℕ, 0 < r → r < L →
      k / 2 ≤ ((qSmall * r : ℕ) : ℝ))
    (hsmallUpper : ∀ r : ℕ, 0 < r → r < L →
      ((qSmall * r : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hsmallRate : ∀ r : ℕ, 0 < r → r < L →
      (((C + qSmall * Bsmall : ℕ) : ℝ) <
        expansionEpsilon epsilon k (qSmall * r) * ((qSmall * r : ℕ) : ℝ))) :
    (Finset.univ.biUnion S).card < T := by
  classical
  let large : Finset I := Finset.univ.filter fun i ↦ L ≤ (S i).card
  let small : Finset I := Finset.univ.filter fun i ↦ (S i).card < L
  let half : ℕ := (T + 1) / 2
  by_contra hnot
  have htotal : T ≤ (Finset.univ.biUnion S).card := Nat.le_of_not_gt hnot
  have hcardTotal : (Finset.univ.biUnion S).card = ∑ i : I, (S i).card := by
    simpa using card_biUnion_eq_sum_card hpair
  have hsplit : (Finset.univ.biUnion S).card =
      (large.biUnion S).card + (small.biUnion S).card := by
    rw [hcardTotal]
    rw [card_biUnion_eq_sum_card (hpair.subset (by simp [large])),
      card_biUnion_eq_sum_card (hpair.subset (by simp [small]))]
    simp only [large, small]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset I)) (p := fun i ↦ L ≤ (S i).card)]
    simp
  have hhalf : T ≤ 2 * half := by
    dsimp [half]
    omega
  have hcase : half ≤ (large.biUnion S).card ∨ half ≤ (small.biUnion S).card := by
    by_contra h
    push_neg at h
    omega
  rcases hcase with hlarge | hsmall
  · have hlargeCard : (large.biUnion S).card = ∑ i ∈ large, (S i).card :=
      card_biUnion_eq_sum_card (hpair.subset (by simp [large]))
    have hsumMax : ∑ i ∈ large, (S i).card ≤ large.card * D := by
      calc
        ∑ i ∈ large, (S i).card ≤ ∑ _i ∈ large, D :=
          Finset.sum_le_sum fun i _ ↦ hmax i
        _ = large.card * D := by simp
    have hqLarge : qLarge ≤ large.card := by
      apply Nat.le_of_mul_le_mul_right (c := D) ?_ hDpos
      exact hlargeSample.trans <| hlarge.trans <| hlargeCard.trans_le hsumMax
    obtain ⟨J, hJlarge, hJcard⟩ := Finset.exists_subset_card_eq hqLarge
    have hJpair : (J : Set I).PairwiseDisjoint S := hpair.subset (by
      intro i hi
      exact Finset.mem_univ i)
    have hJcardEq : (J.biUnion S).card = ∑ i ∈ J, (S i).card :=
      card_biUnion_eq_sum_card hJpair
    have hJlowerNat : qLarge * L ≤ (J.biUnion S).card := by
      rw [hJcardEq, ← hJcard]
      calc
        J.card * L = ∑ _i ∈ J, L := by simp
        _ ≤ ∑ i ∈ J, (S i).card := Finset.sum_le_sum fun i hi ↦ by
          have hiLarge := hJlarge hi
          simpa [large] using hiLarge
    have hJupperNat : (J.biUnion S).card ≤ qLarge * D := by
      rw [hJcardEq, ← hJcard]
      calc
        ∑ i ∈ J, (S i).card ≤ ∑ _i ∈ J, D :=
          Finset.sum_le_sum fun i _ ↦ hmax i
        _ = J.card * D := by simp
    apply no_selected_family_of_deleted_neighborhood_bound
      G epsilon k hexp U S J Blarge
    · exact hlargeLower.trans (by exact_mod_cast hJlowerNat)
    · have hJupperReal : ((J.biUnion S).card : ℝ) ≤
          ((qLarge * D : ℕ) : ℝ) := by
        exact_mod_cast hJupperNat
      exact hJupperReal.trans hlargeUpper
    · intro i hi
      exact hlargeN i <| by
        have := hJlarge hi
        simpa [large] using this
    · simpa [hJcard] using hlargeRate (J.biUnion S).card hJlowerNat hJupperNat
  · have hsmallCard : (small.biUnion S).card = ∑ i ∈ small, (S i).card :=
      card_biUnion_eq_sum_card (hpair.subset (by simp [small]))
    let labelCount : ℕ := (boundedSubsets U C).card
    have hweighted : L * (labelCount * qSmall * L) ≤ ∑ i ∈ small, (S i).card := by
      calc
        L * (labelCount * qSmall * L) ≤ half := by
          simpa [labelCount] using hsmallSample
        _ ≤ (small.biUnion S).card := hsmall
        _ = ∑ i ∈ small, (S i).card := hsmallCard
    have hmapsSize : ∀ i ∈ small, (S i).card ∈ Finset.range L := by
      intro i hi
      simpa [small] using hi
    have hrange : (Finset.range L).Nonempty :=
      Finset.nonempty_range_iff.2 (Nat.ne_of_gt hLpos)
    obtain ⟨r, hrange, hrweight⟩ :=
      Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
        (s := small) (t := Finset.range L) (f := fun i ↦ (S i).card)
        (w := fun i ↦ (S i).card) hmapsSize hrange (by simpa using hweighted)
    have hrlt : r < L := Finset.mem_range.1 hrange
    let sameSize : Finset I := small.filter fun i ↦ (S i).card = r
    have hweightEq : ∑ i ∈ small with (S i).card = r, (S i).card =
        r * sameSize.card := by
      change ∑ i ∈ sameSize, (S i).card = r * sameSize.card
      calc
        ∑ i ∈ sameSize, (S i).card = ∑ _i ∈ sameSize, r :=
          Finset.sum_congr rfl fun i hi ↦ (Finset.mem_filter.1 hi).2
        _ = sameSize.card * r := by simp
        _ = r * sameSize.card := Nat.mul_comm _ _
    have hlabelCountPos : 0 < labelCount := by
      dsimp [labelCount]
      rw [Finset.card_pos]
      exact ⟨∅, by simp [boundedSubsets]⟩
    have hrpos : 0 < r := by
      by_contra hrzero
      have hrzero' : r = 0 := Nat.eq_zero_of_not_pos hrzero
      rw [hweightEq, hrzero'] at hrweight
      have hlabelqpos : 0 < labelCount * qSmall * L := by positivity
      omega
    have hsameSizeMany : labelCount * qSmall ≤ sameSize.card := by
      apply Nat.le_of_mul_le_mul_left (c := r) ?_ hrpos
      rw [hweightEq] at hrweight
      calc
        r * (labelCount * qSmall) ≤ L * (labelCount * qSmall) := by
          exact Nat.mul_le_mul_right (labelCount * qSmall) (Nat.le_of_lt hrlt)
        _ = labelCount * qSmall * L := by ac_rfl
        _ ≤ r * sameSize.card := hrweight
    let blockLabel : I → Finset V := fun i ↦
      blockedExternalNeighborhood G (U : Set V) (S i)
    have hmapsLabel : ∀ i ∈ sameSize,
        blockLabel i ∈ boundedSubsets U C := by
      intro i hi
      apply blockedExternalNeighborhood_mem_boundedSubsets G U (S i)
      apply hsmallU i
      have hiSmall : i ∈ small := (Finset.mem_filter.1 hi).1
      simpa [small] using hiSmall
    have hlabelsNonempty : (boundedSubsets U C).Nonempty :=
      ⟨∅, by simp [boundedSubsets]⟩
    obtain ⟨Z, hZlabel, hZfiber⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := sameSize) (t := boundedSubsets U C) (f := blockLabel)
        hmapsLabel hlabelsNonempty (by simpa [labelCount, mul_comm] using hsameSizeMany)
    let fiber : Finset I := sameSize.filter fun i ↦ blockLabel i = Z
    have hqSmall : qSmall ≤ fiber.card := by simpa [fiber] using hZfiber
    obtain ⟨J, hJfiber, hJcard⟩ := Finset.exists_subset_card_eq hqSmall
    have hJpair : (J : Set I).PairwiseDisjoint S := hpair.subset (by
      intro i hi
      exact Finset.mem_univ i)
    have hJcardEq : (J.biUnion S).card = ∑ i ∈ J, (S i).card :=
      card_biUnion_eq_sum_card hJpair
    have hJsize : ∀ i ∈ J, (S i).card = r := by
      intro i hi
      have hiFiber := hJfiber hi
      have hiSame : i ∈ sameSize := (Finset.mem_filter.1 hiFiber).1
      exact (Finset.mem_filter.1 hiSame).2
    have hJunionCard : (J.biUnion S).card = qSmall * r := by
      rw [hJcardEq]
      calc
        ∑ i ∈ J, (S i).card = ∑ _i ∈ J, r :=
          Finset.sum_congr rfl fun i hi ↦ hJsize i hi
        _ = qSmall * r := by simp [hJcard, mul_comm]
    have hJblocked : ∀ i ∈ J,
        blockedExternalNeighborhood G (U : Set V) (S i) = Z := by
      intro i hi
      have hiFiber := hJfiber hi
      exact (Finset.mem_filter.1 hiFiber).2
    apply no_selected_family_of_common_blocked_neighborhood
      G epsilon k hexp U Z S J Bsmall C
    · rw [hJunionCard]
      exact hsmallLower r hrpos hrlt
    · rw [hJunionCard]
      exact hsmallUpper r hrpos hrlt
    · exact hJblocked
    · exact (mem_boundedSubsets U Z C).1 hZlabel |>.2
    · intro i hi
      apply hsmallN i
      rw [hJsize i hi]
      exact hrlt
    · simpa [hJcard, hJunionCard] using hsmallRate r hrpos hrlt

/-- Size-correlated finite form of Liu--Montgomery Lemma 3.5.  In the large
regime the selected family keeps the exact sum of its neighborhood budgets.
In the small regime both the blocked-neighborhood label space and the sample
size depend on the common cardinality `r`.  This is the form whose hypotheses
match the two asymptotic regimes in the source proof. -/
theorem liuMontgomery_lemma3_5_finite
    [Fintype V] [Fintype I]
    (G : SimpleGraph V) (epsilon k : ℝ) (hexp : IsLMExpander G epsilon k)
    (U : Finset V) (S : I → Finset V)
    (minSize cutoff D T qLarge : ℕ)
    (qSmall neighborBudget blockedBudget largeBudget : ℕ → ℕ)
    (hpair : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint S)
    (hmin : ∀ i : I, minSize ≤ (S i).card)
    (hmax : ∀ i : I, (S i).card ≤ D)
    (hneighborhood : ∀ i : I,
      (availableExternalNeighborhood G (U : Set V) (S i)).card ≤
        neighborBudget (S i).card)
    (hblocked : ∀ i : I, (S i).card < cutoff →
      (blockedExternalNeighborhood G (U : Set V) (S i)).card ≤
        blockedBudget (S i).card)
    (hminSizePos : 0 < minSize) (hcutoffPos : 0 < cutoff)
    (hDpos : 0 < D) (hTpos : 0 < T)
    (hqSmallPos : ∀ r : ℕ, minSize ≤ r → r < cutoff → 0 < qSmall r)
    (hlargeSample : qLarge * D ≤ (T + 1) / 2)
    (hsmallSample :
      ∑ r ∈ Finset.Ico minSize cutoff,
        r * ((boundedSubsets U (blockedBudget r)).card * qSmall r) ≤
          (T + 1) / 2)
    (hlargeLower : k / 2 ≤ ((qLarge * cutoff : ℕ) : ℝ))
    (hlargeUpper : ((qLarge * D : ℕ) : ℝ) ≤
      (Fintype.card V : ℝ) / 2)
    (hlargeBudgetSum : ∀ (J : Finset I) (f : I → ℕ),
      (∀ i ∈ J, cutoff ≤ f i ∧ f i ≤ D) →
      ∑ i ∈ J, neighborBudget (f i) ≤ largeBudget (∑ i ∈ J, f i))
    (hlargeRate : ∀ s : ℕ, qLarge * cutoff ≤ s → s ≤ qLarge * D →
      (((U.card + largeBudget s : ℕ) : ℝ) <
        expansionEpsilon epsilon k s * (s : ℝ)))
    (hsmallLower : ∀ r : ℕ, minSize ≤ r → r < cutoff →
      k / 2 ≤ ((qSmall r * r : ℕ) : ℝ))
    (hsmallUpper : ∀ r : ℕ, minSize ≤ r → r < cutoff →
      ((qSmall r * r : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hsmallRate : ∀ r : ℕ, minSize ≤ r → r < cutoff →
      (((blockedBudget r + qSmall r * neighborBudget r : ℕ) : ℝ) <
        expansionEpsilon epsilon k (qSmall r * r) *
          ((qSmall r * r : ℕ) : ℝ))) :
    (Finset.univ.biUnion S).card < T := by
  classical
  let large : Finset I := Finset.univ.filter fun i ↦ cutoff ≤ (S i).card
  let small : Finset I := Finset.univ.filter fun i ↦ (S i).card < cutoff
  let half : ℕ := (T + 1) / 2
  by_contra hnot
  have htotal : T ≤ (Finset.univ.biUnion S).card := Nat.le_of_not_gt hnot
  have hcardTotal : (Finset.univ.biUnion S).card = ∑ i : I, (S i).card := by
    simpa using card_biUnion_eq_sum_card hpair
  have hsplit : (Finset.univ.biUnion S).card =
      (large.biUnion S).card + (small.biUnion S).card := by
    rw [hcardTotal]
    rw [card_biUnion_eq_sum_card (hpair.subset (by simp [large])),
      card_biUnion_eq_sum_card (hpair.subset (by simp [small]))]
    simp only [large, small]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset I)) (p := fun i ↦ cutoff ≤ (S i).card)]
    simp
  have hhalf : T ≤ 2 * half := by
    dsimp [half]
    omega
  have hcase : half ≤ (large.biUnion S).card ∨
      half ≤ (small.biUnion S).card := by
    by_contra h
    push_neg at h
    omega
  rcases hcase with hlarge | hsmall
  · have hlargeCard : (large.biUnion S).card = ∑ i ∈ large, (S i).card :=
      card_biUnion_eq_sum_card (hpair.subset (by simp [large]))
    have hsumMax : ∑ i ∈ large, (S i).card ≤ large.card * D := by
      calc
        ∑ i ∈ large, (S i).card ≤ ∑ _i ∈ large, D :=
          Finset.sum_le_sum fun i _ ↦ hmax i
        _ = large.card * D := by simp
    have hqLarge : qLarge ≤ large.card := by
      apply Nat.le_of_mul_le_mul_right (c := D) ?_ hDpos
      exact hlargeSample.trans <| hlarge.trans <| hlargeCard.trans_le hsumMax
    obtain ⟨J, hJlarge, hJcard⟩ := Finset.exists_subset_card_eq hqLarge
    have hJpair : (J : Set I).PairwiseDisjoint S := hpair.subset (by simp)
    have hJcardEq : (J.biUnion S).card = ∑ i ∈ J, (S i).card :=
      card_biUnion_eq_sum_card hJpair
    have hJlargeSize : ∀ i ∈ J, cutoff ≤ (S i).card := by
      intro i hi
      simpa [large] using hJlarge hi
    have hJlowerNat : qLarge * cutoff ≤ (J.biUnion S).card := by
      rw [hJcardEq, ← hJcard]
      calc
        J.card * cutoff = ∑ _i ∈ J, cutoff := by simp
        _ ≤ ∑ i ∈ J, (S i).card :=
          Finset.sum_le_sum fun i hi ↦ hJlargeSize i hi
    have hJupperNat : (J.biUnion S).card ≤ qLarge * D := by
      rw [hJcardEq, ← hJcard]
      calc
        ∑ i ∈ J, (S i).card ≤ ∑ _i ∈ J, D :=
          Finset.sum_le_sum fun i _ ↦ hmax i
        _ = J.card * D := by simp
    have hbudgetSum : ∑ i ∈ J, neighborBudget (S i).card ≤
        largeBudget (J.biUnion S).card := by
      rw [hJcardEq]
      apply hlargeBudgetSum J (fun i ↦ (S i).card)
      intro i hi
      exact ⟨hJlargeSize i hi, hmax i⟩
    have hlargeNumeric :
        (((U.card + ∑ i ∈ J, neighborBudget (S i).card : ℕ) : ℝ) <
          expansionEpsilon epsilon k (J.biUnion S).card *
            ((J.biUnion S).card : ℝ)) := by
      have hcast : ((U.card + ∑ i ∈ J, neighborBudget (S i).card : ℕ) : ℝ) ≤
          ((U.card + largeBudget (J.biUnion S).card : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_left hbudgetSum U.card
      exact hcast.trans_lt (hlargeRate (J.biUnion S).card hJlowerNat hJupperNat)
    apply no_selected_family_of_deleted_neighborhood_sum_bound
      G epsilon k hexp U S J (fun i ↦ neighborBudget (S i).card)
    · exact hlargeLower.trans (by exact_mod_cast hJlowerNat)
    · have hupperCast : (((J.biUnion S).card : ℕ) : ℝ) ≤
          ((qLarge * D : ℕ) : ℝ) := by
        exact_mod_cast hJupperNat
      exact hupperCast.trans hlargeUpper
    · intro i _
      exact hneighborhood i
    · exact hlargeNumeric
  · have hsmallCard : (small.biUnion S).card = ∑ i ∈ small, (S i).card :=
      card_biUnion_eq_sum_card (hpair.subset (by simp [small]))
    have hhalfPos : 0 < half := by
      dsimp [half]
      omega
    have hsmallUnionNe : (small.biUnion S).Nonempty :=
      Finset.card_pos.1 (hhalfPos.trans_le hsmall)
    obtain ⟨x, hxsmall⟩ := hsmallUnionNe
    obtain ⟨i₀, hi₀small, _⟩ := Finset.mem_biUnion.1 hxsmall
    have hmapsSize : ∀ i ∈ small,
        (S i).card ∈ Finset.Ico minSize cutoff := by
      intro i hi
      rw [Finset.mem_Ico]
      exact ⟨hmin i, by simpa [small] using hi⟩
    have hsizesNonempty : (Finset.Ico minSize cutoff).Nonempty :=
      ⟨(S i₀).card, hmapsSize i₀ hi₀small⟩
    have hthreshold :
        ∑ r ∈ Finset.Ico minSize cutoff,
          r * ((boundedSubsets U (blockedBudget r)).card * qSmall r) ≤
            ∑ i ∈ small, (S i).card := by
      calc
        _ ≤ half := by simpa [half] using hsmallSample
        _ ≤ (small.biUnion S).card := hsmall
        _ = _ := hsmallCard
    have hfiberSum :
        ∑ r ∈ Finset.Ico minSize cutoff,
            (∑ i ∈ small with (S i).card = r, (S i).card) =
          ∑ i ∈ small, (S i).card := by
      simpa using (Finset.sum_fiberwise_of_maps_to hmapsSize
        (fun i ↦ (S i).card))
    have hexr : ∃ r ∈ Finset.Ico minSize cutoff,
        r * ((boundedSubsets U (blockedBudget r)).card * qSmall r) ≤
          ∑ i ∈ small with (S i).card = r, (S i).card := by
      by_contra hno
      push_neg at hno
      obtain ⟨r₀, hr₀⟩ := hsizesNonempty
      have hsumlt :
          ∑ r ∈ Finset.Ico minSize cutoff,
              (∑ i ∈ small with (S i).card = r, (S i).card) <
            ∑ r ∈ Finset.Ico minSize cutoff,
              r * ((boundedSubsets U (blockedBudget r)).card * qSmall r) := by
        apply Finset.sum_lt_sum
        · intro r hr
          exact (hno r hr).le
        · exact ⟨r₀, hr₀, hno r₀ hr₀⟩
      rw [hfiberSum] at hsumlt
      exact (Nat.not_lt_of_ge hthreshold) hsumlt
    obtain ⟨r, hrange, hrweight⟩ := hexr
    have hrmin : minSize ≤ r := (Finset.mem_Ico.1 hrange).1
    have hrpos : 0 < r := hminSizePos.trans_le hrmin
    have hrlt : r < cutoff := (Finset.mem_Ico.1 hrange).2
    let sameSize : Finset I := small.filter fun i ↦ (S i).card = r
    have hweightEq : ∑ i ∈ small with (S i).card = r, (S i).card =
        r * sameSize.card := by
      change ∑ i ∈ sameSize, (S i).card = r * sameSize.card
      calc
        ∑ i ∈ sameSize, (S i).card = ∑ _i ∈ sameSize, r := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (Finset.mem_filter.1 hi).2
        _ = sameSize.card * r := by simp
        _ = r * sameSize.card := Nat.mul_comm _ _
    rw [hweightEq] at hrweight
    let labelCount : ℕ := (boundedSubsets U (blockedBudget r)).card
    have hlabelCountPos : 0 < labelCount := by
      dsimp [labelCount]
      rw [Finset.card_pos]
      exact ⟨∅, by simp [boundedSubsets]⟩
    have hsameSizeMany : labelCount * qSmall r ≤ sameSize.card := by
      apply Nat.le_of_mul_le_mul_left (c := r) ?_ hrpos
      simpa [labelCount, Nat.mul_assoc] using hrweight
    have hqpos : 0 < qSmall r := hqSmallPos r hrmin hrlt
    let blockLabel : I → Finset V := fun i ↦
      blockedExternalNeighborhood G (U : Set V) (S i)
    have hmapsLabel : ∀ i ∈ sameSize,
        blockLabel i ∈ boundedSubsets U (blockedBudget r) := by
      intro i hi
      apply blockedExternalNeighborhood_mem_boundedSubsets G U (S i)
      have hiSmall : i ∈ small := (Finset.mem_filter.1 hi).1
      have hiSize : (S i).card = r := (Finset.mem_filter.1 hi).2
      simpa [hiSize] using hblocked i (by simpa [small] using hiSmall)
    have hlabelsNonempty : (boundedSubsets U (blockedBudget r)).Nonempty :=
      ⟨∅, by simp [boundedSubsets]⟩
    obtain ⟨Z, hZlabel, hZfiber⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := sameSize) (t := boundedSubsets U (blockedBudget r)) (f := blockLabel)
        hmapsLabel hlabelsNonempty
        (by simpa [labelCount, mul_comm] using hsameSizeMany)
    let fiber : Finset I := sameSize.filter fun i ↦ blockLabel i = Z
    have hqSmall : qSmall r ≤ fiber.card := by simpa [fiber] using hZfiber
    obtain ⟨J, hJfiber, hJcard⟩ := Finset.exists_subset_card_eq hqSmall
    have hJpair : (J : Set I).PairwiseDisjoint S := hpair.subset (by simp)
    have hJcardEq : (J.biUnion S).card = ∑ i ∈ J, (S i).card :=
      card_biUnion_eq_sum_card hJpair
    have hJsize : ∀ i ∈ J, (S i).card = r := by
      intro i hi
      exact (Finset.mem_filter.1 ((Finset.mem_filter.1 (hJfiber hi)).1)).2
    have hJunionCard : (J.biUnion S).card = qSmall r * r := by
      rw [hJcardEq]
      calc
        ∑ i ∈ J, (S i).card = ∑ _i ∈ J, r :=
          Finset.sum_congr rfl fun i hi ↦ hJsize i hi
        _ = qSmall r * r := by simp [hJcard, mul_comm]
    have hJblocked : ∀ i ∈ J,
        blockedExternalNeighborhood G (U : Set V) (S i) = Z := by
      intro i hi
      exact (Finset.mem_filter.1 (hJfiber hi)).2
    apply no_selected_family_of_common_blocked_neighborhood
      G epsilon k hexp U Z S J (neighborBudget r) (blockedBudget r)
    · rw [hJunionCard]
      exact hsmallLower r hrmin hrlt
    · rw [hJunionCard]
      exact hsmallUpper r hrmin hrlt
    · exact hJblocked
    · exact (mem_boundedSubsets U Z (blockedBudget r)).1 hZlabel |>.2
    · intro i hi
      simpa [hJsize i hi] using hneighborhood i
    · simpa [hJcard, hJunionCard] using hsmallRate r hrmin hrlt

/-! ## The many-ball consequence (Liu--Montgomery Lemma 3.7) -/

/-- The source-style separation hypothesis in Lemma 3.7 implies that the
radius-`radius` balls grown with the individual extra deletions `B i` and
`Cset i` are pairwise disjoint.  The comparison is made in `G - U`, so it
remains valid even though the larger forbidden sets depend on the index. -/
theorem pairwiseDisjoint_ballAvoidingFrom_union_three_of_no_short_path
    [Fintype V] [Fintype I]
    (G : SimpleGraph V) (U : Finset V) (A B Cset : I → Finset V)
    (radius : ℕ)
    (hfar : ∀ i j : I, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j,
      ∀ p : G.Walk a b,
        p.IsAvoidingPath (U : Set V) ({a, b} : Set V) →
          radius + radius < p.length) :
    ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius) := by
  classical
  intro i _ j _ hij
  have hdisj : Disjoint
      (ballAvoidingFrom G (U : Set V) (A i) radius)
      (ballAvoidingFrom G (U : Set V) (A j) radius) := by
    apply disjoint_ballAvoidingFrom_of_no_short_path
    intro a ha b hb p hp
    exact hfar i j hij a ha b hb p hp
  apply hdisj.mono
  · apply ballAvoidingFrom_forbidden_anti G
    intro v hv
    exact Or.inl (Or.inl hv)
  · apply ballAvoidingFrom_forbidden_anti G
    intro v hv
    exact Or.inl (Or.inl hv)

/-- Exact finite form of the many-simultaneous-expansions argument in
Liu--Montgomery Lemma 3.7.

For each index, `A i` is grown while avoiding `U ∪ B i ∪ C i`.  The
limited-contact hypothesis controls only the vertices of `C i` actually met.
If the radius-`radius` balls are pairwise disjoint and there are at least `T`
indices, the lower-degree-set obstruction forces one ball to reach `M`.

The parameters following `hcontact` are purely numerical: `growth` is the
comparison curve used to choose the first slow radius, `stepLoss` bounds one
jump of that curve, and the remaining assumptions are exactly those of
`liuMontgomery_lemma3_5_finite` for the resulting first-slow balls. -/
private theorem liuMontgomery_lemma3_7_uniform
    [Fintype V] [Fintype I]
    (G : SimpleGraph V) (epsilon k : ℝ) (hexp : IsLMExpander G epsilon k)
    (U : Finset V) (A B Cset : I → Finset V)
    (contact radius M : ℕ) (growth : ℕ → ℕ)
    (hAne : ∀ i : I, (A i).Nonempty)
    (hstart : ∀ i : I, growth 0 < (A i).card)
    (htargetGrowth : M ≤ growth radius)
    (hcontact : ∀ i : I,
      HasLimitedContactAfterDeletion G (A i) (U ∪ B i) (Cset i) contact)
    (hpairBalls : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius))
    (L D T qLarge qSmall Bneighbor Cblocked degreeIntoU stepLoss Bmax : ℕ)
    (hIndex : T ≤ Fintype.card I)
    (hMD : M ≤ D)
    (hBmax : ∀ i : I, (B i).card ≤ Bmax)
    (hjump : ∀ ell : ℕ, 0 < ell → ell ≤ radius →
      growth ell ≤ growth (ell - 1) + 1 + stepLoss)
    (hneighborBudget : stepLoss + Bmax + contact * radius ≤ Bneighbor)
    (hdegreeU : ∀ i : I, ∀ v ∈ ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius,
        (G.neighborFinset v ∩ U).card ≤ degreeIntoU)
    (hblockedBudget : L * degreeIntoU ≤ Cblocked)
    (hLpos : 0 < L) (hDpos : 0 < D) (hqSmallPos : 0 < qSmall)
    (hlargeSample : qLarge * D ≤ (T + 1) / 2)
    (hsmallSample :
      L * ((boundedSubsets U Cblocked).card * qSmall * L) ≤ (T + 1) / 2)
    (hlargeLower : k / 2 ≤ ((qLarge * L : ℕ) : ℝ))
    (hlargeUpper : ((qLarge * D : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hlargeRate : ∀ s : ℕ, qLarge * L ≤ s → s ≤ qLarge * D →
      (((U.card + qLarge * Bneighbor : ℕ) : ℝ) <
        expansionEpsilon epsilon k s * (s : ℝ)))
    (hsmallLower : ∀ r : ℕ, 0 < r → r < L →
      k / 2 ≤ ((qSmall * r : ℕ) : ℝ))
    (hsmallUpper : ∀ r : ℕ, 0 < r → r < L →
      ((qSmall * r : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hsmallRate : ∀ r : ℕ, 0 < r → r < L →
      (((Cblocked + qSmall * Bneighbor : ℕ) : ℝ) <
        expansionEpsilon epsilon k (qSmall * r) * ((qSmall * r : ℕ) : ℝ))) :
    ∃ i : I, M ≤ (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius).card := by
  classical
  by_contra hnone
  push_neg at hnone
  let X : I → Set V := fun i ↦
    (U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)
  have hfirst (i : I) : ∃ ell : ℕ, 0 < ell ∧ ell ≤ radius ∧
      (ballAvoidingFrom G (X i) (A i) ell).card ≤ growth ell ∧
      growth (ell - 1) <
        (ballAvoidingFrom G (X i) (A i) (ell - 1)).card := by
    apply exists_first_slow_ball G (X i) (A i) radius growth (hstart i)
    exact (Nat.le_of_lt (hnone i)).trans htargetGrowth
  let ell : I → ℕ := fun i ↦ Classical.choose (hfirst i)
  have hell (i : I) : 0 < ell i ∧ ell i ≤ radius ∧
      (ballAvoidingFrom G (X i) (A i) (ell i)).card ≤ growth (ell i) ∧
      growth (ell i - 1) <
        (ballAvoidingFrom G (X i) (A i) (ell i - 1)).card :=
    Classical.choose_spec (hfirst i)
  let slowBall : I → Finset V := fun i ↦
    ballAvoidingFrom G (X i) (A i) (ell i - 1)
  have hslowSubset (i : I) : slowBall i ⊆
      ballAvoidingFrom G (X i) (A i) radius := by
    exact ballAvoidingFrom_radius_mono G (X i) (A i)
      ((Nat.sub_le (ell i) 1).trans (hell i).2.1)
  have hpairSlow : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint slowBall :=
    hpairBalls.mono hslowSubset
  have hslowNonempty (i : I) : (slowBall i).Nonempty := by
    obtain ⟨a, ha⟩ := hAne i
    exact ⟨a, subset_ballAvoidingFrom G (X i) (A i) (ell i - 1) ha⟩
  have hslowMax (i : I) : (slowBall i).card ≤ D := by
    calc
      (slowBall i).card ≤ (ballAvoidingFrom G (X i) (A i) radius).card :=
        Finset.card_le_card (hslowSubset i)
      _ ≤ M := Nat.le_of_lt (hnone i)
      _ ≤ D := hMD
  have hslowNeighborhood (i : I) :
      (availableExternalNeighborhood G (U : Set V) (slowBall i)).card ≤ Bneighbor := by
    have hclaim := card_available_first_slow_ball_le
      G U (B i) (Cset i) (A i) contact (ell i) stepLoss growth
        (hell i).1 (hell i).2.2.1 (hell i).2.2.2
        (hjump (ell i) (hell i).1 (hell i).2.1) (hcontact i)
    have hellradius : ell i ≤ radius := (hell i).2.1
    have hcontactRadius : contact * ell i ≤ contact * radius :=
      Nat.mul_le_mul_left contact hellradius
    have hBi := hBmax i
    dsimp [slowBall, X] at hclaim ⊢
    omega
  have hslowBlocked (i : I) (hi : (slowBall i).card < L) :
      (blockedExternalNeighborhood G (U : Set V) (slowBall i)).card ≤ Cblocked := by
    have hdegree : ∀ v ∈ slowBall i,
        (G.neighborFinset v ∩ U).card ≤ degreeIntoU := by
      intro v hv
      exact hdegreeU i v (hslowSubset i hv)
    have hcount := card_blockedExternalNeighborhood_le_card_mul_of_degree_into
      G U (slowBall i) degreeIntoU hdegree
    calc
      (blockedExternalNeighborhood G (U : Set V) (slowBall i)).card
          ≤ (slowBall i).card * degreeIntoU := hcount
      _ ≤ L * degreeIntoU := Nat.mul_le_mul_right degreeIntoU (Nat.le_of_lt hi)
      _ ≤ Cblocked := hblockedBudget
  have hunionSmall : (Finset.univ.biUnion slowBall).card < T :=
    liuMontgomery_lemma3_5_uniform G epsilon k hexp U slowBall
      L D T qLarge qSmall Bneighbor Bneighbor Cblocked hpairSlow
      hslowNonempty hslowMax
      (fun i _ ↦ hslowNeighborhood i) (fun i _ ↦ hslowNeighborhood i)
      hslowBlocked hLpos hDpos hqSmallPos hlargeSample hsmallSample
      hlargeLower hlargeUpper hlargeRate hsmallLower hsmallUpper hsmallRate
  have hindexUnion : Fintype.card I ≤ (Finset.univ.biUnion slowBall).card := by
    rw [card_biUnion_eq_sum_card hpairSlow]
    calc
      Fintype.card I = ∑ _i : I, 1 := by simp
      _ ≤ ∑ i : I, (slowBall i).card :=
        Finset.sum_le_sum fun i _ ↦ Finset.one_le_card.2 (hslowNonempty i)
  omega

/-- Source-faithful, size-correlated form of Liu--Montgomery Lemma 3.7.
The first-slow neighborhood is charged to `neighborBudget` at its actual
cardinality.  The radius-one bootstrap supplies the lower bound required by
Lemma 3.5, including the high-degree alternative used in the source. -/
theorem liuMontgomery_lemma3_7_correlated
    [Fintype V] [Fintype I]
    (G : SimpleGraph V) (epsilon k : ℝ) (hexp : IsLMExpander G epsilon k)
    (U : Finset V) (A B Cset : I → Finset V)
    (contact radius M : ℕ) (growth : ℕ → ℕ)
    (minSize cutoff D T qLarge degreeIntoU : ℕ)
    (qSmall neighborBudget blockedBudget largeBudget stepLoss : ℕ → ℕ)
    (hstart : ∀ i : I, growth 0 < (A i).card)
    (hstartOne : ∀ i : I, growth 1 < (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) 1).card)
    (hballOneLower : ∀ i : I, minSize ≤ (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) 1).card)
    (htargetGrowth : M ≤ growth radius)
    (hcontact : ∀ i : I,
      HasLimitedContactAfterDeletion G (A i) (U ∪ B i) (Cset i) contact)
    (hpairBalls : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius))
    (hIndex : T ≤ Fintype.card I)
    (hMD : M ≤ D)
    (hjump : ∀ ell : ℕ, 0 < ell → ell ≤ radius →
      growth ell ≤ growth (ell - 1) + 1 + stepLoss ell)
    (hneighborPoint : ∀ (i : I) (ell : ℕ), 0 < ell → ell ≤ radius →
      growth (ell - 1) < (ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
        (A i) (ell - 1)).card →
      stepLoss ell + (B i).card + contact * ell ≤
        neighborBudget (ballAvoidingFrom G
          ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
          (A i) (ell - 1)).card)
    (hdegreeU : ∀ i : I, ∀ v ∈ ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius,
        (G.neighborFinset v ∩ U).card ≤ degreeIntoU)
    (hblockedProfile : ∀ s : ℕ, minSize ≤ s → s < cutoff →
      s * degreeIntoU ≤ blockedBudget s)
    (hminSizePos : 0 < minSize) (hcutoffPos : 0 < cutoff)
    (hDpos : 0 < D) (hTpos : 0 < T)
    (hqSmallPos : ∀ r : ℕ, minSize ≤ r → r < cutoff → 0 < qSmall r)
    (hlargeSample : qLarge * D ≤ (T + 1) / 2)
    (hsmallSample :
      ∑ r ∈ Finset.Ico minSize cutoff,
        r * ((boundedSubsets U (blockedBudget r)).card * qSmall r) ≤
          (T + 1) / 2)
    (hlargeLower : k / 2 ≤ ((qLarge * cutoff : ℕ) : ℝ))
    (hlargeUpper : ((qLarge * D : ℕ) : ℝ) ≤
      (Fintype.card V : ℝ) / 2)
    (hlargeBudgetSum : ∀ (J : Finset I) (f : I → ℕ),
      (∀ i ∈ J, cutoff ≤ f i ∧ f i ≤ D) →
      ∑ i ∈ J, neighborBudget (f i) ≤ largeBudget (∑ i ∈ J, f i))
    (hlargeRate : ∀ s : ℕ, qLarge * cutoff ≤ s → s ≤ qLarge * D →
      (((U.card + largeBudget s : ℕ) : ℝ) <
        expansionEpsilon epsilon k s * (s : ℝ)))
    (hsmallLower : ∀ r : ℕ, minSize ≤ r → r < cutoff →
      k / 2 ≤ ((qSmall r * r : ℕ) : ℝ))
    (hsmallUpper : ∀ r : ℕ, minSize ≤ r → r < cutoff →
      ((qSmall r * r : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hsmallRate : ∀ r : ℕ, minSize ≤ r → r < cutoff →
      (((blockedBudget r + qSmall r * neighborBudget r : ℕ) : ℝ) <
        expansionEpsilon epsilon k (qSmall r * r) *
          ((qSmall r * r : ℕ) : ℝ))) :
    ∃ i : I, M ≤ (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius).card := by
  classical
  by_contra hnone
  push_neg at hnone
  let X : I → Set V := fun i ↦
    (U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)
  have hfirst (i : I) : ∃ ell : ℕ, 0 < ell ∧ ell ≤ radius ∧
      (ballAvoidingFrom G (X i) (A i) ell).card ≤ growth ell ∧
      growth (ell - 1) <
        (ballAvoidingFrom G (X i) (A i) (ell - 1)).card := by
    apply exists_first_slow_ball G (X i) (A i) radius growth (hstart i)
    exact (Nat.le_of_lt (hnone i)).trans htargetGrowth
  let ell : I → ℕ := fun i ↦ Classical.choose (hfirst i)
  have hell (i : I) : 0 < ell i ∧ ell i ≤ radius ∧
      (ballAvoidingFrom G (X i) (A i) (ell i)).card ≤ growth (ell i) ∧
      growth (ell i - 1) <
        (ballAvoidingFrom G (X i) (A i) (ell i - 1)).card :=
    Classical.choose_spec (hfirst i)
  have hellTwo (i : I) : 2 ≤ ell i := by
    by_contra hnot
    have hellPos : 0 < ell i := (hell i).1
    have hellOne : ell i = 1 := by omega
    have hslow := (hell i).2.2.1
    rw [hellOne] at hslow
    exact (Nat.not_le_of_gt (by simpa [X] using hstartOne i)) hslow
  let slowBall : I → Finset V := fun i ↦
    ballAvoidingFrom G (X i) (A i) (ell i - 1)
  have hslowSubset (i : I) : slowBall i ⊆
      ballAvoidingFrom G (X i) (A i) radius :=
    ballAvoidingFrom_radius_mono G (X i) (A i)
      ((Nat.sub_le (ell i) 1).trans (hell i).2.1)
  have hpairSlow : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint slowBall :=
    hpairBalls.mono hslowSubset
  have hslowMin (i : I) : minSize ≤ (slowBall i).card := by
    have hsub : ballAvoidingFrom G (X i) (A i) 1 ⊆ slowBall i :=
      ballAvoidingFrom_radius_mono G (X i) (A i) (by
        have htwo := hellTwo i
        omega)
    have hbase : minSize ≤ (ballAvoidingFrom G (X i) (A i) 1).card := by
      simpa [X] using hballOneLower i
    exact hbase.trans (Finset.card_le_card hsub)
  have hslowMax (i : I) : (slowBall i).card ≤ D := by
    calc
      (slowBall i).card ≤ (ballAvoidingFrom G (X i) (A i) radius).card :=
        Finset.card_le_card (hslowSubset i)
      _ ≤ M := Nat.le_of_lt (hnone i)
      _ ≤ D := hMD
  have hslowNeighborhood (i : I) :
      (availableExternalNeighborhood G (U : Set V) (slowBall i)).card ≤
        neighborBudget (slowBall i).card := by
    have hclaim := card_available_first_slow_ball_le
      G U (B i) (Cset i) (A i) contact (ell i) (stepLoss (ell i)) growth
        (hell i).1 (hell i).2.2.1 (hell i).2.2.2
        (hjump (ell i) (hell i).1 (hell i).2.1) (hcontact i)
    have hpoint := hneighborPoint i (ell i) (hell i).1 (hell i).2.1
      (hell i).2.2.2
    dsimp [slowBall, X] at hclaim hpoint ⊢
    exact hclaim.trans hpoint
  have hslowBlocked (i : I) (hi : (slowBall i).card < cutoff) :
      (blockedExternalNeighborhood G (U : Set V) (slowBall i)).card ≤
        blockedBudget (slowBall i).card := by
    have hdegree : ∀ v ∈ slowBall i,
        (G.neighborFinset v ∩ U).card ≤ degreeIntoU := by
      intro v hv
      exact hdegreeU i v (hslowSubset i hv)
    exact (card_blockedExternalNeighborhood_le_card_mul_of_degree_into
      G U (slowBall i) degreeIntoU hdegree).trans
        (hblockedProfile (slowBall i).card (hslowMin i) hi)
  have hunionSmall : (Finset.univ.biUnion slowBall).card < T :=
    liuMontgomery_lemma3_5_finite G epsilon k hexp U slowBall
      minSize cutoff D T qLarge qSmall neighborBudget blockedBudget largeBudget
      hpairSlow hslowMin hslowMax hslowNeighborhood hslowBlocked
      hminSizePos hcutoffPos hDpos hTpos hqSmallPos hlargeSample hsmallSample
      hlargeLower hlargeUpper hlargeBudgetSum hlargeRate
      hsmallLower hsmallUpper hsmallRate
  have hslowNonempty (i : I) : (slowBall i).Nonempty :=
    Finset.card_pos.1 (hminSizePos.trans_le (hslowMin i))
  have hindexUnion : Fintype.card I ≤ (Finset.univ.biUnion slowBall).card := by
    rw [card_biUnion_eq_sum_card hpairSlow]
    calc
      Fintype.card I = ∑ _i : I, 1 := by simp
      _ ≤ ∑ i : I, (slowBall i).card :=
        Finset.sum_le_sum fun i _ ↦ Finset.one_le_card.2 (hslowNonempty i)
  omega

/-- Canonical source-numbered name for the correlated Lemma 3.7. -/
alias liuMontgomery_lemma3_7_finite := liuMontgomery_lemma3_7_correlated

end Erdos63
