/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Data.Set.Finite.Lattice

/-!
# Small pairwise-disjoint families

This file collects the elementary cardinal bookkeeping used repeatedly in the
proof of the infinite Erdős--Menger theorem.  If a pairwise-disjoint family of
sets all meets a fixed set `S`, choosing one point of `S` from every member of
the family gives an injection into `S`.  The remaining results package the
countable, finite, and regular-cardinal consequences of this observation and
the corresponding bounds for unions of supports.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace FamilyTools

universe u

variable {ι V : Type u} {I : Set ι} {F : ι → Set V} {S : Set V}

/-- Choose a point in `S ∩ F i` for every `i ∈ I`. -/
def meetingSelector
    (hmeet : ∀ i ∈ I, ∃ x ∈ S, x ∈ F i) : I → S :=
  fun i =>
    ⟨Classical.choose (hmeet i.1 i.2),
      (Classical.choose_spec (hmeet i.1 i.2)).1⟩

@[simp]
theorem meetingSelector_mem_target
    (hmeet : ∀ i ∈ I, ∃ x ∈ S, x ∈ F i) (i : I) :
    (meetingSelector hmeet i : V) ∈ S :=
  (meetingSelector hmeet i).2

@[simp]
theorem meetingSelector_mem_family
    (hmeet : ∀ i ∈ I, ∃ x ∈ S, x ∈ F i) (i : I) :
    (meetingSelector hmeet i : V) ∈ F i.1 :=
  (Classical.choose_spec (hmeet i.1 i.2)).2

/-- A selector from pairwise-disjoint family members is injective. -/
theorem meetingSelector_injective
    (hdisj : I.PairwiseDisjoint F)
    (hmeet : ∀ i ∈ I, ∃ x ∈ S, x ∈ F i) :
    Function.Injective (meetingSelector hmeet) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have hd : Disjoint (F i.1) (F j.1) := hdisj i.2 j.2 hne
  exact Set.disjoint_left.1 hd (meetingSelector_mem_family hmeet i)
    (hij ▸ meetingSelector_mem_family hmeet j)

/-- A pairwise-disjoint family whose members all meet `S` has cardinality at
most that of `S`. -/
theorem mk_le_of_pairwiseDisjoint_of_meets
    (hdisj : I.PairwiseDisjoint F)
    (hmeet : ∀ i ∈ I, ∃ x ∈ S, x ∈ F i) :
    #I ≤ #S :=
  Cardinal.mk_le_of_injective (meetingSelector_injective hdisj hmeet)

/-- A pairwise-disjoint family whose members all meet a countable set is
countable. -/
theorem countable_of_pairwiseDisjoint_of_meets
    (hdisj : I.PairwiseDisjoint F) (hS : S.Countable)
    (hmeet : ∀ i ∈ I, ∃ x ∈ S, x ∈ F i) :
    I.Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable]
  exact (mk_le_of_pairwiseDisjoint_of_meets hdisj hmeet).trans hS.le_aleph0

/-- A pairwise-disjoint family whose members all meet a finite set is finite. -/
theorem finite_of_pairwiseDisjoint_of_meets
    (hdisj : I.PairwiseDisjoint F) (hS : S.Finite)
    (hmeet : ∀ i ∈ I, ∃ x ∈ S, x ∈ F i) :
    I.Finite := by
  rw [← Cardinal.lt_aleph0_iff_set_finite]
  exact (mk_le_of_pairwiseDisjoint_of_meets hdisj hmeet).trans_lt hS.lt_aleph0

/-- The strict-cardinal form of the selector argument.  Regularity is not
needed for this step; it enters only when taking a union of the family. -/
theorem mk_lt_of_pairwiseDisjoint_of_meets {κ : Cardinal.{u}}
    (hdisj : I.PairwiseDisjoint F) (hS : #S < κ)
    (hmeet : ∀ i ∈ I, ∃ x ∈ S, x ∈ F i) :
    #I < κ :=
  (mk_le_of_pairwiseDisjoint_of_meets hdisj hmeet).trans_lt hS

/-- A countable union of countable supports is countable, in set-indexed
form. -/
theorem countable_biUnion (hI : I.Countable)
    (hF : ∀ i ∈ I, (F i).Countable) :
    (⋃ i ∈ I, F i).Countable :=
  hI.biUnion hF

/-- A countable union of finite supports is countable. -/
theorem countable_biUnion_of_finite (hI : I.Countable)
    (hF : ∀ i ∈ I, (F i).Finite) :
    (⋃ i ∈ I, F i).Countable :=
  countable_biUnion hI fun i hi => (hF i hi).countable

/-- A finite union of finite supports is finite, in set-indexed form. -/
theorem finite_biUnion (hI : I.Finite)
    (hF : ∀ i ∈ I, (F i).Finite) :
    (⋃ i ∈ I, F i).Finite :=
  hI.biUnion hF

/-- Fewer than `κ` many supports, each of cardinality below the regular
cardinal `κ`, have union of cardinality below `κ`. -/
theorem mk_biUnion_lt_of_isRegular {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) (hI : #I < κ)
    (hF : ∀ i ∈ I, #(F i) < κ) :
    #(⋃ i ∈ I, F i) < κ :=
  (Cardinal.card_biUnion_lt_iff_forall_of_isRegular hκ hI).2 hF

/-- In particular, fewer than `κ` many finite supports have union of
cardinality below a regular `κ`. -/
theorem mk_biUnion_lt_of_finite_of_isRegular {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) (hI : #I < κ)
    (hF : ∀ i ∈ I, (F i).Finite) :
    #(⋃ i ∈ I, F i) < κ :=
  mk_biUnion_lt_of_isRegular hκ hI fun i hi =>
    (hF i hi).lt_aleph0.trans_le hκ.aleph0_le

/-- Combined form used most often: a pairwise-disjoint family meeting a
`< κ` set has size `< κ`, and if all of its supports are `< κ`, their union
is also `< κ`. -/
theorem mk_biUnion_lt_of_pairwiseDisjoint_of_meets {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) (hdisj : I.PairwiseDisjoint F) (hS : #S < κ)
    (hmeet : ∀ i ∈ I, ∃ x ∈ S, x ∈ F i)
    (hF : ∀ i ∈ I, #(F i) < κ) :
    #(⋃ i ∈ I, F i) < κ :=
  mk_biUnion_lt_of_isRegular hκ
    (mk_lt_of_pairwiseDisjoint_of_meets hdisj hS hmeet) hF

/-- The finite-support specialization of the combined regular-cardinal
bound. -/
theorem mk_biUnion_lt_of_pairwiseDisjoint_of_meets_finite
    {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (hdisj : I.PairwiseDisjoint F) (hS : #S < κ)
    (hmeet : ∀ i ∈ I, ∃ x ∈ S, x ∈ F i)
    (hF : ∀ i ∈ I, (F i).Finite) :
    #(⋃ i ∈ I, F i) < κ :=
  mk_biUnion_lt_of_finite_of_isRegular hκ
    (mk_lt_of_pairwiseDisjoint_of_meets hdisj hS hmeet) hF

end FamilyTools
end Erdos599
