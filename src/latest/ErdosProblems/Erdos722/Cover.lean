/-
Copyright 2026 The Lean-Proofs Authors.

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
import ErdosProblems.Erdos722.GreedyChoice
import ErdosProblems.Erdos722.Reserve
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Greedy covering from the reserve

The cover lemma assigns to every edge of a sparse leave one `q`-clique whose
other edges lie in the reserve, with the other-edge sets pairwise disjoint.
This file isolates the exact finite greedy statement.  Its two numerical
hypotheses are discharged from the reserve lower bound and leave
boundedness in the asymptotic assembly.
-/

namespace Erdos722.Cover

open Finset
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.GreedyChoice

noncomputable section

/-- The reserve edges spent by a clique assigned to the root edge `e`. -/
def spill (r : ℕ) (e B : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  cliqueEdges B r \ {e}

/-- Tagging candidates with their root turns root-dependent conflict into
an ordinary symmetric relation. -/
def taggedCandidates (n q r : ℕ)
    (reserve : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (reserveCandidates n q r reserve e).image fun B ↦ (e, B)

/-- Two tagged cover choices conflict when their reserve spills overlap. -/
def CoverConflict (r : ℕ)
    (x y : Finset (Fin n) × Finset (Fin n)) : Prop :=
  ¬Disjoint (spill r x.1 x.2) (spill r y.1 y.2)

noncomputable instance coverConflictDecidableRel (r : ℕ) :
    DecidableRel (CoverConflict (n := n) r) :=
  Classical.decRel _

lemma coverConflict_symmetric : Symmetric (CoverConflict (n := n) r) := by
  intro x y h
  simpa [CoverConflict, disjoint_comm] using h

lemma card_taggedCandidates
    (n q r : ℕ) (reserve : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) :
    (taggedCandidates n q r reserve e).card =
      (reserveCandidates n q r reserve e).card := by
  apply Finset.card_image_iff.mpr
  intro A _ B _ h
  exact congrArg Prod.snd h

/-- A successful output of the cover-choice stage. -/
structure CoverAssignment (n q r : ℕ)
    (leave reserve : Finset (Finset (Fin n))) where
  block : Finset (Fin n) → Finset (Fin n)
  block_mem : ∀ e ∈ leave, block e ∈ reserveCandidates n q r reserve e
  spill_disjoint : ∀ e ∈ leave, ∀ f ∈ leave, e ≠ f →
    Disjoint (spill r e (block e)) (spill r f (block f))

/-- The exact finite greedy cover lemma, parameterized by a per-previous-
choice conflict cap `M`. -/
theorem exists_coverAssignment_of_conflict_bound
    {n q r M : ℕ}
    (leave reserve : Finset (Finset (Fin n)))
    (hlarge : ∀ e ∈ leave,
      leave.card * M < (reserveCandidates n q r reserve e).card)
    (hconflict : ∀ e ∈ leave,
      ∀ z : Finset (Fin n) × Finset (Fin n),
      ((taggedCandidates n q r reserve e).filter
        fun x ↦ CoverConflict r x z).card ≤ M) :
    Nonempty (CoverAssignment n q r leave reserve) := by
  classical
  let defaultBlock : Finset (Fin n) := ∅
  let defaultTag : Finset (Fin n) × Finset (Fin n) :=
    (∅, defaultBlock)
  letI : Nonempty (Finset (Fin n) × Finset (Fin n)) := ⟨defaultTag⟩
  obtain ⟨choice, hchoice, hcompat⟩ :=
    exists_pairwiseCompatible_choice leave
      (taggedCandidates n q r reserve) (CoverConflict r)
      coverConflict_symmetric M
      (fun e he ↦ by simpa [card_taggedCandidates] using hlarge e he)
      hconflict
  let block : Finset (Fin n) → Finset (Fin n) := fun e ↦ (choice e).2
  have hchoice_fst : ∀ e ∈ leave, (choice e).1 = e := by
    intro e he
    have hm := hchoice e he
    obtain ⟨B, _hB, heq⟩ := Finset.mem_image.mp hm
    exact congrArg Prod.fst heq.symm
  refine ⟨{
    block := block
    block_mem := ?_
    spill_disjoint := ?_ }⟩
  · intro e he
    have hm := hchoice e he
    obtain ⟨B, hB, heq⟩ := Finset.mem_image.mp hm
    have hfirst : (choice e).1 = e := congrArg Prod.fst heq.symm
    have hsecond : (choice e).2 = B := congrArg Prod.snd heq.symm
    simpa [block, hsecond] using hB
  · intro e he f hf hef
    have hnot := hcompat e he f hf hef
    simpa [CoverConflict, block, hchoice_fst e he, hchoice_fst f hf] using hnot

lemma CoverAssignment.block_card
    (C : CoverAssignment n q r leave reserve)
    {e : Finset (Fin n)} (he : e ∈ leave) :
    (C.block e).card = q := by
  exact mem_uniformEdges.mp
    (Finset.mem_filter.mp (C.block_mem e he)).1

lemma CoverAssignment.root_subset
    (C : CoverAssignment n q r leave reserve)
    {e : Finset (Fin n)} (he : e ∈ leave) :
    e ⊆ C.block e := by
  exact (Finset.mem_filter.mp (C.block_mem e he)).2.1

lemma CoverAssignment.spill_subset_reserve
    (C : CoverAssignment n q r leave reserve)
    {e : Finset (Fin n)} (he : e ∈ leave) :
    spill r e (C.block e) ⊆ reserve := by
  exact (Finset.mem_filter.mp (C.block_mem e he)).2.2

/-- All reserve edges spent by a cover assignment. -/
def spentEdges (C : CoverAssignment n q r leave reserve) :
    Finset (Finset (Fin n)) :=
  leave.biUnion fun e ↦ spill r e (C.block e)

/-- The actual (unindexed) block family output by a cover assignment. -/
def coverBlocks (C : CoverAssignment n q r leave reserve) :
    Finset (Finset (Fin n)) :=
  leave.image C.block

/-- The root edges together with all reserve spill edges. -/
def coveredEdges (C : CoverAssignment n q r leave reserve) :
    Finset (Finset (Fin n)) :=
  leave ∪ spentEdges C

/-- Local exact-decomposition predicate, kept in the submodule to avoid a
cyclic import with the main problem file. -/
def IsCoverDecomposition (C : CoverAssignment n q r leave reserve) : Prop :=
  (∀ B ∈ coverBlocks C, B.card = q) ∧
    (∀ B ∈ coverBlocks C, cliqueEdges B r ⊆ coveredEdges C) ∧
    ∀ g ∈ coveredEdges C,
      ((coverBlocks C).filter fun B ↦ g ∈ cliqueEdges B r).card = 1

theorem CoverAssignment.spentEdges_subset_reserve
    (C : CoverAssignment n q r leave reserve) :
    spentEdges C ⊆ reserve := by
  intro g hg
  obtain ⟨e, he, hge⟩ := Finset.mem_biUnion.mp hg
  exact C.spill_subset_reserve he hge

/-- Every chosen clique consists exactly of its root edge and its spill. -/
theorem CoverAssignment.cliqueEdges_eq_insert_spill
    (C : CoverAssignment n q r leave reserve)
    {e : Finset (Fin n)} (he : e ∈ leave) (hecard : e.card = r) :
    cliqueEdges (C.block e) r = insert e (spill r e (C.block e)) := by
  apply Finset.Subset.antisymm
  · intro g hg
    by_cases hge : g = e
    · simp [hge]
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
        ⟨hg, by simpa using hge⟩)
  · intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact Finset.mem_powersetCard.mpr ⟨C.root_subset he, hecard⟩
    · exact (Finset.mem_sdiff.mp hg).1

theorem CoverAssignment.block_injectiveOn
    (C : CoverAssignment n q r leave reserve)
    (huniform : ∀ e ∈ leave, e.card = r)
    (hdisjoint : Disjoint leave reserve) :
    Set.InjOn C.block (↑leave : Set (Finset (Fin n))) := by
  intro e he f hf hblock
  have heL : e ∈ leave := he
  have hfL : f ∈ leave := hf
  by_contra hef
  have heClique : e ∈ cliqueEdges (C.block e) r :=
    Finset.mem_powersetCard.mpr ⟨C.root_subset heL, huniform e heL⟩
  have heCliqueF : e ∈ cliqueEdges (C.block f) r := by
    simpa [hblock] using heClique
  have heSpillF : e ∈ spill r f (C.block f) :=
    Finset.mem_sdiff.mpr ⟨heCliqueF, by simpa using hef⟩
  exact Finset.disjoint_left.mp hdisjoint heL
    (C.spill_subset_reserve hfL heSpillF)

/-- Every covered edge has a unique root whose assigned clique contains it. -/
theorem CoverAssignment.existsUnique_root
    (C : CoverAssignment n q r leave reserve)
    (huniform : ∀ e ∈ leave, e.card = r)
    (hdisjoint : Disjoint leave reserve)
    {g : Finset (Fin n)} (hg : g ∈ coveredEdges C) :
    ∃! e : Finset (Fin n), e ∈ leave ∧
      g ∈ cliqueEdges (C.block e) r := by
  rcases Finset.mem_union.mp hg with hgLeave | hgSpent
  · refine ⟨g, ⟨hgLeave, Finset.mem_powersetCard.mpr
      ⟨C.root_subset hgLeave, huniform g hgLeave⟩⟩, ?_⟩
    intro f hf
    by_contra hfg
    have hgSpillF : g ∈ spill r f (C.block f) :=
      Finset.mem_sdiff.mpr ⟨hf.2, by
        simpa using (fun h : g = f ↦ hfg h.symm)⟩
    exact Finset.disjoint_left.mp hdisjoint hgLeave
      (C.spill_subset_reserve hf.1 hgSpillF)
  · obtain ⟨e, heLeave, hgSpillE⟩ := Finset.mem_biUnion.mp hgSpent
    refine ⟨e, ⟨heLeave, (Finset.mem_sdiff.mp hgSpillE).1⟩, ?_⟩
    intro f hf
    by_cases hgf : g = f
    · subst f
      exact (Finset.disjoint_left.mp hdisjoint hf.1
        (C.spill_subset_reserve heLeave hgSpillE)).elim
    · have hgSpillF : g ∈ spill r f (C.block f) :=
        Finset.mem_sdiff.mpr ⟨hf.2, by simpa [eq_comm] using hgf⟩
      by_contra hef
      exact Finset.disjoint_left.mp
        (C.spill_disjoint e heLeave f hf.1 (fun h ↦ hef h.symm))
          hgSpillE hgSpillF

/-- A successful cover assignment is an exact clique decomposition of its
root-plus-spill host. -/
theorem CoverAssignment.isCoverDecomposition
    (C : CoverAssignment n q r leave reserve)
    (huniform : ∀ e ∈ leave, e.card = r)
    (hdisjoint : Disjoint leave reserve) :
    IsCoverDecomposition C := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hB
    exact C.block_card he
  · intro B hB g hg
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hB
    rw [C.cliqueEdges_eq_insert_spill he (huniform e he)] at hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact Finset.mem_union_left _ he
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, hg⟩)
  · intro g hg
    obtain ⟨e, he, huniq⟩ := C.existsUnique_root huniform hdisjoint hg
    have hfilter :
        (coverBlocks C).filter (fun B ↦ g ∈ cliqueEdges B r) =
          {C.block e} := by
      ext B
      constructor
      · intro hB
        have hm := Finset.mem_filter.mp hB
        obtain ⟨f, hf, hBf⟩ := Finset.mem_image.mp hm.1
        have hfe : f = e := huniq f ⟨hf, by simpa [hBf] using hm.2⟩
        subst f
        simpa [hBf]
      · intro hB
        have hBe : B = C.block e := Finset.mem_singleton.mp hB
        subst B
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨e, he.1, rfl⟩, he.2⟩
    rw [hfilter]
    simp

end

end Erdos722.Cover
