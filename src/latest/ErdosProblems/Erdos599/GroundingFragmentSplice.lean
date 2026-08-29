/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFragmentCarrier

/-!
# Simultaneous predecessor splices for Assertion 8.20

After stationary thinning, every retained first-hit prefix is assigned a
piece on a different parent ladder path.  The lemmas here append the
piece's predecessor route and package the resulting paths as a genuine
source--cut warp.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFragmentSplice

open DirectedPath
open PopularGroundingBridge
open GroundingFragmentCarrier

universe u v

variable {V I : Type u} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type u) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- A first-hit prefix meets its target set only at its terminal vertex. -/
theorem firstHit_inter_subset_finish
    {W : Type u} {web : DWeb W} (p : FinitePath web.graph)
    (H : Set W) (hmeet : p.walk.Meets H) :
    (p.firstHit H hmeet).support ∩ H ⊆
      {(p.firstHit H hmeet).finish} := by
  intro x hx
  apply Set.mem_singleton_iff.2
  by_contra hxf
  have hxlast : x ≠
      (p.firstHit H hmeet).walk.support.getLast
        (p.firstHit H hmeet).walk.support_ne_nil := by
    intro h
    apply hxf
    exact h.trans (p.firstHit H hmeet).walk.getLast_support
  have hxdrop : x ∈ (p.firstHit H hmeet).walk.support.dropLast :=
    List.mem_dropLast_of_mem_of_ne_getLast hx.1 hxlast
  exact (p.firstHit_no_mem_before H hmeet hxdrop) hx.2

section Selected

variable {L : Input Gamma I} {kappa : Cardinal.{u}}
variable {U : Popular.KappaIndexed L.lambda kappa}
variable (S : Popular.PopularSeparator U) (r : Request L S.cut)
variable {J : Type v}
variable (p : J → FinitePath L.lambda.graph)
variable (hp : ∀ j, p j ∈ (requestFan S r).paths)
variable (hpinj : Function.Injective p)
variable (hmeet : ∀ j, (p j).walk.Meets (carrier S r))
variable (piece : J → Piece L S r)
variable (hfinish : ∀ j,
  ((p j).firstHit (carrier S r) (hmeet j)).finish ∈ (piece j).carrier)
variable (hparentinj : Function.Injective
  (fun j ↦ (piece j).fragment.parent))

/-- The selected first-hit prefix. -/
def firstPrefix (j : J) : FinitePath L.lambda.graph :=
  (p j).firstHit (carrier S r) (hmeet j)

/-- The selected continuation from the first-hit vertex to the represented
predecessor in the popular cut. -/
def tail (j : J) : FinitePath L.lambda.graph :=
  Classical.choose ((piece j).exists_path_to_cut (hfinish j))

theorem tail_start (j : J) :
    (tail S r p hmeet piece hfinish j).start =
      (firstPrefix S r p hmeet j).finish :=
  (Classical.choose_spec ((piece j).exists_path_to_cut (hfinish j))).1

theorem tail_finish_mem (j : J) :
    (tail S r p hmeet piece hfinish j).finish ∈ S.cut :=
  (Classical.choose_spec ((piece j).exists_path_to_cut (hfinish j))).2.1

theorem tail_support_subset (j : J) :
    (tail S r p hmeet piece hfinish j).support ⊆ (piece j).carrier :=
  (Classical.choose_spec ((piece j).exists_path_to_cut (hfinish j))).2.2

theorem prefix_tail_inter (j : J) :
    (firstPrefix S r p hmeet j).support ∩
        (tail S r p hmeet piece hfinish j).support ⊆
      {(firstPrefix S r p hmeet j).finish} := by
  intro x hx
  apply firstHit_inter_subset_finish (p j) (carrier S r) (hmeet j)
  exact ⟨hx.1, Set.mem_iUnion.2 ⟨piece j,
    tail_support_subset S r p hmeet piece hfinish j hx.2⟩⟩

/-- Append the first-hit prefix to its predecessor continuation. -/
def splice (j : J) : FinitePath L.lambda.graph :=
  (firstPrefix S r p hmeet j).appendFinite
    (tail S r p hmeet piece hfinish j)
    (tail_start S r p hmeet piece hfinish j)
    (prefix_tail_inter S r p hmeet piece hfinish j)

@[simp] theorem splice_start (j : J) :
    (splice S r p hmeet piece hfinish j).start = (p j).start := by
  calc
    (splice S r p hmeet piece hfinish j).start =
        (firstPrefix S r p hmeet j).start :=
      FinitePath.appendFinite_start _ _ _ _
    _ = (p j).start := rfl

@[simp] theorem splice_finish (j : J) :
    (splice S r p hmeet piece hfinish j).finish =
      (tail S r p hmeet piece hfinish j).finish := by
  simp [splice]

theorem splice_support (j : J) :
    (splice S r p hmeet piece hfinish j).support =
      (firstPrefix S r p hmeet j).support ∪
        (tail S r p hmeet piece hfinish j).support := by
  exact FinitePath.support_appendFinite_eq_union _ _ _ _

include hp hpinj in
private theorem prefix_disjoint (j k : J) (hjk : j ≠ k) :
    Disjoint (firstPrefix S r p hmeet j).support
      (firstPrefix S r p hmeet k).support := by
  rw [Set.disjoint_left]
  intro x hxj hxk
  have hpjk : p j ≠ p k := fun h ↦ hjk (hpinj h)
  have hxApex : x ∈ ({requestAuxVertex r} : Set (LV L)) :=
    (requestFan S r).joined (hp j) (hp k) hpjk ⟨
      (p j).firstHit_support_subset (carrier S r) (hmeet j) hxj,
      (p k).firstHit_support_subset (carrier S r) (hmeet k) hxk⟩
  exact Set.disjoint_left.1
    (PopularSwitching.firstHit_support_disjoint_join
      (requestFan S r) (carrier_disjoint_requestAuxVertex S r)
      (hp j) (hmeet j)) hxj hxApex

include hparentinj in
private theorem tail_disjoint (j k : J) (hjk : j ≠ k) :
    Disjoint (tail S r p hmeet piece hfinish j).support
      (tail S r p hmeet piece hfinish k).support := by
  apply (piece j).carrier_disjoint_of_parent_ne (piece k)
      (fun h ↦ hjk (hparentinj h)) |>.mono
  · exact tail_support_subset S r p hmeet piece hfinish j
  · exact tail_support_subset S r p hmeet piece hfinish k

include hparentinj in
private theorem prefix_tail_disjoint (j k : J) (hjk : j ≠ k) :
    Disjoint (firstPrefix S r p hmeet j).support
      (tail S r p hmeet piece hfinish k).support := by
  rw [Set.disjoint_left]
  intro x hxPrefix hxTail
  have hxH : x ∈ carrier S r :=
    Set.mem_iUnion.2 ⟨piece k,
      tail_support_subset S r p hmeet piece hfinish k hxTail⟩
  have hxFinish : x = (firstPrefix S r p hmeet j).finish :=
    Set.mem_singleton_iff.mp
      (firstHit_inter_subset_finish (p j) (carrier S r) (hmeet j)
        ⟨hxPrefix, hxH⟩)
  have hxPieceJ : x ∈ (piece j).carrier := hxFinish ▸ hfinish j
  exact Set.disjoint_left.1
    ((piece j).carrier_disjoint_of_parent_ne (piece k)
      (fun h ↦ hjk (hparentinj h))) hxPieceJ
    (tail_support_subset S r p hmeet piece hfinish k hxTail)

include hp hpinj hparentinj in
/-- The whole selected family of predecessor splices is a genuine warp to
the popular cut. -/
def selectedSpliceWarp : Popular.XSWarp L.lambda S.cut where
  paths := Set.range (splice S r p hmeet piece hfinish)
  disjoint := by
    rintro q ⟨j, rfl⟩ q' ⟨k, rfl⟩ hqq
    have hjk : j ≠ k := by
      intro h
      subst k
      exact hqq rfl
    change Disjoint
      (splice S r p hmeet piece hfinish j).support
      (splice S r p hmeet piece hfinish k).support
    rw [splice_support S r p hmeet piece hfinish j,
      splice_support S r p hmeet piece hfinish k]
    rw [Set.disjoint_left]
    intro x hxj hxk
    rcases hxj with hxPrefixJ | hxTailJ
    · rcases hxk with hxPrefixK | hxTailK
      · exact Set.disjoint_left.1
          (prefix_disjoint S r p hp hpinj hmeet j k hjk)
          hxPrefixJ hxPrefixK
      · exact Set.disjoint_left.1
          (prefix_tail_disjoint S r p hmeet piece hfinish hparentinj j k hjk)
          hxPrefixJ hxTailK
    · rcases hxk with hxPrefixK | hxTailK
      · exact Set.disjoint_left.1
          (prefix_tail_disjoint S r p hmeet piece hfinish hparentinj k j
            (Ne.symm hjk)) hxPrefixK hxTailJ
      · exact Set.disjoint_left.1
          (tail_disjoint S r p hmeet piece hfinish hparentinj j k hjk)
          hxTailJ hxTailK
  starts_in_source := by
    rintro q ⟨j, rfl⟩
    rw [splice_start]
    exact (requestFan S r).starts_in_source (hp j)
  ends_in_target := by
    rintro q ⟨j, rfl⟩
    rw [splice_finish]
    exact tail_finish_mem S r p hmeet piece hfinish j

include hpinj hmeet piece hfinish hparentinj in
theorem index_mem_selectedSpliceWarp (j : J) :
    U.f ⟨(p j).start, (requestFan S r).starts_in_source (hp j)⟩ ∈
      Popular.initialIndicesOf U
        (selectedSpliceWarp S r p hp hpinj hmeet piece hfinish hparentinj).paths
        (selectedSpliceWarp S r p hp hpinj hmeet piece hfinish hparentinj).starts_in_source := by
  let q := splice S r p hmeet piece hfinish j
  have hq : q ∈
      (selectedSpliceWarp S r p hp hpinj hmeet piece hfinish hparentinj).paths :=
    ⟨j, rfl⟩
  refine ⟨q, hq, ?_⟩
  have hs :
      (⟨q.start,
        (selectedSpliceWarp S r p hp hpinj hmeet piece hfinish hparentinj).starts_in_source hq⟩ :
        L.lambda.source) =
      ⟨(p j).start, (requestFan S r).starts_in_source (hp j)⟩ := by
    apply Subtype.ext
    exact splice_start S r p hmeet piece hfinish j
  exact congrArg U.f hs

end Selected

end GroundingFragmentSplice
end Erdos599
