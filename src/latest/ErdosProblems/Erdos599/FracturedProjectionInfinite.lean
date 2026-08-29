/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentPeel
import ErdosProblems.Erdos599.AlternatingInfiniteMacroCompiler

/-!
# Infinite connector-deletion projection for a fractured warp

This file isolates the reusable infinite half of Remark 4.20.  An upstairs
alternating path in the occurrence-split web is first flattened after
contracted connector steps have been deleted.  `InfiniteTraversalBlocks`
records that flattened stream together with the precise occurrence and owner
data needed downstream.  The already verified chronological loop eraser and
maximal-run compressor then produce a genuine infinite alternating path in
the original web.
-/

noncomputable section

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace FracturedAssignmentPeel

open Set DirectedPath Alternating
open Alternating.FracturedDuplication

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

/-! ## Occurrence-aware omega provenance

Forward links coming from two separated holes of one recombined path may
have different occurrence tags but the same carrier.  The generic macro
provenance deliberately identifies same-colour carriers and is therefore
too strong for this application.  The specialized record below asks for
tag injectivity only in the backward colour, where unique ownership by the
reference warp proves it.  Constant-colour forward runs are compiled using
equality of their carriers, not equality of their occurrence tags. -/

structure FracturedEdgeProvenance (B : OmegaBlocks V)
    (Z Y : Set Gamma.DPath) (M : Type v) where
  member : ℕ → M
  colour : M → Direction
  carrier : M → Gamma.DPath
  carrier_injective_on_backward : ∀ {a b : M},
    colour a = .backward → colour b = .backward →
      carrier a = carrier b → a = b
  carrier_mem_forward : ∀ a, colour a = .forward → carrier a ∈ Z
  carrier_mem_backward : ∀ a, colour a = .backward → carrier a ∈ Y
  edge_mem_forward : ∀ k, colour (member k) = .forward →
    (B.rawVertex k, B.rawVertex (k + 1)) ∈ (carrier (member k)).edgeSet
  edge_mem_backward : ∀ k, colour (member k) = .backward →
    (B.rawVertex (k + 1), B.rawVertex k) ∈ (carrier (member k)).edgeSet
  member_convex : ∀ {i j k : ℕ}, i ≤ j → j ≤ k →
    member i = member k → member j = member i

namespace FracturedEdgeProvenance

variable {Z : Set Gamma.DPath} {M : Type v} {B : OmegaBlocks V}

/-- Same-colour edges which join chronologically have the same carrier.
For forward occurrences the tags need not be equal. -/
theorem carrier_eq_of_colour_eq_of_join
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    {i j : ℕ}
    (hcolour : P.colour (P.member i) = P.colour (P.member j))
    (hjoin : B.rawVertex (i + 1) = B.rawVertex j) :
    P.carrier (P.member i) = P.carrier (P.member j) := by
  cases hi : P.colour (P.member i) with
  | forward =>
      have hj : P.colour (P.member j) = .forward :=
        hcolour.symm.trans hi
      have hei := P.edge_mem_forward i hi
      have hej := P.edge_mem_forward j hj
      apply DWeb.IsWarp.eq_of_mem_support hZ
        (P.carrier_mem_forward _ hi) (P.carrier_mem_forward _ hj)
      · exact ((P.carrier (P.member i)).edgeSet_subset_support_prod hei).2
      · rw [hjoin]
        exact ((P.carrier (P.member j)).edgeSet_subset_support_prod hej).1
  | backward =>
      have hj : P.colour (P.member j) = .backward :=
        hcolour.symm.trans hi
      have hei := P.edge_mem_backward i hi
      have hej := P.edge_mem_backward j hj
      apply DWeb.IsWarp.eq_of_mem_support hY
        (P.carrier_mem_backward _ hi) (P.carrier_mem_backward _ hj)
      · exact ((P.carrier (P.member i)).edgeSet_subset_support_prod hei).1
      · rw [hjoin]
        exact ((P.carrier (P.member j)).edgeSet_subset_support_prod hej).2

/-- The retained raw index at loop-erased edge time `n`. -/
noncomputable def retainedIndex
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (n : ℕ) : ℕ :=
  loopErasedIndex B.rawVertex hfinite n

/-- Chronological loop erasure with occurrence-aware edge colours. -/
noncomputable def loopErasedInput
    (P : FracturedEdgeProvenance B Z Y M)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite) :
    RunCompressor.InfiniteInput Gamma.graph where
  vertex n := B.rawVertex (retainedIndex hfinite n)
  vertex_injective := injective_loopErasedVertex B.rawVertex hfinite
  colour n := P.colour (P.member (retainedIndex hfinite n))
  forward_adj n hn := by
    change Gamma.graph.Adj
      (B.rawVertex (loopErasedIndex B.rawVertex hfinite n))
      (B.rawVertex (loopErasedIndex B.rawVertex hfinite (n + 1)))
    rw [← loopErasedIndex_join B.rawVertex hfinite n]
    exact
      (P.carrier (P.member (retainedIndex hfinite n))).edgeSet_subset_adj
        (P.edge_mem_forward (retainedIndex hfinite n) hn)
  backward_adj n hn := by
    change Gamma.graph.Adj
      (B.rawVertex (loopErasedIndex B.rawVertex hfinite (n + 1)))
      (B.rawVertex (loopErasedIndex B.rawVertex hfinite n))
    rw [← loopErasedIndex_join B.rawVertex hfinite n]
    exact
      (P.carrier (P.member (retainedIndex hfinite n))).edgeSet_subset_adj
        (P.edge_mem_backward (retainedIndex hfinite n) hn)

@[simp] theorem loopErasedInput_colour
    (P : FracturedEdgeProvenance B Z Y M)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite) (n : ℕ) :
    (P.loopErasedInput hfinite).colour n =
      P.colour (P.member (retainedIndex hfinite n)) := rfl

theorem loopErasedIndex_carrier_eq_of_colour_eq
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite) (n : ℕ)
    (hcolour :
      P.colour (P.member (retainedIndex hfinite n)) =
        P.colour (P.member (retainedIndex hfinite (n + 1)))) :
    P.carrier (P.member (retainedIndex hfinite n)) =
      P.carrier (P.member (retainedIndex hfinite (n + 1))) := by
  apply P.carrier_eq_of_colour_eq_of_join hZ hY hcolour
  exact loopErasedIndex_join B.rawVertex hfinite n

/-- Carrier-finiteness forces arbitrarily late colour changes. -/
theorem exists_loopErasedIndex_colour_change
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hfiniteVertex : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteCarrier : ∀ p : Gamma.DPath,
      {k | P.carrier (P.member k) = p}.Finite) (n : ℕ) :
    ∃ m, n < m ∧
      P.colour (P.member (retainedIndex hfiniteVertex m)) ≠
        P.colour (P.member (retainedIndex hfiniteVertex n)) := by
  by_contra hno
  push Not at hno
  have hcolour (k : ℕ) :
      P.colour (P.member (retainedIndex hfiniteVertex (n + k))) =
        P.colour (P.member (retainedIndex hfiniteVertex n)) := by
    by_cases hk : k = 0
    · subst k
      simp
    · exact hno (n + k) (by omega)
  have hcarrier (k : ℕ) :
      P.carrier (P.member (retainedIndex hfiniteVertex (n + k))) =
        P.carrier (P.member (retainedIndex hfiniteVertex n)) := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep := P.loopErasedIndex_carrier_eq_of_colour_eq
          hZ hY hfiniteVertex (n + k)
          ((hcolour k).trans (hcolour (k + 1)).symm)
        simpa [Nat.add_assoc] using hstep.symm.trans ih
  have hinj : Function.Injective
      (fun k ↦ retainedIndex hfiniteVertex (n + k)) :=
    fun _ _ h ↦ Nat.add_left_cancel
      ((loopErasedIndex_strictMono B.rawVertex hfiniteVertex).injective h)
  have hinfinite :
      {k | P.carrier (P.member k) =
        P.carrier (P.member (retainedIndex hfiniteVertex n))}.Infinite :=
    Set.infinite_of_injective_forall_mem hinj hcarrier
  exact hinfinite (hfiniteCarrier _)

theorem loopErasedInput_changes
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteCarrier : ∀ p : Gamma.DPath,
      {k | P.carrier (P.member k) = p}.Finite) :
    ∀ n, ∃ m, n < m ∧
      (P.loopErasedInput hfinite).colour m ≠
        (P.loopErasedInput hfinite).colour n := by
  intro n
  exact P.exists_loopErasedIndex_colour_change hZ hY hfinite
    hfiniteCarrier n

/-- Maximal-run compression of the loop-erased occurrence stream. -/
noncomputable def infiniteRunWalk
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteCarrier : ∀ p : Gamma.DPath,
      {k | P.carrier (P.member k) = p}.Finite) :
    InfiniteRunWalk Gamma.graph :=
  (P.loopErasedInput hfinite).toInfiniteRunWalk
    (P.loopErasedInput_changes hZ hY hfinite hfiniteCarrier)

/-- The occurrence tag at the first retained edge of compressed run `i`. -/
noncomputable def infiniteRunOwnerTag
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteCarrier : ∀ p : Gamma.DPath,
      {k | P.carrier (P.member k) = p}.Finite) (i : ℕ) : M :=
  P.member (retainedIndex hfinite
    (RunCompressor.runBoundary (P.loopErasedInput hfinite).colour
      (P.loopErasedInput_changes hZ hY hfinite hfiniteCarrier) i))

@[simp] theorem infiniteRunWalk_run_direction
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteCarrier : ∀ p : Gamma.DPath,
      {k | P.carrier (P.member k) = p}.Finite) (i : ℕ) :
    ((P.infiniteRunWalk hZ hY hfinite hfiniteCarrier).run i).link.direction =
      P.colour (P.infiniteRunOwnerTag hZ hY hfinite hfiniteCarrier i) := by
  simp [infiniteRunWalk, infiniteRunOwnerTag]

/-- All retained edges of a constant-colour compressed run have the same
carrier as its first edge, even when their forward occurrence tags differ. -/
theorem retained_carrier_eq_infiniteRunOwner
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteCarrier : ∀ p : Gamma.DPath,
      {k | P.carrier (P.member k) = p}.Finite)
    {i k : ℕ}
    (hlo : RunCompressor.runBoundary (P.loopErasedInput hfinite).colour
        (P.loopErasedInput_changes hZ hY hfinite hfiniteCarrier) i ≤ k)
    (hhi : k < RunCompressor.runBoundary (P.loopErasedInput hfinite).colour
        (P.loopErasedInput_changes hZ hY hfinite hfiniteCarrier) (i + 1)) :
    P.carrier (P.member (retainedIndex hfinite k)) =
      P.carrier (P.infiniteRunOwnerTag hZ hY hfinite hfiniteCarrier i) := by
  induction k, hlo using Nat.le_induction with
  | base => rfl
  | succ k hlo ih =>
      have hcolour :
          P.colour (P.member (retainedIndex hfinite k)) =
            P.colour (P.member (retainedIndex hfinite (k + 1))) := by
        change (P.loopErasedInput hfinite).colour k =
          (P.loopErasedInput hfinite).colour (k + 1)
        exact (RunCompressor.colour_eq_on_run _ _ hlo
          (Nat.lt_of_succ_lt hhi)).trans
            (RunCompressor.colour_eq_on_run _ _
              (hlo.trans (Nat.le_succ k)) hhi).symm
      exact (P.loopErasedIndex_carrier_eq_of_colour_eq hZ hY hfinite k
        hcolour).symm.trans (ih (Nat.lt_of_succ_lt hhi))

/-- The directed edges of a compressed run lie in one honest carrier. -/
theorem infiniteRunWalk_run_edgeSet_subset_owner
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteCarrier : ∀ p : Gamma.DPath,
      {k | P.carrier (P.member k) = p}.Finite) (i : ℕ) :
    ((P.infiniteRunWalk hZ hY hfinite hfiniteCarrier).run i).link.path.edgeSet ⊆
      (P.carrier
        (P.infiniteRunOwnerTag hZ hY hfinite hfiniteCarrier i)).edgeSet := by
  intro e he
  let S := P.loopErasedInput hfinite
  let hc := P.loopErasedInput_changes hZ hY hfinite hfiniteCarrier
  have hprov := S.projectedRun_edge_provenance hc i he
  rcases hprov with ⟨hdir, k, hklo, hkhi, rfl⟩ |
      ⟨hdir, k, hklo, hkhi, rfl⟩
  · have hcarrier := P.retained_carrier_eq_infiniteRunOwner hZ hY
      hfinite hfiniteCarrier hklo hkhi
    have hcolour : P.colour (P.member (retainedIndex hfinite k)) =
        .forward := by
      change S.colour k = .forward
      have hrundir : (S.projectedRun hc i).link.direction = .forward := hdir
      rw [S.projectedRun_direction] at hrundir
      exact (RunCompressor.colour_eq_on_run S.colour hc hklo hkhi).trans
        hrundir
    have hedge := P.edge_mem_forward (retainedIndex hfinite k) hcolour
    rw [hcarrier] at hedge
    change (B.rawVertex (retainedIndex hfinite k),
      B.rawVertex (retainedIndex hfinite (k + 1))) ∈ _
    unfold retainedIndex
    rw [← loopErasedIndex_join B.rawVertex hfinite k]
    exact hedge
  · have hcarrier := P.retained_carrier_eq_infiniteRunOwner hZ hY
      hfinite hfiniteCarrier hklo hkhi
    have hcolour : P.colour (P.member (retainedIndex hfinite k)) =
        .backward := by
      change S.colour k = .backward
      have hrundir : (S.projectedRun hc i).link.direction = .backward := hdir
      rw [S.projectedRun_direction] at hrundir
      exact (RunCompressor.colour_eq_on_run S.colour hc hklo hkhi).trans
        hrundir
    have hedge := P.edge_mem_backward (retainedIndex hfinite k) hcolour
    rw [hcarrier] at hedge
    change (B.rawVertex (retainedIndex hfinite (k + 1)),
      B.rawVertex (retainedIndex hfinite k)) ∈ _
    unfold retainedIndex
    rw [← loopErasedIndex_join B.rawVertex hfinite k]
    exact hedge

/-- Complete forward/backward warp labels for the compressed stream. -/
theorem infiniteRunWalk_literalBracketLabels
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteCarrier : ∀ p : Gamma.DPath,
      {k | P.carrier (P.member k) = p}.Finite)
    (hroot : B.rawVertex (loopErasedIndex B.rawVertex hfinite 0) ∉
      Gamma.vertexSet Y) :
    (P.infiniteRunWalk hZ hY hfinite hfiniteCarrier).LiteralBracketLabels
      Z Y := by
  refine {
    reference_isWarp := hY
    backward_on := ?_
    forward_on := ?_
    initial_outside := ?_
  }
  · intro i hi
    let a := P.infiniteRunOwnerTag hZ hY hfinite hfiniteCarrier i
    refine ⟨P.carrier a, ?_, ?_⟩
    · apply P.carrier_mem_backward
      exact (P.infiniteRunWalk_run_direction hZ hY hfinite
        hfiniteCarrier i).symm.trans hi
    · apply finitePath_isSubpathOf_of_edgeSet_subset _ _
        ((P.infiniteRunWalk hZ hY hfinite hfiniteCarrier).run i).link.nontrivial
      exact P.infiniteRunWalk_run_edgeSet_subset_owner hZ hY hfinite
        hfiniteCarrier i
  · intro i hi
    let a := P.infiniteRunOwnerTag hZ hY hfinite hfiniteCarrier i
    refine ⟨P.carrier a, ?_, ?_⟩
    · apply P.carrier_mem_forward
      exact (P.infiniteRunWalk_run_direction hZ hY hfinite
        hfiniteCarrier i).symm.trans hi
    · apply finitePath_isSubpathOf_of_edgeSet_subset _ _
        ((P.infiniteRunWalk hZ hY hfinite hfiniteCarrier).run i).link.nontrivial
      exact P.infiniteRunWalk_run_edgeSet_subset_owner hZ hY hfinite
        hfiniteCarrier i
  · intro _hi
    exact hroot

/-- Convex raw tags cannot recur across an intervening colour change. -/
theorem loopErasedIndex_member_ne_of_colour_between
    (P : FracturedEdgeProvenance B Z Y M)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hcolour :
      P.colour (P.member (loopErasedIndex B.rawVertex hfinite j)) ≠
        P.colour (P.member (loopErasedIndex B.rawVertex hfinite i))) :
    P.member (loopErasedIndex B.rawVertex hfinite i) ≠
      P.member (loopErasedIndex B.rawVertex hfinite k) := by
  intro hik
  apply hcolour
  exact congrArg P.colour (P.member_convex
    ((loopErasedIndex_strictMono B.rawVertex hfinite).monotone hij)
    ((loopErasedIndex_strictMono B.rawVertex hfinite).monotone hjk) hik)

theorem infiniteRunOwnerTag_ne_of_lt
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteCarrier : ∀ p : Gamma.DPath,
      {k | P.carrier (P.member k) = p}.Finite)
    {i j : ℕ} (hij : i < j) :
    P.infiniteRunOwnerTag hZ hY hfinite hfiniteCarrier i ≠
      P.infiniteRunOwnerTag hZ hY hfinite hfiniteCarrier j := by
  let S := P.loopErasedInput hfinite
  let hc := P.loopErasedInput_changes hZ hY hfinite hfiniteCarrier
  have hab : RunCompressor.runBoundary S.colour hc i ≤
      RunCompressor.runBoundary S.colour hc (i + 1) :=
    (RunCompressor.runBoundary_lt_succ S.colour hc i).le
  have hbc : RunCompressor.runBoundary S.colour hc (i + 1) ≤
      RunCompressor.runBoundary S.colour hc j :=
    (RunCompressor.runBoundary_strictMono S.colour hc).monotone (by omega)
  have hcolour :
      P.colour (P.member (loopErasedIndex B.rawVertex hfinite
        (RunCompressor.runBoundary S.colour hc (i + 1)))) ≠
      P.colour (P.member (loopErasedIndex B.rawVertex hfinite
        (RunCompressor.runBoundary S.colour hc i))) := by
    change S.colour (RunCompressor.runBoundary S.colour hc (i + 1)) ≠
      S.colour (RunCompressor.runBoundary S.colour hc i)
    exact RunCompressor.colour_runBoundary_succ_ne S.colour hc i
  have hne := P.loopErasedIndex_member_ne_of_colour_between hfinite
    hab hbc hcolour
  simpa [infiniteRunOwnerTag, retainedIndex, S, hc] using hne

/-- Backward owner provenance for the specialized compressed stream. -/
noncomputable def infiniteIndexedBackwardProvenance
    (P : FracturedEdgeProvenance B Z Y M)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteCarrier : ∀ p : Gamma.DPath,
      {k | P.carrier (P.member k) = p}.Finite) :
    AltPath.IndexedBackwardProvenance
      (AltPath.infinite
        (P.infiniteRunWalk hZ hY hfinite hfiniteCarrier).toInfiniteTrace)
      Y ℕ := by
  let W := P.infiniteRunWalk hZ hY hfinite hfiniteCarrier
  refine {
    link := fun i ↦ (W.run i).link
    links_eq_range := W.toInfiniteTrace_links
    owner := fun i _ ↦
      P.carrier (P.infiniteRunOwnerTag hZ hY hfinite hfiniteCarrier i)
    owner_mem := ?_
    isSubpath := ?_
    owner_unique := ?_
  }
  · intro i hi
    apply P.carrier_mem_backward
    exact (P.infiniteRunWalk_run_direction hZ hY hfinite
      hfiniteCarrier i).symm.trans hi
  · intro i _hi
    apply finitePath_isSubpathOf_of_edgeSet_subset _ _
      (W.run i).link.nontrivial
    exact P.infiniteRunWalk_run_edgeSet_subset_owner hZ hY hfinite
      hfiniteCarrier i
  · intro i j hi hj howner
    have hci : P.colour
        (P.infiniteRunOwnerTag hZ hY hfinite hfiniteCarrier i) =
        .backward :=
      (P.infiniteRunWalk_run_direction hZ hY hfinite
        hfiniteCarrier i).symm.trans hi
    have hcj : P.colour
        (P.infiniteRunOwnerTag hZ hY hfinite hfiniteCarrier j) =
        .backward :=
      (P.infiniteRunWalk_run_direction hZ hY hfinite
        hfiniteCarrier j).symm.trans hj
    have htag := P.carrier_injective_on_backward hci hcj howner
    have hij : i = j := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact (P.infiniteRunOwnerTag_ne_of_lt hZ hY hfinite
          hfiniteCarrier hij) htag
      · exact (P.infiniteRunOwnerTag_ne_of_lt hZ hY hfinite
          hfiniteCarrier hji) htag.symm
    subst j
    rfl

end FracturedEdgeProvenance

/-- The connector-deleted omega stream obtained by traversing an upstairs
infinite alternating path.  Tags distinguish convex raw occurrences of a
carrier.  Forward carriers may recur under different tags; only backward
tags are required to be carrier-injective by `EdgeProvenance`.

The forward carriers are members of the honest recombination `Z.edgeWarp`.
The backward carriers are members of the peeled reference
`activeReference Z Y`. -/
structure InfiniteTraversalBlocks
    (Z : FracturedWarp Gamma)
    (Q : AltPath (web Gamma Z).graph)
    (M : Type v) where
  upstairs_infinite : Q.IsInfinite
  upstairs_bracket :
    IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) Q
  blocks : OmegaBlocks V
  provenance :
    FracturedEdgeProvenance blocks Z.edgeWarp (activeReference Z Y) M
  /-- The stream begins at the projection of the selected upstairs path. -/
  rawVertex_zero_eq_project_initial :
    blocks.rawVertex 0 = project Q.initial
  /-- Finite recurrence is exactly the hypothesis of chronological loop
  erasure for an omega stream. -/
  vertex_finite : ∀ n, (occurrenceFiber blocks.rawVertex n).Finite
  /-- No tagged occurrence contributes infinitely many raw edges. -/
  carrier_finite : ∀ p : Gamma.DPath,
    {n | provenance.carrier (provenance.member n) = p}.Finite
  /-- The projected initial lies outside the peeled reference carrier. -/
  initial_outside : blocks.rawVertex 0 ∉
    Gamma.vertexSet (activeReference Z Y)

namespace InfiniteTraversalBlocks

variable {Z : FracturedWarp Gamma}
variable {Q : AltPath (web Gamma Z).graph} {M : Type v}

/-- The result of chronological erasure and maximal-run compression. -/
structure Projection
    (T : InfiniteTraversalBlocks (Y := Y) Z Q M) where
  path : AltPath Gamma.graph
  infinite : path.IsInfinite
  bracket_safe : IsBracketSafe Z.edgeWarp (activeReference Z Y) path
  initial_eq : path.initial = project Q.initial

/-- Compile a certified connector-deleted infinite traversal. -/
noncomputable def compile
    (T : InfiniteTraversalBlocks (Y := Y) Z Q M)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp) : T.Projection := by
  let B := T.blocks
  let P := T.provenance
  have hactiveY : Gamma.IsWarp (activeReference Z Y) :=
    activeReference_isWarp Z hY
  let W : InfiniteRunWalk Gamma.graph :=
    P.infiniteRunWalk Z.edgeWarp_isWarp hactiveY
      T.vertex_finite T.carrier_finite
  have hretainedZero :
      B.rawVertex
          (FracturedEdgeProvenance.retainedIndex T.vertex_finite 0) =
        B.rawVertex 0 := by
    change B.rawVertex (loopErasedIndex B.rawVertex T.vertex_finite 0) =
      B.rawVertex 0
    rw [loopErasedIndex_zero]
    exact lastOccurrence_mem B.rawVertex T.vertex_finite 0
  have hroot :
      B.rawVertex (loopErasedIndex B.rawVertex T.vertex_finite 0) ∉
        Gamma.vertexSet (activeReference Z Y) := by
    change B.rawVertex
      (FracturedEdgeProvenance.retainedIndex T.vertex_finite 0) ∉
        Gamma.vertexSet (activeReference Z Y)
    rw [hretainedZero]
    exact T.initial_outside
  have hlabels : W.LiteralBracketLabels Z.edgeWarp (activeReference Z Y) :=
    P.infiniteRunWalk_literalBracketLabels Z.edgeWarp_isWarp hactiveY
      T.vertex_finite T.carrier_finite hroot
  have hbackward :
      (AltPath.infinite W.toInfiniteTrace).IndexedBackwardProvenance
        (activeReference Z Y) ℕ :=
    P.infiniteIndexedBackwardProvenance Z.edgeWarp_isWarp hactiveY
      T.vertex_finite T.carrier_finite
  refine {
    path := .infinite W.toInfiniteTrace
    infinite := by simp [AltPath.IsInfinite]
    bracket_safe :=
      (W.isLiteralBracketAlternating hlabels).isBracketSafe_of_indexedBackwardProvenance
        Z.edgeWarp_isWarp hactiveY hZfinite hbackward
    initial_eq := ?_ }
  rw [AltPath.initial, W.toInfiniteTrace_initial]
  change B.rawVertex
      (FracturedEdgeProvenance.retainedIndex T.vertex_finite 0) =
    project Q.initial
  rw [hretainedZero]
  exact T.rawVertex_zero_eq_project_initial

/-- Promote the compiled safety certificate from the peeled reference to the
whole reference warp. -/
theorem compile_isSafe_fullReference
    (T : InfiniteTraversalBlocks (Y := Y) Z Q M)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hinitial : project Q.initial ∉ Gamma.vertexSet Y) :
    IsSafe Y (T.compile hY hZfinite).path := by
  apply (T.compile hY hZfinite).bracket_safe.isSafe.of_subwarp hY
    (activeReference_subset Z Y)
  · intro _
    rw [(T.compile hY hZfinite).initial_eq]
    exact hinitial
  · intro t ht
    have hnone :=
      (T.compile hY hZfinite).path.isInfinite_iff_terminal?_eq_none.mp
        (T.compile hY hZfinite).infinite
    rw [hnone] at ht
    simp at ht

end InfiniteTraversalBlocks

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
