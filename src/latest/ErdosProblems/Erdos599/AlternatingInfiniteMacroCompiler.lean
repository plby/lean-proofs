/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingMacroAssembly
import ErdosProblems.Erdos599.AlternatingMacroEdgeTagFinite
import ErdosProblems.Erdos599.RunCompressor

/-!
# The infinite endpoint-pure macro compiler

This file compiles the concrete flattened `MacroChain` stream.  The first
stage below is independent of the particular macro tags: chronological loop
erasure turns any finitely recurrent, provenance-labelled omega stream into
an injective explicitly coloured input for `RunCompressor`.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u v

namespace OmegaBlocks.EdgeProvenance

variable {V : Type u} {Γ : DWeb V} {Z Y : Set Γ.DPath}
variable {M : Type v} {B : OmegaBlocks V}

/-- The retained raw index at loop-erased edge time `n`. -/
noncomputable def retainedIndex
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite) (n : ℕ) : ℕ :=
  loopErasedIndex B.rawVertex hfinite n

/-- The chronologically loop-erased stream, with the colour of each retained
raw edge supplied by its tagged provenance. -/
noncomputable def loopErasedInput
    (P : B.EdgeProvenance Z Y M)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite) :
    RunCompressor.InfiniteInput Γ.graph where
  vertex n := B.rawVertex (retainedIndex hfinite n)
  vertex_injective := injective_loopErasedVertex B.rawVertex hfinite
  colour n := P.colour (P.member (retainedIndex hfinite n))
  forward_adj n hn := by
    change Γ.graph.Adj
      (B.rawVertex (loopErasedIndex B.rawVertex hfinite n))
      (B.rawVertex (loopErasedIndex B.rawVertex hfinite (n + 1)))
    rw [← loopErasedIndex_join B.rawVertex hfinite n]
    exact
      (P.carrier (P.member (retainedIndex hfinite n))).edgeSet_subset_adj
        (P.edge_mem_forward (retainedIndex hfinite n) hn)
  backward_adj n hn := by
    change Γ.graph.Adj
      (B.rawVertex (loopErasedIndex B.rawVertex hfinite (n + 1)))
      (B.rawVertex (loopErasedIndex B.rawVertex hfinite n))
    rw [← loopErasedIndex_join B.rawVertex hfinite n]
    exact
      (P.carrier (P.member (retainedIndex hfinite n))).edgeSet_subset_adj
        (P.edge_mem_backward (retainedIndex hfinite n) hn)

@[simp]
theorem loopErasedInput_vertex
    (P : B.EdgeProvenance Z Y M)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite) (n : ℕ) :
    (P.loopErasedInput hfinite).vertex n =
      B.rawVertex (retainedIndex hfinite n) :=
  rfl

@[simp]
theorem loopErasedInput_colour
    (P : B.EdgeProvenance Z Y M)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite) (n : ℕ) :
    (P.loopErasedInput hfinite).colour n =
      P.colour (P.member (retainedIndex hfinite n)) :=
  rfl

/-- Finite member fibres force the input colours to change infinitely often. -/
theorem loopErasedInput_changes
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteMember : ∀ a : M, {k | P.member k = a}.Finite) :
    ∀ n, ∃ m, n < m ∧
      (P.loopErasedInput hfinite).colour m ≠
        (P.loopErasedInput hfinite).colour n := by
  intro n
  exact P.exists_loopErasedIndex_colour_change hZ hY hfinite
    hfiniteMember n

/-- The compressed infinite alternating run walk of the loop-erased stream. -/
noncomputable def infiniteRunWalk
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteMember : ∀ a : M, {k | P.member k = a}.Finite) :
    InfiniteRunWalk Γ.graph :=
  (P.loopErasedInput hfinite).toInfiniteRunWalk
    (P.loopErasedInput_changes hZ hY hfinite hfiniteMember)

/-- The tagged macro member owning the first retained edge of compressed run
`i`.  Constancy of the colour on a maximal run and warp disjointness imply
that this member owns every edge of the run. -/
noncomputable def infiniteRunOwner
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteMember : ∀ a : M, {k | P.member k = a}.Finite)
    (i : ℕ) : M :=
  P.member (retainedIndex hfinite
    (RunCompressor.runBoundary (P.loopErasedInput hfinite).colour
      (P.loopErasedInput_changes hZ hY hfinite hfiniteMember) i))

@[simp]
theorem infiniteRunWalk_run_direction
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteMember : ∀ a : M, {k | P.member k = a}.Finite)
    (i : ℕ) :
    ((P.infiniteRunWalk hZ hY hfinite hfiniteMember).run i).link.direction =
      P.colour (P.infiniteRunOwner hZ hY hfinite hfiniteMember i) := by
  simp [infiniteRunWalk, infiniteRunOwner]

/-- Every retained edge index inside a compressed run has the run's tagged
owner. -/
theorem retained_member_eq_infiniteRunOwner
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteMember : ∀ a : M, {k | P.member k = a}.Finite)
    {i k : ℕ}
    (hlo : RunCompressor.runBoundary (P.loopErasedInput hfinite).colour
        (P.loopErasedInput_changes hZ hY hfinite hfiniteMember) i ≤ k)
    (hhi : k < RunCompressor.runBoundary (P.loopErasedInput hfinite).colour
        (P.loopErasedInput_changes hZ hY hfinite hfiniteMember) (i + 1)) :
    P.member (retainedIndex hfinite k) =
      P.infiniteRunOwner hZ hY hfinite hfiniteMember i := by
  apply P.loopErasedIndex_member_eq_of_colour_constant hZ hY hfinite hlo
  intro j hjlo hjhi
  change (P.loopErasedInput hfinite).colour j =
    (P.loopErasedInput hfinite).colour
      (RunCompressor.runBoundary (P.loopErasedInput hfinite).colour
        (P.loopErasedInput_changes hZ hY hfinite hfiniteMember) i)
  exact RunCompressor.colour_eq_on_run _ _ hjlo (hjhi.trans_lt hhi)

/-- The directed edge set of a compressed infinite run is contained in the
edge set of its unique tagged macro owner. -/
theorem infiniteRunWalk_run_edgeSet_subset_owner
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteMember : ∀ a : M, {k | P.member k = a}.Finite)
    (i : ℕ) :
    ((P.infiniteRunWalk hZ hY hfinite hfiniteMember).run i).link.path.edgeSet ⊆
      (P.carrier (P.infiniteRunOwner hZ hY hfinite hfiniteMember i)).edgeSet := by
  intro e he
  let S := P.loopErasedInput hfinite
  let hc := P.loopErasedInput_changes hZ hY hfinite hfiniteMember
  have hprov := S.projectedRun_edge_provenance hc i he
  rcases hprov with ⟨hdir, k, hklo, hkhi, rfl⟩ |
      ⟨hdir, k, hklo, hkhi, rfl⟩
  · have hmember := P.retained_member_eq_infiniteRunOwner hZ hY hfinite
      hfiniteMember hklo hkhi
    have hcolour : P.colour (P.member (retainedIndex hfinite k)) = .forward := by
      change S.colour k = .forward
      have hrundir : (S.projectedRun hc i).link.direction = .forward := hdir
      rw [S.projectedRun_direction] at hrundir
      exact (RunCompressor.colour_eq_on_run S.colour hc hklo hkhi).trans hrundir
    have hedge := P.edge_mem_forward (retainedIndex hfinite k) hcolour
    rw [hmember] at hedge
    change (B.rawVertex (retainedIndex hfinite k),
      B.rawVertex (retainedIndex hfinite (k + 1))) ∈ _
    unfold retainedIndex
    rw [← loopErasedIndex_join B.rawVertex hfinite k]
    exact hedge
  · have hmember := P.retained_member_eq_infiniteRunOwner hZ hY hfinite
      hfiniteMember hklo hkhi
    have hcolour : P.colour (P.member (retainedIndex hfinite k)) = .backward := by
      change S.colour k = .backward
      have hrundir : (S.projectedRun hc i).link.direction = .backward := hdir
      rw [S.projectedRun_direction] at hrundir
      exact (RunCompressor.colour_eq_on_run S.colour hc hklo hkhi).trans hrundir
    have hedge := P.edge_mem_backward (retainedIndex hfinite k) hcolour
    rw [hmember] at hedge
    change (B.rawVertex (retainedIndex hfinite (k + 1)),
      B.rawVertex (retainedIndex hfinite k)) ∈ _
    unfold retainedIndex
    rw [← loopErasedIndex_join B.rawVertex hfinite k]
    exact hedge

/-- The complete literal warp labels for the compressed infinite macro
stream. -/
theorem infiniteRunWalk_literalBracketLabels
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteMember : ∀ a : M, {k | P.member k = a}.Finite)
    (hroot : B.rawVertex
        (loopErasedIndex B.rawVertex hfinite 0) ∉ Γ.vertexSet Y) :
    (P.infiniteRunWalk hZ hY hfinite hfiniteMember).LiteralBracketLabels Z Y := by
  refine {
    reference_isWarp := hY
    backward_on := ?_
    forward_on := ?_
    initial_outside := ?_
  }
  · intro i hi
    let a := P.infiniteRunOwner hZ hY hfinite hfiniteMember i
    refine ⟨P.carrier a, ?_, ?_⟩
    · apply P.carrier_mem_backward
      exact (P.infiniteRunWalk_run_direction hZ hY hfinite hfiniteMember i).symm.trans hi
    · apply finitePath_isSubpathOf_of_edgeSet_subset _ _
        ((P.infiniteRunWalk hZ hY hfinite hfiniteMember).run i).link.nontrivial
      exact P.infiniteRunWalk_run_edgeSet_subset_owner hZ hY hfinite hfiniteMember i
  · intro i hi
    let a := P.infiniteRunOwner hZ hY hfinite hfiniteMember i
    refine ⟨P.carrier a, ?_, ?_⟩
    · apply P.carrier_mem_forward
      exact (P.infiniteRunWalk_run_direction hZ hY hfinite hfiniteMember i).symm.trans hi
    · apply finitePath_isSubpathOf_of_edgeSet_subset _ _
        ((P.infiniteRunWalk hZ hY hfinite hfiniteMember).run i).link.nontrivial
      exact P.infiniteRunWalk_run_edgeSet_subset_owner hZ hY hfinite hfiniteMember i
  · intro _hi
    exact hroot

/-- Different compressed runs have different tagged owners.  Between the
two run starts lies the first colour change, and convexity of a raw member
fibre prevents that member from reappearing afterwards. -/
theorem infiniteRunOwner_ne_of_lt
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteMember : ∀ a : M, {k | P.member k = a}.Finite)
    {i j : ℕ} (hij : i < j) :
    P.infiniteRunOwner hZ hY hfinite hfiniteMember i ≠
      P.infiniteRunOwner hZ hY hfinite hfiniteMember j := by
  let S := P.loopErasedInput hfinite
  let hc := P.loopErasedInput_changes hZ hY hfinite hfiniteMember
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
  simpa [infiniteRunOwner, retainedIndex, S, hc] using hne

/-- Indexed backward-owner provenance for the compressed infinite stream. -/
noncomputable def infiniteIndexedBackwardProvenance
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteMember : ∀ a : M, {k | P.member k = a}.Finite) :
    (AltPath.infinite
      (P.infiniteRunWalk hZ hY hfinite hfiniteMember).toInfiniteTrace).IndexedBackwardProvenance
        Y ℕ := by
  let W := P.infiniteRunWalk hZ hY hfinite hfiniteMember
  refine {
    link := fun i ↦ (W.run i).link
    links_eq_range := W.toInfiniteTrace_links
    owner := fun i _ ↦
      P.carrier (P.infiniteRunOwner hZ hY hfinite hfiniteMember i)
    owner_mem := ?_
    isSubpath := ?_
    owner_unique := ?_
  }
  · intro i hi
    apply P.carrier_mem_backward
    exact (P.infiniteRunWalk_run_direction hZ hY hfinite hfiniteMember i).symm.trans hi
  · intro i _hi
    apply finitePath_isSubpathOf_of_edgeSet_subset _ _
      (W.run i).link.nontrivial
    exact P.infiniteRunWalk_run_edgeSet_subset_owner hZ hY hfinite hfiniteMember i
  · intro i j hi hj howner
    have hci : P.colour (P.infiniteRunOwner hZ hY hfinite hfiniteMember i) =
        .backward :=
      (P.infiniteRunWalk_run_direction hZ hY hfinite hfiniteMember i).symm.trans hi
    have hcj : P.colour (P.infiniteRunOwner hZ hY hfinite hfiniteMember j) =
        .backward :=
      (P.infiniteRunWalk_run_direction hZ hY hfinite hfiniteMember j).symm.trans hj
    have htag : P.infiniteRunOwner hZ hY hfinite hfiniteMember i =
        P.infiniteRunOwner hZ hY hfinite hfiniteMember j :=
      P.carrier_injective_on_colour (hci.trans hcj.symm) howner
    have hij : i = j := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact (P.infiniteRunOwner_ne_of_lt hZ hY hfinite hfiniteMember hij) htag
      · exact (P.infiniteRunOwner_ne_of_lt hZ hY hfinite hfiniteMember hji) htag.symm
    subst j
    rfl

end OmegaBlocks.EdgeProvenance

namespace MacroChain

variable {V : Type u} {Γ : DWeb V} {Z Y : Set Γ.DPath}

/-- The unconditional infinite edge-level compiler for a path-level macro
chain. -/
noncomputable def compilation
    (C : MacroChain Z Y)
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) : C.Compilation := by
  let B := C.streamBlocks hZ hY hZfin hYfin hroot
  let P := C.streamEdgeProvenance hZ hY hZfin hYfin hroot
  have hvfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite := by
    intro n
    exact C.rawMacroVertex_fiber_finite hZ hY hZfin hYfin hroot _
  have hmfinite : ∀ a : EdgeTag, {k | P.member k = a}.Finite := by
    intro a
    exact C.streamEdgeTag_fiber_finite hZ hY hZfin hYfin hroot a
  have hrootIndex :
      loopErasedIndex B.rawVertex hvfinite 0 = 0 := by
    apply loopErasedIndex_zero_eq_zero_of_root_unique
    intro k hk
    exact C.rawMacroVertex_root_unique hZ hY hZfin hYfin hroot k hk
  have hrawzero : B.rawVertex 0 = (C.z 0).1.initial := by
    exact (C.rawMacroVertex_eq_root_iff hZ hY hZfin hYfin hroot 0).mpr rfl
  let W := P.infiniteRunWalk hZ hY hvfinite hmfinite
  apply Compilation.ofRunWalk C hZ hY hZfin W
  · apply P.infiniteRunWalk_literalBracketLabels hZ hY hvfinite hmfinite
    rw [hrootIndex, hrawzero]
    exact hroot
  · exact P.infiniteIndexedBackwardProvenance hZ hY hvfinite hmfinite
  · change B.rawVertex (loopErasedIndex B.rawVertex hvfinite 0) = _
    rw [hrootIndex, hrawzero]

end MacroChain

variable {V : Type u} {Γ : DWeb V}

/-- The infinite compiler in exactly the globally quantified form consumed
by `safeAlternatingDichotomyStatement_of_macro_compilers`. -/
noncomputable def infiniteMacroCompiler
    (Z Y : Set Γ.DPath)
    (_hZA : Γ.initialSet Z ⊆ Γ.source)
    (_hZB : Γ.terminalFrontier Z ⊆ Γ.target)
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (_hinit : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (u : V) (hu : u ∈ Γ.initialSet Z \ Γ.vertexSet Y)
    (p₀ : Z) (hp₀ : p₀.1.initial = u)
    (_huT : u ∉ Γ.terminalFrontier Z)
    (C : MacroChain Z Y) (hC₀ : C.z 0 = p₀) : C.Compilation := by
  apply C.compilation hZ hY hZfin hYfin
  rw [hC₀, hp₀]
  exact hu.2

end Alternating
end Erdos599
