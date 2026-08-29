/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceLocalCarrier
import ErdosProblems.Erdos599.FiniteColouredOccurrenceFiniteCarrier

/-!
# A witness-independent tree of safe occurrence words

The nodes remember only a safe word rooted at `s` whose current endpoint is
covered by `W`.  A tree edge is deliberately broader than the deterministic
normalization move: it is any strict literal prefix extension whose new
vertices lie in the current word together with the finite local owner
carrier.  Consequently the relation does not mention a fixed terminal word.

This file proves that every genuine fixed-word normalization successor is a
tree edge.  Thus the exact normalization history can later be mapped into a
single tree shared by all terminal witnesses.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- A safe rooted finite occurrence word whose current endpoint still lies
on the forward warp. -/
structure LocalSafeWordNode (W Y : Set Gamma.DPath) (s : V) where
  word : FiniteColouredOccurrenceWord W Y
  safe : word.IsIntervalSafe
  first_eq : word.vertex 0 = s
  current_mem : word.vertex (Fin.last word.length) ∈ Gamma.vertexSet W

def LocalSafeWordNode.root (s : V) (hs : s ∈ Gamma.vertexSet W) :
    LocalSafeWordNode W Y s where
  word := emptyAt s
  safe := emptyAt_isIntervalSafe s
  first_eq := rfl
  current_mem := by simpa only [emptyAt_last] using hs

theorem LocalSafeWordNode.eq_of_word_eq {s : V}
    {P Q : LocalSafeWordNode W Y s} (h : P.word = Q.word) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- The finite carrier available for one tree extension. -/
def LocalSafeWordNode.extensionCarrier
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y) {s : V}
    (P : LocalSafeWordNode W Y s) : Set V :=
  P.word.vertexSet ∪
    localOwnerCarrier hW hY (P.word.vertex (Fin.last P.word.length))

theorem LocalSafeWordNode.extensionCarrier_finite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y) {s : V}
    (P : LocalSafeWordNode W Y s) : P.extensionCarrier hW hY |>.Finite := by
  exact P.word.vertexSet_finite.union
    (localOwnerCarrier_finite hW hY hWfin hYfin _)

/-- The broad canonical tree edge.  Safety and the rooted/current endpoint
conditions are supplied by the target node itself. -/
def LocalSafeWordExtension
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y) {s : V}
    (P Q : LocalSafeWordNode W Y s) : Prop :=
  P.word.Prefix Q.word ∧ P.word.length < Q.word.length ∧
    Q.word.vertexSet ⊆ P.extensionCarrier hW hY

/-- The broad tree is finitely branching.  The local carrier is finite, and
there are only finitely many literal coloured occurrence words supported on
a fixed finite vertex set. -/
theorem LocalSafeWordExtension.finite_out
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y) {s : V}
    (P : LocalSafeWordNode W Y s) :
    {Q | LocalSafeWordExtension hW hY P Q}.Finite := by
  classical
  apply Set.Finite.of_finite_image
    ((finite_setOf_vertexSet_subset (W := W) (Y := Y)
      (P.extensionCarrier hW hY)
      (P.extensionCarrier_finite hW hY hWfin hYfin)).subset (by
        rintro q ⟨Q, hQ, rfl⟩
        exact hQ.2.2))
  intro Q _ R _ hword
  cases Q
  cases R
  cases hword
  rfl

/-- Every anchored fixed-prefix state has its current endpoint on `W`.
This is derived from balance: it is either the fixed `W` terminal or has an
outgoing edge in the fixed forward relation. -/
theorem FixedSafePrefixState.current_mem_forwardWarp
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    S.word.vertex (Fin.last S.word.length) ∈ Gamma.vertexSet W := by
  rcases S.current_eq_totalFinish_or_hasTotalForward hW hY hYfin
      hfirstOff hlastOff with hterminal | ⟨b, hab⟩
  · rw [hterminal]
    exact terminalFrontier_subset_vertexSet W hlast
  · exact (familyEdges_subset_vertexSet_prod W
      (total.forwardEdges_subset_familyEdges hab)).1

/-- Forget the fixed terminal witness while retaining the safe rooted word. -/
def FixedSafePrefixState.toLocalSafeWordNode
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    (S : FixedSafePrefixState total)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    LocalSafeWordNode W Y (total.vertex 0) where
  word := S.word
  safe := S.safe
  first_eq := S.first_eq
  current_mem := S.current_mem_forwardWarp hW hY hYfin hfirstOff hlast hlastOff

/-- A normalized terminal word is itself a tree node. -/
def FixedNormalizedTerminal.toLocalSafeWordNode
    {total : FiniteColouredOccurrenceWord W Y}
    {S : FixedSafePrefixState total} (T : FixedNormalizedTerminal S)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W) :
    LocalSafeWordNode W Y (total.vertex 0) where
  word := T.word
  safe := T.safe
  first_eq := T.first_eq
  current_mem := by
    rw [T.last_eq]
    exact terminalFrontier_subset_vertexSet W hlast

/-- A literal fixed-word normalization successor is an edge of the broad
witness-independent tree. -/
theorem FixedSafePrefixSuccessor.localSafeWordExtension
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    {S : FixedSafePrefixState total} (N : FixedSafePrefixSuccessor S)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    LocalSafeWordExtension hW hY
      (S.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff)
      (N.next.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff) := by
  refine ⟨N.embedding, N.length_lt, ?_⟩
  change N.next.word.vertexSet ⊆ S.word.vertexSet ∪
    localOwnerCarrier hW hY (S.word.vertex (Fin.last S.word.length))
  rw [N.next_vertexSet]
  have hforwardCovered : N.forward.path.support ⊆
      coveredPathSupport hW
        (S.word.vertex (Fin.last S.word.length)) :=
    finiteForward_support_subset_coveredPathSupport hW hY N.forward.path
      N.forward.nontrivial
      (N.forward.edges_total.trans total.forwardEdges_subset_familyEdges)
      N.forward.join
  have hcontactOwner : N.forward.path.finish ∈ N.referenceOwner.support := by
    rw [← N.backward.extension_finish]
    exact N.backward.extension_isSubpath_owner.1
      N.backward.extension.finish_mem_support
  have hbackwardLocal : N.backward.extension.support ⊆
      localOwnerCarrier hW hY
        (S.word.vertex (Fin.last S.word.length)) := by
    apply (N.backward.extension_isSubpath_owner.1).trans
    exact referenceOwner_support_subset_localOwnerCarrier hW hY
      (hforwardCovered N.forward.path.finish_mem_support)
      N.referenceOwner N.referenceOwner_mem hcontactOwner
  intro x hx
  rcases hx with hxOld | hxBackward
  · rcases hxOld with hxWord | hxForward
    · exact Or.inl hxWord
    · exact Or.inr (Or.inl (hforwardCovered hxForward))
  · exact Or.inr (hbackwardLocal hxBackward)

/-- The retained final forward suffix is one last edge of the broad tree. -/
theorem FixedNormalizedTerminalExtension.localSafeWordExtension
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    {S : FixedSafePrefixState total}
    (E : FixedNormalizedTerminalExtension S)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    LocalSafeWordExtension hW hY
      (S.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff)
      (E.terminal.toLocalSafeWordNode hlast) := by
  refine ⟨E.terminal.embedding, ?_, ?_⟩
  · change S.word.length < E.terminal.word.length
    rw [E.word_eq,
      S.word.appendForwardPath_length E.path E.join E.edges_forward E.fresh]
    have hpositive : 0 < E.path.walk.length := by
      exact Nat.pos_of_ne_zero (fun h ↦ E.nontrivial
        (Walk.endpoints_eq_of_length_eq_zero E.path.walk h))
    omega
  · change E.terminal.word.vertexSet ⊆ S.word.vertexSet ∪
      localOwnerCarrier hW hY (S.word.vertex (Fin.last S.word.length))
    rw [E.word_eq,
      S.word.appendForwardPath_vertexSet E.path E.join E.edges_forward E.fresh]
    have hpathLocal := finiteForward_support_subset_localOwnerCarrier
      hW hY E.path E.nontrivial E.edges_forward E.join
    intro x hx
    exact hx.elim Or.inl (fun h ↦ Or.inr (hpathLocal h))

/-- Map the complete fixed-state reachability history into the common local
safe-word tree. -/
theorem FixedNormalizationSuccessorRelation.toLocalSafeWordExtension
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    {S T : FixedSafePrefixState total}
    (hST : FixedNormalizationSuccessorRelation S T)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    LocalSafeWordExtension hW hY
      (S.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff)
      (T.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff) := by
  obtain ⟨N, rfl⟩ := hST
  exact N.localSafeWordExtension hW hY hYfin hfirstOff hlast hlastOff

theorem FixedNormalizationDerivation.stateNode_reach
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    {S : FixedSafePrefixState total}
    (D : FixedNormalizationDerivation S)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    Relation.ReflTransGen (LocalSafeWordExtension hW hY)
      (S.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff)
      (D.last.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff) := by
  have mapReach : ∀ {T : FixedSafePrefixState total},
      Relation.ReflTransGen FixedNormalizationSuccessorRelation S T →
      Relation.ReflTransGen (LocalSafeWordExtension hW hY)
        (S.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff)
        (T.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff) := by
    intro T hreach
    induction hreach with
    | refl => exact .refl
    | tail hreach hstep ih =>
        exact .tail ih (hstep.toLocalSafeWordExtension hW hY hYfin
          hfirstOff hlast hlastOff)
  exact mapReach D.reach

/-- The retained normalization history reaches the actual normalized
terminal node, including its possible final forward suffix. -/
theorem FixedNormalizationDerivation.terminalNode_reach
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {total : FiniteColouredOccurrenceWord W Y}
    {S : FixedSafePrefixState total}
    (D : FixedNormalizationDerivation S)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    Relation.ReflTransGen (LocalSafeWordExtension hW hY)
      (S.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff)
      (D.conclusion.terminal.toLocalSafeWordNode hlast) := by
  have hstates := D.stateNode_reach hW hY hYfin hfirstOff hlast hlastOff
  rcases D.conclusion.local_step with hsame | ⟨E, hE⟩
  · have hnodes : D.conclusion.terminal.toLocalSafeWordNode hlast =
        D.last.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff := by
      exact LocalSafeWordNode.eq_of_word_eq hsame
    rw [hnodes]
    exact hstates
  · have hedge := E.localSafeWordExtension hW hY hYfin
      hfirstOff hlast hlastOff
    have htarget : E.terminal.toLocalSafeWordNode hlast =
        D.conclusion.terminal.toLocalSafeWordNode hlast := by
      exact LocalSafeWordNode.eq_of_word_eq hE
    rw [← htarget]
    exact hstates.tail hedge

/-- Every finite safe terminal witness normalizes to a terminal node
reachable in the one witness-independent tree rooted at its source. -/
theorem exists_reachable_normalizedTerminalNode
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (total : FiniteColouredOccurrenceWord W Y)
    (htotal : total.IsIntervalSafe)
    (hfirst : total.vertex 0 ∈ Gamma.initialSet W)
    (hfirstOff : total.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W)
    (hlastOff : total.vertex (Fin.last total.length) ∉ Gamma.vertexSet Y) :
    ∃ Q : LocalSafeWordNode W Y (total.vertex 0),
      Relation.ReflTransGen (LocalSafeWordExtension hW hY)
        (LocalSafeWordNode.root (W := W) (Y := Y) (total.vertex 0)
          (initialSet_subset_vertexSet W hfirst)) Q ∧
      Q.word.vertex (Fin.last Q.word.length) =
        total.vertex (Fin.last total.length) := by
  let S := FixedSafePrefixState.initial total
  obtain ⟨D⟩ := S.exists_normalizationDerivation hW hY hWfin hYfin
    htotal hfirst hfirstOff hlast hlastOff
  let Q := D.conclusion.terminal.toLocalSafeWordNode hlast
  refine ⟨Q, ?_, D.conclusion.terminal.last_eq⟩
  have hreach := D.terminalNode_reach hW hY hYfin hfirstOff hlast hlastOff
  have hroot : S.toLocalSafeWordNode hW hY hYfin hfirstOff hlast hlastOff =
      LocalSafeWordNode.root (W := W) (Y := Y) (total.vertex 0)
        (initialSet_subset_vertexSet W hfirst) := by
    exact LocalSafeWordNode.eq_of_word_eq rfl
  rw [hroot] at hreach
  exact hreach

#print axioms LocalSafeWordNode.extensionCarrier_finite
#print axioms LocalSafeWordExtension.finite_out
#print axioms FixedSafePrefixState.current_mem_forwardWarp
#print axioms FixedSafePrefixSuccessor.localSafeWordExtension
#print axioms FixedNormalizedTerminalExtension.localSafeWordExtension
#print axioms FixedNormalizationDerivation.terminalNode_reach
#print axioms exists_reachable_normalizedTerminalNode

end Erdos599.Alternating.FiniteColouredOccurrenceWord
