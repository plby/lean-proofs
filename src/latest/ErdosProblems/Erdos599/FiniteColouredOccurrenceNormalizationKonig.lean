/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceNormalizationTree
import ErdosProblems.Erdos599.InfiniteColouredOccurrenceLimit
import ErdosProblems.Erdos599.ColouredSafeReverseReachability
import ErdosProblems.Erdos599.RelationKonig

/-!
# Kőnig compactness for fixed-warp safe terminal words

Every finite safe terminal witness maps into the same finitely branching
tree of local safe-word extensions.  Infinitely many distinct terminals
therefore force an infinite strict prefix ray.  Its literal omega limit is
an infinite interval-safe occurrence word using the original forward warp.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- A safely reachable terminal has a tree node with the same endpoint. -/
theorem exists_reachableNode_of_mem_safelyReachable
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {s t : V} (hs : s ∈ Gamma.initialSet W)
    (hsOff : s ∉ Gamma.vertexSet Y)
    (ht : t ∈ ColouredSafeReverseReachability.safelyReachable W Y s) :
    ∃ Q : LocalSafeWordNode W Y s,
      Relation.ReflTransGen (LocalSafeWordExtension hW hY)
        (LocalSafeWordNode.root (W := W) (Y := Y) s
          (initialSet_subset_vertexSet W hs)) Q ∧
      Q.word.vertex (Fin.last Q.word.length) = t := by
  rcases ht with ⟨⟨htW, htOff⟩, total, htotal, hfirst, hlast⟩
  subst s
  have htotalFirst : total.vertex 0 ∈ Gamma.initialSet W := hs
  have htotalFirstOff : total.vertex 0 ∉ Gamma.vertexSet Y := hsOff
  have htotalLast : total.vertex (Fin.last total.length) ∈
      Gamma.terminalFrontier W := hlast.symm ▸ htW
  have htotalLastOff : total.vertex (Fin.last total.length) ∉
      Gamma.vertexSet Y := by
    simpa only [hlast] using htOff
  obtain ⟨Q, hreach, hQlast⟩ := exists_reachable_normalizedTerminalNode
    hW hY hWfin hYfin total htotal htotalFirst htotalFirstOff
      htotalLast htotalLastOff
  exact ⟨Q, hreach, hQlast.trans hlast⟩

/-- Infinitely many distinct fixed-warp safe terminals force an infinite
safe occurrence word rooted at the same source. -/
theorem exists_safeInfinite_of_safelyReachable_infinite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {s : V} (hs : s ∈ Gamma.initialSet W)
    (hsOff : s ∉ Gamma.vertexSet Y)
    (hinfinite :
      (ColouredSafeReverseReachability.safelyReachable W Y s).Infinite) :
    ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s := by
  classical
  let root : LocalSafeWordNode W Y s :=
    LocalSafeWordNode.root s (initialSet_subset_vertexSet W hs)
  let reachable : Set (LocalSafeWordNode W Y s) :=
    {Q | Relation.ReflTransGen (LocalSafeWordExtension hW hY) root Q}
  have hreachable : reachable.Infinite := by
    intro hfinite
    apply hinfinite.not_finite
    apply (hfinite.image fun Q ↦
      Q.word.vertex (Fin.last Q.word.length)).subset
    intro t ht
    obtain ⟨Q, hreach, hlast⟩ :=
      exists_reachableNode_of_mem_safelyReachable hW hY hWfin hYfin
        hs hsOff ht
    exact ⟨Q, hreach, hlast⟩
  obtain ⟨f, hf0, _hfinjective, hfstep⟩ :=
    RelationKonig.exists_injective_ray_of_finite_out
      (fun P ↦ LocalSafeWordExtension.finite_out hW hY hWfin hYfin P)
      hreachable
  let C : FiniteColouredOccurrencePrefixChain W Y := {
    stage := fun n ↦ (f n).word
    grows := fun n ↦ (hfstep n).1
    length_strict := fun n ↦ (hfstep n).2.1 }
  have hsafe : ∀ n, (C.stage n).IsIntervalSafe := fun n ↦ (f n).safe
  have hlimitSafe : C.limit.IsIntervalSafe := C.limit_isIntervalSafe hYfin hsafe
  have hlimitFirst : C.limit.vertex 0 = s := by
    have hstage := C.stage_vertex_eq_limit 0 (0 : Fin ((C.stage 0).length + 1))
    have hrootWord : (C.stage 0).vertex 0 = s := by
      change (f 0).word.vertex 0 = s
      rw [hf0]
      rfl
    exact hstage.symm.trans hrootWord
  exact ⟨C.limit, hlimitSafe, hlimitFirst⟩

/-- Contrapositive form used by arbitrary-index Hall: a source with no
fixed-warp safe infinite word has a finite safe-terminal row. -/
theorem safelyReachable_finite_of_no_safeInfinite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {s : V} (hs : s ∈ Gamma.initialSet W)
    (hsOff : s ∉ Gamma.vertexSet Y)
    (hno : ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s) :
    (ColouredSafeReverseReachability.safelyReachable W Y s).Finite := by
  apply Set.not_infinite.mp
  intro hinfinite
  exact hno (exists_safeInfinite_of_safelyReachable_infinite
    hW hY hWfin hYfin hs hsOff hinfinite)

#print axioms exists_reachableNode_of_mem_safelyReachable
#print axioms exists_safeInfinite_of_safelyReachable_infinite
#print axioms safelyReachable_finite_of_no_safeInfinite

end Erdos599.Alternating.FiniteColouredOccurrenceWord
