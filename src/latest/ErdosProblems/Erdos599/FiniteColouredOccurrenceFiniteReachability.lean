/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceNormalizationKonig

/-!
# Finite search regions for fixed-warp safe words

Absence of an infinite safe word makes the entire reachable safe-prefix
graph finite. Its finitely many extension carriers then give a single finite
region containing a normalized witness for every safely reachable terminal.
This does not assert finiteness of an entire union-edge component.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- All safe-prefix nodes reachable from the empty word at a covered vertex. -/
def reachableSafeNodes (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {s : V} (hs : s ∈ Gamma.vertexSet W) : Set (LocalSafeWordNode W Y s) :=
  {P | Relation.ReflTransGen (LocalSafeWordExtension hW hY)
    (LocalSafeWordNode.root s hs) P}

/-- Kőnig extraction applies to the whole reachable state set, independently
of any terminal map or exposed-source condition. -/
theorem exists_safeInfinite_of_reachableSafeNodes_infinite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {s : V} (hs : s ∈ Gamma.vertexSet W)
    (hinfinite : (reachableSafeNodes hW hY hs).Infinite) :
    ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s := by
  obtain ⟨f, hf0, _, hfstep⟩ :=
    RelationKonig.exists_injective_ray_of_finite_out
      (fun P ↦ LocalSafeWordExtension.finite_out hW hY hWfin hYfin P)
      hinfinite
  let C : FiniteColouredOccurrencePrefixChain W Y := {
    stage := fun n ↦ (f n).word
    grows := fun n ↦ (hfstep n).1
    length_strict := fun n ↦ (hfstep n).2.1 }
  refine ⟨C.limit, C.limit_isIntervalSafe hYfin (fun n ↦ (f n).safe), ?_⟩
  have hstage := C.stage_vertex_eq_limit 0 (0 : Fin ((C.stage 0).length + 1))
  have hfirst : (C.stage 0).vertex 0 = s := by
    change (f 0).word.vertex 0 = s
    rw [hf0]
    rfl
  exact hstage.symm.trans hfirst

/-- No infinite safe word implies that only finitely many safe-prefix states
are reachable, a stronger conclusion than finiteness of their terminal row. -/
theorem reachableSafeNodes_finite_of_no_safeInfinite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {s : V} (hs : s ∈ Gamma.vertexSet W)
    (hno : ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s) :
    (reachableSafeNodes hW hY hs).Finite := by
  apply Set.not_infinite.mp
  intro hinfinite
  exact hno (exists_safeInfinite_of_reachableSafeNodes_infinite
    hW hY hWfin hYfin hs hinfinite)

/-- The actual search region: all one-step carriers at reachable states. -/
def safeSearchCarrier (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {s : V} (hs : s ∈ Gamma.vertexSet W) : Set V :=
  ⋃ P ∈ reachableSafeNodes hW hY hs, P.extensionCarrier hW hY

theorem safeSearchCarrier_finite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {s : V} (hs : s ∈ Gamma.vertexSet W)
    (hno : ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s) :
    (safeSearchCarrier hW hY hs).Finite := by
  exact (reachableSafeNodes_finite_of_no_safeInfinite
    hW hY hWfin hYfin hs hno).biUnion fun P _ ↦
      P.extensionCarrier_finite hW hY hWfin hYfin

theorem extensionCarrier_subset_safeSearchCarrier
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {s : V} (hs : s ∈ Gamma.vertexSet W)
    {P : LocalSafeWordNode W Y s}
    (hP : P ∈ reachableSafeNodes hW hY hs) :
    P.extensionCarrier hW hY ⊆ safeSearchCarrier hW hY hs := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP, hx⟩⟩

theorem word_vertexSet_subset_safeSearchCarrier
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {s : V} (hs : s ∈ Gamma.vertexSet W)
    {P : LocalSafeWordNode W Y s}
    (hP : P ∈ reachableSafeNodes hW hY hs) :
    P.word.vertexSet ⊆ safeSearchCarrier hW hY hs :=
  Set.subset_union_left.trans
    (extensionCarrier_subset_safeSearchCarrier hW hY hs hP)

private theorem coveredPathSupport_eq_of_mem_coveredPathSupport
    (hY : Gamma.IsWarp Y) {x a : V}
    (hx : x ∈ coveredPathSupport hY a) :
    coveredPathSupport hY x = coveredPathSupport hY a := by
  classical
  by_cases ha : a ∈ Gamma.vertexSet Y
  · have hcover : coveredPathSupport hY a =
        (DWeb.IsWarp.pathAt hY ha).support := by
      rw [coveredPathSupport, dif_pos ha]
    rw [hcover] at hx ⊢
    exact coveredPathSupport_eq_of_mem hY (DWeb.IsWarp.pathAt_mem hY ha) hx
  · simp only [coveredPathSupport, dif_neg ha, Set.mem_empty_iff_false] at hx

/-- A local carrier contains the whole reference owner of each of its
vertices. This is reference closure only, not forward closure. -/
theorem localOwnerCarrier_referenceClosed
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {a x : V} (hx : x ∈ localOwnerCarrier hW hY a) :
    coveredPathSupport hY x ⊆ localOwnerCarrier hW hY a := by
  intro z hz
  right
  rcases hx with hxW | hxY
  · exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxW, hz⟩⟩
  · obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hxY
    obtain ⟨hyW, hxy⟩ := Set.mem_iUnion.mp hy
    have howners := coveredPathSupport_eq_of_mem_coveredPathSupport hY hxy
    rw [howners] at hz
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyW, hz⟩⟩

private theorem reachable_word_referenceSupport_subset_safeSearchCarrier
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {s : V} (hs : s ∈ Gamma.vertexSet W)
    (hsOff : s ∉ Gamma.vertexSet Y)
    {P : LocalSafeWordNode W Y s}
    (hP : P ∈ reachableSafeNodes hW hY hs) :
    ∀ x ∈ P.word.vertexSet,
      coveredPathSupport hY x ⊆ safeSearchCarrier hW hY hs := by
  classical
  change Relation.ReflTransGen (LocalSafeWordExtension hW hY)
    (LocalSafeWordNode.root s hs) P at hP
  induction hP with
  | refl =>
      intro x hx
      have hxs : x = s := by
        obtain ⟨i, hi⟩ := hx
        exact hi.symm
      subst x
      simp only [coveredPathSupport, dif_neg hsOff]
      exact Set.empty_subset _
  | @tail P Q hreach hstep ih =>
      intro x hx
      rcases hstep.2.2 hx with hxOld | hxLocal
      · exact ih x hxOld
      · exact (localOwnerCarrier_referenceClosed hW hY hxLocal).trans
          (Set.subset_union_right.trans
            (extensionCarrier_subset_safeSearchCarrier hW hY hs hreach))

/-- The finite search region is closed under whole reference owners. This
is the closure needed to keep reference intervals intact in finite-region
arguments; it does not assert closure under all forward owners. -/
theorem safeSearchCarrier_referenceClosed
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {s : V} (hs : s ∈ Gamma.vertexSet W)
    (hsOff : s ∉ Gamma.vertexSet Y)
    {x : V} (hx : x ∈ safeSearchCarrier hW hY hs) :
    coveredPathSupport hY x ⊆ safeSearchCarrier hW hY hs := by
  obtain ⟨P, hP⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hreach, hxP⟩ := Set.mem_iUnion.mp hP
  rcases hxP with hxWord | hxLocal
  · exact reachable_word_referenceSupport_subset_safeSearchCarrier
      hW hY hs hsOff hreach x hxWord
  · exact (localOwnerCarrier_referenceClosed hW hY hxLocal).trans
      (Set.subset_union_right.trans
        (extensionCarrier_subset_safeSearchCarrier hW hY hs hreach))

/-- Every safely reachable terminal has an actual witness inside the one
common search carrier, not merely a terminal lying in that carrier. -/
theorem exists_word_in_safeSearchCarrier_of_mem_safelyReachable
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {s t : V} (hs : s ∈ Gamma.initialSet W)
    (hsOff : s ∉ Gamma.vertexSet Y)
    (ht : t ∈ ColouredSafeReverseReachability.safelyReachable W Y s) :
    ∃ Q : FiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧
      Q.vertex 0 = s ∧ Q.vertex (Fin.last Q.length) = t ∧
      Q.vertexSet ⊆ safeSearchCarrier hW hY (initialSet_subset_vertexSet W hs) := by
  obtain ⟨P, hP, hlast⟩ := exists_reachableNode_of_mem_safelyReachable
    hW hY hWfin hYfin hs hsOff ht
  exact ⟨P.word, P.safe, P.first_eq, hlast,
    word_vertexSet_subset_safeSearchCarrier hW hY
      (initialSet_subset_vertexSet W hs) hP⟩

#print axioms reachableSafeNodes_finite_of_no_safeInfinite
#print axioms safeSearchCarrier_finite
#print axioms safeSearchCarrier_referenceClosed
#print axioms exists_word_in_safeSearchCarrier_of_mem_safelyReachable

end Erdos599.Alternating.FiniteColouredOccurrenceWord
