/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureLocalMatchingOrbit
import ErdosProblems.Erdos599.HalfwayPostClosureMatchingOrbitRoof
import ErdosProblems.Erdos599.HalfwayPostClosureSegmentedRoof

/-!
# Captured-roof geometry of the outside-local matching orbit

Forward steps lie on the captured interval row.  Backward steps lie on the
outside part of the finite interval reference, whose whole carrier is
already roofed at the captured later stage.  Identity steps do not move the
projected vertex.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating
open _root_.Erdos599.TwoWarpMatchingTraversal

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- One matching step against the exact outside interval reference stays in
the captured roof. -/
theorem outsideLocalMatchingStep_preserves_capturedRoof
    {a b : Port V}
    (hab : Step T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) a b)
    (ha : projectPort a ∈ Rlimit.capturedGeometry.outerRoof) :
    projectPort b ∈ Rlimit.capturedGeometry.outerRoof := by
  rcases step_cases hab with
    ⟨x, y, haPort, hbPort, hxy⟩ |
      ⟨x, y, haPort, hbPort, hxy⟩
  · subst a
    subst b
    simp only [projectPort_inl, projectPort_inr] at ha ⊢
    rcases hxy.1 with hRow | hIdentity
    · have hrow : Gamma.vertexSet T.interval.ambientInterval ⊆
          Rlimit.capturedGeometry.outerRoof := by
        rintro v ⟨p, hp, hvp⟩
        exact T.interval.ambientInterval_in_outerRoof p hp hvp
      exact hrow
        ((familyEdges_subset_vertexSet_prod
          T.interval.ambientInterval hRow).2)
    · exact hIdentity.1 ▸ ha
  · subst a
    subst b
    simp only [projectPort_inl, projectPort_inr] at ha ⊢
    rcases hxy.1 with hReference | hIdentity
    · exact T.intervalReference_vertices_subset_capturedRoof
        (vertexSet_outsideReference_subset
          ((familyEdges_subset_vertexSet_prod
            (outsideReference T.intervalReference Rlimit.closedSet)
            hReference).1))
    · exact hIdentity.1 ▸ ha

/-- Every occurrence of a finite outside-local prefix is captured. -/
theorem outsideLocalFiniteOrbit_projectedVertex_mem_capturedRoof
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x) :
    ∀ i, P.projectedVertex i ∈ Rlimit.capturedGeometry.outerRoof := by
  have hnat : ∀ (n : Nat) (hn : n ≤ P.lastIndex),
      projectPort (P.port ⟨n, Nat.lt_succ_of_le hn⟩) ∈
        Rlimit.capturedGeometry.outerRoof := by
    intro n hn
    induction n with
    | zero =>
        simpa [P.starts] using
          Rlimit.later.subset_roof (M.assignmentSource_mem_closedSet hx)
    | succ n ih =>
        let i : Fin P.lastIndex := ⟨n, by omega⟩
        have hprev : projectPort (P.port i.castSucc) ∈
            Rlimit.capturedGeometry.outerRoof := by
          simpa [i] using ih (by omega)
        simpa [i] using
          outsideLocalMatchingStep_preserves_capturedRoof (P.steps i) hprev
  intro i
  exact hnat i.1 (Nat.le_of_lt_succ i.2)

/-- The compiled finite first-return path is still captured. -/
theorem outsideLocalFiniteOrbit_altPath_vertexSet_subset_capturedRoof
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    (P.altPath hrootUnique).vertexSet ⊆
      Rlimit.capturedGeometry.outerRoof := by
  intro v hv
  change v ∈ (P.compressorInput hrootUnique).toFiniteRunWalk.toFiniteTrace.vertexSet at hv
  obtain ⟨n, hn, rfl⟩ :=
    finiteInput_toFiniteTrace_vertexSet_subset
      (P.compressorInput hrootUnique) hv
  have hn' : n ≤ finiteLoopLength P.projectedVertex := by
    simpa only [FinitePortPrefix.compressorInput] using hn.2
  change finiteLoopVertex P.projectedVertex n ∈
    Rlimit.capturedGeometry.outerRoof
  rw [finiteLoopVertex_eq P.projectedVertex hn']
  exact M.outsideLocalFiniteOrbit_projectedVertex_mem_capturedRoof hx P _

/-- Every compiled finite vertex is still an occurrence of the original
outside-local port prefix. -/
theorem outsideLocalFiniteOrbit_altPath_vertex_rawOccurrence
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (_hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0)
    {v : V} (hv : v ∈ (P.altPath hrootUnique).vertexSet) :
    ∃ i, v = P.projectedVertex i := by
  change v ∈ (P.compressorInput hrootUnique).toFiniteRunWalk.toFiniteTrace.vertexSet at hv
  obtain ⟨n, hn, hvn⟩ :=
    finiteInput_toFiniteTrace_vertexSet_subset
      (P.compressorInput hrootUnique) hv
  have hn' : n ≤ finiteLoopLength P.projectedVertex := by
    simpa only [FinitePortPrefix.compressorInput] using hn.2
  refine ⟨finiteLoopIndex P.projectedVertex n, ?_⟩
  have hvn' : finiteLoopVertex P.projectedVertex n = v := by
    simpa only [FinitePortPrefix.compressorInput] using hvn
  rw [finiteLoopVertex_eq P.projectedVertex hn'] at hvn'
  exact hvn'.symm

/-- A compiled distinct first-return path has no closed-set vertex except
its two prescribed endpoints. -/
theorem outsideLocalFirstReturn_altPath_inter_closedSet_subset_endpoints
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (hinterior : ∀ i : Fin (P.lastIndex + 1),
      0 < i.1 → i.1 < P.lastIndex →
        P.projectedVertex i ∉ Rlimit.closedSet)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    (P.altPath hrootUnique).vertexSet ∩ Rlimit.closedSet ⊆
      {x, P.projectedVertex
        ⟨P.lastIndex, Nat.lt_succ_self _⟩} := by
  rintro v ⟨hvPath, hvClosed⟩
  obtain ⟨i, rfl⟩ :=
    M.outsideLocalFiniteOrbit_altPath_vertex_rawOccurrence hx P
      hrootUnique hvPath
  by_cases hi0 : i.1 = 0
  · left
    have hi : i = 0 := Fin.ext hi0
    rw [hi, P.projectedVertex_zero]
  by_cases hilast : i.1 = P.lastIndex
  · right
    exact congrArg P.projectedVertex (Fin.ext hilast)
  · exact False.elim
      (hinterior i (Nat.pos_of_ne_zero hi0) (by omega) hvClosed)

/-- Equivalently, the hammock interior of the compiled first-return path
is disjoint from the closing set. -/
theorem outsideLocalFirstReturn_hammockInterior_disjoint
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (hinterior : ∀ i : Fin (P.lastIndex + 1),
      0 < i.1 → i.1 < P.lastIndex →
        P.projectedVertex i ∉ Rlimit.closedSet)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    Disjoint
      (hammockInterior x
        (.vertex (P.projectedVertex
          ⟨P.lastIndex, Nat.lt_succ_self _⟩))
        (P.altPath hrootUnique))
      Rlimit.closedSet := by
  rw [Set.disjoint_left]
  intro v hvInterior hvClosed
  apply hvInterior.2
  exact M.outsideLocalFirstReturn_altPath_inter_closedSet_subset_endpoints
    hx P hinterior hrootUnique ⟨hvInterior.1, hvClosed⟩

/-- The literal sending step survives chronological erasure as the first
compiled edge.  Since that step leaves the closed set, a distinct
first-return path is genuinely nondegenerate relative to the set. -/
theorem outsideLocalFirstReturn_altPath_not_subset_closedSet
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (hrootUnique : ∀ i,
      P.projectedVertex i = P.projectedVertex 0 → i.1 = 0) :
    ¬(P.altPath hrootUnique).vertexSet ⊆ Rlimit.closedSet := by
  let i : Fin P.lastIndex := ⟨0, P.positive⟩
  have hstep : Step T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet)
      (.inl x) (P.port i.succ) := by
    have hstart : P.port i.castSucc = .inl x := by
      change P.port 0 = .inl x
      exact P.starts
    rw [← hstart]
    exact P.steps i
  have hout : P.projectedVertex i.succ ∉ Rlimit.closedSet := by
    simpa only [FinitePortPrefix.projectedVertex] using
      M.assignmentSource_outsideLocal_successor_projects_outside hx hstep
  let S := P.compressorInput hrootUnique
  have hpositive : 0 < finiteLoopLength P.projectedVertex := by
    simpa only [S, FinitePortPrefix.compressorInput] using S.lastEdge_pos
  have hzero : finiteLoopIndex P.projectedVertex 0 =
      (0 : Fin (P.lastIndex + 1)) :=
    finiteLoopIndex_zero_of_root_unique P.projectedVertex hrootUnique
  have hfirst : S.vertex 1 = P.projectedVertex i.succ := by
    change finiteLoopVertex P.projectedVertex 1 = P.projectedVertex i.succ
    have hs := (finiteLoopVertex_succ P.projectedVertex hpositive).2
    have hidx :
        (⟨(finiteLoopIndex P.projectedVertex 0).1 + 1, by
          have := finiteLoopIndex_lt_top_of_lt_length
            P.projectedVertex hpositive
          omega⟩ : Fin (P.lastIndex + 1)) = i.succ := by
      apply Fin.ext
      have hz := congrArg Fin.val hzero
      simp only [Fin.val_zero] at hz
      simpa only [Fin.val_succ, i] using congrArg (fun n => n + 1) hz
    exact hs.trans (congrArg P.projectedVertex hidx)
  have hfinal : 1 ≤ S.toFiniteRunWalk.finalPosition := by
    simpa only [FiniteRunWalk.finalPosition,
      S.toFiniteRunWalk_final_last] using
        (Nat.succ_le_iff.mpr S.lastEdge_pos)
  have hmem : S.vertex 1 ∈
      (P.altPath hrootUnique).vertexSet := by
    change S.vertex 1 ∈
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).vertexSet
    exact S.toFiniteRunWalk.vertex_mem_toFiniteTrace 1 hfinal
  intro hsubset
  exact hout (hfirst ▸ hsubset hmem)

/-- Every occurrence of an infinite outside-local prefix is captured. -/
theorem outsideLocalInfiniteOrbit_projectedVertex_mem_capturedRoof
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : InfinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x) :
    ∀ n, P.projectedVertex n ∈ Rlimit.capturedGeometry.outerRoof := by
  intro n
  induction n with
  | zero =>
      simpa [P.starts] using
        Rlimit.later.subset_roof (M.assignmentSource_mem_closedSet hx)
  | succ n ih =>
      exact outsideLocalMatchingStep_preserves_capturedRoof (P.steps n) ih

/-- The occurrence-faithful infinite compiler remains captured as well. -/
theorem outsideLocalInfiniteOrbit_altPath_vertexSet_subset_capturedRoof
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : InfinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (houtside : ∀ n, 0 < n →
      P.projectedVertex n ∉ Rlimit.closedSet) :
    (P.altPath (M.assignmentSource_mem_closedSet hx) houtside
      T.interval.ambientInterval_linkage.isWarp
      T.interval.ambientInterval_linkage.finiteCharacter
      (T.intervalReference_isLinkageBetween.isWarp.subset
        (outsideReference_subset
          (Y := T.intervalReference) (X := Rlimit.closedSet)))).vertexSet ⊆
        Rlimit.capturedGeometry.outerRoof := by
  exact P.altPath_vertexSet_subset_of_projectedVertex
    (M.assignmentSource_mem_closedSet hx) houtside
    T.interval.ambientInterval_linkage.isWarp
    T.interval.ambientInterval_linkage.finiteCharacter
    (T.intervalReference_isLinkageBetween.isWarp.subset
      (outsideReference_subset
        (Y := T.intervalReference) (X := Rlimit.closedSet)))
    (M.outsideLocalInfiniteOrbit_projectedVertex_mem_capturedRoof hx P)

/-- The compiled infinite no-return orbit has no closed-set vertex other
than its prescribed source. -/
theorem outsideLocalInfiniteOrbit_altPath_inter_closedSet_subset_source
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : InfinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (houtside : ∀ n, 0 < n →
      P.projectedVertex n ∉ Rlimit.closedSet) :
    (P.altPath (M.assignmentSource_mem_closedSet hx) houtside
      T.interval.ambientInterval_linkage.isWarp
      T.interval.ambientInterval_linkage.finiteCharacter
      (T.intervalReference_isLinkageBetween.isWarp.subset
        (outsideReference_subset
          (Y := T.intervalReference) (X := Rlimit.closedSet)))).vertexSet ∩
        Rlimit.closedSet ⊆ {x} := by
  exact P.altPath_inter_X_subset_root
    (M.assignmentSource_mem_closedSet hx) houtside
    T.interval.ambientInterval_linkage.isWarp
    T.interval.ambientInterval_linkage.finiteCharacter
    (T.intervalReference_isLinkageBetween.isWarp.subset
      (outsideReference_subset
        (Y := T.intervalReference) (X := Rlimit.closedSet)))

/-- Hence the infinite hammock interior is disjoint from the closing set. -/
theorem outsideLocalInfiniteOrbit_hammockInterior_disjoint
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : InfinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (houtside : ∀ n, 0 < n →
      P.projectedVertex n ∉ Rlimit.closedSet) :
    Disjoint
      (hammockInterior x .infinity
        (P.altPath (M.assignmentSource_mem_closedSet hx) houtside
          T.interval.ambientInterval_linkage.isWarp
          T.interval.ambientInterval_linkage.finiteCharacter
          (T.intervalReference_isLinkageBetween.isWarp.subset
            (outsideReference_subset
              (Y := T.intervalReference) (X := Rlimit.closedSet)))))
      Rlimit.closedSet := by
  rw [Set.disjoint_left]
  intro v hvInterior hvClosed
  apply hvInterior.2
  exact M.outsideLocalInfiniteOrbit_altPath_inter_closedSet_subset_source
    hx P houtside ⟨hvInterior.1, hvClosed⟩

/-- The infinite compiled orbit really leaves the closed set; this uses the
positive compressor coordinate, whose occurrence remains outside after
chronological erasure. -/
theorem outsideLocalInfiniteOrbit_altPath_not_subset_closedSet
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : InfinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) x)
    (houtside : ∀ n, 0 < n →
      P.projectedVertex n ∉ Rlimit.closedSet) :
    ¬(P.altPath (M.assignmentSource_mem_closedSet hx) houtside
      T.interval.ambientInterval_linkage.isWarp
      T.interval.ambientInterval_linkage.finiteCharacter
      (T.intervalReference_isLinkageBetween.isWarp.subset
        (outsideReference_subset
          (Y := T.intervalReference) (X := Rlimit.closedSet)))).vertexSet ⊆
        Rlimit.closedSet := by
  let hrootX := M.assignmentSource_mem_closedSet hx
  let hW : Gamma.IsWarp T.interval.ambientInterval :=
    T.interval.ambientInterval_linkage.isWarp
  let hWfinite : Gamma.HasFiniteCharacter T.interval.ambientInterval :=
    T.interval.ambientInterval_linkage.finiteCharacter
  let hY : Gamma.IsWarp
      (outsideReference T.intervalReference Rlimit.closedSet) :=
    T.intervalReference_isLinkageBetween.isWarp.subset
    (outsideReference_subset
      (Y := T.intervalReference) (X := Rlimit.closedSet))
  let hfirst := P.firstLiteral_of_positive_outside hrootX houtside
  let S := P.compressorInput hfirst
  let hchange := P.compressorInput_changes hfirst hW hWfinite hY
  have hout : S.vertex 1 ∉ Rlimit.closedSet := by
    exact P.compressorInput_vertex_positive_outside
      hrootX houtside (n := 1) (by omega)
  have hmem : S.vertex 1 ∈
      (P.altPath hrootX houtside hW hWfinite hY).vertexSet := by
    change S.vertex 1 ∈
      (S.toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet
    rw [S.toInfiniteTrace_vertexSet hchange]
    exact ⟨1, rfl⟩
  intro hsubset
  exact hout (hsubset hmem)

#print axioms outsideLocalMatchingStep_preserves_capturedRoof
#print axioms outsideLocalFiniteOrbit_projectedVertex_mem_capturedRoof
#print axioms outsideLocalFiniteOrbit_altPath_vertexSet_subset_capturedRoof
#print axioms outsideLocalFiniteOrbit_altPath_vertex_rawOccurrence
#print axioms outsideLocalFirstReturn_hammockInterior_disjoint
#print axioms outsideLocalFirstReturn_altPath_not_subset_closedSet
#print axioms outsideLocalInfiniteOrbit_projectedVertex_mem_capturedRoof
#print axioms outsideLocalInfiniteOrbit_altPath_vertexSet_subset_capturedRoof
#print axioms outsideLocalInfiniteOrbit_altPath_inter_closedSet_subset_source
#print axioms outsideLocalInfiniteOrbit_hammockInterior_disjoint
#print axioms outsideLocalInfiniteOrbit_altPath_not_subset_closedSet

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
