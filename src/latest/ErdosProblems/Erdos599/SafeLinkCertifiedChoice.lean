/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkPropositionComplete

/-!
# Safe target paths retaining their Section 6 boundary certificate

The public safe-link theorem only returns a path and the fact that deleting
its support is unhindered.  For an infinite simultaneous selection it is
useful to retain the maximal safe tree used by the proof and the common-web
waves roofing every point of that tree's outer boundary.

The completed proof of Proposition 6.3 does not in fact use the customary
assumption that the maximal tree is disjoint from the target.  We expose
that stronger form first.  An unhindered normalized web then has a maximal
safe tree meeting the target; a path inside it is safely deletable by the
finite-deletion field of `IsTreeSet`, and the unrestricted Proposition 6.3
certificate remains attached to the choice.
-/

noncomputable section

namespace Erdos599
namespace SafeLink

open Set DirectedPath

universe u

variable {V : Type u}

/-- Proposition 6.3 without the unused target-disjointness premise. -/
def UnrestrictedProposition63 (V : Type u) : Prop :=
  ∀ (G : DWeb V), G.IsNormalized →
    ∀ {a : V} {T : Set V}, a ∈ G.source →
      Maximal (G.IsTreeSet a) T →
      ∀ y ∈ G.outerBoundary T,
        ∃ U : Set ((G.delete
            (insert a (nonBoundedTreeVertices G a T))).DPath),
          (G.delete (insert a (nonBoundedTreeVertices G a T))).IsWave U ∧
            y ∈ (G.delete
              (insert a (nonBoundedTreeVertices G a T))).roof
                ((G.delete
                  (insert a (nonBoundedTreeVertices G a T))).terminalFrontier U)

/-- The full quotient-closure proof of Proposition 6.3 is independent of
target-disjointness, so it establishes the unrestricted statement. -/
theorem unrestrictedProposition63 : UnrestrictedProposition63 V := by
  intro G hG a T ha hT y hy
  let base := G.delete {a}
  let hNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  let F := fun z ↦ boundaryObstruction G hG hT z
  let K := groundingSet G a T
  let Y := G.outerBoundary T
  let Q := nonBoundedTreeVertices G a T
  let X := base.sectionSixFullAccumClosure hNoEnter F K Y Q T y
  let M := base.sectionSixFullAccumCommonWave hNoEnter F K Y Q T y
  apply boundaryWave_of_sectionSixData_unconditional
    G hG ha hT hy X M
  · exact base.sectionSixFullAccumClosure_countable hNoEnter
      (fun z ↦ boundaryObstruction_finite G hG hT z)
      (fun t ↦ groundingSet_countable G a T t)
  · exact G.sectionSixFullAccumClosure_subset_offRoot a hNoEnter
      F K Y Q T y (boundaryObstruction_subset G hG hT)
      (groundingSet_subset_offRoot G a T)
  · change F y ⊆ X
    simpa only [base.sectionSixFullAccumStage_zero_carrier] using
      (base.sectionSixFullAccumStage_carrier_subset_closure
        hNoEnter F K Y Q T y 0)
  · exact base.sectionSixFullAccum_meeting_tree_closed
      hNoEnter F K Y Q T y
  · exact base.sectionSixFullAccum_boundary_closed
      hNoEnter F K Y Q T y
  · intro t ht
    exact (sectionSixFullAccumClosure_grounding G hG ha hT y t ht).2

/-- A safe target path together with the maximal safe tree from which it is
drawn and the common-deletion boundary waves attached to that tree. -/
structure CertifiedSafeTargetPath (G : DWeb V) (a : V) where
  tree : Set V
  tree_maximal : Maximal (G.IsTreeSet a) tree
  targetVertex : V
  targetVertex_mem_tree : targetVertex ∈ tree
  targetVertex_mem_target : targetVertex ∈ G.target
  path : FinitePath G.graph
  path_start : path.start = a
  path_finish : path.finish = targetVertex
  path_support_subset_tree : path.support ⊆ tree
  path_safe : G.IsSafeTargetPath a path
  boundaryWaves :
    ∀ y ∈ G.outerBoundary tree,
      ∃ U : Set ((G.delete
          (insert a (nonBoundedTreeVertices G a tree))).DPath),
        (G.delete (insert a (nonBoundedTreeVertices G a tree))).IsWave U ∧
          y ∈ (G.delete
            (insert a (nonBoundedTreeVertices G a tree))).roof
              ((G.delete
                (insert a (nonBoundedTreeVertices G a tree))).terminalFrontier U)

/-- The pointwise boundary certificates can be absorbed into one wave in
their common local deletion.  This compresses an arbitrarily large outer
boundary to a single retained witness for each certified root/tree. -/
theorem CertifiedSafeTargetPath.exists_commonBoundaryWave
    {G : DWeb V} {a : V} (C : CertifiedSafeTargetPath G a) :
    ∃ M : (G.delete
        (insert a (nonBoundedTreeVertices G a C.tree))).Wave,
      G.outerBoundary C.tree ⊆
        (G.delete
          (insert a (nonBoundedTreeVertices G a C.tree))).roof
          ((G.delete
            (insert a (nonBoundedTreeVertices G a C.tree))).terminalFrontier
              M.1) := by
  let H := G.delete (insert a (nonBoundedTreeVertices G a C.tree))
  have hcover : ∀ y, y ∈ G.outerBoundary C.tree →
      ∃ W : H.Wave, y ∈ H.roof (H.terminalFrontier W.1) := by
    intro y hy
    obtain ⟨U, hU, hyU⟩ := C.boundaryWaves y hy
    exact ⟨⟨U, hU⟩, hyU⟩
  simpa only [H] using
    (exists_wave_roofing H (Y := G.outerBoundary C.tree) hcover)

/-- Every maximal safe tree in a normalized unhindered web meets the target.
Otherwise unrestricted Proposition 6.3 promotes its roofed boundary to a
hindrance. -/
theorem maximalTree_meets_target
    (G : DWeb V) (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {a : V} (ha : a ∈ G.source) {T : Set V}
    (hT : Maximal (G.IsTreeSet a) T) :
    (T ∩ G.target).Nonempty := by
  by_contra hempty
  have hdisjoint : Disjoint T G.target := by
    rw [Set.disjoint_left]
    intro t htT htTarget
    exact hempty ⟨t, htT, htTarget⟩
  have hhindered : G.IsHindered :=
    isHindered_of_individual_boundary_waves G
      (insert_root_nonBounded_subset_tree G hT.1) hdisjoint ha
      (fun y hy ↦ unrestrictedProposition63 G hNorm ha hT y hy)
  exact hG hhindered

/-- A path from the root to a target point inside a safe tree has safely
deletable support. -/
theorem isSafeTargetPath_of_mem_maximalTree
    (G : DWeb V) {a t : V} {T : Set V}
    (hT : G.IsTreeSet a T) (htT : t ∈ T) (htTarget : t ∈ G.target) :
    ∃ p : FinitePath G.graph,
      p.start = a ∧ p.finish = t ∧ p.support ⊆ T ∧
        G.IsSafeTargetPath a p := by
  obtain ⟨p, hpstart, hpfinish, hpT⟩ := hT.2.2.1 t htT
  let F := p.support \ {a}
  have hFfinite : F.Finite := (G.finitePath_support_finite p).sdiff
  have hFsub : F ⊆ T \ {a} := by
    intro x hx
    exact ⟨hpT hx.1, hx.2⟩
  have hsafe := hT.2.2.2 F hFfinite hFsub
  have hcarrier : insert a F = p.support := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [F, hpstart ▸ p.start_mem_support]
    · simp [F, hxa]
  have hpSafe : G.IsSafeTargetPath a p := by
    refine ⟨hpstart, hpfinish ▸ htTarget, ?_⟩
    simpa [DWeb.SafeAfterRootDeletion, DWeb.SafeDeletion, hcarrier] using hsafe
  exact ⟨p, hpstart, hpfinish, hpT, hpSafe⟩

/-- Strengthened Theorem 6.1 retaining the safe tree and its boundary-wave
certificate. -/
theorem exists_certifiedSafeTargetPath
    (G : DWeb V) (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {a : V} (ha : a ∈ G.source) :
    Nonempty (CertifiedSafeTargetPath G a) := by
  obtain ⟨T, hT⟩ := exists_maximalTreeSet_of_isUnhindered G hG ha
  obtain ⟨t, htT, htTarget⟩ := maximalTree_meets_target
    G hNorm hG ha hT
  obtain ⟨p, hpstart, hpfinish, hpT, hpSafe⟩ :=
    isSafeTargetPath_of_mem_maximalTree G hT.1 htT htTarget
  exact ⟨{
    tree := T
    tree_maximal := hT
    targetVertex := t
    targetVertex_mem_tree := htT
    targetVertex_mem_target := htTarget
    path := p
    path_start := hpstart
    path_finish := hpfinish
    path_support_subset_tree := hpT
    path_safe := hpSafe
    boundaryWaves := fun y hy ↦
      unrestrictedProposition63 G hNorm ha hT y hy }⟩

#print axioms unrestrictedProposition63
#print axioms CertifiedSafeTargetPath.exists_commonBoundaryWave
#print axioms exists_certifiedSafeTargetPath

end SafeLink
end Erdos599
