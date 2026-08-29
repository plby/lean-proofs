/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularCollectiveSafeBatch
import ErdosProblems.Erdos599.RegularRightBoundary
import ErdosProblems.Erdos599.SingularSafeSelectionFinite

/-!
# A safe selected path need not carry its own boundary wave

The unique source of the three-vertex branching web has two target leaves.
Selecting either target edge is safe because deleting its carrier removes the
only source.  The other target leaf is nevertheless an outer-boundary point
of that carrier, and no wave in the deletion can roof it.

Consequently neither pruning a retained Section 6 tree to the chosen
root--target path nor pruning it to any one-target subtree can supply the
boundary certificate used by collective-tree resurrection.  A valid limit
argument must allow a wave-dependent rerouting/cut; it cannot obtain the
common-deletion certificate by a static path-carrier pruning.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafePathBoundaryCounterexample

open DirectedPath SingularSafeTreeResurrection
open RegularRightBoundary.BranchingStage.Vertex

/-- The carrier of the chosen target edge is exactly its two endpoints. -/
@[simp] theorem vertexSet_targetFamily :
    RegularRightBoundary.BranchingStage.web.vertexSet
      RegularRightBoundary.BranchingStage.targetFamily =
      ({u, b} : Set RegularRightBoundary.BranchingStage.Vertex) := by
  ext x
  simp only [DWeb.mem_vertexSet,
    RegularRightBoundary.BranchingStage.targetFamily]
  constructor
  · rintro ⟨p, rfl, hxp⟩
    change x ∈ RegularRightBoundary.BranchingStage.ub.support at hxp
    simpa only [RegularRightBoundary.BranchingStage.ub_support] using hxp
  · intro hx
    refine ⟨Sum.inl RegularRightBoundary.BranchingStage.ub, rfl, ?_⟩
    change x ∈ RegularRightBoundary.BranchingStage.ub.support
    simpa only [RegularRightBoundary.BranchingStage.ub_support] using hx

/-- The unused target leaf is an outer-boundary point of the chosen path. -/
theorem unusedTarget_mem_outerBoundary :
    c ∈ RegularRightBoundary.BranchingStage.web.outerBoundary
      (RegularRightBoundary.BranchingStage.web.vertexSet
        RegularRightBoundary.BranchingStage.targetFamily) := by
  rw [vertexSet_targetFamily]
  refine ⟨by simp, u, by simp, ?_⟩
  simp [RegularRightBoundary.BranchingStage.web,
    RegularRightBoundary.BranchingStage.graph]

/-- Deleting the chosen path carrier removes the unique source. -/
theorem delete_targetFamily_source_eq_empty :
    (RegularRightBoundary.BranchingStage.web.delete
      (RegularRightBoundary.BranchingStage.web.vertexSet
        RegularRightBoundary.BranchingStage.targetFamily)).source = ∅ := by
  rw [vertexSet_targetFamily]
  ext x
  constructor
  · rintro ⟨hxSource, hxCarrier⟩
    change x ∈ ({u} : Set RegularRightBoundary.BranchingStage.Vertex) at hxSource
    change x ∉ ({u, b} : Set RegularRightBoundary.BranchingStage.Vertex) at hxCarrier
    exact (hxCarrier (Or.inl hxSource)).elim
  · intro hx
    exact hx.elim

/-- Every wave in the deletion of the chosen carrier has empty path family. -/
theorem wave_paths_eq_empty
    (M : (RegularRightBoundary.BranchingStage.web.delete
      (RegularRightBoundary.BranchingStage.web.vertexSet
        RegularRightBoundary.BranchingStage.targetFamily)).Wave) :
    M.1 = ∅ := by
  ext p
  constructor
  · intro hp
    have hpInitial : p.initial ∈
        (RegularRightBoundary.BranchingStage.web.delete
          (RegularRightBoundary.BranchingStage.web.vertexSet
            RegularRightBoundary.BranchingStage.targetFamily)).initialSet M.1 :=
      ⟨p, hp, rfl⟩
    have hpSource := M.2.2.1 hpInitial
    rw [delete_targetFamily_source_eq_empty] at hpSource
    exact hpSource.elim
  · intro hp
    exact hp.elim

/-- Hence the unused target is not roofed by the terminal frontier of any
residual wave. -/
theorem unusedTarget_not_mem_waveRoof
    (M : (RegularRightBoundary.BranchingStage.web.delete
      (RegularRightBoundary.BranchingStage.web.vertexSet
        RegularRightBoundary.BranchingStage.targetFamily)).Wave) :
    c ∉ (RegularRightBoundary.BranchingStage.web.delete
      (RegularRightBoundary.BranchingStage.web.vertexSet
        RegularRightBoundary.BranchingStage.targetFamily)).roof
      ((RegularRightBoundary.BranchingStage.web.delete
        (RegularRightBoundary.BranchingStage.web.vertexSet
          RegularRightBoundary.BranchingStage.targetFamily)).terminalFrontier M.1) := by
  rw [wave_paths_eq_empty M]
  have hfrontier :
      (RegularRightBoundary.BranchingStage.web.delete
        (RegularRightBoundary.BranchingStage.web.vertexSet
          RegularRightBoundary.BranchingStage.targetFamily)).terminalFrontier
        (∅ : Set (RegularRightBoundary.BranchingStage.web.delete
          (RegularRightBoundary.BranchingStage.web.vertexSet
            RegularRightBoundary.BranchingStage.targetFamily)).DPath) = ∅ := by
    ext x
    simp [DWeb.terminalFrontier]
  rw [hfrontier]
  rw [(RegularRightBoundary.BranchingStage.web.delete
    (RegularRightBoundary.BranchingStage.web.vertexSet
      RegularRightBoundary.BranchingStage.targetFamily)).not_mem_roof_iff]
  have hcTarget : c ∈
      (RegularRightBoundary.BranchingStage.web.delete
        (RegularRightBoundary.BranchingStage.web.vertexSet
          RegularRightBoundary.BranchingStage.targetFamily)).target := by
    constructor
    · simp [RegularRightBoundary.BranchingStage.web]
    · rw [vertexSet_targetFamily]
      simp
  obtain ⟨p, hp⟩ := (RegularRightBoundary.BranchingStage.web.delete
      (RegularRightBoundary.BranchingStage.web.vertexSet
        RegularRightBoundary.BranchingStage.targetFamily)).target_subset_reachableToTarget
    hcTarget
  exact ⟨p, hp, Set.disjoint_empty p.support⟩

/-- The exact path-carrier boundary premise is false even though the selected
edge itself is a safely deletable source--target path. -/
theorem targetFamily_not_carrierBoundaryWaveCovered :
    ¬ CarrierBoundaryWaveCovered
      RegularRightBoundary.BranchingStage.web
      RegularRightBoundary.BranchingStage.targetFamily := by
  intro hcover
  obtain ⟨M, hc⟩ := hcover c unusedTarget_mem_outerBoundary
  exact unusedTarget_not_mem_waveRoof M hc

/-- The correct wave-dependent resurrection condition nevertheless holds.
It uses a trivial path at the deleted source rather than forcing the chosen
target edge into the resurrected ambient wave. -/
theorem targetFamily_maximalWavesResurrectAcrossDelete :
    SingularSafeDesignatedLimit.MaximalWavesResurrectAcrossDelete
      RegularRightBoundary.BranchingStage.web
      (RegularRightBoundary.BranchingStage.web.vertexSet
        RegularRightBoundary.BranchingStage.targetFamily) := by
  intro M _hMmax
  rw [SingularSafeDesignatedLimit.isWave_resurrectedWaveFamily_iff]
  intro x hxSource
  apply RegularRightBoundary.BranchingStage.web.subset_roof
  apply Or.inr
  refine ⟨hxSource, ?_⟩
  have hxu : x = u := by
    simpa [RegularRightBoundary.BranchingStage.web] using hxSource
  subst x
  rw [vertexSet_targetFamily]
  simp

/-- No static local-deletion certificate can repair the path pruning.  This
quantifies over the arbitrary deletion set introduced by
`LocalBoundaryWaveCertificate`: if it were absorbable into the chosen final
carrier and its lifted wave avoided that carrier, the general transport
lemma would produce the impossible residual roof at `c`. -/
theorem no_compatibleLocalBoundaryCertificate_of_mem_root_not_mem_unusedTarget
    {T : Set RegularRightBoundary.BranchingStage.Vertex}
    (hu : u ∈ T) (hc : c ∉ T) :
    ¬ ∃ C : SingularCollectiveSafeBatch.LocalBoundaryWaveCertificate
        RegularRightBoundary.BranchingStage.web T,
      SingularCollectiveSafeBatch.LocalBoundaryTransportCompatible
        RegularRightBoundary.BranchingStage.web
        RegularRightBoundary.BranchingStage.targetFamily C := by
  rintro ⟨C, hcompat⟩
  have hcBoundary : c ∈
      RegularRightBoundary.BranchingStage.web.outerBoundary T := by
    refine ⟨hc, u, hu, ?_⟩
    simp [RegularRightBoundary.BranchingStage.web,
      RegularRightBoundary.BranchingStage.graph]
  obtain ⟨M, hcRoof⟩ :=
    SingularCollectiveSafeBatch.exists_finalBoundaryWave_of_localCertificate
      C hcompat hcBoundary
  exact unusedTarget_not_mem_waveRoof M hcRoof

/-- The chosen path carrier is the principal instance of the preceding
one-target-subtree obstruction. -/
theorem no_compatibleLocalBoundaryCertificate_targetFamily :
    ¬ ∃ C : SingularCollectiveSafeBatch.LocalBoundaryWaveCertificate
        RegularRightBoundary.BranchingStage.web
        (RegularRightBoundary.BranchingStage.web.vertexSet
          RegularRightBoundary.BranchingStage.targetFamily),
      SingularCollectiveSafeBatch.LocalBoundaryTransportCompatible
        RegularRightBoundary.BranchingStage.web
        RegularRightBoundary.BranchingStage.targetFamily C := by
  apply no_compatibleLocalBoundaryCertificate_of_mem_root_not_mem_unusedTarget
  · rw [vertexSet_targetFamily]
    simp
  · rw [vertexSet_targetFamily]
    simp

/-- In particular the selected target edge is safe: its carrier deletion has
no surviving source.  This keeps the counterexample inside the exact
one-point safe-link setting. -/
theorem ub_isSafeTargetPath :
    RegularRightBoundary.BranchingStage.web.IsSafeTargetPath u
      RegularRightBoundary.BranchingStage.ub := by
  refine ⟨rfl, by simp [RegularRightBoundary.BranchingStage.web,
    RegularRightBoundary.BranchingStage.ub], ?_⟩
  apply SingularSafeBatch.isUnhindered_of_source_eq_empty
  ext x
  constructor
  · rintro ⟨hxSource, hxCarrier⟩
    have hxu : x = u := by
      simpa [RegularRightBoundary.BranchingStage.web] using hxSource
    subst x
    exact (hxCarrier
      RegularRightBoundary.BranchingStage.ub.start_mem_support).elim
  · intro hx
    exact hx.elim

/-! ## The retained maximal-tree producer is itself too strong -/

/-- The second target edge. -/
def uc : FinitePath RegularRightBoundary.BranchingStage.graph where
  start := u
  finish := c
  walk := .cons (by simp [RegularRightBoundary.BranchingStage.graph]) .nil
  isPath := by
    change [u, c].Nodup
    simp

/-- In the branching web the whole vertex type is an admissible safe tree:
every allowed finite deletion also deletes the unique source. -/
theorem univ_isTreeSet :
    RegularRightBoundary.BranchingStage.web.IsTreeSet u Set.univ := by
  refine ⟨Set.mem_univ u, ?_, ?_, ?_⟩
  · intro x hx
    have hxu : x = u := by
      simpa [RegularRightBoundary.BranchingStage.web] using hx.2
    exact Set.mem_singleton_iff.mpr hxu
  · intro t _ht
    rcases t with (_ | _ | _)
    · let p := FinitePath.trivial
          RegularRightBoundary.BranchingStage.graph u
      exact ⟨p, rfl, rfl, Set.subset_univ _⟩
    · exact ⟨RegularRightBoundary.BranchingStage.ub, rfl, rfl,
        Set.subset_univ _⟩
    · exact ⟨uc, rfl, rfl, Set.subset_univ _⟩
  · intro F _hF _hFsub
    apply SingularSafeBatch.isUnhindered_of_source_eq_empty
    ext x
    constructor
    · rintro ⟨hxSource, hxDeleted⟩
      have hxu : x = u := by
        simpa [RegularRightBoundary.BranchingStage.web] using hxSource
      subst x
      exact (hxDeleted (Set.mem_insert u F)).elim
    · intro hx
      exact hx.elim

/-- Every certified maximal safe tree in the branching web is the whole
three-vertex type. -/
theorem certified_tree_eq_univ
    {C : SafeLink.CertifiedSafeTargetPath
      RegularRightBoundary.BranchingStage.web u} :
    C.tree = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  exact C.tree_maximal.2 univ_isTreeSet (Set.subset_univ C.tree)

/-- A disjoint family whose initial set is a singleton has at most one
terminal-frontier vertex. -/
theorem terminalFrontier_subsingleton_of_initialSet_singleton
    {G : DWeb RegularRightBoundary.BranchingStage.Vertex}
    {P : Set G.DPath} (hwarp : G.IsWarp P)
    (hinit : G.initialSet P = {u}) :
    (G.terminalFrontier P).Subsingleton := by
  rintro x hx y hy
  obtain ⟨p, hpP, hpx⟩ := hx
  obtain ⟨q, hqP, hqy⟩ := hy
  have hpInitial : p.initial = u := by
    have : p.initial ∈ G.initialSet P := ⟨p, hpP, rfl⟩
    simpa only [hinit, Set.mem_singleton_iff] using this
  have hqInitial : q.initial = u := by
    have : q.initial ∈ G.initialSet P := ⟨q, hqP, rfl⟩
    simpa only [hinit, Set.mem_singleton_iff] using this
  have hpq : p = q := by
    by_contra hpq
    have hdisjoint := hwarp hpP hqP hpq
    exact Set.disjoint_left.1 hdisjoint
      (hpInitial.symm ▸ p.initial_mem_support)
      (hqInitial.symm ▸ q.initial_mem_support)
  subst q
  exact Option.some.inj (hpx.symm.trans hqy)

/-- Therefore the retained-tree compatibility predicate proposed as a
producer for the machine is false on the smallest branching safe-link
example, for every cardinal above one.  The maximal retained tree contains
both targets, so compatibility would force both into one singleton-rooted
linkage carrier; normalization makes both terminals, contradicting
disjointness. -/
theorem not_compatibleCertifiedTreeSelectionBelow
    {kappa : Cardinal} (hkappa : 1 < kappa) :
    ¬ SingularCollectiveSafeBatch.CompatibleCertifiedTreeSelectionBelow
      RegularRightBoundary.BranchingStage.web kappa := by
  intro hselect
  have hresidual :
      (RegularRightBoundary.BranchingStage.web.delete ∅).IsUnhindered := by
    simpa only [DWeb.delete_empty] using
      RegularRightBoundary.BranchingStage.isUnhindered
  have hsource : ({u} : Set RegularRightBoundary.BranchingStage.Vertex) ⊆
      (RegularRightBoundary.BranchingStage.web.delete ∅).source := by
    rw [DWeb.delete_empty]
    exact Set.Subset.rfl
  have hcard : Cardinal.mk
      ({u} : Set RegularRightBoundary.BranchingStage.Vertex) < kappa := by
    rw [Cardinal.mk_singleton]
    exact hkappa
  have hselection := hselect ∅ {u} hresidual hsource hcard
  rw [DWeb.delete_empty] at hselection
  obtain ⟨P, C, hP, _hcarrier, hcompat⟩ := hselection
  let i : ({u} : Set RegularRightBoundary.BranchingStage.Vertex) :=
    ⟨u, Set.mem_singleton u⟩
  let Ci : SafeLink.CertifiedSafeTargetPath
      RegularRightBoundary.BranchingStage.web u := C i
  have htree : Ci.tree = Set.univ := certified_tree_eq_univ
  have hbTree : b ∈ Ci.tree := htree.symm ▸ Set.mem_univ b
  have hcTree : c ∈ Ci.tree := htree.symm ▸ Set.mem_univ c
  have hbNonBounded : b ∈ SafeLink.nonBoundedTreeVertices
      RegularRightBoundary.BranchingStage.web u Ci.tree :=
    SingularCollectiveSafeBatch.target_mem_nonBoundedTreeVertices _ hbTree
      (by simp [RegularRightBoundary.BranchingStage.web])
  have hcNonBounded : c ∈ SafeLink.nonBoundedTreeVertices
      RegularRightBoundary.BranchingStage.web u Ci.tree :=
    SingularCollectiveSafeBatch.target_mem_nonBoundedTreeVertices _ hcTree
      (by simp [RegularRightBoundary.BranchingStage.web])
  have hcompatCi :
      SingularCollectiveSafeBatch.BoundaryTransportCompatible
        RegularRightBoundary.BranchingStage.web P Ci := by
    exact hcompat i
  have hbCarrier : b ∈
      RegularRightBoundary.BranchingStage.web.vertexSet P :=
    hcompatCi.1 (Set.mem_insert_of_mem u hbNonBounded)
  have hcCarrier : c ∈
      RegularRightBoundary.BranchingStage.web.vertexSet P :=
    hcompatCi.1 (Set.mem_insert_of_mem u hcNonBounded)
  have hbTerminal : b ∈
      RegularRightBoundary.BranchingStage.web.terminalFrontier P :=
    SingularSafeTreeResurrection.vertexSet_inter_target_subset_terminalFrontier
      RegularRightBoundary.BranchingStage.isNormalized hP
      ⟨hbCarrier, by simp [RegularRightBoundary.BranchingStage.web]⟩
  have hcTerminal : c ∈
      RegularRightBoundary.BranchingStage.web.terminalFrontier P :=
    SingularSafeTreeResurrection.vertexSet_inter_target_subset_terminalFrontier
      RegularRightBoundary.BranchingStage.isNormalized hP
      ⟨hcCarrier, by simp [RegularRightBoundary.BranchingStage.web]⟩
  have hbc : b = c :=
    terminalFrontier_subsingleton_of_initialSet_singleton
      hP.1 hP.2.2.1 hbTerminal hcTerminal
  exact RegularRightBoundary.BranchingStage.Vertex.noConfusion hbc

/-- The failure is specific to the static retained-tree producer, not to the
machine-facing safe-batch conclusion: finite safe-link iteration proves the
exact selector below `aleph0` for this same web. -/
theorem safeBatchSelectionBelow_aleph0_but_not_compatible :
    SingularSafeCompletedMachine.SafeBatchSelectionBelow
        RegularRightBoundary.BranchingStage.web Cardinal.aleph0 ∧
      ¬ SingularCollectiveSafeBatch.CompatibleCertifiedTreeSelectionBelow
        RegularRightBoundary.BranchingStage.web Cardinal.aleph0 := by
  exact ⟨SingularSafeSelectionFinite.safeBatchSelectionBelow_aleph0
      RegularRightBoundary.BranchingStage.isNormalized,
    not_compatibleCertifiedTreeSelectionBelow Cardinal.one_lt_aleph0⟩

#print axioms targetFamily_not_carrierBoundaryWaveCovered
#print axioms targetFamily_maximalWavesResurrectAcrossDelete
#print axioms no_compatibleLocalBoundaryCertificate_of_mem_root_not_mem_unusedTarget
#print axioms no_compatibleLocalBoundaryCertificate_targetFamily
#print axioms ub_isSafeTargetPath
#print axioms not_compatibleCertifiedTreeSelectionBelow
#print axioms safeBatchSelectionBelow_aleph0_but_not_compatible

end SingularSafePathBoundaryCounterexample
end CardinalInduction
end Erdos599
