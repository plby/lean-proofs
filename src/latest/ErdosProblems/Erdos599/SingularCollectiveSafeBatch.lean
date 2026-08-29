/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkCertifiedChoice
import ErdosProblems.Erdos599.SafeLinkGroundFinal
import ErdosProblems.Erdos599.SingularSafeTreeResurrection
import ErdosProblems.Erdos599.SingularSafeCompletedMachine

/-!
# Transporting certified safe-tree boundaries to one final deletion

The boundary wave attached to a `CertifiedSafeTargetPath` lives in the
deletion of its root and all non-bounded vertices of its retained maximal
tree.  Collective resurrection, on the other hand, needs every boundary
wave in the one residual obtained after deleting the final linkage carrier.

This file records the exact transport interface between those statements.
There are two genuine conditions: the local deleted set is contained in
the final carrier and the lifted local wave avoids that carrier.  Under those
conditions the local wave restricts to a wave in the final residual and
continues to roof the same boundary.  Applying this pointwise supplies the
common-deletion premise of `safeDesignatedLinkageOfCollectiveTrees`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularCollectiveSafeBatch

open SingularSafeDesignatedLinkage
open SingularSafeTreeResurrection
open SingularSafeCompletedMachine

universe u

variable {V : Type u}

/-- Roof membership survives restriction from a smaller deletion to a
larger deletion when the witnessing family avoids the larger deleted set. -/
theorem roof_terminalFrontier_restrict_liftDeleteFamily_of_subset
    (G : DWeb V) {S R : Set V} {W : Set (G.delete S).DPath}
    (hSR : S ⊆ R)
    (havoid : Disjoint (G.vertexSet (G.liftDeleteFamily S W)) R)
    {y : V}
    (hy : y ∈ (G.delete S).roof
      ((G.delete S).terminalFrontier W)) :
    y ∈ (G.delete R).roof
      ((G.delete R).terminalFrontier
        (G.restrictDeleteFamily R (G.liftDeleteFamily S W) havoid)) := by
  intro p hp
  let q : DirectedPath.FinitePath (G.delete S).graph :=
    @DirectedPath.FinitePath.lift V (G.delete R).graph
      (G.delete S).graph (fun {_ _} e ↦
        ⟨e.1, fun huS ↦ e.2.1 (hSR huS),
          fun hvS ↦ e.2.2 (hSR hvS)⟩) p
  have hq : (G.delete S).IsTargetPathFrom y q := by
    exact ⟨hp.1, ⟨hp.2.1, fun hzS ↦ hp.2.2 (hSR hzS)⟩⟩
  obtain ⟨z, hzq, hzfrontier⟩ := hy q hq
  refine ⟨z, ?_, ?_⟩
  · have hsupport : q.support = p.support := by
      dsimp only [q]
      exact _root_.Erdos599.DirectedPath.FinitePath.support_lift _ p
    rwa [hsupport] at hzq
  · rw [G.terminalFrontier_restrictDeleteFamily,
      G.terminalFrontier_liftDeleteFamily]
    exact hzfrontier

/-- Fix one of the common local boundary waves supplied by the certified
safe tree.  The arbitrary size of the boundary is compressed into this
single witness before transport to the final deletion. -/
noncomputable def retainedBoundaryWave
    {G : DWeb V} {a : V} (C : SafeLink.CertifiedSafeTargetPath G a) :
    (G.delete
      (insert a (SafeLink.nonBoundedTreeVertices G a C.tree))).Wave :=
  Classical.choose C.exists_commonBoundaryWave

theorem outerBoundary_subset_roof_retainedBoundaryWave
    {G : DWeb V} {a : V} (C : SafeLink.CertifiedSafeTargetPath G a) :
    G.outerBoundary C.tree ⊆
      (G.delete
        (insert a (SafeLink.nonBoundedTreeVertices G a C.tree))).roof
        ((G.delete
          (insert a (SafeLink.nonBoundedTreeVertices G a C.tree))).terminalFrontier
          (retainedBoundaryWave C).1) :=
  Classical.choose_spec C.exists_commonBoundaryWave

/-- No target vertex can lie in a strict roof.  If it belongs to the
separator it is essential, while otherwise its trivial target path avoids
the separator. -/
theorem target_not_mem_strictRoof
    (G : DWeb V) {t : V} (ht : t ∈ G.target) (S : Set V) :
    t ∉ G.strictRoof S := by
  intro htStrict
  by_cases htS : t ∈ S
  · exact htStrict.2 (target_mem_essential ht htS)
  · have htRoof : t ∈ G.roof S := htStrict.1
    let p : DirectedPath.FinitePath G.graph :=
      DirectedPath.FinitePath.trivial G.graph t
    obtain ⟨x, hxp, hxS⟩ := htRoof p ⟨rfl, ht⟩
    have hxt : x = t := by simpa [p] using hxp
    exact htS (hxt ▸ hxS)

/-- Consequently every target point of a retained safe tree belongs to its
Section 6 non-bounded deletion set. -/
theorem target_mem_nonBoundedTreeVertices
    (G : DWeb V) {a t : V} {T : Set V}
    (htT : t ∈ T) (ht : t ∈ G.target) :
    t ∈ SafeLink.nonBoundedTreeVertices G a T := by
  refine ⟨htT, ?_⟩
  rintro ⟨B⟩
  exact target_not_mem_strictRoof G ht _ B.mem_strictRoof

/-! ## Transport from an arbitrary pruned local certificate -/

/-- The most general static local boundary certificate that can be moved to
the final carrier deletion by restriction.  Unlike the Section 6 retained
certificate, its deletion set is not prescribed to contain every
non-bounded vertex of a maximal tree. -/
structure LocalBoundaryWaveCertificate (G : DWeb V) (T : Set V) where
  deleted : Set V
  wave : (G.delete deleted).Wave
  boundary_roof : G.outerBoundary T ⊆
    (G.delete deleted).roof
      ((G.delete deleted).terminalFrontier wave.1)

/-- Exact compatibility of an arbitrary local boundary certificate with a
final linkage carrier.  These two clauses, rather than inclusion of the
whole non-bounded retained-tree region, are all the restriction argument
uses. -/
def LocalBoundaryTransportCompatible
    (G : DWeb V) (P : Set G.DPath) {T : Set V}
    (C : LocalBoundaryWaveCertificate G T) : Prop :=
  C.deleted ⊆ G.vertexSet P ∧
    Disjoint
      (G.vertexSet (G.liftDeleteFamily C.deleted C.wave.1))
      (G.vertexSet P)

/-- The strongest static transport lemma: any boundary wave in any smaller
deletion restricts to the final carrier deletion, provided precisely that
its deleted set is absorbed and its lifted carrier is avoided. -/
theorem exists_finalBoundaryWave_of_localCertificate
    {G : DWeb V} {P : Set G.DPath} {T : Set V}
    (C : LocalBoundaryWaveCertificate G T)
    (hcompat : LocalBoundaryTransportCompatible G P C)
    {y : V} (hy : y ∈ G.outerBoundary T) :
    ∃ U : (G.delete (G.vertexSet P)).Wave,
      y ∈ (G.delete (G.vertexSet P)).roof
        ((G.delete (G.vertexSet P)).terminalFrontier U.1) := by
  have hdeleted : C.deleted ⊆ G.vertexSet P := hcompat.1
  have havoid : Disjoint
      (G.vertexSet (G.liftDeleteFamily C.deleted C.wave.1))
      (G.vertexSet P) := hcompat.2
  let U : Set (G.delete (G.vertexSet P)).DPath :=
    G.restrictDeleteFamily (G.vertexSet P)
      (G.liftDeleteFamily C.deleted C.wave.1) havoid
  have hU : (G.delete (G.vertexSet P)).IsWave U :=
    _root_.Erdos599.SafeLinkGroundFinal.DWeb.IsWave.restrict_liftDeleteFamily_of_subset
      G C.wave.2 hdeleted havoid
  refine ⟨⟨U, hU⟩, ?_⟩
  exact roof_terminalFrontier_restrict_liftDeleteFamily_of_subset
    G hdeleted havoid (C.boundary_roof hy)

/-- Pointwise arbitrary local certificates already give the exact common
final-deletion boundary premise. -/
theorem collectiveTreeBoundaryWaveCovered_of_localCertificates
    {G : DWeb V} {P : Set G.DPath} {I : Type*} {T : I → Set V}
    (C : ∀ i, LocalBoundaryWaveCertificate G (T i))
    (hcompat : ∀ i, LocalBoundaryTransportCompatible G P (C i)) :
    CollectiveTreeBoundaryWaveCovered G P T := by
  intro i y hy
  exact exists_finalBoundaryWave_of_localCertificate (C i) (hcompat i) hy

/-- The exact compatibility needed to move one certified tree's retained
boundary wave to the final linkage deletion.  None of these fields follows
from the pointwise safe-path conclusion alone. -/
def BoundaryTransportCompatible
    (G : DWeb V) (P : Set G.DPath) {a : V}
    (C : SafeLink.CertifiedSafeTargetPath G a) : Prop :=
  let D := insert a (SafeLink.nonBoundedTreeVertices G a C.tree)
  D ⊆ G.vertexSet P ∧
    Disjoint
      (G.vertexSet (G.liftDeleteFamily D (retainedBoundaryWave C).1))
      (G.vertexSet P)

/-- A compatible certified tree supplies boundary-wave coverage in the one
final residual web. -/
theorem exists_finalBoundaryWave
    {G : DWeb V} {P : Set G.DPath} {a : V}
    (C : SafeLink.CertifiedSafeTargetPath G a)
    (hcompat : BoundaryTransportCompatible G P C)
    {y : V} (hy : y ∈ G.outerBoundary C.tree) :
    ∃ U : (G.delete (G.vertexSet P)).Wave,
      y ∈ (G.delete (G.vertexSet P)).roof
        ((G.delete (G.vertexSet P)).terminalFrontier U.1) := by
  let D := insert a (SafeLink.nonBoundedTreeVertices G a C.tree)
  let M := retainedBoundaryWave C
  have hD : D ⊆ G.vertexSet P := hcompat.1
  have havoid : Disjoint
      (G.vertexSet (G.liftDeleteFamily D M.1)) (G.vertexSet P) :=
    hcompat.2
  let U : Set (G.delete (G.vertexSet P)).DPath :=
    G.restrictDeleteFamily (G.vertexSet P)
      (G.liftDeleteFamily D M.1) havoid
  have hU : (G.delete (G.vertexSet P)).IsWave U := by
    exact _root_.Erdos599.SafeLinkGroundFinal.DWeb.IsWave.restrict_liftDeleteFamily_of_subset
      G M.2 hD havoid
  refine ⟨⟨U, hU⟩, ?_⟩
  have hyM : y ∈ (G.delete D).roof
      ((G.delete D).terminalFrontier M.1) := by
    exact outerBoundary_subset_roof_retainedBoundaryWave C hy
  exact roof_terminalFrontier_restrict_liftDeleteFamily_of_subset
    G hD havoid hyM

/-- Pointwise compatibility of retained certified trees implies the exact
common-final-deletion boundary premise used by collective resurrection. -/
theorem collectiveTreeBoundaryWaveCovered_of_compatible
    {G : DWeb V} {P : Set G.DPath} {I : Type*}
    {a : I → V} (C : ∀ i, SafeLink.CertifiedSafeTargetPath G (a i))
    (hcompat : ∀ i, BoundaryTransportCompatible G P (C i)) :
    CollectiveTreeBoundaryWaveCovered G P (fun i ↦ (C i).tree) := by
  intro i y hy
  exact exists_finalBoundaryWave (C i) (hcompat i) hy

/-- Local-deletion inclusion also discharges the apparent extra-target
problem: every target point of a retained tree is non-bounded, hence is in
the final linkage carrier; normalization then makes it the terminal point
of its unique linkage component. -/
theorem iUnion_tree_inter_target_subset_terminalFrontier_of_compatible
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {I : Type*} {a : I → V}
    (C : ∀ i, SafeLink.CertifiedSafeTargetPath G (a i))
    (hcompat : ∀ i, BoundaryTransportCompatible G P (C i)) :
    (⋃ i, (C i).tree) ∩ G.target ⊆ G.terminalFrontier P := by
  rintro t ⟨htTrees, htTarget⟩
  obtain ⟨i, htTree⟩ := Set.mem_iUnion.1 htTrees
  have htNonBounded : t ∈
      SafeLink.nonBoundedTreeVertices G (a i) (C i).tree :=
    target_mem_nonBoundedTreeVertices G htTree htTarget
  have htCarrier : t ∈ G.vertexSet P :=
    (hcompat i).1 (Set.mem_insert_of_mem (a i) htNonBounded)
  exact vertexSet_inter_target_subset_terminalFrontier hNorm hP
    ⟨htCarrier, htTarget⟩

/-- Machine-facing collective constructor after the transport obligations
and target exhaustion have been discharged.  Carrier containment is stated
separately because it belongs to the projected linkage, while compatibility
belongs to the retained boundary waves. -/
def safeDesignatedLinkageOfCompatibleCertifiedTrees
    {G : DWeb V} (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath} (hP : IsLinkageBetween G A G.target P)
    {I : Type*} {a : I → V}
    (C : ∀ i, SafeLink.CertifiedSafeTargetPath G (a i))
    (hcarrier : G.vertexSet P ⊆ ⋃ i, (C i).tree)
    (htarget : (⋃ i, (C i).tree) ∩ G.target ⊆ G.terminalFrontier P)
    (hcompat : ∀ i, BoundaryTransportCompatible G P (C i)) :
    SafeDesignatedLinkage G A :=
  safeDesignatedLinkageOfCollectiveTrees hG hA hP hcarrier htarget
    (collectiveTreeBoundaryWaveCovered_of_compatible C hcompat)

/-- Sharpened constructor: normalization and transport compatibility imply
target exhaustion, so it need not be supplied independently. -/
def safeDesignatedLinkageOfCompatibleCertifiedTrees_normalized
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath} (hP : IsLinkageBetween G A G.target P)
    {I : Type*} {a : I → V}
    (C : ∀ i, SafeLink.CertifiedSafeTargetPath G (a i))
    (hcarrier : G.vertexSet P ⊆ ⋃ i, (C i).tree)
    (hcompat : ∀ i, BoundaryTransportCompatible G P (C i)) :
    SafeDesignatedLinkage G A :=
  safeDesignatedLinkageOfCompatibleCertifiedTrees hG hA hP C hcarrier
    (iUnion_tree_inter_target_subset_terminalFrontier_of_compatible
      hNorm hP C hcompat)
    hcompat

/-- The same constructor in the exact deleted-ambient interface consumed by
the completed-row machine. -/
def safeBatchInDeletionOfCompatibleCertifiedTrees
    {G : DWeb V} {X A : Set V}
    (hresidual : (G.delete X).IsUnhindered)
    (hA : A ⊆ (G.delete X).source)
    {P : Set (G.delete X).DPath}
    (hP : IsLinkageBetween (G.delete X) A (G.delete X).target P)
    {I : Type*} {a : I → V}
    (C : ∀ i,
      SafeLink.CertifiedSafeTargetPath (G.delete X) (a i))
    (hcarrier : (G.delete X).vertexSet P ⊆ ⋃ i, (C i).tree)
    (htarget : (⋃ i, (C i).tree) ∩ (G.delete X).target ⊆
      (G.delete X).terminalFrontier P)
    (hcompat : ∀ i,
      BoundaryTransportCompatible (G.delete X) P (C i)) :
    SafeBatchInDeletion G X A :=
  SafeBatchInDeletion.ofSafeDesignated
    (safeDesignatedLinkageOfCompatibleCertifiedTrees
      hresidual hA hP C hcarrier htarget hcompat)

/-- Normalized deleted-web version with target exhaustion inferred. -/
def safeBatchInDeletionOfCompatibleCertifiedTrees_normalized
    {G : DWeb V} {X A : Set V}
    (hresidual : (G.delete X).IsUnhindered)
    (hNorm : (G.delete X).IsNormalized)
    (hA : A ⊆ (G.delete X).source)
    {P : Set (G.delete X).DPath}
    (hP : IsLinkageBetween (G.delete X) A (G.delete X).target P)
    {I : Type*} {a : I → V}
    (C : ∀ i,
      SafeLink.CertifiedSafeTargetPath (G.delete X) (a i))
    (hcarrier : (G.delete X).vertexSet P ⊆ ⋃ i, (C i).tree)
    (hcompat : ∀ i,
      BoundaryTransportCompatible (G.delete X) P (C i)) :
    SafeBatchInDeletion G X A :=
  SafeBatchInDeletion.ofSafeDesignated
    (safeDesignatedLinkageOfCompatibleCertifiedTrees_normalized
      hresidual hNorm hA hP C hcarrier hcompat)

/-- The exact collective producer still required from the lower-cardinal
induction argument.  It asks for one certified retained tree per requested
source, a disjoint projected target linkage, and the two common-deletion
transport conditions bundled by `BoundaryTransportCompatible`. -/
def CompatibleCertifiedTreeSelectionBelow
    (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (X A : Set V), (G.delete X).IsUnhindered →
    A ⊆ (G.delete X).source → #A < kappa →
    ∃ (P : Set (G.delete X).DPath)
        (C : ∀ i : A,
          SafeLink.CertifiedSafeTargetPath (G.delete X) i.1),
      IsLinkageBetween (G.delete X) A (G.delete X).target P ∧
        (G.delete X).vertexSet P ⊆ ⋃ i, (C i).tree ∧
        ∀ i, BoundaryTransportCompatible (G.delete X) P (C i)

/-- A compatible collective producer compiles directly to the exact
`SafeBatchSelectionBelow` interface of the completed-row machine. -/
theorem safeBatchSelectionBelow_of_compatibleCertifiedTrees
    {G : DWeb V} (hNorm : G.IsNormalized) {kappa : Cardinal.{u}}
    (hselect : CompatibleCertifiedTreeSelectionBelow G kappa) :
    SafeBatchSelectionBelow G kappa := by
  intro X A hresidual hA hcard
  obtain ⟨P, C, hP, hcarrier, hcompat⟩ :=
    hselect X A hresidual hA hcard
  exact ⟨safeBatchInDeletionOfCompatibleCertifiedTrees_normalized
    hresidual (SingularSafeCompletedMachine.isNormalized_delete hNorm X)
    hA hP C hcarrier hcompat⟩

#print axioms roof_terminalFrontier_restrict_liftDeleteFamily_of_subset
#print axioms exists_finalBoundaryWave_of_localCertificate
#print axioms collectiveTreeBoundaryWaveCovered_of_localCertificates
#print axioms collectiveTreeBoundaryWaveCovered_of_compatible
#print axioms iUnion_tree_inter_target_subset_terminalFrontier_of_compatible
#print axioms safeDesignatedLinkageOfCompatibleCertifiedTrees
#print axioms safeDesignatedLinkageOfCompatibleCertifiedTrees_normalized
#print axioms safeBatchInDeletionOfCompatibleCertifiedTrees
#print axioms safeBatchInDeletionOfCompatibleCertifiedTrees_normalized
#print axioms safeBatchSelectionBelow_of_compatibleCertifiedTrees

end SingularCollectiveSafeBatch
end CardinalInduction
end Erdos599
