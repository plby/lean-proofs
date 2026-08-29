/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayRoofedFrontBlueprint

/-!
# Finite character of the roofed half-way front

The canonical inside family of a closed old-slice transaction has no ray.
Indeed, all of its edges form exactly the local macro relation, and that
relation has no directed ray by the finite-character row argument.  This
supplies the finite-character input needed when the simultaneous target-tail
attachment is used as a finite warp.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClosedOldSlice930MacroTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {z : V}

/-- The canonical roofed front contains only finite paths. -/
theorem roofedFrontBlueprint_finiteCharacter
    (Q : ClosedOldSlice930MacroTransaction C W z) :
    (imaginaryWeb Gamma C.selectedReference kappa).HasFiniteCharacter
      Q.roofedFrontBlueprint.paths := by
  intro p hp
  rcases p with p | r
  · exact ⟨p, rfl⟩
  · exfalso
    apply Q.no_directedRay
    let R : DirectedRay V := {
      vertex := r.toFun
      injective := r.injective }
    refine ⟨R, ?_⟩
    rintro e ⟨n, rfl⟩
    rw [Q.macroTransaction.macroEdge_eq_inside]
    change (r n, r (n + 1)) ∈ Q.roofedFrontBlueprint.edgeSet
    exact Set.mem_iUnion.2 ⟨Sum.inr r,
      Set.mem_iUnion.2 ⟨hp, ⟨n, rfl⟩⟩⟩

private theorem attachTargetTailsAcrossReference_finiteCharacter
    {Z : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (U : LinkageBlueprint Gamma Z kappa) {A : Set V}
    (hUroof : U.vertexSet ⊆ C.outerRoof)
    (hUterminal : U.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P)
    (hUfinite : (imaginaryWeb Gamma Z kappa).HasFiniteCharacter U.paths) :
    (imaginaryWeb Gamma Z kappa).HasFiniteCharacter
      (attachTargetTailsAcrossReference
        C U hUroof hUterminal hA hP).paths := by
  apply CardinalInduction.SliceSpliceSource.hasFiniteCharacter_star hUfinite
  exact hasFiniteCharacter_liftOriginalFamily
    (CardinalInduction.SliceSegmentCore.liftStageFamily_finiteCharacter
      C.ladder C.newStage hP.finiteCharacter)

/-- Attach simultaneous original-web target tails to the finite roofed front.
The exact initial boundary is preserved even before the separate global
source-cover argument identifies it with the ambient source. -/
theorem exists_finiteTargetResolvedRoofedFrontBlueprint
    (Q : ClosedOldSlice930MacroTransaction C W z)
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa) :
    ∃ U : LinkageBlueprint Gamma C.selectedReference kappa,
      U.initialSet = Q.roofedFrontBlueprint.initialSet ∧
        Q.roofedFrontBlueprint.vertexSet ⊆ U.vertexSet ∧
        U.terminalSet ⊆ Gamma.target ∧
        U.IsEdgeReal ∧
        (imaginaryWeb Gamma C.selectedReference kappa).HasFiniteCharacter
          U.paths := by
  obtain ⟨P, hP⟩ := C.exists_newStageTargetLinkage_of_mk_le
    hlower hext Q.roofedFrontBlueprint_terminalSet_subset_newSlice
      Q.mk_roofedFrontBlueprint_terminalSet_le
  let U := attachTargetTailsAcrossReference C Q.roofedFrontBlueprint
    Q.roofedFrontBlueprint_vertexSet_subset_outerRoof rfl
    Q.roofedFrontBlueprint_terminalSet_subset_newSlice hP
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · exact attachTargetTailsAcrossReference_initialSet C Q.roofedFrontBlueprint
      Q.roofedFrontBlueprint_vertexSet_subset_outerRoof rfl
      Q.roofedFrontBlueprint_terminalSet_subset_newSlice hP
  · exact vertexSet_subset_attachTargetTailsAcrossReference
      C Q.roofedFrontBlueprint
      Q.roofedFrontBlueprint_vertexSet_subset_outerRoof rfl
      Q.roofedFrontBlueprint_terminalSet_subset_newSlice hP
  · exact attachTargetTailsAcrossReference_terminalSet_subset_target
      C Q.roofedFrontBlueprint
      Q.roofedFrontBlueprint_vertexSet_subset_outerRoof rfl
      Q.roofedFrontBlueprint_terminalSet_subset_newSlice hP
  · exact attachTargetTailsAcrossReference_edge_real C Q.roofedFrontBlueprint
      Q.roofedFrontBlueprint_vertexSet_subset_outerRoof rfl
      Q.roofedFrontBlueprint_terminalSet_subset_newSlice hP
      Q.roofedFrontBlueprint_isEdgeReal
  · exact attachTargetTailsAcrossReference_finiteCharacter
      (Y := Y) C Q.roofedFrontBlueprint
      Q.roofedFrontBlueprint_vertexSet_subset_outerRoof rfl
      Q.roofedFrontBlueprint_terminalSet_subset_newSlice hP
      Q.roofedFrontBlueprint_finiteCharacter

/-- Once the global survivor argument proves that the roofed front's exact
initial boundary is the ambient source, the same construction is already a
fully endpoint-pure target linkage. -/
theorem exists_resolvedRoofedFrontBlueprint
    (Q : ClosedOldSlice930MacroTransaction C W z)
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (hsource : Q.roofedFrontBlueprint.initialSet = Gamma.source) :
    ∃ U : LinkageBlueprint Gamma C.selectedReference kappa,
      U.initialSet = Gamma.source ∧ U.terminalSet ⊆ Gamma.target ∧
        U.IsEdgeReal ∧
        (imaginaryWeb Gamma C.selectedReference kappa).HasFiniteCharacter
          U.paths ∧
        ∀ p ∈ U.paths,
          U.IsPathBetween Gamma.source Gamma.target p := by
  obtain ⟨U, hUinitial, _hUvertex, hUterminal, hUreal, hUfinite⟩ :=
    Q.exists_finiteTargetResolvedRoofedFrontBlueprint hlower hext
  refine ⟨U, hUinitial.trans hsource, hUterminal, hUreal, hUfinite, ?_⟩
  exact endpointPure_of_edgeReal_full U C.normalized hUreal hUfinite
    (hUinitial.trans hsource) hUterminal

end ClosedOldSlice930MacroTransaction

#print axioms
  ClosedOldSlice930MacroTransaction.roofedFrontBlueprint_finiteCharacter
#print axioms
  ClosedOldSlice930MacroTransaction.exists_finiteTargetResolvedRoofedFrontBlueprint
#print axioms
  ClosedOldSlice930MacroTransaction.exists_resolvedRoofedFrontBlueprint

end LinkageBlueprint
end Blueprint
end Erdos599
