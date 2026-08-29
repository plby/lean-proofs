/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteFreedCarrierCorrection

/-!
# An unconditional finite roof-defect update

The marked residual exchange replaces a hindered provisional target linkage
on a finite carrier.  Wave transport across that replacement is not literal:
old carrier vertices which have become available may open new target paths.
The localization theorem shows that these are the only new paths which can
escape the old residual frontier.

This file packages the entire unconditional output.  Starting from a
hindered carrier deletion, choose a maximal residual hindrance and perform
the finite target-linkage update.  In the new deletion, the old maximal
frontier together with one explicitly finite, source-disjoint set roofs the
whole source.  Thus the remaining singular correction is a finite roof
absorption problem, rather than an unjustified wave-continuity assertion.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteRoofDefectUpdate

open DWeb
open SingularMarkedResidualTouchedPaths
open SingularMarkedResidualFiniteFactor
open SingularFiniteTargetLinkageUpdate
open SingularFiniteFreedCarrierCorrection
open SingularFiniteCarrierRoofLocalization

universe u

variable {V : Type u}

/-- Every hindered provisional target linkage admits a finite-support update
and an explicit finite roof defect.  The retained family `RP` is fixed
literally; `TP` and `Q` are the old and new moving blocks. -/
theorem exists_finiteRoofDefectUpdate_of_residual_hindered
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ M : (G.delete (G.vertexSet P)).Wave,
      IsMax M ∧ (G.delete (G.vertexSet P)).IsHindrance M.1 ∧
      ∃ l : List (OneHoleResidualState V), ∃ Q P' : Set G.DPath,
        let TP := touchedDesignatedPaths G P l
        let RP := untouchedDesignatedPaths G P l
        TP.Finite ∧ TP.Nonempty ∧ Q.Finite ∧
        (G.vertexSet (TP ∪ Q)).Finite ∧
        P = RP ∪ TP ∧ P' = RP ∪ Q ∧ RP ⊆ P' ∧
        IsLinkageBetween G A G.target P' ∧
        ∃ F : Set V,
          F = G.vertexSet P \ G.vertexSet P' ∧
          F.Finite ∧
          Disjoint (G.delete (G.vertexSet P')).source F ∧
          (G.delete (G.vertexSet P')).source ⊆
            (G.delete (G.vertexSet P')).roof
              ((G.delete (G.vertexSet P)).terminalFrontier M.1 ∪ F) := by
  obtain ⟨M, hMmax, hMh⟩ :=
    (G.delete (G.vertexSet P)).exists_maximal_hindrance hresidual
  obtain ⟨l, Q, P', hTPfinite, hTPnonempty, hQfinite,
      hlocal, hPsplit, hP'split, hRPsub, _hdisjoint, hP'⟩ :=
    exists_finiteSupportTargetLinkageUpdate_of_residual_hindered
      hNorm hG hA hP hresidual
  let TP := touchedDesignatedPaths G P l
  let RP := untouchedDesignatedPaths G P l
  let F := G.vertexSet P \ G.vertexSet P'
  have hFfinite : F.Finite := by
    apply hlocal.subset
    rintro x ⟨hxP, hxP'⟩
    rw [hPsplit, G.vertexSet_union] at hxP
    rw [G.vertexSet_union]
    rcases hxP with hxRP | hxTP
    · exfalso
      apply hxP'
      rw [hP'split, G.vertexSet_union]
      exact Or.inl hxRP
    · exact Or.inl hxTP
  have hFsource : Disjoint (G.delete (G.vertexSet P')).source F :=
    disjoint_deleteSource_freedCarrier_of_targetLinkage_update
      hNorm hA hP hP'
  have hroof :
      (G.delete (G.vertexSet P')).source ⊆
        (G.delete (G.vertexSet P')).roof
          ((G.delete (G.vertexSet P)).terminalFrontier M.1 ∪ F) :=
    source_subset_roof_frontier_union_freedCarrier
      G (G.vertexSet P) (G.vertexSet P') M.property
  refine ⟨M, hMmax, hMh, l, Q, P', hTPfinite, hTPnonempty,
    hQfinite, hlocal, hPsplit, hP'split, hRPsub, hP', F, ?_,
    hFfinite, ?_, ?_⟩
  · rfl
  · exact hFsource
  · exact hroof

#print axioms exists_finiteRoofDefectUpdate_of_residual_hindered

end SingularFiniteRoofDefectUpdate
end CardinalInduction
end Erdos599
