/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySourceRootTargetLink

/-!
# The realized family of a source-rooted final blueprint

These elementary identities expose the exact original-web family protected
by the final half-way construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Realizing every member of an edge-real blueprint preserves its entire
carrier exactly. -/
@[simp] theorem vertexSet_realFamily
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal) :
    Gamma.vertexSet (U.realFamily hreal) = U.vertexSet := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, rfl⟩, hx⟩
    rw [U.support_realPath hreal] at hx
    exact ⟨p.1, p.2, hx⟩
  · rintro ⟨p, hp, hx⟩
    let ps : U.paths := ⟨p, hp⟩
    refine ⟨U.realPath hreal ps, ⟨ps, rfl⟩, ?_⟩
    rw [U.support_realPath hreal]
    exact hx

/-- Realization cannot increase the number of path members. -/
theorem mk_realFamily_le
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    (hcard : #U.paths ≤ kappa) :
    #(U.realFamily hreal) ≤ kappa :=
  Cardinal.mk_range_le.trans hcard

/-- Every realized source-rooted component starts at an original source. -/
theorem initialSet_realFamily_sourceRoot_subset_source
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal) :
    Gamma.initialSet ((sourceRootBlueprint U).realFamily
      (sourceRootBlueprint_isEdgeReal U hreal)) ⊆ Gamma.source := by
  rw [(sourceRootBlueprint U).initialSet_realFamily]
  exact sourceRootBlueprint_initialSet_subset_source U

/-- The fair target-terminal conclusion transfers literally to the
terminal frontier of the realized family. -/
theorem terminalFrontier_realFamily_sourceRoot_subset_target
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    (htarget : (sourceRootBlueprint U).realPart.terminals ⊆ Gamma.target) :
    Gamma.terminalFrontier ((sourceRootBlueprint U).realFamily
      (sourceRootBlueprint_isEdgeReal U hreal)) ⊆ Gamma.target := by
  rw [(sourceRootBlueprint U).terminalFrontier_realFamily]
  rw [← (sourceRootBlueprint U).realPart_terminals_eq_terminalSet_of_isEdgeReal
    (sourceRootBlueprint_isEdgeReal U hreal)]
  exact htarget

end LinkageBlueprint
end Blueprint
end Erdos599
