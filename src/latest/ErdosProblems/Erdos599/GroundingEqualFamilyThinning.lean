/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaAlternating

/-!
# Local thinning bounds for an auxiliary warp

For a fixed countable gadget carrier, only countably many members of a
vertex-disjoint auxiliary warp can meet it.  This is the local counting fact
available for thinning an equal subwarp.  It does not by itself produce the
global closed switch: transfinite thinning must additionally preserve the
required boundary and absorb every remaining hanging component.
-/

noncomputable section

open Set

namespace Erdos599
namespace Popular

open DirectedPath

universe u v

variable {V : Type u} {I : Type v}

/-- Members of a finite warp which meet one fixed countable vertex set form
a countable subfamily. -/
theorem XSWarp.paths_meeting_countable
    {Gamma : DWeb V} {S R : Set V}
    (P : XSWarp Gamma S) (hR : R.Countable) :
    {p | p ∈ P.paths ∧ (p.support ∩ R).Nonempty}.Countable := by
  let Q : Set (FinitePath Gamma.graph) :=
    {p | p ∈ P.paths ∧ (p.support ∩ R).Nonempty}
  change Q.Countable
  apply FamilyTools.countable_of_pairwiseDisjoint_of_meets
      (I := Q) (F := fun p : FinitePath Gamma.graph ↦ p.support)
      (S := R)
  · intro p hp q hq hpq
    exact P.disjoint hp.1 hq.1 hpq
  · exact hR
  · intro p hp
    obtain ⟨z, hzp, hzR⟩ := hp.2
    exact ⟨z, hzR, hzp⟩

/-- The corresponding set of ordinal source indices is countable.  No
injectivity of the indexing map is needed for this image bound. -/
theorem XSWarp.initialIndices_meeting_countable
    {Gamma : DWeb V} {kappa : Cardinal.{u}} {S R : Set V}
    (U : KappaIndexed Gamma kappa) (P : XSWarp Gamma S)
    (hR : R.Countable) :
    (initialIndicesOf U
      {p | p ∈ P.paths ∧ (p.support ∩ R).Nonempty}
      (fun {_p} hp ↦ P.starts_in_source hp.1)).Countable := by
  let Q : Set (FinitePath Gamma.graph) :=
    {p | p ∈ P.paths ∧ (p.support ∩ R).Nonempty}
  have hQ : Q.Countable := P.paths_meeting_countable hR
  let indexOf : Q → Stationary.Below kappa := fun p ↦
    U.f ⟨p.1.start, P.starts_in_source p.2.1⟩
  let _ : Countable Q := hQ.to_subtype
  refine (Set.countable_range indexOf).mono ?_
  rintro a ⟨p, hp, hpa⟩
  exact ⟨⟨p, hp⟩, hpa⟩

/-- Hence a fixed countable collision carrier removes a nonstationary set
of source indices below the regular uncountable indexing cardinal. -/
theorem XSWarp.initialIndices_meeting_nonstationary
    {Gamma : DWeb V} {kappa : Cardinal.{u}} {S R : Set V}
    (U : KappaIndexed Gamma kappa) (P : XSWarp Gamma S)
    (hR : R.Countable) :
    ¬ Stationary.IsStationaryBelow kappa
      (initialIndicesOf U
        {p | p ∈ P.paths ∧ (p.support ∩ R).Nonempty}
        (fun {_p} hp ↦ P.starts_in_source hp.1)) := by
  exact Stationary.not_isStationaryBelow_of_countable
    U.regular U.uncountable (P.initialIndices_meeting_countable U hR)

end Popular
end Erdos599
