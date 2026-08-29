/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularLocalizedProtectedRegistration
import ErdosProblems.Erdos599.SingularProtectedLowerSelection

/-!
# Truthful lower selection for a regular protected coordinate

For a request `U` of size below the regular cardinal, put
`rho = max #U aleph0`.  If the current stage source has size at least `rho`,
pad `U` inside that source and invoke the protected half-way clause.  If it
does not, the whole source is already smaller than the regular cardinal, so
the lower extension clause gives a full target linkage instead.  The latter
branch registers only the carrier of that linkage; it asserts no artificial
bounded-height half-way geometry.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularLocalizedProtectedSelection

open Blueprint.LinkageBlueprint.CardinalInduction
open RegularProtectedAmbientRebuild
open SingularProtectedLowerSelection

universe u

variable {V : Type u}

/-- The exact large-source/small-source dichotomy behind the visible
registration.  All lower calls retain explicit edge-subweb provenance in
the fixed ambient base. -/
theorem registrationSets_nonempty_of_lower
    {Base Q : DWeb V} {kappa : Cardinal.{u}}
    (huncountable : aleph0 < kappa)
    (hext : ExtensionBelowFor Base kappa)
    (hhalf : ProtectedHalfwayBelowFor Base kappa)
    (hQBase : ∀ {x y : V}, Q.graph.Adj x y → Base.graph.Adj x y)
    (hNorm : Q.IsNormalized) (hQ : Q.IsUnhindered)
    {U : Set V} (hU : U ⊆ Q.source) (hUcard : #U < kappa) :
    (RegularLocalizedProtectedRegistration.registrationSets
      Q U kappa).Nonempty := by
  let rho : Cardinal.{u} := max (#U) aleph0
  have hrhoKappa : rho < kappa :=
    max_lt_iff.mpr ⟨hUcard, huncountable⟩
  have hrhoInfinite : aleph0 ≤ rho := le_max_right _ _
  have hUle : #U ≤ rho := le_max_left _ _
  by_cases hlarge : rho ≤ #Q.source
  · obtain ⟨A₀, hUA₀, hA₀, hA₀card⟩ :=
      SingularExtension.exists_enlargement_of_mk_le
        hU hUle hrhoInfinite hlarge
    obtain ⟨D⟩ := hhalf rho hrhoKappa hrhoInfinite Q
      hQBase hNorm hQ A₀ hA₀ hA₀card
    obtain ⟨X, hX, hXcard⟩ := D.height
    exact ⟨X ∪ Q.vertexSet D.targetPaths, Or.inl
      ⟨rho, hrhoKappa, A₀, hUA₀, D, X, hX, hXcard, rfl⟩⟩
  · have hsourceRho : #Q.source < rho := lt_of_not_ge hlarge
    have hsourceKappa : #Q.source < kappa :=
      hsourceRho.trans hrhoKappa
    have hstep : ExtensionClauseAt Q #Q.source :=
      hext #Q.source hsourceKappa Q hQBase hQ
    obtain ⟨P, hP⟩ := linkable_of_extension_at_source_card Q hstep
    exact
      RegularLocalizedProtectedRegistration.registrationSets_nonempty_of_fullTarget
        (U := U) hsourceKappa hP

/-- Recover the concrete branch chosen by the total visible registration.
The large-source branch may use a padded designated set `A₀`, but the
original request is retained as the explicit subset `U ⊆ A₀`. -/
theorem exists_witness_with_registration_of_lower
    {Base Q : DWeb V} {kappa : Cardinal.{u}}
    (huncountable : aleph0 < kappa)
    (hext : ExtensionBelowFor Base kappa)
    (hhalf : ProtectedHalfwayBelowFor Base kappa)
    (hQBase : ∀ {x y : V}, Q.graph.Adj x y → Base.graph.Adj x y)
    (hNorm : Q.IsNormalized) (hQ : Q.IsUnhindered)
    {U : Set V} (hU : U ⊆ Q.source) (hUcard : #U < kappa) :
    RegularLocalizedProtectedRegistration.IsProtectedRegistrationWitness
        Q U kappa
          (RegularLocalizedProtectedRegistration.registration Q U kappa) ∨
      RegularLocalizedProtectedRegistration.IsFullTargetRegistrationWitness
        Q kappa
          (RegularLocalizedProtectedRegistration.registration Q U kappa) := by
  apply RegularLocalizedProtectedRegistration.exists_witness_with_registration
  exact registrationSets_nonempty_of_lower huncountable hext hhalf hQBase
    hNorm hQ hU hUcard

end RegularLocalizedProtectedSelection
end CardinalInduction
end Erdos599

