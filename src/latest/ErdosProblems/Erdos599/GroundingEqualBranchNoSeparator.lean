/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingStrongTargetNoSeparator
import ErdosProblems.Erdos599.GroundingTargetPureDichotomy

/-!
# The stationary equal branch has no popular separator

A stationary equal subwarp is itself a stationary source--target warp, hence
witnesses strong popularity of the target.  The separator-exclusion theorem
therefore applies immediately.  This small adapter records the exact reason
why Theorem 8.4 cannot simply be invoked again in the equal branch: doing so
would contradict one of the defining fields of `PopularSeparator`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Popular

open DirectedPath Stationary

universe u

variable {V : Type u}

/-- A stationary equal subwarp already makes the target strongly popular,
so no popular separator for the same indexing can exist. -/
theorem not_nonempty_popularSeparator_of_stationary_equalSubwarp
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa)
    (P : XSWarp Gamma Gamma.target)
    (hstat : IsStationaryBelow kappa
      (initialIndicesOf U (U.equalSubwarp P).paths
        (U.equalSubwarp P).starts_in_source)) :
    ¬ Nonempty (PopularSeparator U) := by
  apply not_nonempty_popularSeparator_of_stronglyPopular_target
  exact ⟨U.equalSubwarp P, hstat⟩

/-- Strict source--target descent is incompatible with even a nonempty
equal-index subwarp.  This is the exact type-level obstruction to applying
`theorem8_4_of_sourceIndexed` in the equal branch: source indexing supplies
the cardinal bound, but it cannot manufacture the missing `descends` field
of `KappaUnbalanced`. -/
theorem not_stationary_equalSubwarp_of_descends
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa)
    (P : XSWarp Gamma Gamma.target)
    (hdescends : ∀ (p : FinitePath Gamma.graph)
      (hstart : p.start ∈ Gamma.source)
      (hfinish : p.finish ∈ Gamma.target),
      U.g ⟨p.finish, hfinish⟩ < U.f ⟨p.start, hstart⟩) :
    ¬ IsStationaryBelow kappa
      (initialIndicesOf U (U.equalSubwarp P).paths
        (U.equalSubwarp P).starts_in_source) := by
  intro hstat
  obtain ⟨a, p, hp, _hpa⟩ := hstat.nonempty
  have hlt := hdescends p
    ((U.equalSubwarp P).starts_in_source hp)
    ((U.equalSubwarp P).ends_in_target hp)
  obtain ⟨_hpP, heq⟩ := hp
  exact (ne_of_lt hlt) heq

/-- A stationary equal subwarp prevents the underlying ordinal indexing
from admitting *any* `KappaUnbalanced` extension.  This is the exact input
which `theorem8_4_of_sourceIndexed` still needs in addition to source
injectivity. -/
theorem not_exists_kappaUnbalanced_extension_of_stationary_equalSubwarp
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : KappaIndexed Gamma kappa)
    (P : XSWarp Gamma Gamma.target)
    (hstat : IsStationaryBelow kappa
      (initialIndicesOf U (U.equalSubwarp P).paths
        (U.equalSubwarp P).starts_in_source)) :
    ¬ ∃ X : KappaUnbalanced Gamma kappa, X.toKappaIndexed = U := by
  rintro ⟨X, rfl⟩
  exact not_stationary_equalSubwarp_of_descends
    X.toKappaIndexed P X.descends hstat

end Popular

namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Concrete ladder specialization: the exact equal-branch callback in the
grounding theorem cannot be replaced by another separator callback. -/
theorem not_nonempty_popularAuxiliarySeparator_of_stationary_equalSubwarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    ¬ Nonempty
      (Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :=
  Popular.not_nonempty_popularSeparator_of_stationary_equalSubwarp
    (L.popularAuxiliaryIndexed hL) P hstat

/-- Concrete type-level obstruction: the source-indexed auxiliary package
cannot be promoted to the strict package required by Theorem 8.4 on the
stationary equal branch. -/
theorem not_exists_popularAuxiliaryUnbalanced_of_stationary_equalSubwarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    ¬ ∃ U : Popular.KappaUnbalanced
        (L.popularAuxiliaryInput hL.legal).lambda kappa,
      U.toKappaIndexed = L.popularAuxiliaryIndexed hL :=
  Popular.not_exists_kappaUnbalanced_extension_of_stationary_equalSubwarp
    (L.popularAuxiliaryIndexed hL) P hstat

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.Popular.not_nonempty_popularSeparator_of_stationary_equalSubwarp
#print axioms Erdos599.Popular.not_stationary_equalSubwarp_of_descends
#print axioms
  Erdos599.Popular.not_exists_kappaUnbalanced_extension_of_stationary_equalSubwarp
#print axioms
  Erdos599.DWeb.KappaLadder.not_nonempty_popularAuxiliarySeparator_of_stationary_equalSubwarp
#print axioms
  Erdos599.DWeb.KappaLadder.not_exists_popularAuxiliaryUnbalanced_of_stationary_equalSubwarp
