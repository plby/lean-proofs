/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CountableInitialIndices
import ErdosProblems.Erdos599.PopularSwitching
import ErdosProblems.Erdos599.StationaryCountableFibers

/-!
# Stationary thinning by countable collision carriers

Assertion 8.20 assigns a geometric owner to every path in a hypothetical
stationary subfan.  Paths with one fixed owner all meet a fixed countable
carrier which avoids the common apex.  Hence the initial-index fiber of each
owner is countable.  Regularity then permits a stationary thinning on which
the owner is injective.

This file isolates that generic argument.  The geometric construction of the
owner and carrier remains separate; in particular, this theorem does not
identify the owner with an arbitrary fragment met by the path.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Popular

open DirectedPath Stationary

universe u v

/-- A stationary family of initial indices can be thinned so that its
geometric owner is injective, provided each owner has a countable carrier
away from the joined set and every index is represented by a path meeting
the carrier of its owner. -/
theorem exists_stationary_owner_transversal
    {W : Type u} {web : DWeb W} {kappa : Cardinal.{u}}
    (U : KappaIndexed web kappa) {S : Set W}
    (F : JoinedFamily web S) {X : Type v}
    {A : Set (Below kappa)} (hA : IsStationaryBelow kappa A)
    (owner : Below kappa → X) (carrier : X → Set W)
    (hcarrierCountable : ∀ x, (carrier x).Countable)
    (hcarrierDisjoint : ∀ x, Disjoint (carrier x) S)
    (hrepresented : ∀ a ∈ A,
      ∃ p, ∃ hp : p ∈ F.paths,
        U.f ⟨p.start, F.starts_in_source hp⟩ = a ∧
          ∃ z ∈ carrier (owner a), z ∈ p.support) :
    ∃ B : Set (Below kappa), B ⊆ A ∧ IsStationaryBelow kappa B ∧
      Set.InjOn owner B := by
  apply Stationary.exists_stationary_subset_injOn_of_countable_fibers
    U.regular U.uncountable hA owner
  intro x
  let Fx : JoinedFamily web S :=
    PopularSwitching.restrictPaths F
      {p | ∃ z ∈ carrier x, z ∈ p.support}
  have hFxCountable :
      (initialIndicesOf U Fx.paths Fx.starts_in_source).Countable := by
    apply PopularAuxiliary.Input.joinedFamily_initialIndices_countable_of_meets_countable
      U Fx (hcarrierCountable x) (hcarrierDisjoint x)
    intro p hp
    exact hp.2
  apply hFxCountable.mono
  rintro a ⟨ha, howner⟩
  obtain ⟨p, hp, hpa, z, hzCarrier, hzp⟩ := hrepresented a ha
  have hownerEq : owner a = x := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using howner
  have hpFx : p ∈ Fx.paths := by
    refine ⟨hp, z, ?_, hzp⟩
    simpa only [hownerEq] using hzCarrier
  refine ⟨p, hpFx, ?_⟩
  have hs :
      (⟨p.start, Fx.starts_in_source hpFx⟩ : web.source) =
        ⟨p.start, F.starts_in_source hp⟩ := Subtype.ext rfl
  exact (congrArg U.f hs).trans hpa

end Popular
end Erdos599
