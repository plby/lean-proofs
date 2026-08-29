/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularWeakSplitCandidate

/-!
# Local geometry for the weak regular source-9.15 table

The causal table is indexed by the persistent part visible at its right
frontier.  The provider selects that frontier by the global
persistent/movable club split.  These lemmas identify the two partitions,
so no limit-roof information occurs in the table coordinate itself.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakSource915Geometry

universe u

variable {V : Type u}

/-- At a frontier which contains every globally persistent request and is
disjoint from every movable non-target request, the causal stage-local
persistent set is exactly the global persistent set. -/
theorem stagePersistent_eq_persistentPart_of_split
    {kappa : Cardinal.{u}} {G : DWeb V} {L : G.KappaLadder kappa}
    {U right : Set V}
    (hpersistent :
      RegularPersistentRequestSplit.persistentPart G L U ⊆
        right \ G.target)
    (hmovable : Disjoint
      (RegularPersistentRequestSplit.movablePart G L U \ G.target) right) :
    RegularWeakSplitCandidate.stagePersistent G right U =
      RegularPersistentRequestSplit.persistentPart G L U := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨⟨hxU, hxNotTarget⟩, hxRight⟩
    by_contra hxNotPersistent
    exact Set.disjoint_left.1 hmovable
      ⟨⟨hxU, hxNotPersistent⟩, hxNotTarget⟩ hxRight
  · intro x hx
    exact
      ⟨⟨RegularPersistentRequestSplit.persistentPart_subset_request L U hx,
          (hpersistent hx).2⟩,
        (hpersistent hx).1⟩

/-- The complementary local movable set consequently agrees with the
global movable part. -/
theorem stageMovable_eq_movablePart_of_split
    {kappa : Cardinal.{u}} {G : DWeb V} {L : G.KappaLadder kappa}
    {U right : Set V}
    (hpersistent :
      RegularPersistentRequestSplit.persistentPart G L U ⊆
        right \ G.target)
    (hmovable : Disjoint
      (RegularPersistentRequestSplit.movablePart G L U \ G.target) right) :
    RegularWeakSplitCandidate.stageMovable G right U =
      RegularPersistentRequestSplit.movablePart G L U := by
  unfold RegularWeakSplitCandidate.stageMovable
  unfold RegularPersistentRequestSplit.movablePart
  rw [stagePersistent_eq_persistentPart_of_split hpersistent hmovable]

end RegularWeakSource915Geometry
end CardinalInduction
end Erdos599
