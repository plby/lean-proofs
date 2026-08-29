/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HindranceGrounding

/-!
# Grounded records avoid the limiting target markers

A grounded obstruction record persists as an inessential member of the
limiting ladder.  Every target marker, on the other hand, lies on an
essential member of that ladder.  Warp disjointness therefore keeps the
complete support of every grounded record disjoint from the target-marker
set.  This is the legal-ladder invariant which excludes the smallest raw
finite-source/`BB` duplicate example.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A grounded record is an inessential member of the limiting ladder. -/
theorem groundedRecord_mem_inessentialPaths_limitWarp
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {p : Gamma.DPath}
    (hp : p ∈ (L.popularAuxiliaryInput hlegal).groundedRecords) :
    p ∈ Gamma.inessentialPaths L.limitWarp := by
  obtain ⟨a, _haGround, hchosen⟩ := hp
  apply L.recorded_mem_inessential hlegal.recordedPathsPersist hchosen
  change a.1 + 1 ≤ kappa.ord
  exact (Order.add_one_le_iff).2 a.2

/-- The support of a grounded record misses every target marker of the
auxiliary web. -/
theorem groundedRecord_support_disjoint_targetMarkers
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {p : Gamma.DPath}
    (hp : p ∈ (L.popularAuxiliaryInput hlegal).groundedRecords) :
    Disjoint p.support
      (L.popularAuxiliaryInput hlegal).targetMarkers := by
  have hpInessential : p ∈ Gamma.inessentialPaths L.limitWarp :=
    L.groundedRecord_mem_inessentialPaths_limitWarp hlegal hp
  rw [Set.disjoint_left]
  intro y hyp hyTarget
  obtain ⟨q, hqEssential, hyq⟩ := hyTarget.2
  exact (Gamma.not_mem_inessentialPaths_of_intersects_essential
    (hlegal.warpStages (Ladder.finalStage kappa)) hqEssential
    ⟨y, hyp, hyq⟩) hpInessential

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.groundedRecord_mem_inessentialPaths_limitWarp
#print axioms Erdos599.DWeb.KappaLadder.groundedRecord_support_disjoint_targetMarkers
