/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosurePrefixedAttachment
import ErdosProblems.Erdos599.HalfwayPostClosureSegmentedCardinality

/-!
# Bounds for the actual prefixed post-closure carrier

The constructed carrier lies in the old carrier union the actual small
closing set. This gives its cardinal bound and captured roof without
putting any later outside corridor into the closing set. Global closed-set
membership uses the old blueprint's own closed-carrier bound explicitly.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed currentClosed : Set V}

namespace LimitMoving931GlobalClosure

private theorem mk_paths_le_carrier
    (U : LinkageBlueprint Gamma C.ladder.limitWarp kappa) :
    #U.paths ≤ #U.vertexSet := by
  let f : U.paths → U.vertexSet := fun p =>
    ⟨p.1.initial, p.1, p.2, p.1.initial_mem_support⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro p q hpq
  apply Subtype.ext
  have hinitial : p.1.initial = q.1.initial := congrArg Subtype.val hpq
  by_contra hne
  exact Set.disjoint_left.1 (U.isWarp p.2 q.2 hne)
    p.1.initial_mem_support (hinitial.symm ▸ q.1.initial_mem_support)

theorem mk_current_union_closedSet_le
    (R : LimitMoving931GlobalClosure C globalZ seed)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent) :
    #(current.vertexSet ∪ R.closedSet : Set V) ≤ kappa :=
  (Cardinal.mk_union_le current.vertexSet R.closedSet).trans
    (Cardinal.add_le_of_le C.capacity_infinite
      (current.mk_vertexSet_le_of_mk_paths_le
        C.capacity_infinite hcurrent.card_paths) R.card_le)

theorem prefixed_vertexSet_card_le
    (R : LimitMoving931GlobalClosure C globalZ seed)
    (current U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hcarrier : U.vertexSet ⊆ current.vertexSet ∪ R.closedSet) :
    #U.vertexSet ≤ kappa :=
  (Cardinal.mk_subtype_mono hcarrier).trans
    (R.mk_current_union_closedSet_le current hcurrent)

theorem prefixed_paths_card_le
    (R : LimitMoving931GlobalClosure C globalZ seed)
    (current U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hcarrier : U.vertexSet ⊆ current.vertexSet ∪ R.closedSet) :
    #U.paths ≤ kappa :=
  (mk_paths_le_carrier U).trans
    (R.prefixed_vertexSet_card_le current U hcurrent hcarrier)

theorem prefixed_vertices_roofed
    (R : LimitMoving931GlobalClosure C globalZ seed)
    (current U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hcarrier : U.vertexSet ⊆ current.vertexSet ∪ R.closedSet) :
    U.vertexSet ⊆ Gamma.roof R.capturedGeometry.newSlice := by
  intro x hx
  rcases hcarrier hx with hxOld | hxClosed
  · exact Gamma.roof_cut (C.legal.frontierChronology R.later.current_lt)
      (hcurrent.vertices_roofed hxOld)
  · exact R.later.subset_roof hxClosed

theorem prefixed_vertices_closed_union
    (R : LimitMoving931GlobalClosure C globalZ seed)
    (current U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hcarrier : U.vertexSet ⊆ current.vertexSet ∪ R.closedSet) :
    U.vertexSet ⊆ currentClosed ∪ globalZ := by
  intro x hx
  rcases hcarrier hx with hxOld | hxClosed
  · exact Or.inl (hcurrent.vertices_closed hxOld)
  · exact Or.inr (R.subset_global hxClosed)

theorem prefixed_vertices_closed
    (R : LimitMoving931GlobalClosure C globalZ seed)
    (current U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice globalZ C.persistent)
    (hcarrier : U.vertexSet ⊆ current.vertexSet ∪ R.closedSet) :
    U.vertexSet ⊆ globalZ := by
  simpa only [Set.union_self] using
    R.prefixed_vertices_closed_union current U hcurrent hcarrier

#print axioms prefixed_paths_card_le
#print axioms prefixed_vertices_roofed
#print axioms prefixed_vertices_closed

end LimitMoving931GlobalClosure
end Erdos599.Blueprint.LinkageBlueprint
