/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureActivatedReferencePrefixes

/-!
# Cardinality of the actual activated reference prefixes

Disjointness makes the initial-vertex map injective. Global reference
closure places those initials, and indeed the whole prefixes, in the small
closing set. No count of the full limiting reference is needed.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.activatedReferencePrefixes

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {current : LinkageBlueprint Gamma C.ladder.limitWarp kappa}
variable {X : Set V}

/-- Activated prefixes inject into the closing set by their initial
vertices, since they form a warp. -/
theorem mk_le_closedSet
    (hclosed : ClosedUnderPaths Gamma C.ladder.limitWarp X) :
    #(activatedReferencePrefixes C current X) ≤ #X := by
  let f : activatedReferencePrefixes C current X → X := fun p =>
    ⟨p.1.initial, support_subset hclosed p.2 p.1.initial_mem_support⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro p q hpq
  apply Subtype.ext
  have hinitial : p.1.initial = q.1.initial := congrArg Subtype.val hpq
  by_contra hne
  exact Set.disjoint_left.1 (isWarp p.2 q.2 hne)
    p.1.initial_mem_support (hinitial.symm ▸ q.1.initial_mem_support)

theorem mk_le_of_closedSet_bound
    (hclosed : ClosedUnderPaths Gamma C.ladder.limitWarp X)
    (hX : #X ≤ kappa) :
    #(activatedReferencePrefixes C current X) ≤ kappa :=
  (mk_le_closedSet hclosed).trans hX

/-- The actual moving closure supplies its bound and reference closure;
the prefix family needs no additional cardinality assumption. -/
theorem mk_actual_le {globalZ seed : Set V}
    (R : LimitMoving931GlobalClosure C globalZ seed)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa) :
    #(activatedReferencePrefixes C current R.closedSet) ≤ kappa :=
  mk_le_of_closedSet_bound R.reference_closed R.card_le

#print axioms mk_le_closedSet
#print axioms mk_actual_le

end Erdos599.Blueprint.LinkageBlueprint.activatedReferencePrefixes
