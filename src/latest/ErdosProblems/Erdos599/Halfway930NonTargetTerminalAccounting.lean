/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930DiamondTailAdvance

/-!
# Exact non-target terminal accounting for the honest 9.30/9.31 advance

The two-diamond transaction retains every old real terminal except the
scheduled one, and its only possible new terminal is the endpoint of the
stored ambient target suffix.  Consequently the set of non-target real
terminals changes by deleting exactly the scheduled vertex.  This is the
strict progress invariant required by the varying-frontier scheduler.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClosedOldSlice930DiamondTailTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {z : V}

/-- Any `kappa`-small vertex set can be covered by a schedule indexed by
the actual successor-cardinal ladder stages. -/
theorem exists_successorStage_schedule_covering
    (S : Set V) (hS : #S ≤ kappa) (fallback : V) :
    ∃ schedule : Ladder.Stage (succ kappa) → V,
      S ⊆ Set.range schedule := by
  classical
  have hstage : #(Ladder.Stage (succ kappa)) =
      Cardinal.lift.{u + 1, u} (succ kappa) := by
    rw [Cardinal.mk_Iio_ordinal, Cardinal.card_ord]
  have hle : Cardinal.lift.{u + 1, u} #S ≤
      #(Ladder.Stage (succ kappa)) := by
    rw [hstage]
    exact Cardinal.lift_le.2 (hS.trans (le_succ kappa))
  have he : Nonempty (S ↪ Ladder.Stage (succ kappa)) :=
    Cardinal.lift_mk_le'.1 (by simpa using hle)
  let e : S ↪ Ladder.Stage (succ kappa) := he.some
  let schedule : Ladder.Stage (succ kappa) → V := fun i ↦
    if h : i ∈ Set.range e then
      (Classical.choose h).1
    else fallback
  refine ⟨schedule, ?_⟩
  intro x hx
  let a : S := ⟨x, hx⟩
  refine ⟨e a, ?_⟩
  have hrange : e a ∈ Set.range e := ⟨a, rfl⟩
  simp only [schedule, dif_pos hrange]
  have hchoose : Classical.choose hrange = a :=
    e.injective (Classical.choose_spec hrange)
  exact congrArg Subtype.val hchoose

/-- The active blueprint has at most `kappa` many non-target real
terminals.  Hence the successor-cardinal stage order is long enough to
schedule all of them; no bound on the ambient vertex type is needed. -/
theorem mk_nonTargetRealTerminals_le
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent) :
    #((W.realPart.terminals \ Gamma.target : Set V)) ≤ kappa := by
  have hsub : W.realPart.terminals \ Gamma.target ⊆ W.vertexSet := by
    intro x hx
    exact hx.1.1
  exact (Cardinal.mk_le_mk_of_subset hsub).trans
    (W.mk_vertexSet_le_of_mk_paths_le C.capacity_infinite hW.card_paths)

/-- Specializing the cardinal enumeration to an active old-stage
blueprint gives a genuine successor-stage schedule covering every current
non-target real terminal. -/
theorem exists_nonTargetRealTerminal_schedule
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent)
    (fallback : V) :
    ∃ schedule : Ladder.Stage (succ kappa) → V,
      W.realPart.terminals \ Gamma.target ⊆ Set.range schedule :=
  exists_successorStage_schedule_covering
    (W.realPart.terminals \ Gamma.target)
    (mk_nonTargetRealTerminals_le hW) fallback

/-- An honest two-diamond step deletes precisely its scheduled vertex from
the set of non-target real terminals. -/
theorem result_nonTargetRealTerminals_eq
    (Q : ClosedOldSlice930DiamondTailTransaction C W z) :
    Q.result.realPart.terminals \ Gamma.target =
      (W.realPart.terminals \ Gamma.target) \ {z} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxOldOrTarget := Q.result_realTerminals_subset_old_union_target hx.1
    have hxOld : x ∈ W.realPart.terminals := hxOldOrTarget.resolve_right hx.2
    refine ⟨⟨hxOld, hx.2⟩, ?_⟩
    intro hxz
    have hxeq : x = z := Set.mem_singleton_iff.1 hxz
    subst x
    exact not_mem_realTerminals_of_realLinksTo hx.2 Q.result_realLinksTo hx.1
  · intro x hx
    refine ⟨Q.old_realTerminals_except_subset_result ⟨hx.1.1, hx.2⟩, hx.1.2⟩

/-- In particular, scheduling a non-target terminal makes strict progress
in the terminal-exhaustion order. -/
theorem result_nonTargetRealTerminals_ssubset
    (Q : ClosedOldSlice930DiamondTailTransaction C W z)
    (hzTarget : z ∉ Gamma.target) :
    Q.result.realPart.terminals \ Gamma.target ⊂
      W.realPart.terminals \ Gamma.target := by
  rw [Q.result_nonTargetRealTerminals_eq]
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset, ?_⟩
  intro heq
  have hzOld : z ∈ W.realPart.terminals \ Gamma.target :=
    ⟨Q.scheduled_terminal, hzTarget⟩
  have hzDiff : z ∉ (W.realPart.terminals \ Gamma.target) \ {z} := by
    intro hz
    exact hz.2 (Set.mem_singleton z)
  exact hzDiff (heq.symm ▸ hzOld)

#print axioms result_nonTargetRealTerminals_eq
#print axioms result_nonTargetRealTerminals_ssubset
#print axioms mk_nonTargetRealTerminals_le
#print axioms exists_nonTargetRealTerminal_schedule

end ClosedOldSlice930DiamondTailTransaction

end LinkageBlueprint
end Blueprint
end Erdos599
