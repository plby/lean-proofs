/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLocalizedReferenceRemainder
import ErdosProblems.Erdos599.HalfwayMovingBetaLimit

/-!
# Activated source prefixes for the post-closure splice

If a limiting-reference member which used to witness source coverage meets
the new closed carrier, it can no longer remain in the reference remainder.
The source construction retains its finite selected-stage prefix instead.
Reference closure makes that whole prefix part of the closed set, while its
old disjointness from the current blueprint is inherited from the original
reference-remainder witness.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Source-starting local reference prefixes disjoint from the current
blueprint whose global limiting continuation meets the new closed set. -/
def activatedReferencePrefixes
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (X : Set V) : Set Gamma.DPath :=
  {q | q ∈ localizedReferenceRemainder C.ladder C.newStage current ∧
    (q.support ∩ X).Nonempty}

namespace activatedReferencePrefixes

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {current : LinkageBlueprint Gamma C.ladder.limitWarp kappa}
variable {X : Set V}

theorem subset_localizedReferenceRemainder :
    activatedReferencePrefixes C current X ⊆
      localizedReferenceRemainder C.ladder C.newStage current :=
  fun _ hq ↦ hq.1

theorem subset_ladderReference :
    activatedReferencePrefixes C current X ⊆
      ladderReference C.ladder C.newStage :=
  subset_localizedReferenceRemainder.trans
    (localizedReferenceRemainder_subset C.ladder C.newStage current)

theorem isWarp : Gamma.IsWarp (activatedReferencePrefixes C current X) :=
  (localizedReferenceRemainder_isWarp C.ladder C.newStage current C.legal).subset
    subset_localizedReferenceRemainder

theorem finiteCharacter :
    Gamma.HasFiniteCharacter (activatedReferencePrefixes C current X) :=
  by
    intro q hq
    exact localizedReferenceRemainder_finiteCharacter
      C.ladder C.newStage current hq.1

theorem initialSet_subset_source :
    Gamma.initialSet (activatedReferencePrefixes C current X) ⊆
      Gamma.source := by
  rintro x ⟨q, hq, rfl⟩
  exact hq.1.2.1

theorem terminalFrontier_subset_currentSlice :
    Gamma.terminalFrontier (activatedReferencePrefixes C current X) ⊆
      C.newSlice := by
  rintro x ⟨q, hq, hqx⟩
  exact localizedReferenceRemainder_terminalFrontier_subset
    C.ladder C.newStage current C.legal ⟨q, hq.1, hqx⟩

theorem disjoint_current :
    ∀ p ∈ current.paths, ∀ q ∈ activatedReferencePrefixes C current X,
      Disjoint p.support q.support := by
  intro p hp q hq
  exact localizedReferenceRemainder_disjoint
    C.ladder C.newStage current p hp q hq.1

/-- Global reference closure absorbs each activated finite prefix in full. -/
theorem support_subset
    (hclosed : ClosedUnderPaths Gamma C.ladder.limitWarp X)
    {q : Gamma.DPath} (hq : q ∈ activatedReferencePrefixes C current X) :
    q.support ⊆ X := by
  let qs : ladderReference C.ladder C.newStage :=
    ⟨q, subset_ladderReference hq⟩
  let p := ladderReference.limitExtension C.legal qs
  have hp : p ∈ C.ladder.limitWarp :=
    ladderReference.limitExtension_mem C.legal qs
  have hqp : Gamma.Extends q p :=
    ladderReference.extends_limitExtension C.legal qs
  obtain ⟨x, hxq, hxX⟩ := hq.2
  have hpX : p.support ⊆ X := hclosed p hp
    ⟨x, Gamma.support_mono_of_extends hqp hxq, hxX⟩
  exact (Gamma.support_mono_of_extends hqp).trans hpX

theorem vertexSet_subset
    (hclosed : ClosedUnderPaths Gamma C.ladder.limitWarp X) :
    Gamma.vertexSet (activatedReferencePrefixes C current X) ⊆ X := by
  rintro x ⟨q, hq, hxq⟩
  exact support_subset hclosed hq hxq

/-- A former global reference-remainder witness which meets the closed set
supplies an activated local prefix with the same source initial. -/
theorem initial_mem_of_referenceRemainder_meets
    (hclosed : ClosedUnderPaths Gamma C.ladder.limitWarp X)
    {p : Gamma.DPath} (hp : p ∈ current.referenceRemainder C.newSlice)
    {x : V} (hxInitial : p.initial = x) (hxSource : x ∈ Gamma.source)
    (hpX : (p.support ∩ X).Nonempty) :
    x ∈ Gamma.initialSet (activatedReferencePrefixes C current X) := by
  obtain ⟨t, htp, htSlice⟩ := hp.1.2
  obtain ⟨q, hqReference, _hqTerminal, hqp⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit
      C.legal hp.1.1 htSlice htp
  have hqSource : q.initial ∈ Gamma.source := by
    rw [Gamma.extends_initial hqp, hxInitial]
    exact hxSource
  have hqDisjoint : Disjoint q.support current.vertexSet := by
    apply Set.disjoint_left.2
    intro y hyq hyCurrent
    apply hp.2
    exact ⟨hp.1.1,
      ⟨y, Gamma.support_mono_of_extends hqp hyq, hyCurrent⟩⟩
  have hpSubset : p.support ⊆ X :=
    hclosed p hp.1.1 hpX
  have hqSubset : q.support ⊆ X :=
    (Gamma.support_mono_of_extends hqp).trans hpSubset
  refine ⟨q, ⟨⟨hqReference, hqSource, hqDisjoint⟩, ?_⟩, ?_⟩
  · exact ⟨q.initial, q.initial_mem_support, hqSubset q.initial_mem_support⟩
  · exact (Gamma.extends_initial hqp).trans hxInitial

end activatedReferencePrefixes

#print axioms activatedReferencePrefixes.support_subset
#print axioms activatedReferencePrefixes.initial_mem_of_referenceRemainder_meets

end Erdos599.Blueprint.LinkageBlueprint
