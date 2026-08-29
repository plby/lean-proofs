/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProtectedRestoration
import ErdosProblems.Erdos599.SingularSelectedFreeze

/-!
# A joint safe replacement for the regular completed/pending row

A safe target path in the current deleted quotient is not, by itself, an
iterable regular successor: deletion and quotient do not commute.  The
sound successor chooses the target-reaching coordinates and the next reserve
in one protected batch.  Restoring only the current part of that batch gives
an ambient forward extension disjoint from the protected carrier, while the
unhindered quotient of the protected request web is retained as the next
residual state.

This file exposes that construction in the exact completed/pending form used
by the regular recursion.  In addition to the structural restoration theorem,
normalization proves that every selected coordinate belongs to the completed
part of the new ambient row.  No identification of the protected residual
with an ambient delete/quotient is asserted.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularJointSafeReplacement

open SingularExtension SingularPendingDecomposition SingularPendingReentry
  SingularProtectedRestoration SingularSafeBatch SingularTargetRowMachine
  SingularSelectedFreeze

universe u

variable {V : Type u}

/-! ## The genuinely iterable residual state -/

/-- A protected residual state is a web together with the exact request
coordinates still to be processed.  It intentionally has no field claiming
that the web is equal to an ambient vertex deletion followed by a quotient.
Successive protected batches change the residual web definitionally. -/
structure ProtectedResidualState (V : Type u) where
  web : DWeb V
  requests : Set V
  requests_source : requests ⊆ web.source
  unhindered : web.IsUnhindered

namespace ProtectedResidualState

/-- The residual state carried by the reserve part of a protected batch. -/
def afterBatch
    (S : ProtectedResidualState V) {reserve : Set V}
    {mu : Cardinal.{u}}
    (B : ProtectedBatch S.web S.requests reserve mu) :
    ProtectedResidualState V where
  web := (protectedRequestWeb S.web S.requests reserve).quotient B.boundary
  requests := B.reserveFrontier
  requests_source := B.reserveFrontier_subset_quotientSource
  unhindered := B.quotient_unhindered

@[simp] theorem afterBatch_web
    (S : ProtectedResidualState V) {reserve : Set V}
    {mu : Cardinal.{u}}
    (B : ProtectedBatch S.web S.requests reserve mu) :
    (S.afterBatch B).web =
      (protectedRequestWeb S.web S.requests reserve).quotient B.boundary :=
  rfl

@[simp] theorem afterBatch_requests
    (S : ProtectedResidualState V) {reserve : Set V}
    {mu : Cardinal.{u}}
    (B : ProtectedBatch S.web S.requests reserve mu) :
    (S.afterBatch B).requests = B.reserveFrontier :=
  rfl

theorem mk_afterBatch_requests
    (S : ProtectedResidualState V) {reserve : Set V}
    {mu : Cardinal.{u}}
    (B : ProtectedBatch S.web S.requests reserve mu) :
    #(S.afterBatch B).requests = #reserve :=
  B.mk_reserveFrontier_eq

end ProtectedResidualState

/-- The sound regular successor certificate.  The ambient row is contained
in `restored`; its selected coordinates are certified to lie in the completed
part.  The next residual is deliberately the protected residual carried by
`restored`, rather than an unjustified ambient delete/quotient rewrite. -/
structure JointSafeReplacement
    (G : DWeb V) (old frozen pending : Set G.DPath) (selected : Set V)
    {H : DWeb V} {current reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch H current reserve mu) where
  restored : RestoredProtectedStep G old frozen pending selected B
  cross_disjoint : Disjoint (G.vertexSet frozen)
    (G.vertexSet restored.continuedPaths)
  selected_completed :
    LinksToTarget G (completedPart G restored.paths) selected

namespace JointSafeReplacement

variable {G : DWeb V} {old frozen pending : Set G.DPath}
variable {selected : Set V} {H : DWeb V} {current reserve : Set V}
variable {mu : Cardinal.{u}} {B : ProtectedBatch H current reserve mu}

theorem result_isWarp
    (J : JointSafeReplacement G old frozen pending selected B) :
    G.IsWarp J.restored.paths :=
  J.restored.isWarp

theorem result_finiteCharacter
    (J : JointSafeReplacement G old frozen pending selected B) :
    G.HasFiniteCharacter J.restored.paths :=
  J.restored.finiteCharacter

theorem result_forward
    (J : JointSafeReplacement G old frozen pending selected B) :
    G.ForwardExtension old J.restored.paths :=
  J.restored.forward

theorem frozen_preserved
    (J : JointSafeReplacement G old frozen pending selected B) :
    frozen ⊆ J.restored.paths :=
  J.restored.frozen_preserved

theorem pending_forward
    (J : JointSafeReplacement G old frozen pending selected B) :
    G.ForwardExtension pending J.restored.continuedPaths :=
  J.restored.pendingForward

theorem result_tracks_disjoint
    (J : JointSafeReplacement G old frozen pending selected B) :
    Disjoint (G.vertexSet frozen)
      (G.vertexSet J.restored.continuedPaths) :=
  J.cross_disjoint

theorem next_residual_unhindered
    (J : JointSafeReplacement G old frozen pending selected B) :
    ((protectedRequestWeb H current reserve).quotient
      B.boundary).IsUnhindered :=
  J.restored.nextResidualUnhindered

theorem next_requests_source
    (J : JointSafeReplacement G old frozen pending selected B) :
    J.restored.nextRequests ⊆
      ((protectedRequestWeb H current reserve).quotient
        B.boundary).source :=
  J.restored.nextRequests_source

theorem next_requests_card
    (J : JointSafeReplacement G old frozen pending selected B) :
    #J.restored.nextRequests = #reserve :=
  J.restored.nextRequests_card

/-- Forget the ambient restoration layer and retain exactly the protected
state on which the next batch is chosen. -/
def nextState
    (_J : JointSafeReplacement G old frozen pending selected B) :
    ProtectedResidualState V where
  web := (protectedRequestWeb H current reserve).quotient B.boundary
  requests := B.reserveFrontier
  requests_source := B.reserveFrontier_subset_quotientSource
  unhindered := B.quotient_unhindered

@[simp] theorem nextState_web
    (J : JointSafeReplacement G old frozen pending selected B) :
    J.nextState.web =
      (protectedRequestWeb H current reserve).quotient B.boundary :=
  rfl

@[simp] theorem nextState_requests
    (J : JointSafeReplacement G old frozen pending selected B) :
    J.nextState.requests = B.reserveFrontier :=
  rfl

end JointSafeReplacement

/-- Restore a protected batch and simultaneously freeze every selected
target component.  The old frozen family is retained verbatim, the pending
family advances in the ambient web, and the reserve frontier is carried by
an unhindered protected quotient for the next iteration. -/
theorem exists_jointSafeReplacement
    {G : DWeb V} (hNorm : G.IsNormalized)
    {F W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hFsub : F ⊆ W₂) (hsub : W₁ ⊆ W₂)
    (hdecomp : F ∪ pendingPart G W₁ = W₂)
    (hfamilyDisjoint : Disjoint F (pendingPart G W₁))
    (hWwarp : G.IsWarp W₂)
    (hWfinite : G.HasFiniteCharacter W₂)
    (hsource : G.initialSet W₁ ⊆ G.source)
    {Q reserve : Set V} {mu : Cardinal.{u}}
    (hFQ : G.vertexSet F ⊆ Q)
    (hcurrent : pendingRequests G W₁ S.boundary ⊆
      ((G.delete Q).quotient S.boundary).source)
    (B : ProtectedBatch ((G.delete Q).quotient S.boundary)
      (pendingRequests G W₁ S.boundary) reserve mu) :
    Nonempty
      (JointSafeReplacement G W₂ F (pendingPart G W₁)
        (G.initialSet (pendingPart G W₁)) B) := by
  obtain ⟨R⟩ := restoreProtectedCurrent hNorm S hFsub hsub hdecomp
    hfamilyDisjoint hWwarp hWfinite hsource hFQ hcurrent B
  have hfamilyCross : Disjoint F R.continuedPaths := by
    apply Set.disjoint_left.2
    intro q hqF hqContinued
    obtain ⟨p, hpPending, hpq⟩ := R.pendingForward.2 q hqContinued
    have hqp : q ≠ p := by
      intro hqp
      subst p
      exact Set.disjoint_left.1 hfamilyDisjoint hqF hpPending
    have hdis : Disjoint q.support p.support :=
      hWwarp (hFsub hqF) (hsub hpPending.1) hqp
    have hpInitialQ : p.initial ∈ q.support :=
      G.support_mono_of_extends hpq p.initial_mem_support
    exact Set.disjoint_left.1 hdis hpInitialQ p.initial_mem_support
  have hvertexCross : Disjoint (G.vertexSet F)
      (G.vertexSet R.continuedPaths) := by
    apply Set.disjoint_left.2
    intro x hxF hxContinued
    obtain ⟨p, hpF, hxp⟩ := hxF
    obtain ⟨q, hqContinued, hxq⟩ := hxContinued
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact Set.disjoint_left.1 hfamilyCross hpF hqContinued
    have hpResult : p ∈ R.paths := by
      rw [R.paths_eq]
      exact Or.inl hpF
    have hqResult : q ∈ R.paths := by
      rw [R.paths_eq]
      exact Or.inr hqContinued
    exact Set.disjoint_left.1 (R.isWarp hpResult hqResult hpq) hxp hxq
  exact ⟨
    { restored := R
      cross_disjoint := hvertexCross
      selected_completed := linksToTarget_completedPart hNorm R.links }⟩

/-! ## Ambient restoration frames -/

/-- The ambient information which a residual batch does not contain by
itself.  A frame identifies the selected pending subrow, the family frozen
around it, and the precise deletion/quotient in which the next protected
batch is chosen. -/
structure ProtectedRestorationFrame (G : DWeb V) (row : Set G.DPath) where
  selectedRow : Set G.DPath
  frozen : Set G.DPath
  split : SplitStopover G row
  protectedSet : Set V
  frozen_subset : frozen ⊆ row
  selected_subset : selectedRow ⊆ row
  decomposition : frozen ∪ pendingPart G selectedRow = row
  family_disjoint : Disjoint frozen (pendingPart G selectedRow)
  row_warp : G.IsWarp row
  row_finite : G.HasFiniteCharacter row
  selected_source : G.initialSet selectedRow ⊆ G.source
  frozen_protected : G.vertexSet frozen ⊆ protectedSet
  residual_unhindered :
    ((G.delete protectedSet).quotient split.boundary).IsUnhindered
  requests_source : pendingRequests G selectedRow split.boundary ⊆
    ((G.delete protectedSet).quotient split.boundary).source
  /-- Every component already completed in the ambient row is on the
  literal frozen track. -/
  completed_frozen : completedPart G row ⊆ frozen

namespace ProtectedRestorationFrame

/-- Canonical frame obtained by selecting a set of source coordinates in a
full ambient row.  Every unselected component, as well as every selected
component already completed, lies on the frozen track. -/
def ofSelectedRow
    {G : DWeb V} {row : Set G.DPath} {selected Q : Set V}
    (S : SplitStopover G row)
    (hwarp : G.IsWarp row)
    (hfinite : G.HasFiniteCharacter row)
    (hinitial : G.initialSet row = G.source)
    (hselected : selected ⊆ G.source)
    (hfrozenQ : G.vertexSet (frozenComplement G row selected) ⊆ Q)
    (hresidual : ((G.delete Q).quotient S.boundary).IsUnhindered)
    (hrequests : pendingRequests G
      (SingularSelectedFreeze.selectedRow G row selected)
      S.boundary ⊆ ((G.delete Q).quotient S.boundary).source) :
    ProtectedRestorationFrame G row where
  selectedRow := SingularSelectedFreeze.selectedRow G row selected
  frozen := frozenComplement G row selected
  split := S
  protectedSet := Q
  frozen_subset := frozenComplement_subset G row selected
  selected_subset := selectedRow_subset G row selected
  decomposition := frozenComplement_union_selectedPending G row selected
  family_disjoint :=
    disjoint_frozenComplement_selectedPending G row selected
  row_warp := hwarp
  row_finite := hfinite
  selected_source := by
    rw [initialSet_selectedRow hinitial hselected]
    exact hselected
  frozen_protected := hfrozenQ
  residual_unhindered := hresidual
  requests_source := hrequests
  completed_frozen := by
    intro p hpCompleted
    refine ⟨hpCompleted.1, ?_⟩
    intro hpSelectedPending
    exact hpSelectedPending.2 ⟨hpSelectedPending.1, hpCompleted.2⟩

/-- The residual state definitionally associated with an ambient frame. -/
def state {G : DWeb V} {row : Set G.DPath}
    (F : ProtectedRestorationFrame G row) : ProtectedResidualState V where
  web := (G.delete F.protectedSet).quotient F.split.boundary
  requests := pendingRequests G F.selectedRow F.split.boundary
  requests_source := F.requests_source
  unhindered := F.residual_unhindered

/-- A protected batch can be restored from a frame without any quotient /
deletion commutation. -/
theorem extend
    {G : DWeb V} (hNorm : G.IsNormalized) {row : Set G.DPath}
    (F : ProtectedRestorationFrame G row)
    {reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch F.state.web F.state.requests reserve mu) :
    Nonempty
      (JointSafeReplacement G row F.frozen
        (pendingPart G F.selectedRow)
        (G.initialSet (pendingPart G F.selectedRow)) B) := by
  exact exists_jointSafeReplacement hNorm F.split F.frozen_subset
    F.selected_subset F.decomposition F.family_disjoint F.row_warp
    F.row_finite F.selected_source F.frozen_protected F.requests_source B

end ProtectedRestorationFrame

/-! ## Restoration towers -/

/-- An ambient restoration tower separates the honest protected residual
state from the accumulated ambient row.  `completed` is the set of source
coordinates already known to occur in completed ambient components. -/
structure ProtectedRestorationTower
    (G : DWeb V) (baseRow : Set G.DPath)
    (state : ProtectedResidualState V) (row : Set G.DPath)
    (completed : Set V) : Prop where
  row_warp : G.IsWarp row
  row_finite : G.HasFiniteCharacter row
  initialSet_eq : G.initialSet row = G.initialSet baseRow
  forward : G.ForwardExtension baseRow row
  completed_source : completed ⊆ G.source
  completed_links : LinksToTarget G (completedPart G row) completed

namespace ProtectedRestorationTower

/-- A base row with any already certified completed coordinates is the root
of a restoration tower. -/
theorem root
    {G : DWeb V} {baseRow : Set G.DPath}
    (state : ProtectedResidualState V)
    (hwarp : G.IsWarp baseRow)
    (hfinite : G.HasFiniteCharacter baseRow)
    {completed : Set V}
    (hcompletedSource : completed ⊆ G.source)
    (hcompleted : LinksToTarget G (completedPart G baseRow) completed) :
    ProtectedRestorationTower G baseRow state baseRow completed where
  row_warp := hwarp
  row_finite := hfinite
  initialSet_eq := rfl
  forward := G.forwardExtension_refl baseRow
  completed_source := hcompletedSource
  completed_links := hcompleted

/-- One framed protected batch extends a tower.  Old completed components
are on the literal frozen track, while the selected coordinates are
completed by the restored current part.  The next residual state is the
protected quotient carried by the batch. -/
theorem extend
    {G : DWeb V} (hNorm : G.IsNormalized)
    {baseRow row : Set G.DPath} {completed : Set V}
    (F : ProtectedRestorationFrame G row)
    (T : ProtectedRestorationTower G baseRow F.state row completed)
    {reserve : Set V} {mu : Cardinal.{u}}
    (B : ProtectedBatch F.state.web F.state.requests reserve mu) :
    ∃ J : JointSafeReplacement G row F.frozen
        (pendingPart G F.selectedRow)
        (G.initialSet (pendingPart G F.selectedRow)) B,
      ProtectedRestorationTower G baseRow J.nextState J.restored.paths
        (completed ∪ G.initialSet (pendingPart G F.selectedRow)) := by
  obtain ⟨J⟩ := F.extend hNorm B
  have hOld : LinksToTarget G (completedPart G J.restored.paths)
      completed := by
    intro a ha
    obtain ⟨p, hpOld, q, hpq, hpure, hsuffix⟩ :=
      T.completed_links a ha
    have hpFrozen : p ∈ F.frozen := F.completed_frozen hpOld
    have hpNew : p ∈ J.restored.paths := J.frozen_preserved hpFrozen
    exact ⟨p, ⟨hpNew, hpOld.2⟩, q, hpq, hpure, hsuffix⟩
  have hSelectedSource : G.initialSet (pendingPart G F.selectedRow) ⊆
      G.source := by
    rintro a ⟨p, hp, rfl⟩
    apply F.selected_source
    exact ⟨p, hp.1, rfl⟩
  have hAll : LinksToTarget G (completedPart G J.restored.paths)
      (completed ∪ G.initialSet (pendingPart G F.selectedRow)) := by
    exact SingularSelectedFreeze.linksToTarget_union_of_normalized hNorm
      T.completed_source hSelectedSource hOld J.selected_completed
  refine ⟨J, ?_⟩
  exact
    { row_warp := J.result_isWarp
      row_finite := J.result_finiteCharacter
      initialSet_eq := J.restored.initialSet.trans T.initialSet_eq
      forward := G.forwardExtension_trans T.forward J.result_forward
      completed_source := Set.union_subset T.completed_source hSelectedSource
      completed_links := hAll }

/-- Package a direct-limit row as a tower once the caller has proved the
two properties which are not automatic at a limit: finite character and
the desired completed-coordinate links.  This is the limit interface used
when a scheduler supplies a finite-character compression of a growing
chain; raw thread limits may contain rays and therefore do not satisfy the
finite-character field in general. -/
theorem limit
    {G : DWeb V} {baseRow row : Set G.DPath}
    (state : ProtectedResidualState V) {completed : Set V}
    (hwarp : G.IsWarp row)
    (hfinite : G.HasFiniteCharacter row)
    (hinitial : G.initialSet row = G.initialSet baseRow)
    (hforward : G.ForwardExtension baseRow row)
    (hcompletedSource : completed ⊆ G.source)
    (hcompleted : LinksToTarget G (completedPart G row) completed) :
    ProtectedRestorationTower G baseRow state row completed where
  row_warp := hwarp
  row_finite := hfinite
  initialSet_eq := hinitial
  forward := hforward
  completed_source := hcompletedSource
  completed_links := hcompleted

/-- Direct-limit specialization.  The equality of the base initial set with
the chain's `initialUnion` makes the threadwise limit a genuine two-sided
forward extension of the chosen base stage.  Finite character is retained as
an explicit premise because an unbounded thread of finite prefixes can have
a ray as its raw limit. -/
theorem limitPaths
    {I : Type u} [LinearOrder I]
    {G : DWeb V} (C : G.GrowingWarpChain I) (i₀ : I)
    (state : ProtectedResidualState V) {completed : Set V}
    (hbaseInitial : G.initialSet (C.stage i₀) = C.initialUnion)
    (hfinite : G.HasFiniteCharacter (C.limitPaths G))
    (hcompletedSource : completed ⊆ G.source)
    (hcompleted : LinksToTarget G
      (completedPart G (C.limitPaths G)) completed) :
    ProtectedRestorationTower G (C.stage i₀) state
      (C.limitPaths G) completed := by
  have hforward : G.ForwardExtension (C.stage i₀) (C.limitPaths G) := by
    constructor
    · exact C.grows_limitPaths G i₀
    · intro q hq
      have hqInitialUnion : q.initial ∈ C.initialUnion := by
        rw [← C.initialSet_limitPaths G]
        exact ⟨q, hq, rfl⟩
      have hqInitialStage : q.initial ∈ G.initialSet (C.stage i₀) :=
        hbaseInitial.symm ▸ hqInitialUnion
      obtain ⟨p, hp, hpeq⟩ := hqInitialStage
      obtain ⟨r, hr, hpr⟩ := C.grows_limitPaths G i₀ p hp
      have hrq : r = q :=
        DWeb.IsWarp.eq_of_initial_eq G (C.isWarp_limitPaths G) hr hq
          ((G.extends_initial hpr).symm.trans hpeq)
      exact ⟨p, hp, hrq ▸ hpr⟩
  apply limit state (C.isWarp_limitPaths G) hfinite
  · exact (C.initialSet_limitPaths G).trans hbaseInitial.symm
  · exact hforward
  · exact hcompletedSource
  · exact hcompleted

end ProtectedRestorationTower

end RegularJointSafeReplacement
end CardinalInduction
end Erdos599
