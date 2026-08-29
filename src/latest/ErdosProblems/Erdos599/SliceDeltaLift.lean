/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate
import ErdosProblems.Erdos599.SliceRestrictedDelta
import ErdosProblems.Erdos599.SafeSwitching

/-!
# Lifting the restricted Delta linkage

The lower-cardinal extension in Assertion 9.10 is carried out in the exact
induced web `SliceRestrictedDelta.delta`.  This file forgets that induced
graph restriction.  It records explicitly that support, endpoints, linkage
geometry, and the displayed Delta carrier are unchanged by the lift.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceDeltaLift

open DirectedPath
open SliceRestrictedDelta

universe u

variable {V : Type u}

/-! ## Lifting a stage-web linkage to the ambient web -/

/-- A linkage in an essential quotient stage lifts verbatim to the ambient
web.  The stage lift preserves supports and both endpoints, so all five
linkage fields transport directly. -/
theorem IsLinkageBetween.liftStageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {alpha : Ladder.Stage kappa}
    {A B : Set V} {W : Set (L.stageWeb alpha).DPath}
    (hW : IsLinkageBetween (L.stageWeb alpha) A B W) :
    IsLinkageBetween Gamma A B
      (SliceSegmentCore.liftStageFamily L alpha W) := by
  refine ⟨SliceSegmentCore.liftStageFamily_isWarp L alpha hW.isWarp,
    SliceSegmentCore.liftStageFamily_finiteCharacter L alpha
      hW.finiteCharacter, ?_, ?_, ?_⟩
  · simpa only [SliceSegmentCore.initialSet_liftStageFamily]
      using hW.initialSet_eq
  · simpa only [SliceSegmentCore.terminalFrontier_liftStageFamily]
      using hW.terminalFrontier_subset
  · rintro _ ⟨p, hpW, rfl⟩
    obtain ⟨f, rfl, hends, hsource⟩ := hW.endpointPure p hpW
    refine ⟨SliceSegmentCore.liftStageFinitePath L alpha f,
      SliceSegmentCore.liftStagePath_finite L alpha f, ?_, ?_⟩
    · simpa only [SliceSegmentCore.liftStageFinitePath_support,
        SliceSegmentCore.liftStageFinitePath_start,
        SliceSegmentCore.liftStageFinitePath_finish] using hends
    · simpa only [SliceSegmentCore.liftStageFinitePath_support,
        SliceSegmentCore.liftStageFinitePath_start] using hsource

/-- Right-boundary tightness is likewise unchanged by the ambient stage
lift, since support and terminal are preserved literally. -/
theorem meetsOnlyAtTerminal_liftStageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {alpha : Ladder.Stage kappa}
    {B : Set V} {W : Set (L.stageWeb alpha).DPath}
    (hW : SliceSpliceSource.MeetsOnlyAtTerminal
      (L.stageWeb alpha) W B) :
    SliceSpliceSource.MeetsOnlyAtTerminal Gamma
      (SliceSegmentCore.liftStageFamily L alpha W) B := by
  rintro _ ⟨p, hpW, rfl⟩ x hx hxB
  rw [SliceSegmentCore.liftStagePath_support] at hx
  rw [SliceSegmentCore.liftStagePath_terminal]
  exact hW p hpW x hx hxB

@[simp] theorem support_liftPath
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (p : (delta Q C D T F).DPath) :
    (liftPath Q C D T F p).support = p.support := by
  exact DirectedPath.Path.support_lift
    (fun {_ _} (e : (delta Q C D T F).graph.Adj _ _) => e.1) p

@[simp] theorem initial_liftPath
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (p : (delta Q C D T F).DPath) :
    (liftPath Q C D T F p).initial = p.initial := by
  rcases p with p | p <;> rfl

@[simp] theorem terminal_liftPath
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (p : (delta Q C D T F).DPath) :
    Q.terminal? (liftPath Q C D T F p) =
      (delta Q C D T F).terminal? p := by
  rcases p with p | p <;> rfl

/-- Forget the induced-graph restriction on every member of a family. -/
def liftFamily (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (R : Set (delta Q C D T F).DPath) : Set Q.DPath :=
  Set.range fun p : R => liftPath Q C D T F p.1

theorem isPathBetween_liftPath
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {A B : Set V} {p : (delta Q C D T F).DPath}
    (hp : IsPathBetween (delta Q C D T F) A B p) :
    IsPathBetween Q A B (liftPath Q C D T F p) := by
  rcases hp with ⟨q, rfl, hends, hsource⟩
  let q' : DirectedPath.FinitePath Q.graph := q.lift
    (fun {_ _} (e : (delta Q C D T F).graph.Adj _ _) => e.1)
  refine ⟨q', rfl, ?_, ?_⟩
  · rw [show q'.support = q.support by
      exact DirectedPath.FinitePath.support_lift _ q]
    exact hends
  · rw [show q'.support = q.support by
      exact DirectedPath.FinitePath.support_lift _ q]
    exact hsource

theorem initialSet_liftFamily
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (R : Set (delta Q C D T F).DPath) :
    Q.initialSet (liftFamily Q C D T F R) =
      (delta Q C D T F).initialSet R := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, hx⟩
    exact ⟨p.1, p.2, by simpa only [initial_liftPath] using hx⟩
  · rintro ⟨p, hpR, hx⟩
    exact ⟨liftPath Q C D T F p, ⟨⟨p, hpR⟩, rfl⟩,
      by simpa only [initial_liftPath] using hx⟩

theorem terminalFrontier_liftFamily
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (R : Set (delta Q C D T F).DPath) :
    Q.terminalFrontier (liftFamily Q C D T F R) =
      (delta Q C D T F).terminalFrontier R := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, hx⟩
    exact ⟨p.1, p.2, by simpa only [terminal_liftPath] using hx⟩
  · rintro ⟨p, hpR, hx⟩
    exact ⟨liftPath Q C D T F p, ⟨⟨p, hpR⟩, rfl⟩,
      by simpa only [terminal_liftPath] using hx⟩

/-- A linkage in Delta is literally an ambient linkage after forgetting the
induced-graph edge witnesses. -/
theorem IsLinkageBetween.liftDelta
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {A B : Set V} {R : Set (delta Q C D T F).DPath}
    (hR : IsLinkageBetween (delta Q C D T F) A B R) :
    IsLinkageBetween Q A B (liftFamily Q C D T F R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    change Disjoint
      (liftPath Q C D T F p.1).support
      (liftPath Q C D T F q.1).support
    rw [support_liftPath, support_liftPath]
    apply hR.isWarp p.2 q.2
    intro hpq'
    apply hpq
    have hpq'' : p = q := Subtype.ext hpq'
    subst q
    rfl
  · rintro _ ⟨p, rfl⟩
    obtain ⟨q, hpq⟩ := hR.finiteCharacter p.2
    refine ⟨q.lift
      (fun {_ _} (e : (delta Q C D T F).graph.Adj _ _) => e.1), ?_⟩
    change liftPath Q C D T F p.1 = .inl
      (q.lift (fun {_ _} (e : (delta Q C D T F).graph.Adj _ _) => e.1))
    rw [hpq]
    rfl
  · simpa only [initialSet_liftFamily] using hR.initialSet_eq
  · simpa only [terminalFrontier_liftFamily] using
      hR.terminalFrontier_subset
  · rintro _ ⟨p, rfl⟩
    exact isPathBetween_liftPath Q C D T F (hR.endpointPure p.1 p.2)

/-- Every member of a finite-character Delta family lies in the displayed
induced carrier, provided its initial vertex does. -/
theorem member_support_subset_carrier
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {R : Set (delta Q C D T F).DPath}
    (hfinite : (delta Q C D T F).HasFiniteCharacter R)
    (hinitial : (delta Q C D T F).initialSet R ⊆
      carrier Q C T F) {p : (delta Q C D T F).DPath} (hpR : p ∈ R) :
    p.support ⊆ carrier Q C T F := by
  obtain ⟨q, hpq⟩ := hfinite hpR
  rcases p with p | p
  · change (Sum.inl p : (delta Q C D T F).DPath) = .inl q at hpq
    have hpq' : p = q := Sum.inl.inj hpq
    subst q
    intro x hx
    by_cases hxstart : x = p.start
    · subst x
      apply hinitial
      exact ⟨.inl p, hpR, rfl⟩
    · obtain ⟨y, hyx⟩ :=
        Alternating.FinitePath.exists_edge_to_of_mem_of_ne_start
          p hx hxstart
      exact (p.edgeSet_subset_adj hyx).2.2
  · simp at hpq

theorem vertexSet_liftFamily_subset_carrier
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {R : Set (delta Q C D T F).DPath}
    (hfinite : (delta Q C D T F).HasFiniteCharacter R)
    (hinitial : (delta Q C D T F).initialSet R ⊆
      carrier Q C T F) :
    Q.vertexSet (liftFamily Q C D T F R) ⊆ carrier Q C T F := by
  rintro x ⟨_, ⟨p, rfl⟩, hx⟩
  exact member_support_subset_carrier Q C D T F hfinite hinitial p.2
    (by simpa only [support_liftPath] using hx)

/-! ## The normalized restricted web

The actual regular-cardinal construction uses `normalizedDelta`: unlike the
raw induced web, it automatically has no edges entering its intermediate
source or leaving its target.  The normalization only deletes edges, so the
same literal lift to `Q` preserves every path datum. -/

/-- Forget both the induced-graph restriction and the source/target edge
normalization on one path. -/
def liftNormalizedPath (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (p : (normalizedDelta Q C D T F).DPath) : Q.DPath :=
  p.lift fun {_ _} (e : (normalizedDelta Q C D T F).graph.Adj _ _) =>
    e.1.1

@[simp] theorem support_liftNormalizedPath
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (p : (normalizedDelta Q C D T F).DPath) :
    (liftNormalizedPath Q C D T F p).support = p.support := by
  exact DirectedPath.Path.support_lift
    (fun {_ _} (e : (normalizedDelta Q C D T F).graph.Adj _ _) =>
      e.1.1) p

@[simp] theorem initial_liftNormalizedPath
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (p : (normalizedDelta Q C D T F).DPath) :
    (liftNormalizedPath Q C D T F p).initial = p.initial := by
  rcases p with p | p <;> rfl

@[simp] theorem terminal_liftNormalizedPath
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (p : (normalizedDelta Q C D T F).DPath) :
    Q.terminal? (liftNormalizedPath Q C D T F p) =
      (normalizedDelta Q C D T F).terminal? p := by
  rcases p with p | p <;> rfl

/-- Forget the normalized induced graph on every member of a family. -/
def liftNormalizedFamily (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (R : Set (normalizedDelta Q C D T F).DPath) : Set Q.DPath :=
  Set.range fun p : R => liftNormalizedPath Q C D T F p.1

theorem isPathBetween_liftNormalizedPath
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {A B : Set V} {p : (normalizedDelta Q C D T F).DPath}
    (hp : IsPathBetween (normalizedDelta Q C D T F) A B p) :
    IsPathBetween Q A B (liftNormalizedPath Q C D T F p) := by
  rcases hp with ⟨q, rfl, hends, hsource⟩
  let q' : DirectedPath.FinitePath Q.graph := q.lift
    (fun {_ _} (e : (normalizedDelta Q C D T F).graph.Adj _ _) =>
      e.1.1)
  refine ⟨q', rfl, ?_, ?_⟩
  · rw [show q'.support = q.support by
      exact DirectedPath.FinitePath.support_lift _ q]
    exact hends
  · rw [show q'.support = q.support by
      exact DirectedPath.FinitePath.support_lift _ q]
    exact hsource

theorem initialSet_liftNormalizedFamily
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (R : Set (normalizedDelta Q C D T F).DPath) :
    Q.initialSet (liftNormalizedFamily Q C D T F R) =
      (normalizedDelta Q C D T F).initialSet R := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, hx⟩
    exact ⟨p.1, p.2,
      by simpa only [initial_liftNormalizedPath] using hx⟩
  · rintro ⟨p, hpR, hx⟩
    exact ⟨liftNormalizedPath Q C D T F p, ⟨⟨p, hpR⟩, rfl⟩,
      by simpa only [initial_liftNormalizedPath] using hx⟩

theorem terminalFrontier_liftNormalizedFamily
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (R : Set (normalizedDelta Q C D T F).DPath) :
    Q.terminalFrontier (liftNormalizedFamily Q C D T F R) =
      (normalizedDelta Q C D T F).terminalFrontier R := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, hx⟩
    exact ⟨p.1, p.2,
      by simpa only [terminal_liftNormalizedPath] using hx⟩
  · rintro ⟨p, hpR, hx⟩
    exact ⟨liftNormalizedPath Q C D T F p, ⟨⟨p, hpR⟩, rfl⟩,
      by simpa only [terminal_liftNormalizedPath] using hx⟩

/-- Lifting out of normalized `Delta` preserves right-boundary tightness.
In fact no linkage hypothesis is needed: normalization ensures that every
path which visits the derived target `T` terminates at that visit, and the
literal lift preserves both support and terminal. -/
theorem meetsOnlyAtTerminal_liftNormalizedFamily
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    (R : Set (normalizedDelta Q C D T F).DPath) :
    SliceSpliceSource.MeetsOnlyAtTerminal Q
      (liftNormalizedFamily Q C D T F R) T := by
  rintro _ ⟨p, rfl⟩ x hx hxT
  rw [support_liftNormalizedPath] at hx
  rw [terminal_liftNormalizedPath]
  have hxTarget : x ∈ (normalizedDelta Q C D T F).target := by
    change x ∈ T
    exact hxT
  exact DWeb.IsNormalized.terminal?_eq_of_mem_path
    (delta Q C D T F).normalized_isNormalized p.1 hx
      hxTarget

/-- A linkage in normalized Delta is an ambient linkage after forgetting
the two graph restrictions. -/
theorem IsLinkageBetween.liftNormalizedDelta
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {A B : Set V} {R : Set (normalizedDelta Q C D T F).DPath}
    (hR : IsLinkageBetween (normalizedDelta Q C D T F) A B R) :
    IsLinkageBetween Q A B (liftNormalizedFamily Q C D T F R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    change Disjoint
      (liftNormalizedPath Q C D T F p.1).support
      (liftNormalizedPath Q C D T F q.1).support
    rw [support_liftNormalizedPath, support_liftNormalizedPath]
    apply hR.isWarp p.2 q.2
    intro hpq'
    apply hpq
    have hpq'' : p = q := Subtype.ext hpq'
    subst q
    rfl
  · rintro _ ⟨p, rfl⟩
    obtain ⟨q, hpq⟩ := hR.finiteCharacter p.2
    refine ⟨q.lift
      (fun {_ _} (e : (normalizedDelta Q C D T F).graph.Adj _ _) =>
        e.1.1), ?_⟩
    change liftNormalizedPath Q C D T F p.1 = .inl
      (q.lift
        (fun {_ _} (e : (normalizedDelta Q C D T F).graph.Adj _ _) =>
          e.1.1))
    rw [hpq]
    rfl
  · simpa only [initialSet_liftNormalizedFamily] using hR.initialSet_eq
  · simpa only [terminalFrontier_liftNormalizedFamily] using
      hR.terminalFrontier_subset
  · rintro _ ⟨p, rfl⟩
    exact isPathBetween_liftNormalizedPath Q C D T F
      (hR.endpointPure p.1 p.2)

/-- A normalized-Delta path stays in the displayed induced carrier once
its initial vertex is there. -/
theorem normalized_member_support_subset_carrier
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {R : Set (normalizedDelta Q C D T F).DPath}
    (hfinite : (normalizedDelta Q C D T F).HasFiniteCharacter R)
    (hinitial : (normalizedDelta Q C D T F).initialSet R ⊆
      carrier Q C T F)
    {p : (normalizedDelta Q C D T F).DPath} (hpR : p ∈ R) :
    p.support ⊆ carrier Q C T F := by
  obtain ⟨q, hpq⟩ := hfinite hpR
  rcases p with p | p
  · change (Sum.inl p : (normalizedDelta Q C D T F).DPath) =
      .inl q at hpq
    have hpq' : p = q := Sum.inl.inj hpq
    subst q
    intro x hx
    by_cases hxstart : x = p.start
    · subst x
      apply hinitial
      exact ⟨.inl p, hpR, rfl⟩
    · obtain ⟨y, hyx⟩ :=
        Alternating.FinitePath.exists_edge_to_of_mem_of_ne_start
          p hx hxstart
      exact (p.edgeSet_subset_adj hyx).1.2.2
  · simp at hpq

theorem vertexSet_liftNormalizedFamily_subset_carrier
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {R : Set (normalizedDelta Q C D T F).DPath}
    (hfinite : (normalizedDelta Q C D T F).HasFiniteCharacter R)
    (hinitial : (normalizedDelta Q C D T F).initialSet R ⊆
      carrier Q C T F) :
    Q.vertexSet (liftNormalizedFamily Q C D T F R) ⊆
      carrier Q C T F := by
  rintro x ⟨_, ⟨p, rfl⟩, hx⟩
  exact normalized_member_support_subset_carrier Q C D T F hfinite
    hinitial p.2 (by simpa only [support_liftNormalizedPath] using hx)

/-! ## Retyping the old suffix linkage in normalized Delta -/

/-- Star compatibility with an old family ending on `D` says that every
new path meets `D` only at its initial vertex. -/
theorem sourcePure_of_starCompatible
    (Q : DWeb V) {D : Set V} {W F : Set Q.DPath}
    (hD : D ⊆ Q.terminalFrontier W)
    (hcompat : Q.StarCompatible W F) :
    ∀ p ∈ F, p.support ∩ D ⊆ {p.initial} := by
  intro p hpF x hx
  obtain ⟨w, hwW, hwterm⟩ := hD hx.2
  have hmeet := hcompat w hwW p hpF x
    (Q.terminal_mem_support hwterm) hx.1
  exact Set.mem_singleton_iff.2 hmeet.2.symm

/-- Every ambient edge between support vertices of a chosen suffix belongs
to the induced Delta graph. -/
theorem finiteMemberCarrierEdge
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F) (p : F) :
    ∀ {x y : V}, Q.graph.Adj x y →
      x ∈ (Q.finiteMemberPath F
        (IsLinkageBetween.finiteCharacter hF) p).support →
      y ∈ (Q.finiteMemberPath F
        (IsLinkageBetween.finiteCharacter hF) p).support →
      (delta Q C D T F).graph.Adj x y := by
  intro x y e hx hy
  refine ⟨e, ?_, ?_⟩
  · apply SliceRestrictedDelta.member_support_subset_carrier Q C T F p.2
    rw [Q.finiteMemberPath_eq F
      (IsLinkageBetween.finiteCharacter hF) p]
    exact hx
  · apply SliceRestrictedDelta.member_support_subset_carrier Q C T F p.2
    rw [Q.finiteMemberPath_eq F
      (IsLinkageBetween.finiteCharacter hF) p]
    exact hy

/-- The finite member of an ambient linkage, with all its edges retyped in
the raw induced Delta carrier. -/
def restrictedFiniteMember
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F) (p : F) :
    DirectedPath.FinitePath (delta Q C D T F).graph :=
  let q := Q.finiteMemberPath F (IsLinkageBetween.finiteCharacter hF) p
  q.restrictGraphOnSupport (finiteMemberCarrierEdge Q C D T hF p)

@[simp] theorem support_restrictedFiniteMember
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F) (p : F) :
    (restrictedFiniteMember Q C D T hF p).support = p.1.support := by
  unfold restrictedFiniteMember
  let q := Q.finiteMemberPath F (IsLinkageBetween.finiteCharacter hF) p
  calc
    (q.restrictGraphOnSupport
        (finiteMemberCarrierEdge Q C D T hF p)).support = q.support :=
      DirectedPath.FinitePath.support_restrictGraphOnSupport q
        (finiteMemberCarrierEdge Q C D T hF p)
    _ = p.1.support := (congrArg Path.support
      (Q.finiteMemberPath_eq F
        (IsLinkageBetween.finiteCharacter hF) p)).symm

@[simp] theorem start_restrictedFiniteMember
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F) (p : F) :
    (restrictedFiniteMember Q C D T hF p).start = p.1.initial := by
  rw [restrictedFiniteMember]
  change (Q.finiteMemberPath F
    (IsLinkageBetween.finiteCharacter hF) p).start = p.1.initial
  exact (congrArg Path.initial
    (Q.finiteMemberPath_eq F (IsLinkageBetween.finiteCharacter hF) p)).symm

@[simp] theorem finish_restrictedFiniteMember
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F) (p : F) :
    some (restrictedFiniteMember Q C D T hF p).finish = Q.terminal? p.1 := by
  rw [restrictedFiniteMember]
  change some (Q.finiteMemberPath F
    (IsLinkageBetween.finiteCharacter hF) p).finish =
    Q.terminal? p.1
  exact (congrArg Q.terminal?
    (Q.finiteMemberPath_eq F (IsLinkageBetween.finiteCharacter hF) p)).symm

/-- Retype one old suffix in normalized Delta without truncating it.  The
two purity hypotheses are exactly what makes every actual path edge survive
normalization. -/
def normalizedRestrictedFiniteMember
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (p : F) :
    DirectedPath.FinitePath (normalizedDelta Q C D T F).graph := by
  change DirectedPath.FinitePath (delta Q C D T F).normalized.graph
  let q := restrictedFiniteMember Q C D T hF p
  have hs : ∀ {z}, z ∈ q.walk.support.tail →
      z ∉ (delta Q C D T F).source := by
    intro z hz hzD
    have hzSupport : z ∈ p.1.support := by
      rw [← support_restrictedFiniteMember Q C D T hF p]
      exact List.mem_of_mem_tail hz
    have hzInitial : z = p.1.initial :=
      Set.mem_singleton_iff.mp (hsource p.1 p.2 ⟨hzSupport, hzD⟩)
    exact DWeb.walk_start_not_mem_tail2 q.walk q.isPath
      (by simpa only [q, start_restrictedFiniteMember] using
        (hzInitial ▸ hz))
  have ht : ∀ {z}, z ∈ q.walk.support.dropLast →
      z ∉ (delta Q C D T F).target := by
    intro z hz hzT
    have hzSupport : z ∈ p.1.support := by
      rw [← support_restrictedFiniteMember Q C D T hF p]
      exact List.mem_of_mem_dropLast hz
    have hzTerminal : Q.terminal? p.1 = some z :=
      htarget p.1 p.2 z hzSupport hzT
    have hzFinish : q.finish = z := by
      apply Option.some.inj
      exact (finish_restrictedFiniteMember Q C D T hF p).trans hzTerminal
    exact DWeb.walk_finish_not_mem_dropLast2 q.walk q.isPath
      (hzFinish ▸ hz)
  exact
    { start := q.start
      finish := q.finish
      walk := (delta Q C D T F).normalizeWalk q.walk hs ht
      isPath := by
        change ((delta Q C D T F).normalizeWalk q.walk hs ht).support.Nodup
        rw [(delta Q C D T F).support_normalizeWalk]
        exact q.isPath }

def normalizedRestrictedPath
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (p : F) : (normalizedDelta Q C D T F).DPath :=
  .inl (normalizedRestrictedFiniteMember Q C D T hF hsource htarget p)

@[simp] theorem support_normalizedRestrictedFiniteMember
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (p : F) :
    (normalizedRestrictedFiniteMember Q C D T hF hsource htarget p).support =
      p.1.support := by
  unfold normalizedRestrictedFiniteMember
  ext x
  change x ∈ ((delta Q C D T F).normalizeWalk _ _ _).support ↔
    x ∈ p.1.support
  rw [(delta Q C D T F).support_normalizeWalk]
  exact Set.ext_iff.mp (support_restrictedFiniteMember Q C D T hF p) x

@[simp] theorem start_normalizedRestrictedFiniteMember
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (p : F) :
    (normalizedRestrictedFiniteMember Q C D T hF hsource htarget p).start =
      p.1.initial := by
  exact start_restrictedFiniteMember Q C D T hF p

@[simp] theorem finish_normalizedRestrictedFiniteMember
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (p : F) :
    some
        (normalizedRestrictedFiniteMember Q C D T hF hsource htarget p).finish =
      Q.terminal? p.1 := by
  exact finish_restrictedFiniteMember Q C D T hF p

@[simp] theorem support_normalizedRestrictedPath
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (p : F) :
    (normalizedRestrictedPath Q C D T hF hsource htarget p).support =
      p.1.support := by
  exact support_normalizedRestrictedFiniteMember
    Q C D T hF hsource htarget p

@[simp] theorem initial_normalizedRestrictedPath
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (p : F) :
    (normalizedRestrictedPath Q C D T hF hsource htarget p).initial =
      p.1.initial := by
  exact start_normalizedRestrictedFiniteMember
    Q C D T hF hsource htarget p

@[simp] theorem terminal_normalizedRestrictedPath
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : SliceSpliceSource.MeetsOnlyAtTerminal Q F T)
    (p : F) :
    (normalizedDelta Q C D T F).terminal?
        (normalizedRestrictedPath Q C D T hF hsource htarget p) =
      Q.terminal? p.1 := by
  exact finish_normalizedRestrictedFiniteMember
    Q C D T hF hsource htarget p

def normalizedRestrictedFamily
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : SliceSpliceSource.MeetsOnlyAtTerminal Q F T) :
    Set (normalizedDelta Q C D T F).DPath :=
  Set.range (normalizedRestrictedPath Q C D T hF hsource htarget)

/-- An ambient, source- and target-pure suffix linkage retypes verbatim in
normalized Delta. -/
theorem normalizedRestrictedFamily_isLinkageBetween
    (Q : DWeb V) (C D T : Set V) {A : Set V} {F : Set Q.DPath}
    (hF : IsLinkageBetween Q A T F)
    (hsource : ∀ p ∈ F, p.support ∩ D ⊆ {p.initial})
    (htarget : SliceSpliceSource.MeetsOnlyAtTerminal Q F T) :
    IsLinkageBetween (normalizedDelta Q C D T F) A T
      (normalizedRestrictedFamily Q C D T hF hsource htarget) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    change Disjoint
      (normalizedRestrictedPath Q C D T hF hsource htarget p).support
      (normalizedRestrictedPath Q C D T hF hsource htarget q).support
    rw [support_normalizedRestrictedPath,
      support_normalizedRestrictedPath]
    apply hF.isWarp p.2 q.2
    intro hpq'
    apply hpq
    have hpq'' : p = q := Subtype.ext hpq'
    subst q
    rfl
  · rintro _ ⟨p, rfl⟩
    exact ⟨_, rfl⟩
  · ext x
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, hx⟩
      rw [initial_normalizedRestrictedPath] at hx
      rw [← hF.initialSet_eq]
      exact ⟨p.1, p.2, hx⟩
    · intro hx
      rw [← hF.initialSet_eq] at hx
      obtain ⟨p, hpF, hpx⟩ := hx
      exact ⟨normalizedRestrictedPath Q C D T hF hsource htarget
          ⟨p, hpF⟩,
        ⟨⟨p, hpF⟩, rfl⟩,
        by simpa only [initial_normalizedRestrictedPath] using hpx⟩
  · rintro x ⟨_, ⟨p, rfl⟩, hx⟩
    apply hF.terminalFrontier_subset
    exact ⟨p.1, p.2,
      by simpa only [terminal_normalizedRestrictedPath] using hx⟩
  · rintro _ ⟨p, rfl⟩
    rcases hF.endpointPure p.1 p.2 with ⟨q, hpq, hends, hsourceEnds⟩
    have hsupport := support_normalizedRestrictedFiniteMember
      Q C D T hF hsource htarget p
    have hstart := start_normalizedRestrictedFiniteMember
      Q C D T hF hsource htarget p
    have hfinishSome := finish_normalizedRestrictedFiniteMember
      Q C D T hF hsource htarget p
    rw [hpq] at hsupport hstart hfinishSome
    have hfinish := Option.some.inj hfinishSome
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [hsupport, hstart, hfinish]
      exact hends
    · rw [hsupport, hstart]
      exact hsourceEnds

/-! ## Compatibility of the filled Delta linkage -/

/-- Any full linkage produced in normalized Delta is compatible with the
old stopped family.  On the annular summand of the Delta carrier this
follows from old-roof containment and tightness at `C`; on the suffix
summand it follows from the whole-family exchange compatibility.  In both
cases the intersection vertex lies in `D`, so source purity of the Delta
linkage makes it the initial vertex of the continuation. -/
theorem starCompatible_liftNormalizedFamily
    (Q : DWeb V) {C D T E : Set V} {W F : Set Q.DPath}
    (hWroof : Q.vertexSet W ⊆ Q.roof C)
    (hWtight : SliceSpliceSource.MeetsOnlyAtTerminal Q W C)
    (hD : Q.terminalFrontier W ⊆ D)
    (hF : IsLinkageBetween Q (D \ E) T F)
    (hWF : Q.StarCompatible W F)
    (hDcarrier : D ⊆ carrier Q C T F)
    {R : Set (normalizedDelta Q C D T F).DPath}
    (hR : IsLinkageBetween (normalizedDelta Q C D T F) D T R) :
    Q.StarCompatible W (liftNormalizedFamily Q C D T F R) := by
  have hRcarrier : Q.vertexSet (liftNormalizedFamily Q C D T F R) ⊆
      carrier Q C T F := by
    apply vertexSet_liftNormalizedFamily_subset_carrier Q C D T F
      hR.finiteCharacter
    rw [hR.initialSet_eq]
    exact hDcarrier
  intro p hpW _ hq x hxp hxq
  obtain ⟨r, rfl⟩ := hq
  have hxr : x ∈ r.1.support := by
    simpa only [support_liftNormalizedPath] using hxq
  have initial_eq_of_mem_D (hxD : x ∈ D) : r.1.initial = x := by
    rcases hR.endpointPure r.1 r.2 with
      ⟨s, hrs, _hends, hsource⟩
    have hxsource : x ∈ s.support ∩ D := by
      have hxr' := hxr
      rw [hrs] at hxr'
      exact ⟨hxr', hxD⟩
    have hxstart : x = s.start := by
      apply Set.mem_singleton_iff.mp
      rw [← hsource]
      exact hxsource
    rw [hrs]
    exact hxstart.symm
  have hxCarrier : x ∈ carrier Q C T F := by
    apply hRcarrier
    exact ⟨liftNormalizedPath Q C D T F r.1,
      ⟨r, rfl⟩, hxq⟩
  rcases hxCarrier with hxAnnulus | hxSuffix
  · have hxEssential : x ∈ Q.essential C := by
      by_contra hxNotEssential
      exact hxAnnulus.2 ⟨hWroof ⟨p, hpW, hxp⟩, hxNotEssential⟩
    have hpterminal : Q.terminal? p = some x :=
      hWtight p hpW x hxp (Q.essential_subset C hxEssential)
    have hxD : x ∈ D := hD ⟨p, hpW, hpterminal⟩
    exact ⟨hpterminal, by
      rw [initial_liftNormalizedPath]
      exact initial_eq_of_mem_D hxD⟩
  · obtain ⟨f, hfF, hxf⟩ := hxSuffix
    have hmeet := hWF p hpW f hfF x hxp hxf
    have hfInitial : f.initial ∈ D \ E := by
      rw [← hF.initialSet_eq]
      exact ⟨f, hfF, rfl⟩
    have hxD : x ∈ D := by
      rw [← hmeet.2]
      exact hfInitial.1
    exact ⟨hmeet.1, by
      rw [initial_liftNormalizedPath]
      exact initial_eq_of_mem_D hxD⟩

/-- Normalized source-faithful form of the preceding compatibility lemma.
The separating stop-over `C` can meet the old source, so its halfway
linkage need not meet `C` only at its terminal.  No tightening hypothesis
is needed when `D` is exactly the old terminal frontier.  If an annular
intersection is the old path's initial vertex, ambient normalization makes
it the new path's initial vertex as well; it therefore lies in `D`, and
warp disjointness with the old path ending there forces the old path itself
to end there. -/
theorem starCompatible_liftNormalizedFamily_of_normalized
    (Q : DWeb V) {C D T E : Set V} {W F : Set Q.DPath}
    (hNorm : Q.IsNormalized)
    (hW : IsLinkageBetween Q Q.source C W)
    (hWroof : Q.vertexSet W ⊆ Q.roof C)
    (hD : D = Q.terminalFrontier W)
    (hF : IsLinkageBetween Q (D \ E) T F)
    (hWF : Q.StarCompatible W F)
    (hDcarrier : D ⊆ carrier Q C T F)
    {R : Set (normalizedDelta Q C D T F).DPath}
    (hR : IsLinkageBetween (normalizedDelta Q C D T F) D T R) :
    Q.StarCompatible W (liftNormalizedFamily Q C D T F R) := by
  have hRcarrier : Q.vertexSet (liftNormalizedFamily Q C D T F R) ⊆
      carrier Q C T F := by
    apply vertexSet_liftNormalizedFamily_subset_carrier Q C D T F
      hR.finiteCharacter
    rw [hR.initialSet_eq]
    exact hDcarrier
  intro p hpW _ hq x hxp hxq
  obtain ⟨r, rfl⟩ := hq
  have hxr : x ∈ r.1.support := by
    simpa only [support_liftNormalizedPath] using hxq
  have initial_eq_of_mem_D (hxD : x ∈ D) : r.1.initial = x := by
    rcases hR.endpointPure r.1 r.2 with
      ⟨s, hrs, _hends, hsource⟩
    have hxsource : x ∈ s.support ∩ D := by
      have hxr' := hxr
      rw [hrs] at hxr'
      exact ⟨hxr', hxD⟩
    have hxstart : x = s.start := by
      apply Set.mem_singleton_iff.mp
      rw [← hsource]
      exact hxsource
    rw [hrs]
    exact hxstart.symm
  have hxCarrier : x ∈ carrier Q C T F := by
    apply hRcarrier
    exact ⟨liftNormalizedPath Q C D T F r.1,
      ⟨r, rfl⟩, hxq⟩
  rcases hxCarrier with hxAnnulus | hxSuffix
  · have hxEssential : x ∈ Q.essential C := by
      by_contra hxNotEssential
      exact hxAnnulus.2 ⟨hWroof ⟨p, hpW, hxp⟩, hxNotEssential⟩
    have hxC : x ∈ C := Q.essential_subset C hxEssential
    obtain ⟨f, rfl, hends, _hsource⟩ := hW.endpointPure p hpW
    have hxEnds : x ∈ ({f.start, f.finish} : Set V) := by
      rw [← hends]
      exact ⟨hxp, Or.inr hxC⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hxEnds
    rcases hxEnds with hxStart | hxFinish
    · have hxSource : x ∈ Q.source := by
        rw [hxStart]
        rw [← hW.initialSet_eq]
        exact ⟨Sum.inl f, hpW, rfl⟩
      have hxInitialLift :
          x = (liftNormalizedPath Q C D T F r.1).initial :=
        hNorm.eq_initial_of_mem_path
          (liftNormalizedPath Q C D T F r.1) hxq hxSource
      rw [initial_liftNormalizedPath] at hxInitialLift
      have hrInitialD : r.1.initial ∈ D := by
        exact (Set.ext_iff.mp hR.initialSet_eq r.1.initial).mp
          ⟨r.1, r.2, rfl⟩
      have hxD : x ∈ D := hxInitialLift.symm ▸ hrInitialD
      have hxFrontier : x ∈ Q.terminalFrontier W := by
        rw [← hD]
        exact hxD
      obtain ⟨p', hp'W, hp'terminal⟩ := hxFrontier
      have hp'eq : p' = (Sum.inl f : Q.DPath) := by
        by_contra hp'ne
        exact Set.disjoint_left.1
          (hW.isWarp hp'W hpW hp'ne)
          (Q.terminal_mem_support hp'terminal) hxp
      have hpterminal : Q.terminal? (Sum.inl f : Q.DPath) = some x := by
        rw [← hp'eq]
        exact hp'terminal
      exact ⟨hpterminal, by
        rw [initial_liftNormalizedPath]
        exact hxInitialLift.symm⟩
    · have hpterminal : Q.terminal? (Sum.inl f : Q.DPath) = some x := by
        change some f.finish = some x
        exact congrArg some hxFinish.symm
      have hxD : x ∈ D := by
        rw [hD]
        exact ⟨Sum.inl f, hpW, hpterminal⟩
      exact ⟨hpterminal, by
        rw [initial_liftNormalizedPath]
        exact initial_eq_of_mem_D hxD⟩
  · obtain ⟨f, hfF, hxf⟩ := hxSuffix
    have hmeet := hWF p hpW f hfF x hxp hxf
    have hfInitial : f.initial ∈ D \ E := by
      rw [← hF.initialSet_eq]
      exact ⟨f, hfF, rfl⟩
    have hxD : x ∈ D := by
      rw [← hmeet.2]
      exact hfInitial.1
    exact ⟨hmeet.1, by
      rw [initial_liftNormalizedPath]
      exact initial_eq_of_mem_D hxD⟩

/-! ## The suffix half of the localized strict-roof identity -/

/-- A vertex of a suffix which lies in the old strict roof is in the new
strict roof of `C \ D` inside normalized Delta.  Indeed, a Delta target path
avoiding `C \ D` cannot visit `D` after its (non-`C`) start, hence avoids all
of `C`.  Its terminal lies outside the old strict roof; trimmedness of `C`
then puts that terminal outside the whole old roof.  Lifting the path to
`Q` contradicts old-roof membership of the initial vertex. -/
theorem suffix_strictRoof_subset_normalizedDelta_strictRoof
    (Q : DWeb V) {C D T : Set V} (F : Set Q.DPath)
    (hDC : D ⊆ C) (hCtrim : IsTrimmedSeparator Q C)
    (hTstrict : Disjoint (Q.strictRoof C) T) :
    Q.vertexSet F ∩ Q.strictRoof C ⊆
      (normalizedDelta Q C D T F).strictRoof (C \ D) := by
  intro x hx
  have hxNotC : x ∉ C := by
    intro hxC
    have hxEssential : x ∈ Q.essential C := by
      rw [hCtrim]
      exact hxC
    exact hx.2.2 hxEssential
  have hxNotD : x ∉ D := fun hxD => hxNotC (hDC hxD)
  have hxRoof : x ∈ (normalizedDelta Q C D T F).roof (C \ D) := by
    by_contra hxNotRoof
    obtain ⟨p, hpTarget, hpAvoid⟩ :=
      ((normalizedDelta Q C D T F).not_mem_roof_iff (C \ D) x).1
        hxNotRoof
    let q : DirectedPath.FinitePath Q.graph := p.lift
      (fun {_ _} (e : (normalizedDelta Q C D T F).graph.Adj _ _) =>
        e.1.1)
    have hqSupport : q.support = p.support :=
      DirectedPath.FinitePath.support_lift
        (fun {_ _} (e : (normalizedDelta Q C D T F).graph.Adj _ _) =>
          e.1.1) p
    have hqAvoidC : Disjoint q.support C := by
      apply Set.disjoint_left.2
      intro y hyq hyC
      have hyp : y ∈ p.support := by rwa [← hqSupport]
      by_cases hyD : y ∈ D
      · have hyStart : y = p.start :=
          DWeb.IsNormalized.eq_start_of_mem_walk
            (by
              change (delta Q C D T F).normalized.IsNormalized
              exact (delta Q C D T F).normalized_isNormalized)
            p.walk hyp hyD
        have hyEqX : y = x := hyStart.trans hpTarget.1
        exact False.elim (hxNotD (hyEqX ▸ hyD))
      · exact Set.disjoint_left.1 hpAvoid hyp ⟨hyC, hyD⟩
    have hpFinishNotRoof : p.finish ∉ Q.roof C := by
      intro hpRoof
      have hpNotStrict : p.finish ∉ Q.strictRoof C :=
        fun hpStrict => Set.disjoint_left.1 hTstrict hpStrict hpTarget.2
      apply hpNotStrict
      refine ⟨hpRoof, ?_⟩
      intro hpEssential
      apply Set.disjoint_left.1 hqAvoidC
      · rw [hqSupport]
        exact p.finish_mem_support
      · rw [hCtrim] at hpEssential
        exact hpEssential
    have hqFinishNotRoof : q.finish ∉ Q.roof C := by
      exact hpFinishNotRoof
    have hqDisjointRoof : Disjoint q.support (Q.roof C) :=
      Q.finitePath_support_disjoint_roof_of_finish_not_roof
        C q hqAvoidC hqFinishNotRoof
    apply Set.disjoint_left.1 hqDisjointRoof
    · exact q.start_mem_support
    · rw [show q.start = p.start by rfl, hpTarget.1]
      exact hx.2.1
  exact ⟨hxRoof, fun hxEssential =>
    hxNotC ((normalizedDelta Q C D T F).essential_subset
      (C \ D) hxEssential).1⟩

end SliceDeltaLift
end CardinalInduction
end Erdos599
