/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkBridge
import ErdosProblems.Erdos599.SafeLinkClosure

/-!
# Final assembly lemmas for the safe-link proposition

This module records the small ambient/quotient comparisons used when the
closed common-quotient wave is reduced by the non-bounded tree vertices.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- An essential point in a quotient is essential for the same set in the
ambient web.  A quotient target path witnessing non-roofing lifts verbatim. -/
theorem quotient_essential_subset_original (X S : Set V) :
    (G.quotient X).essential S ⊆ G.essential S := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  obtain ⟨p, hp, hpAvoid⟩ :=
    ((G.quotient X).not_mem_roof_iff (S \ {x}) x).1 hx.2
  let q : DirectedPath.FinitePath G.graph :=
    p.lift (fun {_ _} e ↦ G.quotient_adj_imp e)
  apply (G.not_mem_roof_iff (S \ {x}) x).2
  refine ⟨q, ⟨hp.1, hp.2⟩, ?_⟩
  apply Set.disjoint_left.2
  intro y hyq hyS
  apply Set.disjoint_left.1 hpAvoid
  · simpa only [q, DirectedPath.FinitePath.support_lift] using hyq
  · exact hyS

end DWeb

namespace SafeLink

variable {V : Type u}

/-- Paths in a quotient of the root-deleted web avoid the deleted root when
the commitment set is off the root. -/
theorem quotientWave_support_ne_root
    (G : DWeb V) {a : V} {T X : Set V} (hXT : X ⊆ T \ {a})
    {W : Set (((G.delete {a}).quotient X).DPath)}
    (hW : ((G.delete {a}).quotient X).IsWave W)
    {p : ((G.delete {a}).quotient X).DPath} (hpW : p ∈ W)
    {q : V} (hqp : q ∈ p.support) : q ≠ a := by
  let base := G.delete {a}
  let H := base.quotient X
  have hpSource : p.initial ∈ H.source := hW.2.1 ⟨p, hpW, rfl⟩
  have hpInitialNe : p.initial ≠ a := by
    intro hpa
    rcases hpSource.1 with hpBaseSource | hpX
    · exact hpBaseSource.2 (by simpa [hpa])
    · exact (hXT hpX).2 (by simpa [hpa])
  let pb : base.DPath := base.liftQuotientPath X p
  have hpbInitial : pb.initial ∉ ({a} : Set V) := by
    simpa only [Set.mem_singleton_iff, pb,
      base.initial_liftQuotientPath] using hpInitialNe
  have hAvoid := G.liftDeletePath_avoids {a} pb hpbInitial
  intro hqa
  apply Set.disjoint_left.1 hAvoid
  · simpa only [pb, G.support_liftDeletePath,
      base.support_liftQuotientPath] using hqp
  · exact hqa ▸ Set.mem_singleton a

/-- A nonterminal contact of an essential common-quotient path with a
non-bounded tree vertex must already lie on a path meeting the commitment
set.  Otherwise self-roofing would make that vertex bounded. -/
theorem nonterminal_nonBounded_contact_meets_commitment
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T X : Set V} (hT : G.IsTreeSet a T)
    (hXcount : X.Countable) (hXT : X ⊆ T \ {a})
    {W : Set (((G.delete {a}).quotient X).DPath)}
    (hW : ((G.delete {a}).quotient X).IsWave W) :
    let H := (G.delete {a}).quotient X
    ∀ p ∈ H.essentialWarpPart W, ∀ q ∈ p.support,
      q ∈ nonBoundedTreeVertices G a T → H.terminal? p ≠ some q →
        (p.support ∩ X).Nonempty := by
  let base := G.delete {a}
  let H := base.quotient X
  dsimp only
  intro p hp q hqp hqQ hpNotTerminal
  by_contra hpX
  have hNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  have hSourceX : Disjoint base.source X :=
    tree_offRoot_disjoint_delete_source G hT hXT
  have hqRoofBase : q ∈ base.roof (H.terminalFrontier W) :=
    quotientWave_vertexSet_subset_original_roof
      base hNoEnter hSourceX hW ⟨p, hp.1, hqp⟩
  have hqNotTerminal : q ∉ H.terminalFrontier W := by
    intro hqTerminal
    exact hpNotTerminal
      (DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
        H hW.1 hp.1 hqp hqTerminal)
  let L := liftDeleteQuotientFamily G a X W
  have hterminalL : G.terminalFrontier L = H.terminalFrontier W := by
    dsimp only [L, H, base, liftDeleteQuotientFamily]
    rw [G.terminalFrontier_liftDeleteFamily,
      terminalFrontier_liftQuotientFamily]
  have hqNeA : q ≠ a :=
    quotientWave_support_ne_root G hXT hW hp.1 hqp
  have hqRoofG : q ∈ G.roof (G.terminalFrontier L) := by
    rw [hterminalL]
    exact roof_delete_source_subset_ambient_of_ne
      G hG ha hqNeA hqRoofBase
  have hqStrictG : q ∈ G.strictRoof (G.terminalFrontier L) := by
    refine ⟨hqRoofG, ?_⟩
    intro hqEss
    exact hqNotTerminal (by
      rw [← hterminalL]
      exact G.essential_subset _ hqEss)
  exact not_mem_strictRoof_of_mem_nonBounded
    G a T hqQ hXcount hXT hW hqStrictG

/-- Assertion 6.4 for the actual common-quotient wave.  Essentiality is
computed in the quotient, while boundedness is defined using the roof in
the original normalized web; the proof explicitly transports both facts. -/
theorem assertion6_4_quotient
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T X : Set V} (hT : G.IsTreeSet a T)
    (hXcount : X.Countable) (hXT : X ⊆ T \ {a})
    {W : Set (((G.delete {a}).quotient X).DPath)}
    (hW : ((G.delete {a}).quotient X).IsWave W)
    (hclosed : ((G.delete {a}).quotient X).vertexSet
      (((G.delete {a}).quotient X).essentialMeetingPaths W X) ∩ T ⊆ X)
    (hground : X \ nonBoundedTreeVertices G a T ⊆
      G.strictRoof (G.terminalFrontier
        (liftDeleteQuotientFamily G a X W))) :
    let H := (G.delete {a}).quotient X
    H.terminalFrontier (H.essentialMeetingPaths W X) ∩ T ⊆
        nonBoundedTreeVertices G a T ∧
      H.vertexSet (H.essentialMeetingPaths W X) ∩
          nonBoundedTreeVertices G a T ⊆
        H.terminalFrontier (H.essentialMeetingPaths W X) := by
  let base := G.delete {a}
  let H := base.quotient X
  let Q := nonBoundedTreeVertices G a T
  let L := liftDeleteQuotientFamily G a X W
  have hNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  have hSourceX : Disjoint base.source X :=
    tree_offRoot_disjoint_delete_source G hT hXT
  have hselfBase : H.vertexSet W ⊆
      base.roof (H.terminalFrontier W) :=
    quotientWave_vertexSet_subset_original_roof
      base hNoEnter hSourceX hW
  have hterminalL : G.terminalFrontier L = H.terminalFrontier W := by
    dsimp only [L, H, base, liftDeleteQuotientFamily]
    rw [G.terminalFrontier_liftDeleteFamily,
      terminalFrontier_liftQuotientFamily]
  constructor
  · intro t ht
    obtain ⟨p, hp, hpt⟩ := ht.1
    have hpW : p ∈ W := hp.1.1
    have hpMeet : (p.support ∩ X).Nonempty := hp.2
    have htSupport : t ∈ p.support := H.terminal_mem_support hpt
    have htMeeting : t ∈ H.vertexSet (H.essentialMeetingPaths W X) :=
      ⟨p, hp, htSupport⟩
    have htX : t ∈ X := hclosed ⟨htMeeting, ht.2⟩
    by_contra htQ
    have htStrict : t ∈ G.strictRoof (G.terminalFrontier L) :=
      hground ⟨htX, htQ⟩
    obtain ⟨s, hps, hsEss⟩ := hp.1.2
    have hst : s = t := Option.some.inj (hps.symm.trans hpt)
    have htEssH : t ∈ H.essential (H.terminalFrontier W) := hst ▸ hsEss
    have htEssBase : t ∈ base.essential (H.terminalFrontier W) :=
      base.quotient_essential_subset_original X _ htEssH
    have htEssG : t ∈ G.essential (G.terminalFrontier L) := by
      rw [hterminalL]
      exact G.delete_essential_subset_essential
        (H.terminalFrontier W) {a} htEssBase
    exact Set.disjoint_left.1
      (G.disjoint_strictRoof_essential (G.terminalFrontier L))
      htStrict htEssG
  · intro q hq
    obtain ⟨p, hp, hqp⟩ := hq.1
    have hpW : p ∈ W := hp.1.1
    have hpSource : p.initial ∈ H.source :=
      hW.2.1 ⟨p, hpW, rfl⟩
    have hpInitialNe : p.initial ≠ a := by
      intro hpa
      rcases hpSource.1 with hpBaseSource | hpX
      · exact hpBaseSource.2 (by simpa [hpa])
      · exact (hXT hpX).2 (by simpa [hpa])
    have hqNeA : q ≠ a := by
      exact quotientWave_support_ne_root G hXT hW hpW hqp
    by_contra hnotTerminalMeeting
    have hnotTerminalW : q ∉ H.terminalFrontier W := by
      intro hqTerminal
      have hpTerminal : H.terminal? p = some q :=
        DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
          H hW.1 hpW hqp hqTerminal
      exact hnotTerminalMeeting ⟨p, hp, hpTerminal⟩
    have hqRoofBase : q ∈ base.roof (H.terminalFrontier W) :=
      hselfBase ⟨p, hpW, hqp⟩
    have hqRoofG : q ∈ G.roof (G.terminalFrontier L) := by
      rw [hterminalL]
      exact roof_delete_source_subset_ambient_of_ne
        G hG ha hqNeA hqRoofBase
    have hqStrictG : q ∈ G.strictRoof (G.terminalFrontier L) := by
      refine ⟨hqRoofG, ?_⟩
      intro hqEss
      exact hnotTerminalW (by
        rw [← hterminalL]
        exact G.essential_subset _ hqEss)
    exact not_mem_strictRoof_of_mem_nonBounded
      G a T hq.2 hXcount hXT hW hqStrictG

/-- Remove the common wave's members ending at non-bounded tree vertices
and commute the resulting deletion past the quotient.  The output is the
genuine wave in `(Γ-a-Q)/X` used before bringing the wave to the ground. -/
theorem exists_reducedQuotientWave
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T X : Set V} (hT : G.IsTreeSet a T)
    (hXcount : X.Countable) (hXT : X ⊆ T \ {a})
    {W : Set (((G.delete {a}).quotient X).DPath)}
    (hW : ((G.delete {a}).quotient X).IsWave W)
    (hclosed : ((G.delete {a}).quotient X).vertexSet
      (((G.delete {a}).quotient X).essentialMeetingPaths W X) ∩ T ⊆ X)
    (hground : X \ nonBoundedTreeVertices G a T ⊆
      G.strictRoof (G.terminalFrontier
        (liftDeleteQuotientFamily G a X W))) :
    ∃ W' : Set ((((G.delete {a}).delete
        (nonBoundedTreeVertices G a T)).quotient X).DPath),
      (((G.delete {a}).delete
        (nonBoundedTreeVertices G a T)).quotient X).IsWave W' := by
  let base := G.delete {a}
  let H := base.quotient X
  let Q := nonBoundedTreeVertices G a T
  have h64 := assertion6_4_quotient G hG ha hT hXcount hXT
    hW hclosed hground
  have hforce : ∀ p ∈ H.essentialWarpPart W, ∀ q ∈ p.support,
      q ∈ Q → H.terminal? p ≠ some q →
        (p.support ∩ X).Nonempty := by
    exact nonterminal_nonBounded_contact_meets_commitment
      G hG ha hT hXcount hXT hW
  let hcontact :
      H.vertexSet (H.essentialMeetingPaths W X) ∩ Q ⊆
        H.terminalFrontier (H.essentialMeetingPaths W X) := h64.2
  let U : Set (H.delete Q).DPath :=
    H.deleteTerminalSubfamily (H.essentialWarpPart W) Q
      hW.essentialWarpPart.1
      (H.essentialWarpPart_contact_of_nonterminal_meeting_contact
        hforce hcontact)
  have hU : (H.delete Q).IsWave U := by
    exact H.isWave_deleteTerminalSubfamily_essentialMeeting_nonterminal
      hW hforce hcontact
  let W' : Set ((base.delete Q).quotient X).DPath :=
    base.transportQuotientDeleteWave X Q U
  have hbaseNoEnter : base.NoEdgeEnters base.source :=
    delete_root_noEdgeEnters_source G hG a
  have hW' : ((base.delete Q).quotient X).IsWave W' := by
    exact base.isWave_transportQuotientDeleteWave hbaseNoEnter hU
  exact ⟨W', hW'⟩

end SafeLink

end Erdos599
