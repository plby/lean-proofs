/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.Blueprint
import ErdosProblems.Erdos599.SeededHammock
import ErdosProblems.Erdos599.Blueprint931
import ErdosProblems.Erdos599.WaveLimits
import ErdosProblems.Erdos599.RoofQuotient

/-!
# The half-way-linkage clause

This file contains the half-way half of the simultaneous cardinal induction
in Aharoni--Berger, Section 9.  As documented in `CardinalInduction.lean`, the
literal globally-minimal stop-over clause in the paper is false; the internal
induction therefore uses the repaired trimmed stop-over invariant.  The
hypothesis that the web is unhindered remains essential: without it even a
one-point source in a web with empty target is a counterexample.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction

open DirectedPath

universe u

variable {V : Type u}

/-! ## Elementary facts about repaired stop-over sets -/

/-- The simultaneous hypotheses available while proving the half-way
clause already link every unhindered auxiliary web whose whole source has
cardinality at most the current cardinal.  Strictly smaller source sets use
the lower induction hypothesis; equality uses the current extension clause
with the whole source as the designated set and the empty complementary
linkage.

This is the source-faithful way in which Assertions 9.30--9.31 invoke the
induction: their auxiliary quotient and slice webs have source cardinal at
most `kappa`, even when the ambient web has many more sources. -/
theorem isLinkable_of_source_mk_le_current
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hext : UniversalExtensionClauseAt V kappa)
    (Delta : DWeb V) (hDelta : Delta.IsUnhindered)
    (hsource : #Delta.source <= kappa) :
    IsLinkable Delta := by
  rcases lt_or_eq_of_le hsource with hlt | heq
  · exact linkable_of_cardinalInductionAt_source Delta
      (hlower #Delta.source hlt Delta hDelta)
  · apply linkable_of_extension_at_source_card Delta
    simpa only [heq] using hext Delta hDelta

namespace IsSeparatingHalfwayStopover

theorem quotient_source_eq {Gamma : DWeb V} {W : Set Gamma.DPath}
    {C : Set V} (h : IsSeparatingHalfwayStopover Gamma W C) :
    (Gamma.quotient C).source = C := by
  rw [DWeb.quotient_source, Set.union_comm]
  calc
    Gamma.essential (C ∪ Gamma.source) = Gamma.essential C :=
      RelationalRoof.essential_union_eq_of_subset_roof
        Gamma.graph.Adj Gamma.target h.separator
    _ = C := h.stopover.minimal

theorem quotient_unhindered {Gamma : DWeb V} {W : Set Gamma.DPath}
    {C : Set V} (h : IsSeparatingHalfwayStopover Gamma W C) :
    (Gamma.quotient C).IsUnhindered :=
  h.stopover.quotient_unhindered

end IsSeparatingHalfwayStopover

/-- A target vertex belonging to a set is essential in that set: its
trivial target path avoids all the other members. -/
theorem target_mem_essential {Γ : DWeb V} {S : Set V} {b : V}
    (hbB : b ∈ Γ.target) (hbS : b ∈ S) : b ∈ Γ.essential S := by
  rw [Γ.mem_essential_iff]
  refine ⟨hbS, (Γ.not_mem_roof_iff (S \ {b}) b).2 ?_⟩
  let p : FinitePath Γ.graph := FinitePath.trivial Γ.graph b
  refine ⟨p, ⟨rfl, hbB⟩, ?_⟩
  apply Set.disjoint_left.2
  intro x hxp hx
  have hxb : x = b := by
    simpa [p] using hxp
  exact hx.2 hxb

/-- Every subset of the target is a repaired (trimmed) separator. -/
theorem target_subset_isTrimmedSeparator {Γ : DWeb V} {C : Set V}
    (hC : C ⊆ Γ.target) : IsTrimmedSeparator Γ C := by
  apply Set.Subset.antisymm (Γ.essential_subset C)
  intro b hb
  exact target_mem_essential (hC hb) hb
theorem essential_source_union_target (Γ : DWeb V) :
    Γ.essential (Γ.source ∪ Γ.target) = Γ.target := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx.1 with hxA | hxB
    · by_contra hxnotB
      obtain ⟨p, hp, hav⟩ :=
        (Γ.not_mem_roof_iff ((Γ.source ∪ Γ.target) \ {x}) x).1 hx.2
      apply Set.disjoint_left.1 hav p.finish_mem_support
      exact ⟨Or.inr hp.2, fun h ↦ hxnotB (h ▸ hp.2)⟩
    · exact hxB
  · intro b hb
    exact target_mem_essential hb (Or.inr hb)

@[simp] theorem quotient_target_source (Γ : DWeb V) :
    (Γ.quotient Γ.target).source = Γ.target := by
  exact essential_source_union_target Γ

theorem quotient_target_walk_start_eq_finish (Γ : DWeb V)
    {a b : V} (p : Walk (Γ.quotient Γ.target).graph a b)
    (hb : b ∈ Γ.target) : a = b := by
  induction p with
  | nil => rfl
  | @cons a c b h p ih =>
      have hcb : c = b := ih hb
      subst c
      exact False.elim (h.2.2.2 hb)

theorem quotient_target_isUnhindered (Γ : DWeb V) :
    (Γ.quotient Γ.target).IsUnhindered := by
  rw [DWeb.isUnhindered_iff]
  intro W hW
  apply Set.Subset.antisymm hW.2.1
  intro b hb
  rw [quotient_target_source Γ] at hb
  have hbB : b ∈ Γ.target := hb
  let q : FinitePath (Γ.quotient Γ.target).graph :=
    FinitePath.trivial (Γ.quotient Γ.target).graph b
  have hbq : q.start ∈ (Γ.quotient Γ.target).source := by
    change b ∈ (Γ.quotient Γ.target).source
    rw [quotient_target_source]
    exact hb
  obtain ⟨x, hxq, hxfrontier⟩ := hW.2.2 hbq q ⟨rfl, hbB⟩
  have hxb : x = b := by simpa [q] using hxq
  subst x
  obtain ⟨p, hpW, hpterm⟩ := hxfrontier
  refine (Γ.quotient Γ.target).mem_initialSet.2 ⟨p, hpW, ?_⟩
  rcases p with p | r
  · have hpfinish : p.finish = b := by simpa using hpterm
    exact (quotient_target_walk_start_eq_finish Γ p.walk
      (hpfinish ▸ hbB)).trans hpfinish
  · simp at hpterm

theorem fullLinkage_linksToTarget
    {Γ : DWeb V} {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L)
    (hA₀ : A₀ ⊆ Γ.source) : LinksToTarget Γ L A₀ := by
  intro a ha
  have haI : a ∈ Γ.initialSet L := hL.initialSet_eq.symm ▸ hA₀ ha
  obtain ⟨p, hpL, hpinit⟩ := (Γ.mem_initialSet).1 haI
  obtain ⟨q, rfl⟩ := hL.finiteCharacter hpL
  change q.start = a at hpinit
  obtain ⟨r, hr, hrunion, hrsource⟩ := hL.endpointPure (Sum.inl q) hpL
  have hrq : r = q := by simpa using hr.symm
  subst r
  refine ⟨Sum.inl q, hpL, q, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      have hxA : x ∈ Γ.source := hA₀ hx.2
      have hxstart : x = q.start := by
        have hxmem : x ∈ q.support ∩ Γ.source := ⟨hx.1, hxA⟩
        rw [hrsource] at hxmem
        simpa using hxmem
      exact hxstart.trans hpinit
    · intro x hx
      have hxa : x = a := by simpa using hx
      subst x
      exact ⟨hpinit ▸ q.start_mem_support, ha⟩
  · refine ⟨[], q.walk.support.tail, ?_, q.finish, ?_, ?_⟩
    · have hsupport : q.walk.support = q.start :: q.walk.support.tail := by
        have h := (List.cons_head_tail q.walk.support_ne_nil).symm
        simpa only [q.walk.head_support] using h
      exact hsupport.trans (congrArg (fun x ↦ x :: q.walk.support.tail) hpinit)
    · apply hL.terminalFrontier_subset
      exact ⟨Sum.inl q, hpL, rfl⟩
    · have hsupport : q.walk.support = q.start :: q.walk.support.tail := by
        have h := (List.cons_head_tail q.walk.support_ne_nil).symm
        simpa only [q.walk.head_support] using h
      have hfinish : q.finish ∈ q.start :: q.walk.support.tail := by
        rw [← hsupport]
        exact q.finish_mem_support
      simpa only [hpinit] using hfinish

theorem fullLinkage_isHalfwayLinkage
    {Γ : DWeb V} {L : Set Γ.DPath}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L) :
    IsHalfwayLinkage Γ L := by
  refine ⟨Γ.target, hL, target_subset_isTrimmedSeparator Set.Subset.rfl, ?_⟩
  exact quotient_target_isUnhindered Γ


/-! ## The maximal-wave stopover used at the start of the construction -/

/-- Every concrete web has a forward-extension-maximal wave.  This is the
concrete Zorn application obtained by combining the chain limit theorem with
the abstract maximal-wave wrapper. -/
theorem exists_forwardExtension_maximal_wave (Γ : DWeb V) :
    ∃ M : Γ.Wave, IsMax M := by
  have hchain : ∀ c : Set Γ.Wave, IsChain (· ≤ ·) c → c.Nonempty →
      ∃ ub : Γ.Wave, ∀ W ∈ c, W ≤ ub := by
    intro c hc hcne
    let U : Γ.Wave :=
      ⟨Γ.waveChainUpper c hcne hc, Γ.isWave_waveChainUpper c hcne hc⟩
    exact ⟨U, fun W hW ↦ Γ.forwardExtension_waveChainUpper c hcne hc hW⟩
  obtain ⟨M, _hbase, hM⟩ := Γ.exists_maximal_forward_extension
    (⟨Γ.trivialWave, Γ.isWave_trivialWave⟩ : Γ.Wave) hchain
  exact ⟨M, hM⟩

/-- Seeded form of the same Zorn construction.  It is the useful interface
for a height-controlled Section 9 wave: the chosen maximal wave genuinely
forward-extends the supplied seed, so target-link certificates can be
transported by `linksToTarget_essentialWarpPart_of_forwardExtension` below. -/
theorem exists_forwardExtension_maximal_wave_above
    {Γ : DWeb V} (U : Γ.Wave) :
    ∃ M : Γ.Wave, U ≤ M ∧ IsMax M := by
  have hchain : ∀ c : Set Γ.Wave, IsChain (· ≤ ·) c → c.Nonempty →
      ∃ ub : Γ.Wave, ∀ W ∈ c, W ≤ ub := by
    intro c hc hcne
    let ub : Γ.Wave :=
      ⟨Γ.waveChainUpper c hcne hc, Γ.isWave_waveChainUpper c hcne hc⟩
    exact ⟨ub, fun W hW ↦
      Γ.forwardExtension_waveChainUpper c hcne hc hW⟩
  exact Γ.exists_maximal_forward_extension U hchain

/-- In an unhindered web the essential part of every wave starts at every
source and has finite character.  Under the explicit endpoint-purity
condition (which is automatic for the normalized ladder warps used below),
it is therefore a finite source linkage to its own terminal frontier. -/
theorem essentialWarpPart_isLinkageBetween
    {Γ : DWeb V} (hΓ : Γ.IsUnhindered) {W : Set Γ.DPath}
    (hW : Γ.IsWave W)
    (hpure : ∀ p ∈ Γ.essentialWarpPart W,
      IsPathBetween Γ Γ.source
        (Γ.terminalFrontier (Γ.essentialWarpPart W)) p) :
    IsLinkageBetween Γ Γ.source (Γ.terminalFrontier (Γ.essentialWarpPart W))
      (Γ.essentialWarpPart W) := by
  have hWE : Γ.IsWave (Γ.essentialWarpPart W) := hW.essentialWarpPart
  refine ⟨hWE.1, ?_, ?_, Set.Subset.rfl, hpure⟩
  · intro p hp
    obtain ⟨t, hpt, _ht⟩ := hp.2
    rcases p with p | r
    · exact ⟨p, rfl⟩
    · simp at hpt
  · exact (Γ.isUnhindered_iff.mp hΓ _ hWE)

/-- A full wave has the endpoint purity required by the Section 9 linkage
predicate.  Fullness is the important point: if another source occurred in
the interior of a member, the member starting at that source would meet it;
the warp condition then forces the two members to be equal.  The identical
argument at the terminal frontier handles the other endpoint. -/
theorem wave_endpointPure_of_initialSet_eq
    {Γ : DWeb V} {W : Set Γ.DPath} (hW : Γ.IsWave W)
    (hfinite : Γ.HasFiniteCharacter W)
    (hinitial : Γ.initialSet W = Γ.source) :
    ∀ p ∈ W, IsPathBetween Γ Γ.source (Γ.terminalFrontier W) p := by
  intro p hp
  obtain ⟨q, rfl⟩ := hfinite hp
  have hsource : q.support ∩ Γ.source = {q.start} := by
      apply Set.Subset.antisymm
      · intro x hx
        have hxinitial : x ∈ Γ.initialSet W := hinitial.symm ▸ hx.2
        obtain ⟨p, hpW, hpstart⟩ := hxinitial
        have hpq : p = (Sum.inl q : Γ.DPath) := by
          by_contra hpq
          exact Set.disjoint_left.1 (hW.1 hpW hp hpq)
            (hpstart ▸ p.initial_mem_support) hx.1
        subst p
        change x = q.start
        exact hpstart.symm
      · intro x hx
        have hxq : x = q.start := by simpa using hx
        subst x
        exact ⟨q.start_mem_support,
          hW.2.1 ⟨(Sum.inl q : Γ.DPath), hp, rfl⟩⟩
  have hterminal :
      q.support ∩ Γ.terminalFrontier W = {q.finish} := by
    apply Set.Subset.antisymm
    · exact DWeb.IsWarp.finite_support_inter_terminalFrontier Γ hW.1 hp
    · intro x hx
      have hxq : x = q.finish := by simpa using hx
      subst x
      exact ⟨q.finish_mem_support,
        ⟨(Sum.inl q : Γ.DPath), hp, rfl⟩⟩
  refine ⟨q, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, hterminal]
  ext x
  simp [or_comm]

/-- The essential part of a wave has finite character, so the preceding
endpoint-purity argument applies without a ray case. -/
theorem essentialWarpPart_endpointPure_of_unhindered
    {Γ : DWeb V} (hΓ : Γ.IsUnhindered) {W : Set Γ.DPath}
    (hW : Γ.IsWave W) :
    ∀ p ∈ Γ.essentialWarpPart W,
      IsPathBetween Γ Γ.source
        (Γ.terminalFrontier (Γ.essentialWarpPart W)) p := by
  have hWE : Γ.IsWave (Γ.essentialWarpPart W) := hW.essentialWarpPart
  have hinitial : Γ.initialSet (Γ.essentialWarpPart W) = Γ.source :=
    (Γ.isUnhindered_iff.mp hΓ _ hWE)
  have hfinite : Γ.HasFiniteCharacter (Γ.essentialWarpPart W) := by
    intro p hp
    obtain ⟨t, hpt, _ht⟩ := hp.2
    rcases p with q | r
    · exact ⟨q, rfl⟩
    · simp at hpt
  exact wave_endpointPure_of_initialSet_eq hWE hfinite hinitial

/-- Looseness implies unhinderedness, at the concrete-web level. -/
theorem isUnhindered_of_isLoose {Γ : DWeb V} (hΓ : Γ.IsLoose) :
    Γ.IsUnhindered := by
  rw [Γ.isUnhindered_iff]
  intro W hW
  rw [hΓ W hW, Γ.initialSet_trivialWave]

/-- A forward-maximal wave in an unhindered web has a canonical trimmed
half-way stopover: take its essential part.  Lemma 3.26 supplies the
unhindered quotient, while fullness supplies endpoint purity. -/
theorem essentialWarpPart_isHalfwayStopover_of_isMax
    {Γ : DWeb V} (hΓ : Γ.IsUnhindered) {W : Set Γ.DPath}
    (hW : Γ.IsWave W) (hmax : IsMax (⟨W, hW⟩ : Γ.Wave)) :
    IsHalfwayStopover Γ (Γ.essentialWarpPart W)
      (Γ.essential (Γ.terminalFrontier W)) := by
  have hpure := essentialWarpPart_endpointPure_of_unhindered hΓ hW
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Γ.terminalFrontier_essentialWarpPart] using
      (essentialWarpPart_isLinkageBetween hΓ hW hpure)
  · exact Γ.essential_idem (Γ.terminalFrontier W)
  · exact isUnhindered_of_isLoose
      (Γ.quotient_essentialTerminalFrontier_isLoose_of_isMax hW hmax)

/-- The canonical maximal-wave stop-over also carries the stronger local
separator certificate used by the regular slice argument.  This fact is
kept separate from `IsHalfwayStopover`: the public half-way clause only
needs the sound weak trimmed invariant, while source Lemma 2.19 additionally
uses separation at this particular construction point. -/
theorem essentialWarpPart_isSeparatingHalfwayStopover_of_isMax
    {Γ : DWeb V} (hΓ : Γ.IsUnhindered) {W : Set Γ.DPath}
    (hW : Γ.IsWave W) (hmax : IsMax (⟨W, hW⟩ : Γ.Wave)) :
    IsSeparatingHalfwayStopover Γ (Γ.essentialWarpPart W)
      (Γ.essential (Γ.terminalFrontier W)) := by
  refine ⟨essentialWarpPart_isHalfwayStopover_of_isMax hΓ hW hmax, ?_⟩
  rw [IsSeparatorFrom, Γ.roof_essential]
  exact hW.2.2

/-- Target-link certificates survive passage from a full wave to any
forward extension, after the latter is trimmed to its essential finite
part.  Fullness of both waves is supplied by unhinderedness.  It rules out
both a ray extension of a selected finite component and the appearance of
another designated source later on that component. -/
theorem linksToTarget_essentialWarpPart_of_forwardExtension
    {Γ : DWeb V} (hΓ : Γ.IsUnhindered) {U W : Set Γ.DPath}
    (hU : Γ.IsWave U) (hW : Γ.IsWave W)
    (hUW : Γ.ForwardExtension U W) {A₀ : Set V}
    (hA₀ : A₀ ⊆ Γ.source) (hlinks : LinksToTarget Γ U A₀) :
    LinksToTarget Γ (Γ.essentialWarpPart W) A₀ := by
  have hUinitial : Γ.initialSet U = Γ.source :=
    Γ.isUnhindered_iff.mp hΓ U hU
  have hWE : Γ.IsWave (Γ.essentialWarpPart W) := hW.essentialWarpPart
  have hWEinitial : Γ.initialSet (Γ.essentialWarpPart W) = Γ.source :=
    Γ.isUnhindered_iff.mp hΓ _ hWE
  intro a ha
  obtain ⟨p, hpU, q, rfl, hqA₀, before, after, hqsupport,
      b, hbtarget, hbafter⟩ := hlinks a ha
  have haq : a ∈ q.support := by
    have : a ∈ q.support ∩ A₀ := hqA₀.symm ▸ Set.mem_singleton a
    exact this.1
  have hqstart : q.start = a := by
    have haInitial : a ∈ Γ.initialSet U := hUinitial.symm ▸ hA₀ ha
    obtain ⟨s, hsU, hsstart⟩ := haInitial
    have hsq : s = (Sum.inl q : Γ.DPath) := by
      by_contra hne
      exact Set.disjoint_left.1 (hU.1 hsU hpU hne)
        (hsstart ▸ s.initial_mem_support) haq
    subst s
    exact hsstart
  obtain ⟨r, hrW, hqr⟩ := hUW.1 (.inl q) hpU
  have hrstart : r.initial = a := by
    rw [← hqstart]
    exact (Γ.extends_initial hqr).symm
  have haWEinitial : a ∈ Γ.initialSet (Γ.essentialWarpPart W) :=
    hWEinitial.symm ▸ hA₀ ha
  obtain ⟨s, hsWE, hsstart⟩ := haWEinitial
  have hrs : r = s := by
    by_contra hne
    exact Set.disjoint_left.1 (hW.1 hrW hsWE.1 hne)
      r.initial_mem_support (hrstart.trans hsstart.symm ▸ s.initial_mem_support)
  have hrWE : r ∈ Γ.essentialWarpPart W := hrs ▸ hsWE
  rcases r with r | r
  · refine ⟨(.inl r : Γ.DPath), hrWE, r, rfl, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · rintro x ⟨hxr, hxA₀⟩
        have hxInitial : x ∈ Γ.initialSet (Γ.essentialWarpPart W) :=
          hWEinitial.symm ▸ hA₀ hxA₀
        obtain ⟨t, htWE, htstart⟩ := hxInitial
        have htr : t = (Sum.inl r : Γ.DPath) := by
          by_contra hne
          exact Set.disjoint_left.1 (hW.1 htWE.1 hrWE.1 hne)
            (htstart ▸ t.initial_mem_support) hxr
        subst t
        change r.start = a at hrstart
        exact htstart.symm.trans hrstart
      · intro x hx
        have hxa : x = a := by simpa using hx
        subst x
        exact ⟨hrstart ▸ r.start_mem_support, ha⟩
    · change q.IsPrefixOf r at hqr
      rcases hqr with ⟨extra, hextra⟩
      refine ⟨before, after ++ extra, ?_, b, hbtarget, ?_⟩
      · rw [← hextra, hqsupport]
        simp only [List.append_assoc, List.cons_append]
      · exact List.mem_append_left _ hbafter
  · obtain ⟨t, ht, _⟩ := hrWE.2
    simp at ht

/-- Final maximal-wave conversion used by the blueprint recursion.  Once
the recursion has arranged the target links and the height witness, no
further graph construction is needed. -/
theorem halfwayLinkageOfAltitude_of_maximalWave
    {Γ : DWeb V} (hΓ : Γ.IsUnhindered) {W : Set Γ.DPath}
    (hW : Γ.IsWave W) (hmax : IsMax (⟨W, hW⟩ : Γ.Wave))
    {A₀ : Set V} {κ : Cardinal.{u}}
    (hlinks : LinksToTarget Γ (Γ.essentialWarpPart W) A₀)
    (hheight : HeightAtMost Γ
      (Γ.essential (Γ.terminalFrontier W)) κ) :
    IsHalfwayLinkageOfAltitude Γ A₀ κ (Γ.essentialWarpPart W) := by
  exact halfwayLinkageOfAltitude_of_stopover
    (essentialWarpPart_isHalfwayStopover_of_isMax hΓ hW hmax)
    hlinks hheight

end CardinalInduction
end Erdos599
namespace Erdos599
namespace Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {ZBefore innerRoof roof : Set V}

/-! A standalone construction of the closure used in Assertions 9.22--9.25. -/

/- The construction below is retained as an independently checked prototype.
The scheduler-facing development uses the reusable version in
`SeededHammock.lean`, which is available to Assertions 9.30 and 9.31 without
creating an import cycle through this file. -/
namespace LocalSeeded

private theorem image_subtype_subset {X : Type u} {K : Set X}
    (s : Set K) : Subtype.val '' s ⊆ K := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

private theorem mk_image_subtype_eq {X : Type u} {K : Set X}
    (s : Set K) : #(Subtype.val '' s : Set X) = #s :=
  Cardinal.mk_image_eq_of_injOn Subtype.val s Set.injOn_subtype_val

/-- A hammock can be extended to an inclusion-maximal hammock while
retaining every member of the seed.  The seeded form is needed in the
large-cardinal branch: an arbitrary maximal hammock need not contain a
given large hammock. -/
theorem exists_maximal_hammock_superset (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (u : V) (e : AltEnd V)
    {K : Set (AltPath Gamma.graph)} (hK : Hammock Gamma Y u e K) :
    ∃ H : Set (AltPath Gamma.graph), K ⊆ H ∧
      Maximal (fun L ↦ Hammock Gamma Y u e L) H := by
  apply zorn_subset_nonempty
    {L : Set (AltPath Gamma.graph) | Hammock Gamma Y u e L}
  · intro c hcsub hc hcne
    exact ⟨⋃₀ c, hammock_sUnion_of_chain hcsub hc,
      fun L hLc ↦ Set.subset_sUnion_of_mem hLc⟩
  · exact hK

/-- Zorn plus cardinal thinning produces the exact two-branch
`MaximalUpTo` witness, rather than assuming one. -/
theorem exists_hammockMaximalUpTo (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (u : V) (e : AltEnd V) (rho : Cardinal.{u}) :
    ∃ H : Set (AltPath Gamma.graph),
      HammockMaximalUpTo Gamma Y u e rho H ∧
        (HasHammockCard Gamma Y u e rho → #H = rho) := by
  by_cases hlarge : ∃ K : Set (AltPath Gamma.graph),
      Hammock Gamma Y u e K ∧ succ rho ≤ #K
  · obtain ⟨K, hK, hlargeK⟩ := hlarge
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.mp
      ((le_succ rho).trans hlargeK)
    obtain ⟨t, ht⟩ := Cardinal.le_mk_iff_exists_set.mp hlargeK
    let H : Set (AltPath Gamma.graph) := Subtype.val '' s
    let L : Set (AltPath Gamma.graph) := Subtype.val '' t
    have hHK : H ⊆ K := image_subtype_subset s
    have hLK : L ⊆ K := image_subtype_subset t
    refine ⟨H, maximalUpTo_of_large (hK.subset hHK) ?_
      (hK.subset hLK) ?_, fun _ ↦ ?_⟩
    · exact (mk_image_subtype_eq s).trans hs
    · exact (mk_image_subtype_eq t).trans ht
    · exact (mk_image_subtype_eq s).trans hs
  · by_cases hrho : HasHammockCard Gamma Y u e rho
    · obtain ⟨K, hK, hKcard⟩ := hrho
      obtain ⟨M, hKM, hM⟩ :=
        exists_maximal_hammock_superset Gamma Y u e hK
      have hMcard : #M ≤ rho := by
        by_contra hnot
        exact hlarge ⟨M, hM.1, succ_le_of_lt (lt_of_not_ge hnot)⟩
      have hrhoM : rho ≤ #M := by
        rw [← hKcard]
        exact Cardinal.mk_subtype_mono hKM
      have hMeq : #M = rho := le_antisymm hMcard hrhoM
      exact ⟨M, maximalUpTo_of_maximal hM.1 hM hMcard,
        fun _ ↦ hMeq⟩
    · obtain ⟨M, hM⟩ := exists_maximal_hammock Gamma Y u e
      have hMcard : #M ≤ rho := by
        by_contra hnot
        exact hlarge ⟨M, hM.1, succ_le_of_lt (lt_of_not_ge hnot)⟩
      exact ⟨M, maximalUpTo_of_maximal hM.1 hM hMcard,
        fun h ↦ (hrho h).elim⟩

theorem finiteTrace_vertexSet_countable {D : Digraph V}
    (Q : FiniteTrace D) : Q.vertexSet.Countable := by
  exact Set.countable_iUnion fun i => (Q.link i).path.support_countable

theorem infiniteTrace_vertexSet_countable {D : Digraph V}
    (Q : InfiniteTrace D) : Q.vertexSet.Countable := by
  exact Set.countable_iUnion fun i => (Q.link i).path.support_countable

theorem altPath_vertexSet_countable {D : Digraph V} (Q : AltPath D) :
    Q.vertexSet.Countable := by
  cases Q with
  | trivial v => simp [AltPath.vertexSet]
  | finite Q => exact finiteTrace_vertexSet_countable Q
  | infinite Q => exact infiniteTrace_vertexSet_countable Q

private theorem mk_iUnion_le_of_le {I X : Type u} {f : I → Set X}
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hI : #I ≤ kappa) (hf : ∀ i, #(f i) ≤ kappa) :
    #(⋃ i, f i) ≤ kappa := by
  refine (Cardinal.mk_iUnion_le f).trans ?_
  exact Cardinal.mul_le_of_le hkappa hI (ciSup_le' hf)

abbrev EligiblePair (ZBefore innerRoof roof : Set V) :=
  {q : V × AltEnd V //
    HammockEligible ZBefore innerRoof roof q.1 q.2}

/-- The large-hammock part of the closing-up construction.  Unlike the
bare `MaximalUpTo` predicate, this records that a hammock of the requested
cardinality is itself contained in the closure whenever one exists. -/
def LargeHammockClosed (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (Z ZBefore innerRoof roof : Set V) (rho : Cardinal.{u}) : Prop :=
  ∀ u e, HammockEligible ZBefore innerRoof roof u e →
    HasHammockCard Gamma Y u e rho →
      ∃ H : Set (AltPath Gamma.graph),
        Hammock Gamma Y u e H ∧ #H = rho ∧ HammockContained H Z

private def eligiblePairEmbedding (ZBefore innerRoof roof : Set V) :
    EligiblePair ZBefore innerRoof roof ↪ ZBefore × Option ZBefore where
  toFun q :=
    (⟨q.1.1, q.2.1.1⟩,
      match h : q.1.2 with
      | .vertex v => some ⟨v, by
          have hv : v ∈ ZBefore ∩ roof := by
            simpa [HammockEligible, h] using q.2.2
          exact hv.1⟩
      | .infinity => none)
  inj' := by
    rintro ⟨⟨u, e⟩, he⟩ ⟨⟨u', e'⟩, he'⟩ h
    apply Subtype.ext
    have hu : u = u' := congrArg (fun z => (z.1 : V)) h
    subst u'
    apply Prod.ext
    · rfl
    cases e with
    | infinity =>
        cases e' with
        | infinity => rfl
        | vertex v => simp at h
    | vertex v =>
        cases e' with
        | infinity => simp at h
        | vertex v' =>
            have hv : v = v' := by
              simpa using
                congrArg (fun z => Option.map Subtype.val z.2) h
            subst v'
            rfl

theorem mk_eligiblePair_le {ZBefore innerRoof roof : Set V}
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa) :
    #(EligiblePair ZBefore innerRoof roof) ≤ kappa := by
  refine (Cardinal.mk_le_of_injective
    (eligiblePairEmbedding ZBefore innerRoof roof).injective).trans ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id,
    Cardinal.mk_option]
  apply Cardinal.mul_le_of_le hkappa hZBefore
  exact Cardinal.add_le_of_le hkappa hZBefore
    (Cardinal.one_le_aleph0.trans hkappa)

noncomputable def chosenHammock (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (q : EligiblePair ZBefore innerRoof roof) :
    Set (AltPath Gamma.graph) :=
  Classical.choose (exists_hammockMaximalUpTo Gamma Y q.1.1 q.1.2 rho)

theorem chosenHammock_spec (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (q : EligiblePair ZBefore innerRoof roof) :
    HammockMaximalUpTo Gamma Y q.1.1 q.1.2 rho
      (chosenHammock Gamma Y rho q) :=
  (Classical.choose_spec
    (exists_hammockMaximalUpTo Gamma Y q.1.1 q.1.2 rho)).1

theorem chosenHammock_card_eq_of_hasHammockCard
    (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (q : EligiblePair ZBefore innerRoof roof)
    (hlarge : HasHammockCard Gamma Y q.1.1 q.1.2 rho) :
    #(chosenHammock Gamma Y rho q) = rho :=
  (Classical.choose_spec
    (exists_hammockMaximalUpTo Gamma Y q.1.1 q.1.2 rho)).2 hlarge

def chosenHammockVertices (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (q : EligiblePair ZBefore innerRoof roof) : Set V :=
  ⋃ Q : chosenHammock Gamma Y rho q, Q.1.vertexSet

def allHammockVertices (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (ZBefore innerRoof roof : Set V) : Set V :=
  ⋃ q : EligiblePair ZBefore innerRoof roof,
    chosenHammockVertices Gamma Y rho q

theorem chosenHammock_contained_all (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (q : EligiblePair ZBefore innerRoof roof) :
    HammockContained (chosenHammock Gamma Y rho q)
      (allHammockVertices Gamma Y rho ZBefore innerRoof roof) := by
  intro x hx
  simp only [hammockVertexSet, allHammockVertices,
    chosenHammockVertices, Set.mem_iUnion] at hx ⊢
  obtain ⟨Q, hQ, hxQ⟩ := hx
  exact ⟨q, ⟨Q, hQ⟩, hxQ⟩

theorem mk_chosenHammockVertices_le (Gamma : DWeb V)
    (Y : Set Gamma.DPath) {rho kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (q : EligiblePair ZBefore innerRoof roof) :
    #(chosenHammockVertices Gamma Y rho q) ≤ kappa := by
  apply mk_iUnion_le_of_le hkappa
  · exact (chosenHammock_spec Gamma Y rho q).card_le.trans hrho
  · intro Q
    exact (altPath_vertexSet_countable Q.1).le_aleph0.trans hkappa

theorem mk_allHammockVertices_le (Gamma : DWeb V)
    (Y : Set Gamma.DPath) {rho kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa) :
    #(allHammockVertices Gamma Y rho ZBefore innerRoof roof) ≤ kappa := by
  apply mk_iUnion_le_of_le hkappa
  · exact mk_eligiblePair_le hkappa hZBefore
  · exact mk_chosenHammockVertices_le Gamma Y hkappa hrho

theorem allHammockVertices_subset_roof (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (hSafeRoof : ∀ Q : AltPath Gamma.graph, IsSafe Y Q → Q.vertexSet ⊆ roof) :
    allHammockVertices Gamma Y rho ZBefore innerRoof roof ⊆ roof := by
  intro x hx
  obtain ⟨q, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.1 hx
  exact hSafeRoof Q.1
    ((chosenHammock_spec Gamma Y rho q).isHammock.1 Q.1 Q.2).1 hxQ

end LocalSeeded

private theorem mk_iUnion_le_of_le {I X : Type u} {f : I → Set X}
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hI : #I ≤ kappa) (hf : ∀ i, #(f i) ≤ kappa) :
    #(⋃ i, f i) ≤ kappa := by
  refine (Cardinal.mk_iUnion_le f).trans ?_
  exact Cardinal.mul_le_of_le hkappa hI (ciSup_le' hf)

abbrev TargetVertex (T roof : Set V) := {v : V // v ∈ T ∩ roof}

noncomputable def targetChoice (Gamma : DWeb V) (T roof B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (v : TargetVertex T roof) : FinitePath Gamma.graph :=
  Classical.choose (hTarget v.1 v.2)

theorem targetChoice_spec (Gamma : DWeb V) (T roof B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (v : TargetVertex T roof) :
    (targetChoice Gamma T roof B Preserves hTarget v).start = v ∧
      (targetChoice Gamma T roof B Preserves hTarget v).finish ∈ B ∧
      (targetChoice Gamma T roof B Preserves hTarget v).support ⊆ roof ∧
      Preserves (targetChoice Gamma T roof B Preserves hTarget v) :=
  Classical.choose_spec (hTarget v.1 v.2)

abbrev ActiveTarget (T roof X : Set V) :=
  {v : TargetVertex T roof // (v.1 : V) ∈ X}

def targetVertices (Gamma : DWeb V) (T roof B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (X : Set V) : Set V :=
  ⋃ v : ActiveTarget T roof X,
    (targetChoice Gamma T roof B Preserves hTarget v.1).support

private def activeTargetEmbedding (T roof X : Set V) :
    ActiveTarget T roof X ↪ X where
  toFun v := ⟨v.1.1, v.2⟩
  inj' := by
    intro v w h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : X => (z : V)) h

theorem mk_targetVertices_le (Gamma : DWeb V) (T roof B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (X : Set V) {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hX : #X ≤ kappa) :
    #(targetVertices Gamma T roof B Preserves hTarget X) ≤ kappa := by
  apply mk_iUnion_le_of_le hkappa
  · exact (Cardinal.mk_le_of_injective
      (activeTargetEmbedding T roof X).injective).trans hX
  · intro v
    exact (targetChoice Gamma T roof B Preserves hTarget v.1).support_countable
      |>.le_aleph0.trans hkappa

theorem targetVertices_subset_roof (Gamma : DWeb V) (T roof B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (X : Set V) :
    targetVertices Gamma T roof B Preserves hTarget X ⊆ roof := by
  intro x hx
  obtain ⟨v, hx⟩ := Set.mem_iUnion.1 hx
  exact (targetChoice_spec Gamma T roof B Preserves hTarget v.1).2.2.1 hx

abbrev MeetingPath (Gamma : DWeb V) (Y : Set Gamma.DPath) (X : Set V) :=
  {p : Gamma.DPath // p ∈ Y ∧ (p.support ∩ X).Nonempty}

noncomputable def meetingPoint (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (X : Set V) (p : MeetingPath Gamma Y X) : X :=
  ⟨Classical.choose p.2.2,
    (Classical.choose_spec p.2.2).2⟩

theorem meetingPoint_mem_support (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (X : Set V) (p : MeetingPath Gamma Y X) :
    (meetingPoint Gamma Y X p : V) ∈ p.1.support :=
  (Classical.choose_spec p.2.2).1

theorem meetingPoint_injective (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (X : Set V) (hY : Gamma.IsWarp Y) :
    Function.Injective (meetingPoint Gamma Y X) := by
  intro p q hpq
  apply Subtype.ext
  by_contra hpne
  have hd : Disjoint p.1.support q.1.support := hY p.2.1 q.2.1 hpne
  exact Set.disjoint_left.1 hd
    (meetingPoint_mem_support Gamma Y X p)
    (hpq ▸ meetingPoint_mem_support Gamma Y X q)

def meetingVertices (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (X : Set V) : Set V :=
  ⋃ p : MeetingPath Gamma Y X, p.1.support

theorem mk_meetingVertices_le (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (X : Set V) (hY : Gamma.IsWarp Y)
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hX : #X ≤ kappa) :
    #(meetingVertices Gamma Y X) ≤ kappa := by
  apply mk_iUnion_le_of_le hkappa
  · exact (Cardinal.mk_le_of_injective
      (meetingPoint_injective Gamma Y X hY)).trans hX
  · intro p
    exact p.1.support_countable.le_aleph0.trans hkappa

theorem meetingVertices_subset_roof (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (X roof : Set V)
    (hYroof : ∀ p ∈ Y, p.support ⊆ roof) :
    meetingVertices Gamma Y X ⊆ roof := by
  intro x hx
  obtain ⟨p, hxp⟩ := Set.mem_iUnion.1 hx
  exact hYroof p.1 p.2.1 hxp

theorem support_subset_meetingVertices (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (X : Set V) {p : Gamma.DPath}
    (hpY : p ∈ Y) (hpX : (p.support ∩ X).Nonempty) :
    p.support ⊆ meetingVertices Gamma Y X := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨⟨p, hpY, hpX⟩, hx⟩

private theorem mk_union_le_of_le {A B : Set V} {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hA : #A ≤ kappa) (hB : #B ≤ kappa) :
    #(A ∪ B : Set V) ≤ kappa :=
  (Cardinal.mk_union_le A B).trans
    (Cardinal.add_le_of_le hkappa hA hB)

def closingStep (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (X : Set V) : Set V :=
  ((X ∪ allHammockVertices Gamma Y rho ZBefore innerRoof roof) ∪
      targetVertices Gamma T roof B Preserves hTarget X) ∪
    meetingVertices Gamma Y X

theorem subset_closingStep (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (X : Set V) :
    X ⊆ closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves hTarget X :=
  fun _ hx ↦ Or.inl (Or.inl (Or.inl hx))

theorem allHammockVertices_subset_closingStep (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (X : Set V) :
    allHammockVertices Gamma Y rho ZBefore innerRoof roof ⊆
      closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves hTarget X :=
  fun _ hx ↦ Or.inl (Or.inl (Or.inr hx))

theorem targetVertices_subset_closingStep (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (X : Set V) :
    targetVertices Gamma T roof B Preserves hTarget X ⊆
      closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves hTarget X :=
  fun _ hx ↦ Or.inl (Or.inr hx)

theorem meetingVertices_subset_closingStep (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (X : Set V) :
    meetingVertices Gamma Y X ⊆
      closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves hTarget X :=
  fun _ hx ↦ Or.inr hx

theorem mk_closingStep_le (Gamma : DWeb V) (Y : Set Gamma.DPath)
    {rho kappa : Cardinal.{u}} (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (hY : Gamma.IsWarp Y) (hkappa : aleph0 ≤ kappa)
    (hrho : rho ≤ kappa) (hZBefore : #ZBefore ≤ kappa)
    (X : Set V) (hX : #X ≤ kappa) :
    #(closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves hTarget X) ≤
      kappa := by
  apply mk_union_le_of_le hkappa
  · apply mk_union_le_of_le hkappa
    · apply mk_union_le_of_le hkappa hX
      exact mk_allHammockVertices_le Gamma Y hkappa hrho hZBefore
    · exact mk_targetVertices_le Gamma T roof B Preserves hTarget X hkappa hX
  · exact mk_meetingVertices_le Gamma Y X hY hkappa hX

theorem closingStep_subset_roof (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (ZBefore innerRoof roof T B : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (hSafeRoof : ∀ Q : AltPath Gamma.graph, IsSafe Y Q → Q.vertexSet ⊆ roof)
    (hYroof : ∀ p ∈ Y, p.support ⊆ roof)
    (X : Set V) (hX : X ⊆ roof) :
    closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves hTarget X ⊆ roof := by
  rintro x ((hx | hx) | hx)
  · rcases hx with hx | hx
    · exact hX hx
    · exact allHammockVertices_subset_roof Gamma Y rho hSafeRoof hx
  · exact targetVertices_subset_roof Gamma T roof B Preserves hTarget X hx
  · exact meetingVertices_subset_roof Gamma Y X roof hYroof hx

def closureStage (step : Set V → Set V) (X0 : Set V) : ℕ → Set V
  | 0 => X0
  | n + 1 => step (closureStage step X0 n)

def omegaClosure (step : Set V → Set V) (X0 : Set V) : Set V :=
  ⋃ n, closureStage step X0 n

theorem closureStage_subset_omegaClosure (step : Set V → Set V)
    (X0 : Set V) (n : ℕ) :
    closureStage step X0 n ⊆ omegaClosure step X0 :=
  fun _ hx ↦ Set.mem_iUnion.2 ⟨n, hx⟩

theorem mk_closureStage_le {step : Set V → Set V} {X0 : Set V}
    {kappa : Cardinal.{u}} (hX0 : #X0 ≤ kappa)
    (hstep : ∀ (X : Set V), #X ≤ kappa → #(step X) ≤ kappa) :
    ∀ n, #(closureStage step X0 n) ≤ kappa
  | 0 => hX0
  | n + 1 => hstep _ (mk_closureStage_le hX0 hstep n)

theorem closureStage_subset_roof {step : Set V → Set V}
    {X0 roof : Set V} (hX0 : X0 ⊆ roof)
    (hstep : ∀ X, X ⊆ roof → step X ⊆ roof) :
    ∀ n, closureStage step X0 n ⊆ roof
  | 0 => hX0
  | n + 1 => hstep _ (closureStage_subset_roof hX0 hstep n)

/-- Simultaneous closure theorem underlying Assertions 9.22--9.25.

The only existential hypothesis is the local Assertion 9.23 input: at each
eligible target vertex a preserving path exists.  Hammocks are constructed
internally by Zorn and thinning, and the final `Z` is the omega closure of
the explicitly defined one-step operator. -/
theorem exists_assertions_9_22_to_9_25
    (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho kappa : Cardinal.{u})
    (ZBefore innerRoof roof T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (hY : Gamma.IsWarp Y)
    (hYroof : ∀ p ∈ Y, p.support ⊆ roof)
    (hSafeRoof : ∀ Q : AltPath Gamma.graph, IsSafe Y Q → Q.vertexSet ⊆ roof)
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa)
    (hX0card : #X0 ≤ kappa) (hX0roof : X0 ⊆ roof) :
    ∃ Z : Set V,
      X0 ⊆ Z ∧ #Z ≤ kappa ∧
      HammockClosedUpTo Gamma Y Z ZBefore innerRoof roof rho ∧
      LargeHammockClosed Gamma Y Z ZBefore innerRoof roof rho ∧
      HasPreservingTargetPaths Gamma T Z B Preserves ∧
      ClosedUnderPaths Gamma Y Z ∧ ContainedInRoof Z roof := by
  let step : Set V → Set V :=
    closingStep Gamma Y rho ZBefore innerRoof roof T B Preserves hTarget
  let Z : Set V := omegaClosure step X0
  have hstageCard : ∀ n, #(closureStage step X0 n) ≤ kappa := by
    apply mk_closureStage_le hX0card
    intro X hX
    exact mk_closingStep_le Gamma Y ZBefore innerRoof roof T B Preserves
      hTarget hY hkappa hrho hZBefore X hX
  have hstageRoof : ∀ n, closureStage step X0 n ⊆ roof := by
    apply closureStage_subset_roof hX0roof
    intro X hX
    exact closingStep_subset_roof Gamma Y rho ZBefore innerRoof roof T B
      Preserves hTarget hSafeRoof hYroof X hX
  have hZroof : Z ⊆ roof := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
    exact hstageRoof n hxn
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_, ?_, hZroof⟩
  · exact closureStage_subset_omegaClosure step X0 0
  · change #(⋃ n, closureStage step X0 n) ≤ kappa
    let stages : ULift.{u} ℕ → Set V :=
      fun n => closureStage step X0 n.down
    have heq : (⋃ n, closureStage step X0 n) = ⋃ i, stages i := by
      ext x
      simp [stages]
    rw [heq]
    apply mk_iUnion_le_of_le hkappa
    · simpa [Cardinal.mk_nat] using hkappa
    · intro i
      exact hstageCard i.down
  · intro u e helig
    let q : EligiblePair ZBefore innerRoof roof := ⟨(u, e), helig⟩
    refine ⟨chosenHammock Gamma Y rho q, chosenHammock_spec Gamma Y rho q, ?_⟩
    apply (chosenHammock_contained_all Gamma Y rho q).trans
    apply (allHammockVertices_subset_closingStep Gamma Y rho ZBefore innerRoof
      roof T B Preserves hTarget X0).trans
    change step X0 ⊆ Z
    exact closureStage_subset_omegaClosure step X0 1
  · intro u e helig hlarge
    let q : EligiblePair ZBefore innerRoof roof := ⟨(u, e), helig⟩
    refine ⟨chosenHammock Gamma Y rho q,
      (chosenHammock_spec Gamma Y rho q).isHammock,
      chosenHammock_card_eq_of_hasHammockCard Gamma Y rho q hlarge, ?_⟩
    apply (chosenHammock_contained_all Gamma Y rho q).trans
    apply (allHammockVertices_subset_closingStep Gamma Y rho ZBefore innerRoof
      roof T B Preserves hTarget X0).trans
    change step X0 ⊆ Z
    exact closureStage_subset_omegaClosure step X0 1
  · intro v hv
    have hvRoof : v ∈ roof := hZroof hv.2
    let tv : TargetVertex T roof := ⟨v, hv.1, hvRoof⟩
    let p := targetChoice Gamma T roof B Preserves hTarget tv
    obtain ⟨n, hvn⟩ := Set.mem_iUnion.1 hv.2
    have hpSupport : p.support ⊆ Z := by
      have hpTarget : p.support ⊆
          targetVertices Gamma T roof B Preserves hTarget
            (closureStage step X0 n) := by
        intro x hx
        exact Set.mem_iUnion.2 ⟨⟨tv, hvn⟩, hx⟩
      apply hpTarget.trans
      apply (targetVertices_subset_closingStep Gamma Y rho ZBefore
        innerRoof roof T B Preserves hTarget (closureStage step X0 n)).trans
      change step (closureStage step X0 n) ⊆ Z
      exact closureStage_subset_omegaClosure step X0 (n + 1)
    exact ⟨p, (targetChoice_spec Gamma T roof B Preserves hTarget tv).1,
      (targetChoice_spec Gamma T roof B Preserves hTarget tv).2.1,
      hpSupport,
      (targetChoice_spec Gamma T roof B Preserves hTarget tv).2.2.2⟩
  · intro p hpY hpMeet
    obtain ⟨x, hxp, hxZ⟩ := hpMeet
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hxZ
    apply (support_subset_meetingVertices Gamma Y (closureStage step X0 n)
      hpY ⟨x, hxp, hxn⟩).trans
    apply (meetingVertices_subset_closingStep Gamma Y rho ZBefore innerRoof
      roof T B Preserves hTarget (closureStage step X0 n)).trans
    change step (closureStage step X0 n) ⊆ Z
    exact closureStage_subset_omegaClosure step X0 (n + 1)

/-- Equality-cardinal version used when the seed already has the required
size (as in the source's `lambda^+` closing-up construction). -/
theorem exists_assertions_9_22_to_9_25_card_eq
    (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho kappa : Cardinal.{u})
    (ZBefore innerRoof roof T B X0 : Set V)
    (Preserves : FinitePath Gamma.graph → Prop)
    (hTarget : ∀ v ∈ T ∩ roof, ∃ p : FinitePath Gamma.graph,
      p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ roof ∧ Preserves p)
    (hY : Gamma.IsWarp Y)
    (hYroof : ∀ p ∈ Y, p.support ⊆ roof)
    (hSafeRoof : ∀ Q : AltPath Gamma.graph, IsSafe Y Q → Q.vertexSet ⊆ roof)
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa)
    (hX0card : #X0 = kappa) (hX0roof : X0 ⊆ roof) :
    ∃ Z : Set V,
      X0 ⊆ Z ∧ #Z = kappa ∧
      HammockClosedUpTo Gamma Y Z ZBefore innerRoof roof rho ∧
      LargeHammockClosed Gamma Y Z ZBefore innerRoof roof rho ∧
      HasPreservingTargetPaths Gamma T Z B Preserves ∧
      ClosedUnderPaths Gamma Y Z ∧ ContainedInRoof Z roof := by
  obtain ⟨Z, hX0Z, hZcard, hH, hHlarge, hT, hYclosed, hroof⟩ :=
    exists_assertions_9_22_to_9_25 Gamma Y rho kappa ZBefore innerRoof roof
      T B X0 Preserves hTarget hY hYroof hSafeRoof hkappa hrho hZBefore
      hX0card.le hX0roof
  refine ⟨Z, hX0Z, le_antisymm hZcard ?_, hH, hHlarge, hT,
    hYclosed, hroof⟩
  rw [← hX0card]
  exact Cardinal.mk_subtype_mono hX0Z

end Blueprint
end Erdos599
namespace Erdos599.CardinalInduction

open Cardinal Set
open DirectedPath

universe u

namespace Hybrid

variable {V : Type u} (Γ : DWeb V)

/-- The paths of a linkage whose initial vertices are selected. -/
def selectedPart (L : Set Γ.DPath) (A₀ : Set V) : Set Γ.DPath :=
  {p | p ∈ L ∧ p.initial ∈ A₀}

/-- Keep selected linkage paths, and stop every other source immediately. -/
def warp (L : Set Γ.DPath) (A₀ : Set V) : Set Γ.DPath :=
  selectedPart Γ L A₀ ∪ Γ.trivialPath '' (Γ.source \ A₀)

/-- The selected terminal vertices of the original linkage. -/
def terminals (L : Set Γ.DPath) (A₀ : Set V) : Set V :=
  Γ.terminalFrontier (selectedPart Γ L A₀)

/-- The hybrid stopover: unselected sources plus selected terminals. -/
def stopover (L : Set Γ.DPath) (A₀ : Set V) : Set V :=
  (Γ.source \ A₀) ∪ terminals Γ L A₀

@[simp] theorem mem_selectedPart {L : Set Γ.DPath} {A₀ : Set V} {p : Γ.DPath} :
    p ∈ selectedPart Γ L A₀ ↔ p ∈ L ∧ p.initial ∈ A₀ :=
  Iff.rfl

theorem source_mem_support_eq_initial {L : Set Γ.DPath}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L)
    {p : Γ.DPath} (hp : p ∈ L) {x : V}
    (hxp : x ∈ p.support) (hxA : x ∈ Γ.source) : x = p.initial := by
  obtain ⟨q, rfl, -, hsource⟩ := hL.endpointPure p hp
  have hxinter : x ∈ q.support ∩ Γ.source := ⟨hxp, hxA⟩
  rw [hsource] at hxinter
  change x = q.start
  simpa using hxinter

theorem warp_isWarp {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L) :
    Γ.IsWarp (warp Γ L A₀) := by
  intro p hp q hq hpq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact hL.isWarp hp.1 hq.1 hpq
  · rcases hq with ⟨b, hb, rfl⟩
    change Disjoint p.support (Γ.trivialPath b).support
    rw [Γ.support_trivialPath]
    apply Set.disjoint_singleton_right.2
    intro hbp
    have hbeq : b = p.initial :=
      source_mem_support_eq_initial Γ hL hp.1 hbp hb.1
    exact hb.2 (hbeq ▸ hp.2)
  · rcases hp with ⟨a, ha, rfl⟩
    change Disjoint (Γ.trivialPath a).support q.support
    rw [Γ.support_trivialPath]
    apply Set.disjoint_singleton_left.2
    intro haq
    have haeq : a = q.initial :=
      source_mem_support_eq_initial Γ hL hq.1 haq ha.1
    exact ha.2 (haeq ▸ hq.2)
  · rcases hp with ⟨a, ha, rfl⟩
    rcases hq with ⟨b, hb, rfl⟩
    change Disjoint (Γ.trivialPath a).support (Γ.trivialPath b).support
    rw [Γ.support_trivialPath, Γ.support_trivialPath]
    apply Set.disjoint_singleton.2
    intro hab
    apply hpq
    subst b
    rfl

theorem warp_finiteCharacter {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L) :
    Γ.HasFiniteCharacter (warp Γ L A₀) := by
  intro p hp
  rcases hp with hp | ⟨a, ha, rfl⟩
  · exact hL.finiteCharacter hp.1
  · exact ⟨DirectedPath.FinitePath.trivial Γ.graph a, rfl⟩

theorem warp_initialSet {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L) :
    Γ.initialSet (warp Γ L A₀) = Γ.source := by
  ext a
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with hp | ⟨b, hb, rfl⟩
    · rw [← hL.initialSet_eq]
      exact ⟨p, hp.1, rfl⟩
    · simpa using hb.1
  · intro ha
    by_cases ha₀ : a ∈ A₀
    · rw [← hL.initialSet_eq] at ha
      obtain ⟨p, hp, hpa⟩ := ha
      refine ⟨p, Or.inl ⟨hp, ?_⟩, hpa⟩
      simpa [hpa] using ha₀
    · refine ⟨Γ.trivialPath a, Or.inr ⟨a, ⟨ha, ha₀⟩, rfl⟩, ?_⟩
      exact Γ.initial_trivialPath a

theorem warp_terminalFrontier_subset {L : Set Γ.DPath} {A₀ : Set V} :
    Γ.terminalFrontier (warp Γ L A₀) ⊆ stopover Γ L A₀ := by
  rintro x ⟨p, hp, hpx⟩
  rcases hp with hp | ⟨a, ha, rfl⟩
  · exact Or.inr ⟨p, hp, hpx⟩
  · left
    simp only [Γ.terminal?_trivialPath, Option.some.injEq] at hpx
    subst x
    exact ha

theorem stopover_subset_source_union_target {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L) :
    stopover Γ L A₀ ⊆ Γ.source ∪ Γ.target := by
  rintro x (hx | hx)
  · exact Or.inl hx.1
  · rcases hx with ⟨p, hp, hpx⟩
    exact Or.inr (hL.terminalFrontier_subset ⟨p, hp.1, hpx⟩)

theorem warp_endpointPure {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L) :
    ∀ p ∈ warp Γ L A₀,
      IsPathBetween Γ Γ.source (stopover Γ L A₀) p := by
  intro p hp
  rcases hp with hp | ⟨a, ha, rfl⟩
  · obtain ⟨q, rfl, hends, hsource⟩ := hL.endpointPure p hp.1
    have hstartA : q.start ∈ Γ.source := by
      rw [← hL.initialSet_eq]
      exact ⟨.inl q, hp.1, rfl⟩
    have hfinishC : q.finish ∈ stopover Γ L A₀ :=
      Or.inr ⟨.inl q, hp, rfl⟩
    refine ⟨q, rfl, ?_, hsource⟩
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hx⟩
      have hx' : x ∈ q.support ∩ (Γ.source ∪ Γ.target) :=
        ⟨hxq, hx.elim Or.inl
          (fun hxC => stopover_subset_source_union_target Γ hL hxC)⟩
      simpa [hends] using hx'
    · intro x hx
      have hxq : x ∈ q.support := by
        have hx' : x ∈ q.support ∩ (Γ.source ∪ Γ.target) := by
          rw [hends]
          exact hx
        exact hx'.1
      rcases hx with (rfl | rfl)
      · exact ⟨hxq, Or.inl hstartA⟩
      · exact ⟨hxq, Or.inr hfinishC⟩
  · refine ⟨DirectedPath.FinitePath.trivial Γ.graph a, rfl, ?_, ?_⟩
    · rw [DirectedPath.FinitePath.support_trivial]
      simp [ha.1]
    · rw [DirectedPath.FinitePath.support_trivial]
      simp [ha.1]

theorem warp_isLinkageBetween {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L) :
    IsLinkageBetween Γ Γ.source (stopover Γ L A₀) (warp Γ L A₀) :=
  ⟨warp_isWarp Γ hL, warp_finiteCharacter Γ hL,
    warp_initialSet Γ hL, warp_terminalFrontier_subset Γ,
    warp_endpointPure Γ hL⟩

theorem warp_linksToTarget {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L)
    (hA₀ : A₀ ⊆ Γ.source) :
    LinksToTarget Γ (warp Γ L A₀) A₀ := by
  intro a ha₀
  have haA : a ∈ Γ.initialSet L := hL.initialSet_eq.symm ▸ hA₀ ha₀
  obtain ⟨p, hpL, hpa⟩ := haA
  obtain ⟨q, rfl, -, hsource⟩ := hL.endpointPure p hpL
  change q.start = a at hpa
  have hqstart₀ : q.start ∈ A₀ := hpa ▸ ha₀
  have hpselected : (Sum.inl q : Γ.DPath) ∈ selectedPart Γ L A₀ := by
    refine ⟨hpL, ?_⟩
    exact hqstart₀
  refine ⟨.inl q, Or.inl hpselected, q, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hx₀⟩
      have hxsource : x ∈ q.support ∩ Γ.source := ⟨hxq, hA₀ hx₀⟩
      rw [hsource] at hxsource
      simpa [hpa] using hxsource
    · intro x hx
      have hxa : x = a := by simpa using hx
      subst x
      exact ⟨hpa ▸ q.start_mem_support, ha₀⟩
  · have hsupport : q.walk.support = q.start :: q.walk.support.tail := by
      have h := (List.cons_head_tail q.walk.support_ne_nil).symm
      simpa [q.walk.head_support] using h
    refine ⟨[], q.walk.support.tail, ?_, ?_⟩
    · simpa [hpa] using hsupport
    · have hfinishB : q.finish ∈ Γ.target :=
        hL.terminalFrontier_subset ⟨.inl q, hpL, rfl⟩
      have hfinishmem : q.finish ∈ q.start :: q.walk.support.tail := by
        rw [← hsupport]
        exact q.finish_mem_support
      exact ⟨q.finish, hfinishB, hpa ▸ hfinishmem⟩

theorem target_mem_essential {S : Set V} {b : V}
    (hbS : b ∈ S) (hbB : b ∈ Γ.target) : b ∈ Γ.essential S := by
  refine ⟨hbS, (Γ.not_mem_roof_iff (S \ {b}) b).2 ?_⟩
  let q := DirectedPath.FinitePath.trivial Γ.graph b
  refine ⟨q, ⟨rfl, hbB⟩, ?_⟩
  rw [Γ.avoids_iff_not_meets]
  rintro ⟨x, hxq, hxS, hxb⟩
  have hxb' : x = b := by
    simpa [q] using hxq
  exact hxb hxb'

theorem stopover_isTrimmed {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L) :
    IsTrimmedSeparator Γ (stopover Γ L A₀) := by
  apply Set.Subset.antisymm
  · exact Γ.essential_subset _
  · intro x hxC
    rcases hxC with hx | hx
    · have hxInitial : x ∈ Γ.initialSet L := hL.initialSet_eq.symm ▸ hx.1
      obtain ⟨p, hpL, hpx⟩ := hxInitial
      obtain ⟨q, rfl, -, -⟩ := hL.endpointPure p hpL
      change q.start = x at hpx
      refine ⟨Or.inl hx, (Γ.not_mem_roof_iff
        (stopover Γ L A₀ \ {x}) x).2 ?_⟩
      have hfinishB : q.finish ∈ Γ.target :=
        hL.terminalFrontier_subset ⟨.inl q, hpL, rfl⟩
      refine ⟨q, ⟨hpx, hfinishB⟩, ?_⟩
      apply Set.disjoint_left.2
      intro y hyq hyC
      rcases hyC.1 with hyA | hyT
      · have hyx : y = x := by
          have hyqstart :=
            source_mem_support_eq_initial Γ hL hpL hyq hyA.1
          change y = q.start at hyqstart
          calc
            y = q.start := hyqstart
            _ = x := hpx
        exact hyC.2 (by simp [hyx])
      · rcases hyT with ⟨r, hr, hry⟩
        have hyr : y ∈ r.support := Γ.terminal_mem_support hry
        by_cases hrq : r = (Sum.inl q : Γ.DPath)
        · subst r
          have hqselected := (mem_selectedPart Γ).1 hr
          have hq₀ := hqselected.2
          change q.start ∈ A₀ at hq₀
          have hqx₀ : x ∈ A₀ := by
            exact hpx ▸ hq₀
          exact hx.2 hqx₀
        · exact Set.disjoint_left.1 (hL.isWarp hr.1 hpL hrq) hyr hyq
    · rcases hx with ⟨p, hp, hpx⟩
      exact target_mem_essential Γ (Or.inr ⟨p, hp, hpx⟩)
        (hL.terminalFrontier_subset ⟨p, hp.1, hpx⟩)

/-- A selected terminal has a canonical selected path ending there. -/
noncomputable def terminalPath {L : Set Γ.DPath} {A₀ : Set V}
    (t : terminals Γ L A₀) : Γ.DPath :=
  Classical.choose t.2

theorem terminalPath_spec {L : Set Γ.DPath} {A₀ : Set V}
    (t : terminals Γ L A₀) :
    terminalPath Γ t ∈ selectedPart Γ L A₀ ∧
      (terminalPath Γ t).terminal? = some (t : V) :=
  Classical.choose_spec t.2

/-- Send each selected terminal to the initial vertex of its selected path. -/
noncomputable def terminalInitial {L : Set Γ.DPath} {A₀ : Set V}
    (t : terminals Γ L A₀) : A₀ :=
  ⟨(terminalPath Γ t).initial, (terminalPath_spec Γ t).1.2⟩

theorem terminalInitial_injective {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L) :
    Function.Injective (terminalInitial Γ (L := L) (A₀ := A₀)) := by
  intro s t hst
  have hinitial : (terminalPath Γ s).initial =
      (terminalPath Γ t).initial :=
    congrArg Subtype.val hst
  have hpath : terminalPath Γ s = terminalPath Γ t := by
    by_contra hne
    have hd := hL.isWarp
      (terminalPath_spec Γ s).1.1
      (terminalPath_spec Γ t).1.1 hne
    exact Set.disjoint_left.1 hd
      (terminalPath Γ s).initial_mem_support
      (hinitial ▸ (terminalPath Γ t).initial_mem_support)
  apply Subtype.ext
  exact Option.some.inj <| calc
    some (s : V) = (terminalPath Γ s).terminal? :=
      (terminalPath_spec Γ s).2.symm
    _ = (terminalPath Γ t).terminal? :=
      congrArg (fun p : Γ.DPath => p.terminal?) hpath
    _ = some (t : V) := (terminalPath_spec Γ t).2

theorem mk_terminals_le {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L) :
    #(terminals Γ L A₀) ≤ #A₀ :=
  Cardinal.mk_le_of_injective (terminalInitial_injective Γ hL)

theorem stopover_subset_source_union_nonSourceTerminals
    {L : Set Γ.DPath} {A₀ : Set V} :
    stopover Γ L A₀ ⊆
      Γ.source ∪ (terminals Γ L A₀ \ Γ.source) := by
  rintro x (hx | hx)
  · exact Or.inl hx.1
  · by_cases hxA : x ∈ Γ.source
    · exact Or.inl hxA
    · exact Or.inr ⟨hx, hxA⟩

/-- The non-source selected terminals witness height at most `#A₀`. -/
theorem stopover_heightAtMost {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L) :
    HeightAtMost Γ (stopover Γ L A₀) (#A₀) := by
  let X : Set V := terminals Γ L A₀ \ Γ.source
  refine ⟨X, ?_, ?_⟩
  · refine ⟨?_, (Γ.quotient X).trivialWave,
      (Γ.quotient X).isWave_trivialWave, ?_⟩
    · dsimp [X]
      exact Set.sdiff_subset_compl _ _
    · rw [(Γ.quotient X).terminalFrontier_trivialWave,
        DWeb.quotient_source, Γ.roof_essential]
      exact (stopover_subset_source_union_nonSourceTerminals Γ).trans
        (Γ.subset_roof (Γ.source ∪ X))
  · exact (Cardinal.mk_le_mk_of_subset Set.sdiff_subset).trans
      (mk_terminals_le Γ hL)

/-- Hybrid factorization of a full endpoint-pure linkage.  The only
additional premise is precisely the quotient-unhindered condition that is
not implied by unhinderedness of the original web for an arbitrary full
linkage. -/
theorem halfwayLinkageOfAltitude_hybrid {L : Set Γ.DPath} {A₀ : Set V}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L)
    (hA₀ : A₀ ⊆ Γ.source)
    (hquot : (Γ.quotient (stopover Γ L A₀)).IsUnhindered) :
    IsHalfwayLinkageOfAltitude Γ A₀ (#A₀) (warp Γ L A₀) := by
  apply halfwayLinkageOfAltitude_of_stopover
  · exact
      { linkage := warp_isLinkageBetween Γ hL
        minimal := stopover_isTrimmed Γ hL
        quotient_unhindered := hquot }
  · exact warp_linksToTarget Γ hL hA₀
  · exact stopover_heightAtMost Γ hL

/-- Cardinal-renamed form of the hybrid factorization. -/
theorem halfwayLinkageOfAltitude_hybrid_of_mk_le {L : Set Γ.DPath}
    {A₀ : Set V} {κ : Cardinal.{u}}
    (hL : IsLinkageBetween Γ Γ.source Γ.target L)
    (hA₀ : A₀ ⊆ Γ.source)
    (hquot : (Γ.quotient (stopover Γ L A₀)).IsUnhindered)
    (hcard : #A₀ ≤ κ) :
    IsHalfwayLinkageOfAltitude Γ A₀ κ (warp Γ L A₀) := by
  apply halfwayLinkageOfAltitude_of_stopover
  · exact
      { linkage := warp_isLinkageBetween Γ hL
        minimal := stopover_isTrimmed Γ hL
        quotient_unhindered := hquot }
  · exact warp_linksToTarget Γ hL hA₀
  · exact HeightAtMost.mono_card hcard (stopover_heightAtMost Γ hL)

end Hybrid

end Erdos599.CardinalInduction

namespace Erdos599
namespace Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Γ : DWeb V} {Y : Set Γ.DPath} {κ : Cardinal.{u}}

namespace LinkageBlueprint

/-- Literal conclusion of source Assertion 9.30.  In particular, it has no
parameter `B` and does not claim the later relation (9.32). -/
def SourceContinuationConclusion
    (W cut U : LinkageBlueprint Γ Y κ) (u : V) (T : Set V) : Prop :=
  cut.OrdinaryExtends U ∧ U.RealLinksTo u T ∧
    W.realPart.terminals ⊆ U.realPart.terminals ∪ {u}

/-- The exact first case split in the proof of source Assertion 9.30.  A
terminal of the real part is either already a terminal of the whole
blueprint, or its next blueprint edge is imaginary. -/
theorem real_terminal_is_terminal_or_has_imaginary_edge
    {W : LinkageBlueprint Γ Y κ} {u : V}
    (hu : u ∈ W.realPart.terminals) :
    u ∈ W.terminalSet ∨ ∃ v, IsImaginaryEdge Γ Y κ u v := by
  by_cases hut : u ∈ W.terminalSet
  · exact Or.inl hut
  · right
    obtain ⟨v, huv⟩ :=
      W.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet hu.1 hut
    refine ⟨v, ?_⟩
    have hadj : (imaginaryGraph Γ Y κ).Adj u v := by
      rcases Set.mem_iUnion.1 huv with ⟨p, huv⟩
      rcases Set.mem_iUnion.1 huv with ⟨hpW, hpedge⟩
      exact p.edgeSet_subset_adj hpedge
    rcases hadj with horiginal | himaginary
    · exact False.elim <| hu.2 ⟨v,
        W.mem_realPart_of_mem_edgeSet_of_original huv horiginal⟩
    · exact himaginary

/-- In the terminal branch, the blueprint terminal condition gives exactly
the large infinity hammock used by source Assertion 9.30, provided the
persistent set is known to lie in the current ladder slice. -/
theorem terminal_outside_slice_has_infinite_hammock
    {W : LinkageBlueprint Γ Y κ} {u : V} {T Z persistent : Set V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hpersistent : persistent ⊆ T)
    (huterm : u ∈ W.terminalSet) (huT : u ∉ T) :
    HasHammockCard Γ Y u .infinity (succ κ) := by
  rcases hW.terminals_popular huterm with hpopular | huT'
  · rcases hpopular with hupersistent | hhammock
    · exact False.elim (huT (hpersistent hupersistent))
    · exact hhammock
  · exact False.elim (huT huT')

/-- The branch of source Assertion 9.30 in which the chosen real terminal
already belongs to the current ladder slice.  In this branch the unchanged
blueprint is the required continuation. -/
theorem exists_continuation_of_mem_slice
    {W : LinkageBlueprint Γ Y κ} {u : V} {T Z persistent : Set V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (huterm : u ∈ W.terminalSet) (huT : u ∈ T) :
    ∃ U : LinkageBlueprint Γ Y κ,
      U.IsLinkageBlueprint T Z persistent ∧
        ContinuationConclusion W W U u T := by
  refine ⟨W, hW, W.isCutAt_self_of_mem_terminalSet huterm,
    ordinaryExtends_refl W, ?_, ?_⟩
  · let p : DirectedPath.FinitePath Γ.graph :=
      DirectedPath.FinitePath.trivial Γ.graph u
    refine ⟨p, rfl, huT, ?_, ?_⟩
    · have huvertex : u ∈ W.vertexSet := by
        rcases huterm with ⟨q, hqW, hqterm⟩
        exact ⟨q, hqW, q.terminal_mem_support u hqterm⟩
      simpa [p, LinkageBlueprint.realPart] using huvertex
    · simp [p, DirectedPath.FinitePath.edgeSet]
  · intro x hx
    exact hx.1

/-- The same already-in-the-slice branch, stated with the literal source
conclusion rather than the stronger current project predicate. -/
theorem exists_source_continuation_of_mem_slice
    {W : LinkageBlueprint Γ Y κ} {u : V} {T Z persistent : Set V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hu : u ∈ W.realPart.terminals) (huT : u ∈ T) :
    ∃ U : LinkageBlueprint Γ Y κ,
      U.IsLinkageBlueprint T Z persistent ∧
        SourceContinuationConclusion W W U u T := by
  refine ⟨W, hW, ordinaryExtends_refl W, ?_, fun _ hx ↦ Or.inl hx⟩
  let p : DirectedPath.FinitePath Γ.graph :=
    DirectedPath.FinitePath.trivial Γ.graph u
  refine ⟨p, rfl, huT, ?_, ?_⟩
  · simpa [p, LinkageBlueprint.realPart] using
      (show u ∈ W.vertexSet from hu.1)
  · simp [p, DirectedPath.FinitePath.edgeSet]

/-- A current continuation can never link a vertex to the empty slice.
This records the missing-ladder-hypothesis obstruction independently of
any particular graph. -/
theorem not_continuationConclusion_empty
    (W cut U : LinkageBlueprint Γ Y κ) (u : V) :
    ¬ ContinuationConclusion W cut U u ∅ := by
  intro h
  rcases h.links with ⟨p, _hpstart, hpfinish, _hpsupport, _hpedge⟩
  exact hpfinish

end LinkageBlueprint

/-! A concrete sanity check: `IsLinkageBlueprint` plus a formally vacuous
instance of the current hammock-closure predicate does not imply Assertion
9.30.  The missing ladder compatibility (`persistent ⊆ T`) is essential. -/

private def emptyUnitWeb : DWeb Unit where
  graph := ⟨fun _ _ ↦ False⟩
  source := ∅
  target := ∅

private def singletonUnitBlueprint :
    LinkageBlueprint emptyUnitWeb ∅ ℵ₀ where
  paths := {DirectedPath.Path.trivial
    (imaginaryGraph emptyUnitWeb ∅ ℵ₀) ()}
  isWarp := Set.pairwiseDisjoint_singleton _ _

private theorem singletonUnitBlueprint_isLB :
    singletonUnitBlueprint.IsLinkageBlueprint ∅ Set.univ Set.univ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx p hp
    exact False.elim hp.2
  · simp [emptyUnitWeb]
  · exact fun _ _ ↦ Set.mem_univ _
  · change #({DirectedPath.Path.trivial
      (imaginaryGraph emptyUnitWeb ∅ ℵ₀) ()} :
        Set (DirectedPath.Path (imaginaryGraph emptyUnitWeb ∅ ℵ₀))) ≤ ℵ₀
    simp
  · intro r hr
    have : False := by
      simpa [singletonUnitBlueprint, DirectedPath.Path.trivial] using hr
    exact this.elim
  · intro x hx
    exact Or.inl (Or.inl (Set.mem_univ x))

private theorem unit_real_terminal :
    () ∈ singletonUnitBlueprint.realPart.terminals := by
  constructor
  · refine ⟨DirectedPath.Path.trivial
      (imaginaryGraph emptyUnitWeb ∅ ℵ₀) (), ?_, ?_⟩
    · exact Set.mem_singleton _
    · exact DirectedPath.Path.terminal_mem_support _ () rfl
  · rintro ⟨v, hv⟩
    rcases hv with ⟨hvW, _hvadj⟩
    rcases Set.mem_iUnion.1 hvW with ⟨p, hvW⟩
    rcases Set.mem_iUnion.1 hvW with ⟨hp, hpedge⟩
    simp only [singletonUnitBlueprint, Set.mem_singleton_iff] at hp
    subst p
    simpa [DirectedPath.Path.trivial, DirectedPath.FinitePath.trivial,
      DirectedPath.FinitePath.edgeSet] using hpedge

private theorem vacuous_hammock_closure :
    HammockClosedUpTo emptyUnitWeb ∅ Set.univ ∅ Set.univ Set.univ ℵ₀ := by
  intro u e helig
  exact False.elim helig.1.1

/-- Exact counterexample to deriving `ContinuationConclusion` from the two
currently available high-level hypotheses alone. -/
theorem current_api_hypotheses_do_not_imply_assertion930 :
    singletonUnitBlueprint.IsLinkageBlueprint ∅ Set.univ Set.univ ∧
      () ∈ singletonUnitBlueprint.realPart.terminals ∧
      HammockClosedUpTo emptyUnitWeb ∅ Set.univ ∅ Set.univ Set.univ ℵ₀ ∧
      ¬ ∃ U : LinkageBlueprint emptyUnitWeb ∅ ℵ₀,
        U.IsLinkageBlueprint ∅ Set.univ Set.univ ∧
          LinkageBlueprint.ContinuationConclusion
            singletonUnitBlueprint singletonUnitBlueprint U () ∅ := by
  refine ⟨singletonUnitBlueprint_isLB, unit_real_terminal,
    vacuous_hammock_closure, ?_⟩
  rintro ⟨U, _hU, hcontinuation⟩
  exact LinkageBlueprint.not_continuationConclusion_empty
    singletonUnitBlueprint singletonUnitBlueprint U () hcontinuation

end Blueprint
end Erdos599

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath

universe u v

variable {V : Type u}
variable {Γ : DWeb V} {Y : Set Γ.DPath} {κ : Cardinal.{u}}

/--
The stable-limit assertion for the concrete `limit` representation currently
used by `Blueprint.lean`.

`paths_monotone` is the representation-level coherence invariant: since
`limit` takes the set liminf of *whole path values*, a path which is to
survive must remain literally present at all later stages.  `union_card` is
the independent cardinal bookkeeping invariant supplied by the outer
recursion (the union of the stage path sets still has size at most `κ`).
Neither hypothesis mentions the proposed limit's blueprint, stability, or
real-extension conclusions.
-/
theorem stableLimitConclusion_limit_of_monotone
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (stage : I → LinkageBlueprint Γ Y κ)
    (T Z persistent B : Set V)
    (paths_monotone : Monotone fun i ↦ (stage i).paths)
    (union_card : #(⋃ i, (stage i).paths) ≤ κ)
    (reference_isWarp : Γ.IsWarp Y)
    (isBlueprint : ∀ i, (stage i).IsLinkageBlueprint T Z persistent)
    (stable : ∀ i, (stage i).Stable T persistent) :
    StableLimitConclusion stage (limit stage) T Z persistent B := by
  let L : LinkageBlueprint Γ Y κ := limit stage
  have paths_eq : L.paths = ⋃ i, (stage i).paths := by
    change WarpLimits.setLiminf (fun i ↦ (stage i).paths) = _
    exact WarpLimits.setLiminf_eq_iUnion_of_monotone paths_monotone
  have stage_paths_subset (i : I) : (stage i).paths ⊆ L.paths := by
    rw [paths_eq]
    exact Set.subset_iUnion (fun j ↦ (stage j).paths) i
  have stage_vertices_subset (i : I) :
      (stage i).vertexSet ⊆ L.vertexSet := by
    rintro x ⟨p, hp, hxp⟩
    exact ⟨p, stage_paths_subset i hp, hxp⟩
  have stage_initials_subset (i : I) :
      (stage i).initialSet ⊆ L.initialSet := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨p, stage_paths_subset i hp, rfl⟩
  have stage_terminals_subset (i : I) :
      (stage i).terminalSet ⊆ L.terminalSet := by
    rintro x ⟨p, hp, hpx⟩
    exact ⟨p, stage_paths_subset i hp, hpx⟩
  have stage_edges_subset (i : I) :
      (stage i).edgeSet ⊆ L.edgeSet := by
    intro e he
    simp only [edgeSet, Set.mem_iUnion] at he ⊢
    obtain ⟨p, hpstage, hep⟩ := he
    exact ⟨p, stage_paths_subset i hpstage, hep⟩
  have limit_path_at_stage {p : DirectedPath.Path (imaginaryGraph Γ Y κ)}
      (hp : p ∈ L.paths) : ∃ i, p ∈ (stage i).paths := by
    rw [paths_eq] at hp
    exact Set.mem_iUnion.1 hp
  have limit_isBlueprint : L.IsLinkageBlueprint T Z persistent := by
    refine
      { vertices_roofed := ?_
        covers_source := ?_
        vertices_closed := ?_
        card_paths := ?_
        infinitely_many_strong := ?_
        terminals_popular := ?_ }
    · rintro x ⟨p, hpL, hxp⟩
      obtain ⟨i, hpi⟩ := limit_path_at_stage hpL
      exact (isBlueprint i).vertices_roofed ⟨p, hpi, hxp⟩
    · intro a ha
      let i0 : I := Classical.choice inferInstance
      rcases (isBlueprint i0).covers_source ha with hinitial | hretained
      · exact Or.inl (stage_initials_subset i0 hinitial)
      · rcases hretained with ⟨p, hpDiff, hpinitial⟩
        rcases hpDiff with ⟨hpT, hpnoti0⟩
        by_cases hpmeetL : (p.support ∩ L.vertexSet).Nonempty
        · obtain ⟨x, hxp, hxL⟩ := hpmeetL
          obtain ⟨q, hqL, hxq⟩ := hxL
          obtain ⟨j, hqj⟩ := limit_path_at_stage hqL
          obtain ⟨k, _hi0k, hjk⟩ := exists_ge_ge i0 j
          have hxk : x ∈ (stage k).vertexSet :=
            ⟨q, paths_monotone hjk hqj, hxq⟩
          rcases (isBlueprint k).covers_source ha with hkinitial | hkretained
          · exact Or.inl (stage_initials_subset k hkinitial)
          · rcases hkretained with ⟨r, hrDiff, hrinitial⟩
            rcases hrDiff with ⟨hrT, hrnotk⟩
            have hrp : r = p := by
              by_contra hrp
              have hdrp := reference_isWarp hrT.1 hpT.1 hrp
              have har : a ∈ r.support := by
                rw [← hrinitial]
                exact r.initial_mem_support
              have hap : a ∈ p.support := by
                rw [← hpinitial]
                exact p.initial_mem_support
              exact (Set.disjoint_left.1 hdrp har hap).elim
            subst r
            exact (hrnotk ⟨hpT.1, ⟨x, hxp, hxk⟩⟩).elim
        · exact Or.inr
            ⟨p, ⟨hpT, fun hpL ↦ hpmeetL hpL.2⟩, hpinitial⟩
    · rintro x ⟨p, hpL, hxp⟩
      obtain ⟨i, hpi⟩ := limit_path_at_stage hpL
      exact (isBlueprint i).vertices_closed ⟨p, hpi, hxp⟩
    · rw [paths_eq]
      exact union_card
    · intro r hr
      obtain ⟨i, hri⟩ := limit_path_at_stage hr
      exact (isBlueprint i).infinitely_many_strong r hri
    · rintro x ⟨p, hpL, hpx⟩
      obtain ⟨i, hpi⟩ := limit_path_at_stage hpL
      exact (isBlueprint i).terminals_popular ⟨p, hpi, hpx⟩
  have limit_stable : L.Stable T persistent := by
    rintro x ⟨⟨p, hpL, hpx⟩, hxT⟩
    obtain ⟨i, hpi⟩ := limit_path_at_stage hpL
    exact stable i ⟨⟨p, hpi, hpx⟩, hxT⟩
  refine ⟨limit_isBlueprint, limit_stable, ?_⟩
  intro i
  constructor
  · constructor
    · exact stage_vertices_subset i
    · intro e he
      exact stage_edges_subset i he.1 |> fun h ↦ ⟨h, he.2⟩
  · intro x hx
    by_cases hxterm : x ∈ (stage i).terminalSet
    · exact Or.inl (Or.inl ⟨stage_terminals_subset i hxterm, hxterm⟩)
    · obtain ⟨y, hy⟩ :=
        (stage i).exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
          hx hxterm
      exact Or.inl (Or.inr ⟨y, hy, stage_edges_subset i hy⟩)

end Erdos599.Blueprint.LinkageBlueprint

namespace Erdos599
namespace Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u}

namespace Assertion931

variable {Γ : DWeb V} {Y : Set Γ.DPath} {κ : Cardinal.{u}}

/-! The graph-lift used in Assertion 9.31 preserves the traversed edges,
not only the support.  This elementary API is absent upstream. -/

theorem walk_edgeSet_lift {D E : Digraph V}
    (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) {a b : V}
    (p : Walk D a b) : (p.lift hDE).edgeSet = p.edgeSet := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [Walk.lift, Walk.edgeSet_cons, ih]

theorem finitePath_edgeSet_lift {D E : Digraph V}
    (hDE : ∀ {x y}, D.Adj x y → E.Adj x y)
    (p : FinitePath D) : (p.lift hDE).edgeSet = p.edgeSet := by
  exact walk_edgeSet_lift hDE p.walk

/-- Lift an original finite path to the imaginary-edge augmentation. -/
def liftOriginal (p : FinitePath Γ.graph) :
    FinitePath (imaginaryGraph Γ Y κ) :=
  p.lift (fun h => original_adj_imaginaryGraph h)

@[simp] theorem liftOriginal_start (p : FinitePath Γ.graph) :
    (liftOriginal (Y := Y) (κ := κ) p).start = p.start := rfl

@[simp] theorem liftOriginal_finish (p : FinitePath Γ.graph) :
    (liftOriginal (Y := Y) (κ := κ) p).finish = p.finish := rfl

@[simp] theorem liftOriginal_support (p : FinitePath Γ.graph) :
    (liftOriginal (Y := Y) (κ := κ) p).support = p.support :=
  FinitePath.support_lift _ p

@[simp] theorem liftOriginal_edgeSet (p : FinitePath Γ.graph) :
    (liftOriginal (Y := Y) (κ := κ) p).edgeSet = p.edgeSet :=
  finitePath_edgeSet_lift _ p

/-- Raw data of the path family produced after the fractured-warp safe
assignment has been compiled into actual paths of `D ∪ IE`.  Its fields are
the local obligations established in the source proof, stated on the raw
path set rather than on a pre-existing result blueprint. -/
structure DerivedPathFamily (W : LinkageBlueprint Γ Y κ)
    (z : V) (Told Tnew Z persistent B : Set V) where
  paths : Set (Path (imaginaryGraph Γ Y κ))
  isWarp : (imaginaryWeb Γ Y κ).IsWarp paths
  vertices_roofed : (imaginaryWeb Γ Y κ).vertexSet paths ⊆ Γ.roof Tnew
  covers_source : Γ.source ⊆
    (imaginaryWeb Γ Y κ).initialSet paths ∪
      Γ.initialSet
        (LinkageBlueprint.referencePathsMeeting Y Tnew \
          LinkageBlueprint.referencePathsMeeting Y
            ((imaginaryWeb Γ Y κ).vertexSet paths))
  vertices_closed : (imaginaryWeb Γ Y κ).vertexSet paths ⊆ Z
  card_paths : #paths ≤ κ
  infinitely_many_strong :
    ∀ r : Ray (imaginaryGraph Γ Y κ),
      (Sum.inr r : Path (imaginaryGraph Γ Y κ)) ∈ paths →
        (LinkageBlueprint.strongEdgeIndices r).Infinite
  terminals_popular : (imaginaryWeb Γ Y κ).terminalFrontier paths ⊆
    {u | IsPopular Γ Y persistent κ u} ∪ Tnew
  stable : (imaginaryWeb Γ Y κ).terminalFrontier paths ∩ Tnew ⊆ persistent
  ordinary_extends_vertices :
    W.vertexSet ⊆ (imaginaryWeb Γ Y κ).vertexSet paths
  ordinary_extends_edges : W.edgeSet ⊆ ⋃ p ∈ paths, p.edgeSet
  targetPath : FinitePath Γ.graph
  targetPath_start : targetPath.start = z
  targetPath_finish : targetPath.finish ∈ B
  targetPath_vertices :
    targetPath.support ⊆ (imaginaryWeb Γ Y κ).vertexSet paths
  targetPath_edges :
    targetPath.edgeSet ⊆ ⋃ p ∈ paths, p.edgeSet
  preserves_real_terminals :
    W.realPart.terminals ⊆
      (FamilyGraph.terminals {
        vertices := (imaginaryWeb Γ Y κ).vertexSet paths
        edges := (⋃ p ∈ paths, p.edgeSet) ∩
          {e | Γ.graph.Adj e.1 e.2} }) ∪ Told
  preserves_persistent_terminals :
    W.terminalSet ∩ persistent ⊆
      (imaginaryWeb Γ Y κ).terminalFrontier paths ∪ {z}

/-- Bundle the compiled path family.  This is a construction, rather than a
result blueprint supplied as a hypothesis. -/
def DerivedPathFamily.blueprint
    {W : LinkageBlueprint Γ Y κ} {z : V} {Told Tnew Z persistent B : Set V}
    (D : DerivedPathFamily W z Told Tnew Z persistent B) :
    LinkageBlueprint Γ Y κ where
  paths := D.paths
  isWarp := D.isWarp

@[simp] theorem DerivedPathFamily.blueprint_paths
    {W : LinkageBlueprint Γ Y κ} {z : V} {Told Tnew Z persistent B : Set V}
    (D : DerivedPathFamily W z Told Tnew Z persistent B) :
    D.blueprint.paths = D.paths := rfl

theorem DerivedPathFamily.isLinkageBlueprint
    {W : LinkageBlueprint Γ Y κ} {z : V} {Told Tnew Z persistent B : Set V}
    (D : DerivedPathFamily W z Told Tnew Z persistent B) :
    D.blueprint.IsLinkageBlueprint Tnew Z persistent := by
  exact {
    vertices_roofed := D.vertices_roofed
    covers_source := D.covers_source
    vertices_closed := D.vertices_closed
    card_paths := D.card_paths
    infinitely_many_strong := D.infinitely_many_strong
    terminals_popular := D.terminals_popular }

theorem DerivedPathFamily.isStable
    {W : LinkageBlueprint Γ Y κ} {z : V} {Told Tnew Z persistent B : Set V}
    (D : DerivedPathFamily W z Told Tnew Z persistent B) :
    D.blueprint.Stable Tnew persistent :=
  D.stable

theorem DerivedPathFamily.ordinaryExtends
    {W : LinkageBlueprint Γ Y κ} {z : V} {Told Tnew Z persistent B : Set V}
    (D : DerivedPathFamily W z Told Tnew Z persistent B) :
    W.OrdinaryExtends D.blueprint :=
  ⟨D.ordinary_extends_vertices, D.ordinary_extends_edges⟩

theorem DerivedPathFamily.realLinksTo
    {W : LinkageBlueprint Γ Y κ} {z : V} {Told Tnew Z persistent B : Set V}
    (D : DerivedPathFamily W z Told Tnew Z persistent B) :
    D.blueprint.RealLinksTo z B := by
  refine ⟨D.targetPath, D.targetPath_start, D.targetPath_finish, ?_, ?_⟩
  · exact D.targetPath_vertices
  · intro e he
    refine ⟨?_, D.targetPath.edgeSet_subset_adj he⟩
    exact D.targetPath_edges he

theorem DerivedPathFamily.advanceConclusion
    {W : LinkageBlueprint Γ Y κ} {z : V} {Told Tnew Z persistent B : Set V}
    (D : DerivedPathFamily W z Told Tnew Z persistent B) :
    LinkageBlueprint.AdvanceConclusion W D.blueprint z Told persistent B := by
  refine ⟨D.ordinaryExtends, D.realLinksTo, ?_,
    D.preserves_persistent_terminals⟩
  simpa [DerivedPathFamily.blueprint, LinkageBlueprint.realPart,
    LinkageBlueprint.vertexSet, LinkageBlueprint.edgeSet] using
      D.preserves_real_terminals

/-- The fully checked final assembly of Assertion 9.31 once its source
construction has produced the raw family and discharged the local
closure/safe-assignment obligations. -/
theorem assertion931_of_derivedPathFamily
    {W : LinkageBlueprint Γ Y κ} {z : V} {Told Tnew Z persistent B : Set V}
    (D : DerivedPathFamily W z Told Tnew Z persistent B) :
    ∃ U : LinkageBlueprint Γ Y κ,
      U.IsLinkageBlueprint Tnew Z persistent ∧
      U.Stable Tnew persistent ∧
      LinkageBlueprint.AdvanceConclusion W U z Told persistent B := by
  exact ⟨D.blueprint, D.isLinkageBlueprint, D.isStable, D.advanceConclusion⟩

end Assertion931
end Blueprint
end Erdos599

namespace Erdos599
namespace Blueprint

open DirectedPath

universe u v

variable {V : Type u}

/-- A walk reinterpreted in the digraph whose edges are precisely `E`. -/
structure EdgeRestrictedWalk {D : Digraph V} (E : Set (V × V))
    {a b : V} (p : Walk D a b) where
  walk : Walk (RelationalRoof.relationDigraph (fun x y ↦ (x, y) ∈ E)) a b
  support_eq : walk.support = p.support
  edgeSet_eq : walk.edgeSet = p.edgeSet

/-- Reinterpret a walk in an edge-subgraph, preserving its ordered support
and its edge set definitionally up to the displayed equalities. -/
def restrictWalkEdges {D : Digraph V} (E : Set (V × V)) :
    ∀ {a b : V} (p : Walk D a b), p.edgeSet ⊆ E → EdgeRestrictedWalk E p
  | _, _, .nil, _ => ⟨.nil, rfl, rfl⟩
  | _, _, .cons (u := a) (v := c) h p, hE => by
      have htail : p.edgeSet ⊆ E := fun e he ↦ hE (by simp [he])
      let q := restrictWalkEdges E p htail
      refine ⟨Walk.cons (hE (by simp)) q.walk, ?_, ?_⟩
      · exact congrArg (List.cons a) q.support_eq
      · simp only [Walk.edgeSet_cons]
        exact congrArg (fun s ↦ {(a, c)} ∪ s) q.edgeSet_eq

@[simp] theorem edgeSet_liftWalk {D E : Digraph V}
    (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) :
    ∀ {a b : V} (p : Walk D a b), (p.lift hDE).edgeSet = p.edgeSet := by
  intro a b p
  induction p with
  | nil => rfl
  | cons h p ih => simp [Walk.lift, ih]

namespace LinkageBlueprint

variable {Γ : DWeb V} {Y : Set Γ.DPath} {κ : Cardinal.{u}}

/-- Real reachability is transitive inside a fixed blueprint.  The proof
forms a walk in the relation of real blueprint edges and then erases loops. -/
theorem realLinksTo_trans {U : LinkageBlueprint Γ Y κ}
    {u z : V} {B : Set V}
    (huz : U.RealLinksTo u {z}) (hzB : U.RealLinksTo z B) :
    U.RealLinksTo u B := by
  rcases huz with ⟨p, hpstart, hpfinish, hpsupport, hpedge⟩
  rcases hzB with ⟨q, hqstart, hqfinish, hqsupport, hqedge⟩
  have hpfinish' : p.finish = z := by simpa using hpfinish
  let pE := (restrictWalkEdges U.realPart.edges p.walk hpedge).walk
  let qE := (restrictWalkEdges U.realPart.edges q.walk hqedge).walk
  let qE' : Walk (RelationalRoof.relationDigraph
      (fun x y ↦ (x, y) ∈ U.realPart.edges)) p.finish q.finish :=
    RelationalRoof.castStart _ (hqstart.trans hpfinish'.symm) qE
  let r := pE.append qE'
  obtain ⟨s, hs⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := fun x y ↦ (x, y) ∈ U.realPart.edges) r
  let s' : FinitePath Γ.graph :=
    { start := p.start
      finish := q.finish
      walk := s.1.lift (fun h ↦ U.realPart_edges_are_original h)
      isPath := Walk.isPath_lift _ s.2 }
  refine ⟨s', hpstart, hqfinish, ?_, ?_⟩
  · intro x hx
    have hxs : x ∈ s.1.support := by
      change x ∈ (s.1.lift (fun h ↦ U.realPart_edges_are_original h)).support at hx
      simpa only [Walk.support_lift] using hx
    have hxr : x ∈ r.support := hs hxs
    rw [Walk.support_append] at hxr
    rcases List.mem_append.1 hxr with hxp | hxq
    · apply hpsupport
      change x ∈ p.walk.support
      simpa only [pE, (restrictWalkEdges U.realPart.edges p.walk hpedge).support_eq] using hxp
    · apply hqsupport
      have hxq' : x ∈ qE'.support := List.mem_of_mem_tail hxq
      change x ∈ q.walk.support
      simpa only [qE', RelationalRoof.support_castStart, qE,
        (restrictWalkEdges U.realPart.edges q.walk hqedge).support_eq] using hxq'
  · intro e he
    have he' : e ∈ s.1.edgeSet := by
      change e ∈ (s.1.lift (fun h ↦ U.realPart_edges_are_original h)).edgeSet at he
      simpa only [edgeSet_liftWalk] using he
    exact s.1.edgeSet_subset_adj he'

/-- Monotonicity of real reachability under inclusion of real family graphs. -/
theorem realLinksTo_mono {W U : LinkageBlueprint Γ Y κ}
    {u : V} {B : Set V} (hWU : W.realPart.Extends U.realPart)
    (h : W.RealLinksTo u B) : U.RealLinksTo u B := by
  rcases h with ⟨p, hpstart, hpfinish, hpsupport, hpedges⟩
  exact ⟨p, hpstart, hpfinish, hpsupport.trans hWU.1, hpedges.trans hWU.2⟩

/-- Monotonicity of completed real vertices under inclusion of real parts. -/
theorem completedRealVertices_mono {W U : LinkageBlueprint Γ Y κ}
    {B : Set V} (hWU : W.realPart.Extends U.realPart) :
    W.completedRealVertices B ⊆ U.completedRealVertices B := by
  rintro x ⟨p, hpfinish, hpsupport, hpedges, hxp⟩
  exact ⟨p, hpfinish, hpsupport.trans hWU.1, hpedges.trans hWU.2, hxp⟩

/-- Every vertex of a completed real path itself has a real continuation
to the same target set. -/
theorem realLinksTo_of_mem_completedRealVertices
    {W : LinkageBlueprint Γ Y κ} {x : V} {B : Set V}
    (hx : x ∈ W.completedRealVertices B) : W.RealLinksTo x B := by
  rcases hx with ⟨p, hpB, hpsupport, hpedges, hxp⟩
  let q := p.suffixFrom x hxp
  refine ⟨q, p.suffixFrom_start x hxp, ?_, ?_, ?_⟩
  · simpa [q] using hpB
  · exact (p.suffixFrom_support_subset x hxp).trans hpsupport
  · exact (p.suffixFrom_edgeSet_subset x hxp).trans hpedges

/-- The strengthened, endpoint-explicit output of 9.30 used by 9.34.  All
fields are concrete consequences of the continuation construction. -/
structure Continuation930 (W cut V' : LinkageBlueprint Γ Y κ)
    (u z : V) (T B : Set V) : Prop where
  conclusion : ContinuationConclusion W cut V' u T
  links_to_endpoint : V'.RealLinksTo u {z}
  endpoint_mem_slice : z ∈ T
  endpoint_terminal : z ∈ V'.terminalSet
  preserves_other_terminals :
    W.realPart.terminals \ {u} ⊆ V'.realPart.terminals
  endpoint_fresh : z ∉ W.realPart.terminals \ {u}
  real_extends_to_endpoint : W.RealExtends V' {z}

/-- Endpoint-explicit form of the first branch of Assertion 9.30.  When the
scheduled real terminal is already a terminal of the whole blueprint and
already belongs to the current slice, the identity continuation works and
the endpoint is the scheduled vertex itself. -/
theorem continuation930_of_terminal_mem_slice
    {W : LinkageBlueprint Γ Y κ} {u : V} {T B : Set V}
    (hureal : u ∈ W.realPart.terminals)
    (huterm : u ∈ W.terminalSet) (huT : u ∈ T) :
    Continuation930 W W W u u T B := by
  let p : DirectedPath.FinitePath Γ.graph :=
    DirectedPath.FinitePath.trivial Γ.graph u
  have hlinks : W.RealLinksTo u {u} := by
    refine ⟨p, rfl, Set.mem_singleton u, ?_, ?_⟩
    · simpa [p, LinkageBlueprint.realPart] using hureal.1
    · simp [p, DirectedPath.FinitePath.edgeSet]
  have hlinksT : W.RealLinksTo u T := by
    refine ⟨p, rfl, huT, ?_, ?_⟩
    · simpa [p, LinkageBlueprint.realPart] using hureal.1
    · simp [p, DirectedPath.FinitePath.edgeSet]
  refine
    { conclusion := ?_
      links_to_endpoint := hlinks
      endpoint_mem_slice := huT
      endpoint_terminal := huterm
      preserves_other_terminals := fun _ hx ↦ hx.1
      endpoint_fresh := by simp
      real_extends_to_endpoint := realExtends_refl W {u} }
  exact ⟨W.isCutAt_self_of_mem_terminalSet huterm,
    ordinaryExtends_refl W, hlinksT, fun _ hx ↦ hx.1⟩

/-- The exact derived interface from 9.31 needed in 9.34.  The two graph
inclusions follow from ordinary forward extension.  The two preservation
fields are the concrete consequences of the printed terminal clauses for
the 9.30 ancestor `W`; they make explicit the ancestor dependence which the
bare `AdvanceConclusion` predicate currently loses. -/
structure Advance931 (W V' U : LinkageBlueprint Γ Y κ)
    (z : V) (T Z persistent B : Set V) : Prop where
  conclusion : AdvanceConclusion V' U z T persistent B
  isBlueprint : U.IsLinkageBlueprint T Z persistent
  stable : U.Stable T persistent
  family_extends : V'.familyGraph.Extends U.familyGraph
  real_extends : V'.realPart.Extends U.realPart
  preserves_except : V'.realPart.terminals \ {z} ⊆ U.realPart.terminals
  preserves_inherited_full_terminals :
    ∀ x, x ∈ W.terminalSet → x ∈ V'.terminalSet → x ≠ z →
      x ∈ U.terminalSet

/-- Package the source-faithful 9.31 orientation compiler into the exact
interface consumed by the 9.34 scheduler.  The result blueprint is the
canonical root-orbit decomposition of `O`; it is not supplied as an input. -/
theorem exists_advance931_of_compiled
    (A W : LinkageBlueprint Γ Y κ)
    (O : Alternating.RelationDecomposition.ForwardOrientation
      (imaginaryGraph Γ Y κ))
    {z : V} {T Z persistent B : Set V}
    (hroof : (orientationBlueprint O).vertexSet ⊆ Γ.roof T)
    (hcover : Γ.source ⊆
      (orientationBlueprint O).initialSet ∪
        (orientationBlueprint O).retainedReferenceInitials T)
    (hclosed : (orientationBlueprint O).vertexSet ⊆ Z)
    (hcard : #(orientationBlueprint O).paths ≤ κ)
    (hstrong : (orientationBlueprint O).InfinitelyManyStrongEdges)
    (hpopular : (orientationBlueprint O).terminalSet ⊆
      {u | IsPopular Γ Y persistent κ u} ∪ T)
    (hstable : (orientationBlueprint O).Stable T persistent)
    (hvertices : W.vertexSet ⊆ (orientationBlueprint O).vertexSet)
    (hedges : W.edgeSet ⊆ O.edge)
    (p : FinitePath Γ.graph)
    (hpstart : p.start = z) (hpfinish : p.finish ∈ B)
    (hpvertices : p.support ⊆ (orientationBlueprint O).vertexSet)
    (hpedges : p.edgeSet ⊆ O.edge)
    (hrealTerminals : W.realPart.terminals ⊆
      (orientationBlueprint O).realPart.terminals ∪ T)
    (hpersistent : W.terminalSet ∩ persistent ⊆
      (orientationBlueprint O).terminalSet ∪ {z})
    (hpreserves : W.realPart.terminals \ {z} ⊆
      (orientationBlueprint O).realPart.terminals)
    (hinherited : ∀ x, x ∈ A.terminalSet → x ∈ W.terminalSet → x ≠ z →
      x ∈ (orientationBlueprint O).terminalSet) :
    ∃ U : LinkageBlueprint Γ Y κ,
      Advance931 A W U z T Z persistent B := by
  obtain ⟨U, hU, hstableU, hconclusion, hfamily, hreal,
      hpreservesU, hinheritedU⟩ :=
    Erdos599.Blueprint.exists_compiled_advance A W O hroof hcover hclosed
      hcard hstrong hpopular hstable hvertices hedges p hpstart hpfinish
      hpvertices hpedges hrealTerminals hpersistent hpreserves hinherited
  exact ⟨U, hconclusion, hU, hstableU, hfamily, hreal,
    hpreservesU, hinheritedU⟩

/-- Assertion 9.34, assembled from the endpoint-explicit 9.30 continuation
and the derived 9.31 interface. -/
theorem assertion934_of_930_931
    {W cut V' U : LinkageBlueprint Γ Y κ} {u z : V}
    {T Z persistent B : Set V}
    (h30 : Continuation930 W cut V' u z T B)
    (h31 : Advance931 W V' U z T Z persistent B) :
    StableExtensionConclusion W U u T Z persistent B := by
  have hlinksUZ : U.RealLinksTo u {z} :=
    realLinksTo_mono h31.real_extends h30.links_to_endpoint
  have hlinksUB : U.RealLinksTo u B :=
    realLinksTo_trans hlinksUZ h31.conclusion.links
  have hreal : W.RealExtends U B := by
    refine ⟨FamilyGraph.extends_trans
      h30.real_extends_to_endpoint.1 h31.real_extends, ?_⟩
    intro x hxW
    rcases h30.real_extends_to_endpoint.2 hxW with hxAB | hxcomplete
    · rcases hxAB with hxterm | hxedge
      · rcases hxterm with ⟨hxV, hxWterm⟩
        by_cases hxz : x = z
        · subst x
          exact Or.inr h31.conclusion.links.start_mem_completedRealVertices
        · exact Or.inl (Or.inl
            ⟨h31.preserves_inherited_full_terminals x hxWterm hxV hxz,
              hxWterm⟩)
      · rcases hxedge with ⟨y, hyW, hyV⟩
        exact Or.inl (Or.inr ⟨y, hyW, h31.family_extends.2 hyV⟩)
    · have hxVz : V'.RealLinksTo x {z} :=
        realLinksTo_of_mem_completedRealVertices hxcomplete
      have hxUz : U.RealLinksTo x {z} :=
        realLinksTo_mono h31.real_extends hxVz
      exact Or.inr
        (realLinksTo_trans hxUz h31.conclusion.links).start_mem_completedRealVertices
  refine ⟨h31.isBlueprint, h31.stable, hreal, hlinksUB, ?_⟩
  intro x hx
  have hxV := h30.preserves_other_terminals hx
  have hxne : x ≠ z := by
    intro hxz
    subst x
    exact h30.endpoint_fresh hx
  exact h31.preserves_except ⟨hxV, hxne⟩

/-- Existential form of Assertion 9.34 from concrete existence theorems for
9.30 and 9.31. -/
theorem exists_assertion934
    {W : LinkageBlueprint Γ Y κ} {u : V} {T Z persistent B : Set V}
    (h30 : ∃ (cut V' : LinkageBlueprint Γ Y κ) (z : V),
      Continuation930 W cut V' u z T B)
    (h31 : ∀ (cut V' : LinkageBlueprint Γ Y κ) (z : V),
      Continuation930 W cut V' u z T B →
        ∃ U : LinkageBlueprint Γ Y κ, Advance931 W V' U z T Z persistent B) :
    ∃ U : LinkageBlueprint Γ Y κ,
      StableExtensionConclusion W U u T Z persistent B := by
  obtain ⟨cut, V', z, hV⟩ := h30
  obtain ⟨U, hU⟩ := h31 cut V' z hV
  exact ⟨U, assertion934_of_930_931 hV hU⟩

/-- Bundled, representation-independent target for the repaired 9.30
construction.  In particular, the implementation may replace a whole
simultaneously assigned family; it need not use the single-path `diamond`
operation. -/
def Continuation930Compiler (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Γ Y κ) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals → u ∈ T →
        ∃ (cut V' : LinkageBlueprint Γ Y κ) (z : V),
          Continuation930 W cut V' u z T B

/-- Bundled target for 9.31, exposing the old-blueprint invariant needed by
the concrete assignment/orientation compiler. -/
def Advance931Compiler (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Γ Y κ) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
        ∃ U : LinkageBlueprint Γ Y κ,
          Advance931 W V' U z T Z persistent B

/-- The successor operation consumed by the terminal scheduler. -/
def Stable934Compiler (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Γ Y κ) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals → u ∈ T →
        ∃ U : LinkageBlueprint Γ Y κ,
          StableExtensionConclusion W U u T Z persistent B

/-- Assertions 9.30 and 9.31, in their bundled compiler forms, supply the
exact stable successor used by the final terminal recursion. -/
theorem stable934Compiler_of_930_931
    {T Z persistent B : Set V}
    (h30 : Continuation930Compiler (Γ := Γ) (Y := Y) (κ := κ)
      T Z persistent B)
    (h31 : Advance931Compiler (Γ := Γ) (Y := Y) (κ := κ)
      T Z persistent B) :
    Stable934Compiler (Γ := Γ) (Y := Y) (κ := κ)
      T Z persistent B := by
  intro W u hW hpersistent hu huT
  apply exists_assertion934
  · exact h30 W u hW hpersistent hu huT
  · intro cut V' z hcontinuation
    exact h31 W cut V' u z hW hcontinuation

/-! ### The terminal-scheduling invariant -/

/-- A completed path starting outside `B` supplies an outgoing real edge,
so its start cannot be a terminal of the real part. -/
private theorem walk_exists_first_edge_of_start_ne_finish {D : Digraph V} :
    ∀ {a b : V} (p : Walk D a b), a ≠ b → ∃ c, (a, c) ∈ p.edgeSet
  | _, _, .nil, hab => (hab rfl).elim
  | _, _, .cons (v := c) h p, _ => ⟨c, by simp⟩

theorem not_mem_realTerminals_of_realLinksTo {W : LinkageBlueprint Γ Y κ}
    {u : V} {B : Set V} (huB : u ∉ B) (h : W.RealLinksTo u B) :
    u ∉ W.realPart.terminals := by
  rintro ⟨huV, huTail⟩
  rcases h with ⟨p, hpstart, hpfinish, hpsupport, hpedge⟩
  have hne : p.start ≠ p.finish := by
    intro heq
    apply huB
    simpa [← hpstart, heq] using hpfinish
  obtain ⟨c, hc⟩ := walk_exists_first_edge_of_start_ne_finish p.walk hne
  apply huTail
  refine ⟨c, ?_⟩
  apply hpedge
  simpa only [FinitePath.edgeSet, hpstart] using hc

/-- A concrete terminal-scheduled chain.  `fair` is the scheduling invariant:
every non-target terminal of the final limit is assigned a stage, and
`resolved` records the 9.34 path produced at that stage.  `absorbed` is the
9.33 limit inclusion for real parts. -/
structure TerminalScheduledChain (I : Type v)
    (stage : I → LinkageBlueprint Γ Y κ)
    (limit : LinkageBlueprint Γ Y κ) (B : Set V) where
  scheduled : I → V
  absorbed : ∀ i, (stage i).realPart.Extends limit.realPart
  fair : ∀ x ∈ limit.realPart.terminals, x ∉ B →
    ∃ i, scheduled i = x
  resolved : ∀ i, (stage i).RealLinksTo (scheduled i) B
  real_limit : limit.familyGraph.edges ⊆ {e | Γ.graph.Adj e.1 e.2}

/-- The terminal-scheduled limit has no real terminal outside `B`. -/
theorem TerminalScheduledChain.final_terminals_subset
    {I : Type v} {stage : I → LinkageBlueprint Γ Y κ}
    {limit : LinkageBlueprint Γ Y κ} {B : Set V}
    (C : TerminalScheduledChain I stage limit B) :
    limit.realPart.terminals ⊆ B := by
  intro x hx
  by_contra hxB
  obtain ⟨i, hi⟩ := C.fair x hx hxB
  have hstage : (stage i).RealLinksTo x B := hi ▸ C.resolved i
  have hlimit : limit.RealLinksTo x B := realLinksTo_mono (C.absorbed i) hstage
  exact not_mem_realTerminals_of_realLinksTo hxB hlimit hx

/-- At the terminal stage the blueprint graph equals its real part. -/
theorem TerminalScheduledChain.final_familyGraph_eq_realPart
    {I : Type v} {stage : I → LinkageBlueprint Γ Y κ}
    {limit : LinkageBlueprint Γ Y κ} {B : Set V}
    (C : TerminalScheduledChain I stage limit B) :
    limit.familyGraph.vertices = limit.realPart.vertices ∧
      limit.familyGraph.edges = limit.realPart.edges := by
  refine ⟨rfl, ?_⟩
  apply Set.Subset.antisymm
  · intro e he
    exact ⟨he, C.real_limit he⟩
  · exact Set.inter_subset_left

end LinkageBlueprint

end Blueprint
end Erdos599
noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath
open Blueprint
open CardinalInduction

universe u v

variable {V : Type u}

/-! A pathwise change-of-graph operation.  Unlike `Path.lift`, its edge
condition is needed only on edges actually traversed by the path. -/

namespace DirectedPath

variable {D E : Digraph V}

def Walk.restrictGraphOnEdges : {a b : V} → (p : Walk D a b) →
    (∀ e, e ∈ p.edgeSet → E.Adj e.1 e.2) → Walk E a b
  | _, _, .nil, _ => .nil
  | _, _, @Walk.cons _ _ x y z e p, h =>
      .cons (h (x, y) (by simp))
        (Walk.restrictGraphOnEdges p (fun f hf => h f (by simp [hf])))

@[simp] theorem Walk.support_restrictGraphOnEdges {a b : V}
    (p : Walk D a b) (h : ∀ e, e ∈ p.edgeSet → E.Adj e.1 e.2) :
    (Walk.restrictGraphOnEdges p h).support = p.support := by
  induction p with
  | nil => rfl
  | @cons x y z e p ih =>
      simp only [Walk.restrictGraphOnEdges, Walk.support_cons]
      exact congrArg (List.cons x) (ih _)

def FinitePath.restrictGraphOnEdges (p : FinitePath D)
    (h : ∀ e, e ∈ p.edgeSet → E.Adj e.1 e.2) : FinitePath E where
  start := p.start
  finish := p.finish
  walk := Walk.restrictGraphOnEdges p.walk (fun e he ↦ h e he)
  isPath := by
    change (Walk.restrictGraphOnEdges p.walk (fun e he ↦ h e he)).support.Nodup
    rw [Walk.support_restrictGraphOnEdges]
    exact p.isPath

@[simp] theorem FinitePath.support_restrictGraphOnEdges (p : FinitePath D)
    (h : ∀ e, e ∈ p.edgeSet → E.Adj e.1 e.2) :
    (FinitePath.restrictGraphOnEdges p h).support = p.support := by
  ext x
  change x ∈ (Walk.restrictGraphOnEdges p.walk _).support ↔
    x ∈ p.walk.support
  rw [Walk.support_restrictGraphOnEdges]

def Ray.restrictGraphOnEdges (r : Ray D)
    (h : ∀ e, e ∈ r.edgeSet → E.Adj e.1 e.2) : Ray E where
  toFun := r.toFun
  adj_succ n := h (r n, r (n + 1)) (by exact ⟨n, rfl⟩)
  injective := r.injective

@[simp] theorem Ray.support_restrictGraphOnEdges (r : Ray D)
    (h : ∀ e, e ∈ r.edgeSet → E.Adj e.1 e.2) :
    (Ray.restrictGraphOnEdges r h).support = r.support := rfl

def Path.restrictGraphOnEdges (p : Path D)
    (h : ∀ e, e ∈ p.edgeSet → E.Adj e.1 e.2) : Path E :=
  match p with
  | .inl q => .inl (FinitePath.restrictGraphOnEdges q h)
  | .inr r => .inr (Ray.restrictGraphOnEdges r h)

@[simp] theorem Path.support_restrictGraphOnEdges (p : Path D)
    (h : ∀ e, e ∈ p.edgeSet → E.Adj e.1 e.2) :
    (Path.restrictGraphOnEdges p h).support = p.support := by
  cases p with
  | inl p => exact FinitePath.support_restrictGraphOnEdges p h
  | inr r => exact Ray.support_restrictGraphOnEdges r h

@[simp] theorem Path.initial_restrictGraphOnEdges (p : Path D)
    (h : ∀ e, e ∈ p.edgeSet → E.Adj e.1 e.2) :
    (Path.restrictGraphOnEdges p h).initial = p.initial := by
  cases p <;> rfl

@[simp] theorem Path.terminal_restrictGraphOnEdges (p : Path D)
    (h : ∀ e, e ∈ p.edgeSet → E.Adj e.1 e.2) :
    (Path.restrictGraphOnEdges p h).terminal? = p.terminal? := by
  cases p <;> rfl

theorem Walk.noOutgoingAtEnd_of_isPath {a b : V}
    (p : Walk D a b) (hp : p.IsPath) (y : V) :
    (b, y) ∉ p.edgeSet := by
  induction p with
  | nil => simp
  | @cons a c b e p ih =>
      intro he
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at he
      rcases he with he | he
      · have hab : a = b := (congrArg Prod.fst he).symm
        exact (List.nodup_cons.mp hp).1 (hab ▸ p.end_mem_support)
      · exact ih (List.nodup_cons.mp hp).2 he

theorem FinitePath.noOutgoingAtFinish (p : FinitePath D) (y : V) :
    (p.finish, y) ∉ p.edgeSet :=
  p.walk.noOutgoingAtEnd_of_isPath p.isPath y

end DirectedPath

namespace Blueprint.LinkageBlueprint

variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- A final blueprint is edge-real when every edge used by it is an
edge of the original web. -/
def IsEdgeReal (U : LinkageBlueprint Gamma Y kappa) : Prop :=
  U.edgeSet ⊆ {e | Gamma.graph.Adj e.1 e.2}

/-- Reinterpret one member of an edge-real blueprint in the original web. -/
def realPath (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    (p : U.paths) : Gamma.DPath :=
  p.1.restrictGraphOnEdges fun e he =>
    hreal (Set.mem_iUnion.2 <| Exists.intro p.1 <|
      Set.mem_iUnion.2 <| Exists.intro p.2 he)

/-- Finite specialization of `realPath`, with the membership proof made
explicit so subsequent support rewrites do not depend on proof terms. -/
def realFinitePath (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (Sum.inl q : DirectedPath.Path (imaginaryGraph Gamma Y kappa)) ∈
      U.paths) : FinitePath Gamma.graph :=
  q.restrictGraphOnEdges fun e he ↦
    hreal (Set.mem_iUnion.2 <| Exists.intro (Sum.inl q) <|
      Set.mem_iUnion.2 <| Exists.intro hq he)

@[simp] theorem support_realFinitePath
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    (q : FinitePath (imaginaryGraph Gamma Y kappa)) (hq : (.inl q) ∈ U.paths) :
    (U.realFinitePath hreal q hq).support = q.support :=
  q.support_restrictGraphOnEdges _

@[simp] theorem walk_support_realFinitePath
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    (q : FinitePath (imaginaryGraph Gamma Y kappa)) (hq : (.inl q) ∈ U.paths) :
    (U.realFinitePath hreal q hq).walk.support = q.walk.support :=
  q.walk.support_restrictGraphOnEdges _

@[simp] theorem start_realFinitePath
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    (q : FinitePath (imaginaryGraph Gamma Y kappa)) (hq : (.inl q) ∈ U.paths) :
    (U.realFinitePath hreal q hq).start = q.start := rfl

@[simp] theorem finish_realFinitePath
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    (q : FinitePath (imaginaryGraph Gamma Y kappa)) (hq : (.inl q) ∈ U.paths) :
    (U.realFinitePath hreal q hq).finish = q.finish := rfl

theorem realPath_inl_eq
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    (q : FinitePath (imaginaryGraph Gamma Y kappa)) (hq : (.inl q) ∈ U.paths) :
    U.realPath hreal ⟨.inl q, hq⟩ = .inl (U.realFinitePath hreal q hq) :=
  rfl

/-- The actual original-web path family represented by an edge-real
blueprint. -/
def realFamily (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal) :
    Set Gamma.DPath := Set.range (U.realPath hreal)

/-- The paper's final family: the realized blueprint together with the
untouched paths of the reference warp. -/
def completedFamily (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) (R : Set Gamma.DPath) : Set Gamma.DPath :=
  U.realFamily hreal ∪ R

/-- The canonical untouched portion of the reference warp appearing in
blueprint condition (2). -/
def referenceRemainder (U : LinkageBlueprint Gamma Y kappa) (T : Set V) :
    Set Gamma.DPath :=
  referencePathsMeeting Y T \ referencePathsMeeting Y U.vertexSet

theorem referenceRemainder_subset (U : LinkageBlueprint Gamma Y kappa)
    (T : Set V) : U.referenceRemainder T ⊆ Y := by
  intro p hp
  exact hp.1.1

theorem isWarp_referenceRemainder (U : LinkageBlueprint Gamma Y kappa)
    (T : Set V) (hY : Gamma.IsWarp Y) :
    Gamma.IsWarp (U.referenceRemainder T) := by
  intro p hp q hq hpq
  exact hY hp.1.1 hq.1.1 hpq

theorem disjoint_referenceRemainder
    (U : LinkageBlueprint Gamma Y kappa) (T : Set V) :
    ∀ p ∈ U.paths, ∀ q ∈ U.referenceRemainder T,
      Disjoint p.support q.support := by
  intro p hp q hq
  apply Set.disjoint_left.2
  intro x hxp hxq
  apply hq.2
  exact ⟨hq.1.1, ⟨x, hxq, ⟨p, hp, hxp⟩⟩⟩

/-- The endpoint-purity information which an imaginary-graph blueprint
must carry before it can be converted to an actual linkage.  This is a
path-level structural condition, stated before changing graphs. -/
def IsPathBetween (U : LinkageBlueprint Gamma Y kappa)
    (A C : Set V) (p : DirectedPath.Path (imaginaryGraph Gamma Y kappa)) :
    Prop :=
  ∃ q : FinitePath (imaginaryGraph Gamma Y kappa),
    p = .inl q ∧
      q.support ∩ (A ∪ C) = {q.start, q.finish} ∧
      q.support ∩ A = {q.start}

/-- The target-link certificate which the final recursion must retain for
the distinguished sources.  It is the exact pathwise data needed after
changing from the imaginary graph back to the original graph. -/
def BlueprintLinksToTarget (U : LinkageBlueprint Gamma Y kappa)
    (A0 : Set V) : Prop :=
  ∀ a ∈ A0, ∃ p ∈ U.paths,
    ∃ q : FinitePath (imaginaryGraph Gamma Y kappa),
      p = .inl q ∧ q.support ∩ A0 = {a} ∧
        CardinalInduction.FinitePathSuffixMeets q a Gamma.target

/-- A convenient terminal-state criterion for the local target
certificates: every designated source is the initial point of a blueprint
member, and every blueprint terminal is already in the target. -/
theorem blueprintLinksToTarget_of_initial_terminal
    (U : LinkageBlueprint Gamma Y kappa) {A0 C : Set V}
    (hA0 : A0 ⊆ Gamma.source)
    (hinitial : A0 ⊆ U.initialSet)
    (hpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hterminal : U.terminalSet ⊆ Gamma.target) :
    U.BlueprintLinksToTarget A0 := by
  intro a ha
  obtain ⟨p, hp, hpa⟩ := hinitial ha
  obtain ⟨q, hpq, _hAC, hsource⟩ := hpure p hp
  subst p
  have hstart : q.start = a := by
    change q.start = a at hpa
    exact hpa
  refine ⟨.inl q, hp, q, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA0⟩
      have hx : x ∈ q.support ∩ Gamma.source := ⟨hxq, hA0 hxA0⟩
      have : x ∈ ({q.start} : Set V) := hsource ▸ hx
      have hxeq : x = q.start := Set.mem_singleton_iff.1 this
      exact Set.mem_singleton_iff.2 (hxeq.trans hstart)
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.1 hx
      subst x
      refine ⟨?_, ha⟩
      rw [← hstart]
      exact q.start_mem_support
  · have hfinish : q.finish ∈ Gamma.target :=
      hterminal ⟨.inl q, hp, rfl⟩
    have hsplit : q.walk.support = q.start :: q.walk.support.tail := by
      simpa only [q.walk.head_support] using
        (List.cons_head_tail q.walk.support_ne_nil).symm
    have hsplit' : q.walk.support = a :: q.walk.support.tail := by
      simpa only [hstart] using hsplit
    refine ⟨[], q.walk.support.tail, by simpa using hsplit',
      q.finish, hfinish, ?_⟩
    rw [← hsplit']
    exact q.finish_mem_support

/-- For a finite endpoint-pure blueprint, the abstract path terminals are
terminals of its family graph.  This is the bridge from the terminal
scheduler's `final_terminals_subset` conclusion to `terminalSet ⊆ target`. -/
theorem terminalSet_subset_familyGraph_terminals
    (U : LinkageBlueprint Gamma Y kappa) {A C : Set V}
    (hpure : ∀ p ∈ U.paths, U.IsPathBetween A C p) :
    U.terminalSet ⊆ U.familyGraph.terminals := by
  rintro x ⟨p, hp, hpx⟩
  have hxp : x ∈ p.support :=
    (imaginaryWeb Gamma Y kappa).terminal_mem_support hpx
  refine ⟨⟨p, hp, hxp⟩, ?_⟩
  rintro ⟨y, hy⟩
  simp only [familyGraph, edgeSet, Set.mem_iUnion] at hy
  obtain ⟨q, hq, hxy⟩ := hy
  have hxq : x ∈ q.support := q.edgeSet_subset_support_prod hxy |>.1
  have hpq : p = q := U.path_eq_of_mem_support hp hq hxp hxq
  subst q
  obtain ⟨r, hpr, _⟩ := hpure p hp
  subst p
  have hrx : r.finish = x := by
    apply Option.some.inj
    exact ((imaginaryWeb Gamma Y kappa).terminal?_finite r).symm.trans hpx
  subst x
  exact r.noOutgoingAtFinish y hxy

/-- Endpoint purity supplies the reverse inclusion missing from blueprint
condition (2), turning its source cover into the exact initial-set equality
required by `IsLinkageBetween`. -/
theorem initialSet_union_referenceRemainder_eq_source
    (U : LinkageBlueprint Gamma Y kappa) (T : Set V) {C : Set V}
    (hcover : Gamma.source ⊆
      U.initialSet ∪ Gamma.initialSet (U.referenceRemainder T))
    (hUpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hRpure : ∀ p ∈ U.referenceRemainder T,
      CardinalInduction.IsPathBetween Gamma Gamma.source C p) :
    U.initialSet ∪ Gamma.initialSet (U.referenceRemainder T) =
      Gamma.source := by
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · obtain ⟨p, hp, hpx⟩ := hx
      obtain ⟨q, hpq, _hAC, hsource⟩ := hUpure p hp
      subst p
      change q.start = x at hpx
      have hqsource : q.start ∈ Gamma.source := by
        have hm : q.start ∈ q.support ∩ Gamma.source :=
          hsource.symm ▸ (show q.start ∈ ({q.start} : Set V) by rfl)
        exact hm.2
      exact hpx ▸ hqsource
    · obtain ⟨p, hp, hpx⟩ := hx
      obtain ⟨q, hpq, _hAC, hsource⟩ := hRpure p hp
      subst p
      change q.start = x at hpx
      have hqsource : q.start ∈ Gamma.source := by
        have hm : q.start ∈ q.support ∩ Gamma.source :=
          hsource.symm ▸ (show q.start ∈ ({q.start} : Set V) by rfl)
        exact hm.2
      exact hpx ▸ hqsource
  · exact hcover

@[simp] theorem support_realPath (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) (p : U.paths) :
    (U.realPath hreal p).support = p.1.support := by
  exact p.1.support_restrictGraphOnEdges _

@[simp] theorem initial_realPath (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) (p : U.paths) :
    (U.realPath hreal p).initial = p.1.initial := by
  exact p.1.initial_restrictGraphOnEdges _

@[simp] theorem terminal_realPath (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) (p : U.paths) :
    Gamma.terminal? (U.realPath hreal p) =
      (imaginaryWeb Gamma Y kappa).terminal? p.1 := by
  exact p.1.terminal_restrictGraphOnEdges _

theorem isWarp_realFamily (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) : Gamma.IsWarp (U.realFamily hreal) := by
  rintro q hq r hr hqr
  obtain ⟨p, rfl⟩ := hq
  obtain ⟨s, rfl⟩ := hr
  change Disjoint (U.realPath hreal p).support
    (U.realPath hreal s).support
  rw [U.support_realPath hreal, U.support_realPath hreal]
  apply U.isWarp p.2 s.2
  intro hps
  apply hqr
  have hps' : p = s := Subtype.ext hps
  subst s
  rfl

theorem initialSet_realFamily (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) :
    Gamma.initialSet (U.realFamily hreal) = U.initialSet := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, rfl⟩, hqx⟩
    change (U.realPath hreal p).initial = x at hqx
    rw [U.initial_realPath hreal] at hqx
    exact ⟨p.1, p.2, hqx⟩
  · rintro ⟨p, hp, hpx⟩
    let ps : U.paths := ⟨p, hp⟩
    refine ⟨U.realPath hreal ps, ⟨ps, rfl⟩, ?_⟩
    change (U.realPath hreal ps).initial = x
    rw [U.initial_realPath hreal]
    exact hpx

theorem terminalFrontier_realFamily (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) :
    Gamma.terminalFrontier (U.realFamily hreal) = U.terminalSet := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, rfl⟩, hqx⟩
    exact ⟨p.1, p.2, by simpa using hqx⟩
  · rintro ⟨p, hp, hpx⟩
    let ps : U.paths := ⟨p, hp⟩
    exact ⟨U.realPath hreal ps, ⟨ps, rfl⟩, by simpa using hpx⟩

theorem finiteCharacter_realFamily (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal)
    (hfinite : ∀ p ∈ U.paths,
      ∃ q : FinitePath (imaginaryGraph Gamma Y kappa), p = .inl q) :
    Gamma.HasFiniteCharacter (U.realFamily hreal) := by
  rintro q ⟨⟨p, hp⟩, rfl⟩
  obtain ⟨fp, hfp⟩ := hfinite p hp
  subst p
  let ps : U.paths := ⟨.inl fp, hp⟩
  change ∃ q, U.realPath hreal ps = .inl q
  exact ⟨U.realFinitePath hreal fp hp, rfl⟩

theorem isPathBetween_realPath (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) {A C : Set V} (p : U.paths)
    (hp : U.IsPathBetween A C p.1) :
    CardinalInduction.IsPathBetween Gamma A C (U.realPath hreal p) := by
  rcases p with ⟨p, hpU⟩
  change U.IsPathBetween A C p at hp
  obtain ⟨q, hpq, hAC, hA⟩ := hp
  subst p
  let ps : U.paths := ⟨.inl q, hpU⟩
  change CardinalInduction.IsPathBetween Gamma A C (U.realPath hreal ps)
  refine ⟨U.realFinitePath hreal q hpU, rfl, ?_, ?_⟩
  · rw [U.support_realFinitePath, U.start_realFinitePath,
      U.finish_realFinitePath]
    exact hAC
  · rw [U.support_realFinitePath, U.start_realFinitePath]
    exact hA

theorem finiteCharacter_realFamily_of_pathBetween
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    {A C : Set V} (hpure : ∀ p ∈ U.paths, U.IsPathBetween A C p) :
    Gamma.HasFiniteCharacter (U.realFamily hreal) := by
  apply U.finiteCharacter_realFamily hreal
  intro p hp
  obtain ⟨q, hpq, -⟩ := hpure p hp
  exact ⟨q, hpq⟩

theorem endpointPure_realFamily
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    {A C : Set V} (hpure : ∀ p ∈ U.paths, U.IsPathBetween A C p) :
    ∀ p ∈ U.realFamily hreal,
      CardinalInduction.IsPathBetween Gamma A C p := by
  rintro p ⟨q, rfl⟩
  exact U.isPathBetween_realPath hreal q (hpure q.1 q.2)

theorem linksToTarget_realFamily (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) {A0 : Set V}
    (hlinks : U.BlueprintLinksToTarget A0) :
    LinksToTarget Gamma (U.realFamily hreal) A0 := by
  intro a ha
  obtain ⟨p, hp, q, hpq, hqA, before, after, hqsplit,
    b, hb, hbafter⟩ := hlinks a ha
  subst p
  let ps : U.paths := ⟨.inl q, hp⟩
  refine ⟨U.realPath hreal ps, ⟨ps, rfl⟩,
    U.realFinitePath hreal q hp, rfl, ?_, ?_⟩
  · rw [U.support_realFinitePath]
    exact hqA
  · refine ⟨before, after, ?_, b, hb, hbafter⟩
    rw [U.walk_support_realFinitePath]
    exact hqsplit

theorem isWarp_completedFamily (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) {R : Set Gamma.DPath}
    (hRwarp : Gamma.IsWarp R)
    (hcross : ∀ p ∈ U.paths, ∀ q ∈ R, Disjoint p.support q.support) :
    Gamma.IsWarp (U.completedFamily hreal R) := by
  intro p hp q hq hpq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact U.isWarp_realFamily hreal hp hq hpq
  · obtain ⟨r, rfl⟩ := hp
    change Disjoint (U.realPath hreal r).support q.support
    rw [U.support_realPath hreal]
    exact hcross r.1 r.2 q hq
  · obtain ⟨r, rfl⟩ := hq
    change Disjoint p.support (U.realPath hreal r).support
    rw [U.support_realPath hreal]
    exact (hcross r.1 r.2 p hp).symm
  · exact hRwarp hp hq hpq

theorem finiteCharacter_completedFamily (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) {R : Set Gamma.DPath}
    (hUfinite : ∀ p ∈ U.paths,
      ∃ q : FinitePath (imaginaryGraph Gamma Y kappa), p = .inl q)
    (hRfinite : Gamma.HasFiniteCharacter R) :
    Gamma.HasFiniteCharacter (U.completedFamily hreal R) := by
  intro p hp
  rcases hp with hp | hp
  · exact U.finiteCharacter_realFamily hreal hUfinite hp
  · exact hRfinite hp

theorem endpointPure_completedFamily
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    {R : Set Gamma.DPath} {A C : Set V}
    (hUpure : ∀ p ∈ U.paths, U.IsPathBetween A C p)
    (hRpure : ∀ p ∈ R, CardinalInduction.IsPathBetween Gamma A C p) :
    ∀ p ∈ U.completedFamily hreal R,
      CardinalInduction.IsPathBetween Gamma A C p := by
  intro p hp
  rcases hp with hp | hp
  · exact U.endpointPure_realFamily hreal hUpure p hp
  · exact hRpure p hp

theorem initialSet_completedFamily (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) (R : Set Gamma.DPath) :
    Gamma.initialSet (U.completedFamily hreal R) =
      U.initialSet ∪ Gamma.initialSet R := by
  rw [completedFamily]
  ext x
  simp only [Gamma.mem_initialSet, Set.mem_union]
  constructor
  · rintro ⟨p, hp | hp, hpx⟩
    · left
      rw [← U.initialSet_realFamily hreal]
      exact ⟨p, hp, hpx⟩
    · exact Or.inr ⟨p, hp, hpx⟩
  · rintro (hx | hx)
    · rw [← U.initialSet_realFamily hreal] at hx
      obtain ⟨p, hp, hpx⟩ := hx
      exact ⟨p, Or.inl hp, hpx⟩
    · obtain ⟨p, hp, hpx⟩ := hx
      exact ⟨p, Or.inr hp, hpx⟩

theorem terminalFrontier_completedFamily
    (U : LinkageBlueprint Gamma Y kappa) (hreal : U.IsEdgeReal)
    (R : Set Gamma.DPath) :
    Gamma.terminalFrontier (U.completedFamily hreal R) =
      U.terminalSet ∪ Gamma.terminalFrontier R := by
  rw [completedFamily]
  ext x
  simp only [Gamma.mem_terminalFrontier, Set.mem_union]
  constructor
  · rintro ⟨p, hp | hp, hpx⟩
    · left
      rw [← U.terminalFrontier_realFamily hreal]
      exact ⟨p, hp, hpx⟩
    · exact Or.inr ⟨p, hp, hpx⟩
  · rintro (hx | hx)
    · rw [← U.terminalFrontier_realFamily hreal] at hx
      obtain ⟨p, hp, hpx⟩ := hx
      exact ⟨p, Or.inl hp, hpx⟩
    · obtain ⟨p, hp, hpx⟩ := hx
      exact ⟨p, Or.inr hp, hpx⟩

theorem linksToTarget_completedFamily (U : LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal) (R : Set Gamma.DPath) {A0 : Set V}
    (hlinks : U.BlueprintLinksToTarget A0) :
    LinksToTarget Gamma (U.completedFamily hreal R) A0 := by
  intro a ha
  obtain ⟨p, hp, hpinit, b, hb, hpterm⟩ :=
    U.linksToTarget_realFamily hreal hlinks a ha
  exact ⟨p, Or.inl hp, hpinit, b, hb, hpterm⟩

end Blueprint.LinkageBlueprint

namespace CardinalInduction

open Blueprint.LinkageBlueprint

variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- Structural terminal-state data sufficient to turn the last linkage
blueprint into the actual halfway linkage required by Theorem 9.2.

The height hypotheses expose the quotient witness itself rather than
assuming `HeightAtMost`; the repaired stop-over condition is supplied by
the structural trimmed-frontier equality `essential C = C`. -/
theorem exists_halfwayStopover_of_terminalBlueprint
    (U : Blueprint.LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal)
    (hinitial : U.initialSet = Gamma.source)
    {C A0 X : Set V}
    (hterminal : U.terminalSet = C)
    (hpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hessential : Gamma.essential C = C)
    (hunhindered : (Gamma.quotient C).IsUnhindered)
    (hlinks : U.BlueprintLinksToTarget A0)
    (hXsource : X ⊆ Gamma.sourceᶜ)
    (Q : Set (Gamma.quotient X).DPath)
    (hQwave : (Gamma.quotient X).IsWave Q)
    (hCroof : C ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q))
    (hXcard : #X ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayStopover Gamma W C ∧
      LinksToTarget Gamma W A0 ∧
      HeightAtMost Gamma C kappa ∧
      Gamma.terminalFrontier W = C := by
  let W := U.realFamily hreal
  have hwarp : Gamma.IsWarp W := U.isWarp_realFamily hreal
  have hfin : Gamma.HasFiniteCharacter W :=
    U.finiteCharacter_realFamily_of_pathBetween hreal hpure
  have hinit : Gamma.initialSet W = Gamma.source := by
    rw [U.initialSet_realFamily hreal, hinitial]
  have hterm : Gamma.terminalFrontier W = C := by
    rw [U.terminalFrontier_realFamily hreal, hterminal]
  have hlinkage : IsLinkageBetween Gamma Gamma.source C W :=
    ⟨hwarp, hfin, hinit, hterm.le,
      U.endpointPure_realFamily hreal hpure⟩
  refine ⟨W, ⟨hlinkage, hessential, hunhindered⟩,
    U.linksToTarget_realFamily hreal hlinks, ?_⟩
  exact ⟨⟨X, ⟨hXsource, Q, hQwave, hCroof⟩, hXcard⟩, hterm⟩

/-- Source-faithful variant including the untouched part `R` of the ladder
warp.  The hypotheses state exactly the component-level facts that the
terminal recursion must export: cross-disjointness and the two frontier
equalities after adjoining `R`. -/
theorem exists_halfwayStopover_of_terminalBlueprint_withReference
    (U : Blueprint.LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal)
    (R : Set Gamma.DPath)
    (hRwarp : Gamma.IsWarp R)
    (hcross : ∀ p ∈ U.paths, ∀ q ∈ R,
      Disjoint p.support q.support)
    {C A0 X : Set V}
    (hinitial : U.initialSet ∪ Gamma.initialSet R = Gamma.source)
    (hterminal : U.terminalSet ∪ Gamma.terminalFrontier R = C)
    (hUpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hRpure : ∀ p ∈ R, IsPathBetween Gamma Gamma.source C p)
    (hessential : Gamma.essential C = C)
    (hunhindered : (Gamma.quotient C).IsUnhindered)
    (hlinks : U.BlueprintLinksToTarget A0)
    (hXsource : X ⊆ Gamma.sourceᶜ)
    (Q : Set (Gamma.quotient X).DPath)
    (hQwave : (Gamma.quotient X).IsWave Q)
    (hCroof : C ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q))
    (hXcard : #X ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayStopover Gamma W C ∧
      LinksToTarget Gamma W A0 ∧
      HeightAtMost Gamma C kappa ∧
      Gamma.terminalFrontier W = C := by
  let W := U.completedFamily hreal R
  have hwarp : Gamma.IsWarp W :=
    U.isWarp_completedFamily hreal hRwarp hcross
  have hUfinite : ∀ p ∈ U.paths,
      ∃ q : FinitePath (Blueprint.imaginaryGraph Gamma Y kappa),
        p = .inl q := by
    intro p hp
    obtain ⟨q, hpq, -⟩ := hUpure p hp
    exact ⟨q, hpq⟩
  have hRfinite : Gamma.HasFiniteCharacter R := by
    intro p hp
    obtain ⟨q, hpq, -⟩ := hRpure p hp
    exact ⟨q, hpq⟩
  have hfin : Gamma.HasFiniteCharacter W :=
    U.finiteCharacter_completedFamily hreal hUfinite hRfinite
  have hinit : Gamma.initialSet W = Gamma.source := by
    rw [U.initialSet_completedFamily hreal R, hinitial]
  have hterm : Gamma.terminalFrontier W = C := by
    rw [U.terminalFrontier_completedFamily hreal R, hterminal]
  have hlinkage : IsLinkageBetween Gamma Gamma.source C W :=
    ⟨hwarp, hfin, hinit, hterm.le,
      U.endpointPure_completedFamily hreal hUpure hRpure⟩
  refine ⟨W, ⟨hlinkage, hessential, hunhindered⟩,
    U.linksToTarget_completedFamily hreal R hlinks, ?_⟩
  exact ⟨⟨X, ⟨hXsource, Q, hQwave, hCroof⟩, hXcard⟩, hterm⟩

/-- The same terminal conversion in the packaged altitude form. -/
theorem halfwayLinkageOfAltitude_of_terminalBlueprint
    (U : Blueprint.LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal)
    (hinitial : U.initialSet = Gamma.source)
    {C A0 X : Set V}
    (hterminal : U.terminalSet = C)
    (hpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hessential : Gamma.essential C = C)
    (hunhindered : (Gamma.quotient C).IsUnhindered)
    (hlinks : U.BlueprintLinksToTarget A0)
    (hXsource : X ⊆ Gamma.sourceᶜ)
    (Q : Set (Gamma.quotient X).DPath)
    (hQwave : (Gamma.quotient X).IsWave Q)
    (hCroof : C ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q))
    (hXcard : #X ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  obtain ⟨W, hstop, htarget, hheight, _hfrontier⟩ :=
    exists_halfwayStopover_of_terminalBlueprint U hreal hinitial
      hterminal hpure hessential hunhindered hlinks hXsource Q hQwave
      hCroof hXcard
  exact ⟨W, halfwayLinkageOfAltitude_of_stopover hstop htarget hheight⟩

/-- Packaged source-faithful terminal conversion.  This is the form used
after the terminal scheduler: the final edge-real blueprint is adjoined to
the untouched reference paths, and all remaining assumptions are local
structural invariants of that decomposition or explicit witnesses. -/
theorem halfwayLinkageOfAltitude_of_terminalBlueprint_withReference
    (U : Blueprint.LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal)
    (R : Set Gamma.DPath)
    (hRwarp : Gamma.IsWarp R)
    (hcross : ∀ p ∈ U.paths, ∀ q ∈ R,
      Disjoint p.support q.support)
    {C A0 X : Set V}
    (hinitial : U.initialSet ∪ Gamma.initialSet R = Gamma.source)
    (hterminal : U.terminalSet ∪ Gamma.terminalFrontier R = C)
    (hUpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hRpure : ∀ p ∈ R, IsPathBetween Gamma Gamma.source C p)
    (hessential : Gamma.essential C = C)
    (hunhindered : (Gamma.quotient C).IsUnhindered)
    (hlinks : U.BlueprintLinksToTarget A0)
    (hXsource : X ⊆ Gamma.sourceᶜ)
    (Q : Set (Gamma.quotient X).DPath)
    (hQwave : (Gamma.quotient X).IsWave Q)
    (hCroof : C ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q))
    (hXcard : #X ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  obtain ⟨W, hstop, htarget, hheight, _hfrontier⟩ :=
    exists_halfwayStopover_of_terminalBlueprint_withReference
      U hreal R hRwarp hcross hinitial hterminal hUpure hRpure hessential
      hunhindered hlinks hXsource Q hQwave hCroof hXcard
  exact ⟨W, halfwayLinkageOfAltitude_of_stopover hstop htarget hheight⟩

/-- Canonical-reference form of the terminal conversion.  Here the added
family is determined by the blueprint itself; warpness and cross-disjointness
are consequences of the reference warp invariant rather than hypotheses. -/
theorem halfwayLinkageOfAltitude_of_terminalBlueprint_canonicalReference
    (U : Blueprint.LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal)
    (T : Set V)
    (hYwarp : Gamma.IsWarp Y)
    {C A0 X : Set V}
    (hinitial : U.initialSet ∪
      Gamma.initialSet (U.referenceRemainder T) = Gamma.source)
    (hterminal : U.terminalSet ∪
      Gamma.terminalFrontier (U.referenceRemainder T) = C)
    (hUpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hRpure : ∀ p ∈ U.referenceRemainder T,
      IsPathBetween Gamma Gamma.source C p)
    (hessential : Gamma.essential C = C)
    (hunhindered : (Gamma.quotient C).IsUnhindered)
    (hlinks : U.BlueprintLinksToTarget A0)
    (hXsource : X ⊆ Gamma.sourceᶜ)
    (Q : Set (Gamma.quotient X).DPath)
    (hQwave : (Gamma.quotient X).IsWave Q)
    (hCroof : C ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q))
    (hXcard : #X ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  exact halfwayLinkageOfAltitude_of_terminalBlueprint_withReference
    U hreal (U.referenceRemainder T)
    (U.isWarp_referenceRemainder T hYwarp)
    (U.disjoint_referenceRemainder T)
    hinitial hterminal hUpure hRpure hessential hunhindered hlinks
    hXsource Q hQwave hCroof hXcard

/-- Fully fieldwise terminal-data form.  The target-link certificate is
derived rather than assumed: designated sources start blueprint members and
all blueprint terminals lie in the target. -/
theorem halfwayLinkageOfAltitude_of_terminalData
    (U : Blueprint.LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal)
    (T : Set V)
    (hYwarp : Gamma.IsWarp Y)
    {C A0 X : Set V}
    (hA0source : A0 ⊆ Gamma.source)
    (hA0initial : A0 ⊆ U.initialSet)
    (hinitial : U.initialSet ∪
      Gamma.initialSet (U.referenceRemainder T) = Gamma.source)
    (hterminal : U.terminalSet ∪
      Gamma.terminalFrontier (U.referenceRemainder T) = C)
    (hUterminal_target : U.terminalSet ⊆ Gamma.target)
    (hUpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hRpure : ∀ p ∈ U.referenceRemainder T,
      IsPathBetween Gamma Gamma.source C p)
    (hessential : Gamma.essential C = C)
    (hunhindered : (Gamma.quotient C).IsUnhindered)
    (hXsource : X ⊆ Gamma.sourceᶜ)
    (Q : Set (Gamma.quotient X).DPath)
    (hQwave : (Gamma.quotient X).IsWave Q)
    (hCroof : C ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q))
    (hXcard : #X ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  apply halfwayLinkageOfAltitude_of_terminalBlueprint_canonicalReference
    U hreal T hYwarp hinitial hterminal hUpure hRpure hessential
    hunhindered
  · exact U.blueprintLinksToTarget_of_initial_terminal
      hA0source hA0initial hUpure hUterminal_target
  · exact hXsource
  · exact hQwave
  · exact hCroof
  · exact hXcard

/-- Global-assignment finalization lane.  A construction which resolves all
terminals simultaneously need not manufacture an indexed
`TerminalScheduledChain`: it is enough to return an edge-real blueprint
whose real-part terminals already lie in the target. -/
theorem halfwayLinkageOfAltitude_of_globallyResolvedBlueprint
    (U : Blueprint.LinkageBlueprint Gamma Y kappa)
    (hreal : U.IsEdgeReal)
    (hrealTerminals : U.realPart.terminals ⊆ Gamma.target)
    (T : Set V)
    (hYwarp : Gamma.IsWarp Y)
    {C A0 X : Set V}
    (hA0source : A0 ⊆ Gamma.source)
    (hA0initial : A0 ⊆ U.initialSet)
    (hinitial : U.initialSet ∪
      Gamma.initialSet (U.referenceRemainder T) = Gamma.source)
    (hterminal : U.terminalSet ∪
      Gamma.terminalFrontier (U.referenceRemainder T) = C)
    (hUpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hRpure : ∀ p ∈ U.referenceRemainder T,
      IsPathBetween Gamma Gamma.source C p)
    (hessential : Gamma.essential C = C)
    (hunhindered : (Gamma.quotient C).IsUnhindered)
    (hXsource : X ⊆ Gamma.sourceᶜ)
    (Q : Set (Gamma.quotient X).DPath)
    (hQwave : (Gamma.quotient X).IsWave Q)
    (hCroof : C ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q))
    (hXcard : #X ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  have hgraph : U.familyGraph = U.realPart := by
    change Blueprint.FamilyGraph.mk U.familyGraph.vertices U.familyGraph.edges =
      Blueprint.FamilyGraph.mk U.realPart.vertices U.realPart.edges
    apply congrArg₂ (fun vertices edges ↦
      Blueprint.FamilyGraph.mk vertices edges)
    · rfl
    · change U.familyGraph.edges =
        U.familyGraph.edges ∩ {e | Gamma.graph.Adj e.1 e.2}
      apply Set.Subset.antisymm
      · intro e he
        exact ⟨he, hreal he⟩
      · exact Set.inter_subset_left
  have hUterminal_target : U.terminalSet ⊆ Gamma.target := by
    intro x hx
    have hxterm := U.terminalSet_subset_familyGraph_terminals hUpure hx
    rw [hgraph] at hxterm
    exact hrealTerminals hxterm
  exact halfwayLinkageOfAltitude_of_terminalData
    U hreal T hYwarp hA0source hA0initial hinitial hterminal
    hUterminal_target hUpure hRpure hessential hunhindered hXsource
    Q hQwave hCroof hXcard

/-- Scheduler-facing wrapper.  The scheduler supplies both facts peculiar
to the terminal recursion: all final edges are real and all resulting
family-graph terminals lie in the target.  Everything else is ordinary
source/reference/frontier/height structural data. -/
theorem halfwayLinkageOfAltitude_of_terminalScheduledChain
    {I : Type v}
    {stage : I → Blueprint.LinkageBlueprint Gamma Y kappa}
    {U : Blueprint.LinkageBlueprint Gamma Y kappa}
    (S : Blueprint.LinkageBlueprint.TerminalScheduledChain
      I stage U Gamma.target)
    (T : Set V)
    (hYwarp : Gamma.IsWarp Y)
    {C A0 X : Set V}
    (hA0source : A0 ⊆ Gamma.source)
    (hA0initial : A0 ⊆ U.initialSet)
    (hinitial : U.initialSet ∪
      Gamma.initialSet (U.referenceRemainder T) = Gamma.source)
    (hterminal : U.terminalSet ∪
      Gamma.terminalFrontier (U.referenceRemainder T) = C)
    (hUpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hRpure : ∀ p ∈ U.referenceRemainder T,
      IsPathBetween Gamma Gamma.source C p)
    (hessential : Gamma.essential C = C)
    (hunhindered : (Gamma.quotient C).IsUnhindered)
    (hXsource : X ⊆ Gamma.sourceᶜ)
    (Q : Set (Gamma.quotient X).DPath)
    (hQwave : (Gamma.quotient X).IsWave Q)
    (hCroof : C ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q))
    (hXcard : #X ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  have hreal : U.IsEdgeReal := by
    intro e he
    exact S.real_limit he
  have hgraph : U.familyGraph = U.realPart := by
    change Blueprint.FamilyGraph.mk U.familyGraph.vertices U.familyGraph.edges =
      Blueprint.FamilyGraph.mk U.realPart.vertices U.realPart.edges
    exact congrArg₂ (fun vertices edges ↦
      Blueprint.FamilyGraph.mk vertices edges)
      S.final_familyGraph_eq_realPart.1
      S.final_familyGraph_eq_realPart.2
  have hUterminal_target : U.terminalSet ⊆ Gamma.target := by
    intro x hx
    have hxterm := U.terminalSet_subset_familyGraph_terminals hUpure hx
    rw [hgraph] at hxterm
    exact S.final_terminals_subset hxterm
  exact halfwayLinkageOfAltitude_of_terminalData
    U hreal T hYwarp hA0source hA0initial hinitial hterminal
    hUterminal_target hUpure hRpure hessential hunhindered hXsource
    Q hQwave hCroof hXcard

/-- Source-faithful blueprint wrapper.  Blueprint condition (2) provides
the forward source cover, while endpoint purity proves the reverse
inclusion, so no exact initial-set equality is assumed. -/
theorem halfwayLinkageOfAltitude_of_scheduledBlueprint
    {I : Type v}
    {stage : I → Blueprint.LinkageBlueprint Gamma Y kappa}
    {U : Blueprint.LinkageBlueprint Gamma Y kappa}
    (S : Blueprint.LinkageBlueprint.TerminalScheduledChain
      I stage U Gamma.target)
    (T Z persistent : Set V)
    (hUblueprint : U.IsLinkageBlueprint T Z persistent)
    (hYwarp : Gamma.IsWarp Y)
    {C A0 X : Set V}
    (hA0source : A0 ⊆ Gamma.source)
    (hA0initial : A0 ⊆ U.initialSet)
    (hterminal : U.terminalSet ∪
      Gamma.terminalFrontier (U.referenceRemainder T) = C)
    (hUpure : ∀ p ∈ U.paths, U.IsPathBetween Gamma.source C p)
    (hRpure : ∀ p ∈ U.referenceRemainder T,
      IsPathBetween Gamma Gamma.source C p)
    (hessential : Gamma.essential C = C)
    (hunhindered : (Gamma.quotient C).IsUnhindered)
    (hXsource : X ⊆ Gamma.sourceᶜ)
    (Q : Set (Gamma.quotient X).DPath)
    (hQwave : (Gamma.quotient X).IsWave Q)
    (hCroof : C ⊆
      Gamma.roof ((Gamma.quotient X).terminalFrontier Q))
    (hXcard : #X ≤ kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  have hinitial : U.initialSet ∪
      Gamma.initialSet (U.referenceRemainder T) = Gamma.source :=
    U.initialSet_union_referenceRemainder_eq_source T
      hUblueprint.covers_source hUpure hRpure
  exact halfwayLinkageOfAltitude_of_terminalScheduledChain
    S T hYwarp hA0source hA0initial hinitial hterminal hUpure hRpure
    hessential hunhindered hXsource Q hQwave hCroof hXcard

/-! ### The final construction certificate

The Section 9 recursion has two legitimate ways to discharge all pending
real terminals: a fair stable-limit recursion, or one coupled simultaneous
assignment.  The latter should not be forced through the former's
representation-level `paths_monotone` premise.  The following certificate
therefore packages the common *mathematical* endpoint of both constructions:
an edge-real blueprint, its untouched reference remainder, and the explicit
height witness for their common terminal frontier.

This is intentionally stronger than the public half-way conclusion but does
not assume that conclusion, a linkage, or a stop-over.  In particular, all
warp, endpoint-purity, quotient-unhinderedness, and height data which turn the
raw blueprint into a half-way linkage remain explicit fields. -/

structure GloballyResolvedBlueprintCertificate (Gamma : DWeb V)
    (A0 : Set V) (kappa : Cardinal.{u}) where
  reference : Set Gamma.DPath
  blueprint : Blueprint.LinkageBlueprint Gamma reference kappa
  slice : Set V
  stopover : Set V
  heightDelete : Set V
  heightWave : Set (Gamma.quotient heightDelete).DPath
  reference_isWarp : Gamma.IsWarp reference
  edge_real : blueprint.IsEdgeReal
  real_terminals_target : blueprint.realPart.terminals ⊆ Gamma.target
  designated_source : A0 ⊆ Gamma.source
  designated_initial : A0 ⊆ blueprint.initialSet
  source_cover : blueprint.initialSet ∪
    Gamma.initialSet (blueprint.referenceRemainder slice) = Gamma.source
  terminal_frontier : blueprint.terminalSet ∪
    Gamma.terminalFrontier (blueprint.referenceRemainder slice) = stopover
  blueprint_endpointPure : ∀ p ∈ blueprint.paths,
    blueprint.IsPathBetween Gamma.source stopover p
  reference_endpointPure : ∀ p ∈ blueprint.referenceRemainder slice,
    IsPathBetween Gamma Gamma.source stopover p
  stopover_trimmed : Gamma.essential stopover = stopover
  quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  heightDelete_nonSource : heightDelete ⊆ Gamma.sourceᶜ
  heightWave_isWave : (Gamma.quotient heightDelete).IsWave heightWave
  stopover_roofed : stopover ⊆ Gamma.roof
    ((Gamma.quotient heightDelete).terminalFrontier heightWave)
  heightDelete_card : #heightDelete ≤ kappa

/-- A globally resolved construction certificate contains exactly the data
needed to produce the qualified half-way linkage. -/
theorem GloballyResolvedBlueprintCertificate.exists_halfwayLinkage
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (C : GloballyResolvedBlueprintCertificate Gamma A0 kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  exact halfwayLinkageOfAltitude_of_globallyResolvedBlueprint
    C.blueprint C.edge_real C.real_terminals_target C.slice
    C.reference_isWarp C.designated_source C.designated_initial
    C.source_cover C.terminal_frontier C.blueprint_endpointPure
    C.reference_endpointPure C.stopover_trimmed C.quotient_unhindered
    C.heightDelete_nonSource C.heightWave C.heightWave_isWave
    C.stopover_roofed C.heightDelete_card

/-- A single globally resolved certificate for every designated `kappa`-set
is a sound construction-level interface for the half-way clause. -/
theorem halfwayClauseAt_of_globallyResolvedBlueprintCertificates
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcert : ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
      Nonempty (GloballyResolvedBlueprintCertificate Gamma A0 kappa)) :
    HalfwayClauseAt Gamma kappa := by
  intro A0 hA0 hcard
  exact (hcert A0 hA0 hcard).some.exists_halfwayLinkage

/-! ### Construction-level compiler interfaces

The preceding theorem is deliberately fieldwise: it is convenient when the
last simultaneous assignment resolves every terminal at once.  The source
proof also permits a fair terminal recursion.  The next certificate packages
that second route and derives the two genuinely terminal-specific fields of a
`GloballyResolvedBlueprintCertificate` from `TerminalScheduledChain` instead
of asking a caller to prove them a second time.

Neither compiler below assumes a half-way linkage or a half-way clause.  Its
output is the concrete blueprint, reference remainder, terminal schedule, and
height witness from which those conclusions were proved above. -/

/-- The concrete endpoint of a fair terminal recursion.  All structural and
height data are explicit; edge reality and the final-terminal inclusion are
derived from `schedule`. -/
structure TerminalScheduledBlueprintCertificate (Gamma : DWeb V)
    (A0 : Set V) (kappa : Cardinal.{u}) where
  reference : Set Gamma.DPath
  blueprint : Blueprint.LinkageBlueprint Gamma reference kappa
  index : Type u
  stage : index → Blueprint.LinkageBlueprint Gamma reference kappa
  schedule : Blueprint.LinkageBlueprint.TerminalScheduledChain
    index stage blueprint Gamma.target
  slice : Set V
  stopover : Set V
  heightDelete : Set V
  heightWave : Set (Gamma.quotient heightDelete).DPath
  reference_isWarp : Gamma.IsWarp reference
  designated_source : A0 ⊆ Gamma.source
  designated_initial : A0 ⊆ blueprint.initialSet
  source_cover : blueprint.initialSet ∪
    Gamma.initialSet (blueprint.referenceRemainder slice) = Gamma.source
  terminal_frontier : blueprint.terminalSet ∪
    Gamma.terminalFrontier (blueprint.referenceRemainder slice) = stopover
  blueprint_endpointPure : ∀ p ∈ blueprint.paths,
    blueprint.IsPathBetween Gamma.source stopover p
  reference_endpointPure : ∀ p ∈ blueprint.referenceRemainder slice,
    IsPathBetween Gamma Gamma.source stopover p
  stopover_trimmed : Gamma.essential stopover = stopover
  quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  heightDelete_nonSource : heightDelete ⊆ Gamma.sourceᶜ
  heightWave_isWave : (Gamma.quotient heightDelete).IsWave heightWave
  stopover_roofed : stopover ⊆ Gamma.roof
    ((Gamma.quotient heightDelete).terminalFrontier heightWave)
  heightDelete_card : #heightDelete ≤ kappa

/-- Forget the representation of the fair terminal recursion.  The scheduler
proves precisely that every final blueprint edge is real and every final real
terminal belongs to the target. -/
def TerminalScheduledBlueprintCertificate.toGloballyResolved
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (C : TerminalScheduledBlueprintCertificate Gamma A0 kappa) :
    GloballyResolvedBlueprintCertificate Gamma A0 kappa where
  reference := C.reference
  blueprint := C.blueprint
  slice := C.slice
  stopover := C.stopover
  heightDelete := C.heightDelete
  heightWave := C.heightWave
  reference_isWarp := C.reference_isWarp
  edge_real := C.schedule.real_limit
  real_terminals_target := C.schedule.final_terminals_subset
  designated_source := C.designated_source
  designated_initial := C.designated_initial
  source_cover := C.source_cover
  terminal_frontier := C.terminal_frontier
  blueprint_endpointPure := C.blueprint_endpointPure
  reference_endpointPure := C.reference_endpointPure
  stopover_trimmed := C.stopover_trimmed
  quotient_unhindered := C.quotient_unhindered
  heightDelete_nonSource := C.heightDelete_nonSource
  heightWave_isWave := C.heightWave_isWave
  stopover_roofed := C.stopover_roofed
  heightDelete_card := C.heightDelete_card

theorem TerminalScheduledBlueprintCertificate.exists_halfwayLinkage
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (C : TerminalScheduledBlueprintCertificate Gamma A0 kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W :=
  C.toGloballyResolved.exists_halfwayLinkage

/-- Minimal construction interface at one web and one cardinal.  This is the
direct globally-resolved lane, after either the simultaneous 9.31 assignment
or the terminal recursion has been compiled. -/
def GloballyResolvedBlueprintCompiler (Gamma : DWeb V)
    (kappa : Cardinal.{u}) : Prop :=
  ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
    Nonempty (GloballyResolvedBlueprintCertificate Gamma A0 kappa)

/-- Scheduler-form construction interface at one web and one cardinal. -/
def TerminalScheduledBlueprintCompiler (Gamma : DWeb V)
    (kappa : Cardinal.{u}) : Prop :=
  ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
    Nonempty (TerminalScheduledBlueprintCertificate Gamma A0 kappa)

theorem globallyResolvedBlueprintCompiler_of_terminalScheduled
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : TerminalScheduledBlueprintCompiler Gamma kappa) :
    GloballyResolvedBlueprintCompiler Gamma kappa := by
  intro A0 hA0 hcard
  exact (hcompile A0 hA0 hcard).map
    TerminalScheduledBlueprintCertificate.toGloballyResolved

theorem halfwayClauseAt_of_globallyResolvedBlueprintCompiler
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : GloballyResolvedBlueprintCompiler Gamma kappa) :
    HalfwayClauseAt Gamma kappa :=
  halfwayClauseAt_of_globallyResolvedBlueprintCertificates hcompile

theorem halfwayClauseAt_of_terminalScheduledBlueprintCompiler
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : TerminalScheduledBlueprintCompiler Gamma kappa) :
    HalfwayClauseAt Gamma kappa :=
  halfwayClauseAt_of_globallyResolvedBlueprintCompiler
    (globallyResolvedBlueprintCompiler_of_terminalScheduled hcompile)

/-- The uniform construction hypothesis left by the Section 9 blueprint
argument.  Its inputs are exactly the lower-cardinal induction, the current
extension clause (used in 9.31), infinitude of the cardinal, and
unhinderedness of the current web. -/
def UniversalGloballyResolvedBlueprintCompiler (V : Type u) : Prop :=
  ∀ kappa : Cardinal.{u},
    UniversalCardinalInductionBelow V kappa →
    UniversalExtensionClauseAt V kappa →
    ℵ₀ ≤ kappa →
    ∀ Gamma : DWeb V, Gamma.IsUnhindered →
      GloballyResolvedBlueprintCompiler Gamma kappa

/-- Uniform fair-scheduler form of the same Section 9 construction input. -/
def UniversalTerminalScheduledBlueprintCompiler (V : Type u) : Prop :=
  ∀ kappa : Cardinal.{u},
    UniversalCardinalInductionBelow V kappa →
    UniversalExtensionClauseAt V kappa →
    ℵ₀ ≤ kappa →
    ∀ Gamma : DWeb V, Gamma.IsUnhindered →
      TerminalScheduledBlueprintCompiler Gamma kappa

theorem universalGloballyResolvedBlueprintCompiler_of_terminalScheduled
    (hcompile : UniversalTerminalScheduledBlueprintCompiler V) :
    UniversalGloballyResolvedBlueprintCompiler V := by
  intro kappa hlower hext hkappa Gamma hGamma
  exact globallyResolvedBlueprintCompiler_of_terminalScheduled
    (hcompile kappa hlower hext hkappa Gamma hGamma)

/-- Exact reduction of the half-way step used by
`universalCardinalInduction_of_steps` to the construction-level global
blueprint compiler. -/
theorem halfwayClauseStep_of_globallyResolvedBlueprintCompiler
    (hcompile : UniversalGloballyResolvedBlueprintCompiler V) :
    ∀ kappa : Cardinal.{u},
      UniversalCardinalInductionBelow V kappa →
      UniversalExtensionClauseAt V kappa →
      ℵ₀ ≤ kappa →
      ∀ Gamma : DWeb V, Gamma.IsUnhindered → HalfwayClauseAt Gamma kappa := by
  intro kappa hlower hext hkappa Gamma hGamma
  exact halfwayClauseAt_of_globallyResolvedBlueprintCompiler
    (hcompile kappa hlower hext hkappa Gamma hGamma)

/-- Scheduler-form reduction of the uniform half-way step. -/
theorem halfwayClauseStep_of_terminalScheduledBlueprintCompiler
    (hcompile : UniversalTerminalScheduledBlueprintCompiler V) :
    ∀ kappa : Cardinal.{u},
      UniversalCardinalInductionBelow V kappa →
      UniversalExtensionClauseAt V kappa →
      ℵ₀ ≤ kappa →
      ∀ Gamma : DWeb V, Gamma.IsUnhindered → HalfwayClauseAt Gamma kappa :=
  halfwayClauseStep_of_globallyResolvedBlueprintCompiler
    (universalGloballyResolvedBlueprintCompiler_of_terminalScheduled hcompile)

end CardinalInduction

end Erdos599
