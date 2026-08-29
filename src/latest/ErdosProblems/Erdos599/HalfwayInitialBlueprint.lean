/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause
import ErdosProblems.Erdos599.Ladder

/-!
# The initial blueprint in the half-way construction

The terminal scheduler starts from the members of the reference linkage
whose initial vertices lie in the designated set.  This file constructs that
blueprint directly.  In particular, the source-cover condition is proved from
the untouched reference members; it is not included as an input certificate.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath
open Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace InitialReference

variable {T A0 : Set V}

private theorem exists_finite_member
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) (a : A0) :
    ∃ q : FinitePath Gamma.graph,
      (Sum.inl q : Gamma.DPath) ∈ Y ∧ q.start = a.1 := by
  have haInitial : a.1 ∈ Gamma.initialSet Y :=
    hY.initialSet_eq.symm ▸ hA0 a.2
  obtain ⟨p, hpY, hpstart⟩ := haInitial
  obtain ⟨q, rfl⟩ := hY.finiteCharacter hpY
  exact ⟨q, hpY, hpstart⟩

private noncomputable def finiteMember
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) (a : A0) :
    FinitePath Gamma.graph :=
  Classical.choose (exists_finite_member hY hA0 a)

private theorem finiteMember_mem
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) (a : A0) :
    (Sum.inl (finiteMember hY hA0 a) : Gamma.DPath) ∈ Y :=
  (Classical.choose_spec (exists_finite_member hY hA0 a)).1

@[simp] private theorem finiteMember_start
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) (a : A0) :
    (finiteMember hY hA0 a).start = a.1 :=
  (Classical.choose_spec (exists_finite_member hY hA0 a)).2

private noncomputable def path
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) (a : A0) :
    Path (imaginaryGraph Gamma Y kappa) :=
  Sum.inl (Assertion931.liftOriginal (Y := Y) (κ := kappa)
    (finiteMember hY hA0 a))

private noncomputable def blueprint
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) :
    LinkageBlueprint Gamma Y kappa where
  paths := Set.range (path (kappa := kappa) hY hA0)
  isWarp := by
    rintro p ⟨a, rfl⟩ q ⟨b, rfl⟩ hpq
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hpq rfl
    have hfinite : finiteMember hY hA0 a ≠ finiteMember hY hA0 b := by
      intro heq
      apply hab
      apply Subtype.ext
      rw [← finiteMember_start hY hA0 a,
        ← finiteMember_start hY hA0 b, heq]
    have hdisjoint := hY.isWarp
      (finiteMember_mem hY hA0 a) (finiteMember_mem hY hA0 b)
      (fun heq ↦ hfinite (Sum.inl.inj heq))
    change Disjoint (finiteMember hY hA0 a).support
      (finiteMember hY hA0 b).support at hdisjoint
    change Disjoint
      (Assertion931.liftOriginal (Y := Y) (κ := kappa)
        (finiteMember hY hA0 a)).support
      (Assertion931.liftOriginal (Y := Y) (κ := kappa)
        (finiteMember hY hA0 b)).support
    simpa only [Assertion931.liftOriginal_support] using hdisjoint

@[simp] private theorem blueprint_paths
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) :
    (blueprint (kappa := kappa) hY hA0).paths =
      Set.range (path (kappa := kappa) hY hA0) :=
  rfl

private theorem initialSet_eq
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) :
    (blueprint (kappa := kappa) hY hA0).initialSet = A0 := by
  ext x
  constructor
  · rintro ⟨p, ⟨a, rfl⟩, hpstart⟩
    change
      (Assertion931.liftOriginal (Y := Y) (κ := kappa)
        (finiteMember hY hA0 a)).start = x at hpstart
    have hax : a.1 = x := by
      simpa only [Assertion931.liftOriginal_start,
        finiteMember_start] using hpstart
    exact hax ▸ a.2
  · intro hx
    let a : A0 := ⟨x, hx⟩
    refine ⟨path (kappa := kappa) hY hA0 a, ⟨a, rfl⟩, ?_⟩
    change
      (Assertion931.liftOriginal (Y := Y) (κ := kappa)
        (finiteMember hY hA0 a)).start = x
    simp only [Assertion931.liftOriginal_start, finiteMember_start, a]

private theorem terminalSet_subset
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) :
    (blueprint (kappa := kappa) hY hA0).terminalSet ⊆ T := by
  rintro x ⟨p, ⟨a, rfl⟩, hpterm⟩
  have hfinish : (finiteMember hY hA0 a).finish = x := by
    simpa only [path, DWeb.terminal?, Path.terminal?,
      Assertion931.liftOriginal_finish] using Option.some.inj hpterm
  exact hY.terminalFrontier_subset
    ⟨Sum.inl (finiteMember hY hA0 a), finiteMember_mem hY hA0 a,
      congrArg some hfinish⟩

private theorem path_support
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) (a : A0) :
    (path (kappa := kappa) hY hA0 a).support =
      (finiteMember hY hA0 a).support := by
  change
    (Assertion931.liftOriginal (Y := Y) (κ := kappa)
      (finiteMember hY hA0 a)).support = _
  exact Assertion931.liftOriginal_support _

private theorem path_edgeSet
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) (a : A0) :
    (path (kappa := kappa) hY hA0 a).edgeSet =
      (finiteMember hY hA0 a).edgeSet := by
  change
    (Assertion931.liftOriginal (Y := Y) (κ := kappa)
      (finiteMember hY hA0 a)).edgeSet = _
  exact Assertion931.liftOriginal_edgeSet _

private theorem reference_member_meets_T
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y) {p : Gamma.DPath} (hpY : p ∈ Y) :
    p ∈ referencePathsMeeting Y T := by
  obtain ⟨q, rfl⟩ := hY.finiteCharacter hpY
  refine ⟨hpY, q.finish, q.finish_mem_support, ?_⟩
  exact hY.terminalFrontier_subset ⟨Sum.inl q, hpY, rfl⟩

private theorem reference_member_avoids_blueprint_of_initial_not_mem
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) {p : Gamma.DPath} (hpY : p ∈ Y)
    (hpinitial : p.initial ∉ A0) :
    p ∉ referencePathsMeeting Y
      (blueprint (kappa := kappa) hY hA0).vertexSet := by
  rintro ⟨_hpY, x, hxp, hxblue⟩
  obtain ⟨q, ⟨a, hqa⟩, hxq⟩ := hxblue
  subst q
  have hpeq : p = Sum.inl (finiteMember hY hA0 a) := by
    apply DWeb.IsWarp.eq_of_mem_support hY.isWarp hpY
      (finiteMember_mem hY hA0 a) hxp
    change x ∈
      (Assertion931.liftOriginal (Y := Y) (κ := kappa)
        (finiteMember hY hA0 a)).support at hxq
    rw [Assertion931.liftOriginal_support] at hxq
    exact hxq
  apply hpinitial
  have hpstart : p.initial = a.1 := by
    rw [hpeq]
    exact finiteMember_start hY hA0 a
  exact hpstart ▸ a.2

private theorem covers_source
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) :
    Gamma.source ⊆
      (blueprint (kappa := kappa) hY hA0).initialSet ∪
        (blueprint (kappa := kappa) hY hA0).retainedReferenceInitials T := by
  intro x hxsource
  by_cases hxA0 : x ∈ A0
  · left
    simpa only [initialSet_eq] using hxA0
  · right
    have hxInitial : x ∈ Gamma.initialSet Y :=
      hY.initialSet_eq.symm ▸ hxsource
    obtain ⟨p, hpY, hpstart⟩ := hxInitial
    refine ⟨p, ⟨reference_member_meets_T hY hpY, ?_⟩, hpstart⟩
    exact reference_member_avoids_blueprint_of_initial_not_mem hY hA0 hpY
      (fun hpA0 ↦ hxA0 (hpstart.symm ▸ hpA0))

private theorem endpointPure
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) :
    ∀ p ∈ (blueprint (kappa := kappa) hY hA0).paths,
      (blueprint (kappa := kappa) hY hA0).IsPathBetween
        Gamma.source T p := by
  rintro p ⟨a, rfl⟩
  refine ⟨Assertion931.liftOriginal (Y := Y) (κ := kappa)
      (finiteMember hY hA0 a), rfl, ?_⟩
  obtain ⟨q, hq, hqAC, hqA⟩ :=
    hY.endpointPure _ (finiteMember_mem hY hA0 a)
  have hqeq : q = finiteMember hY hA0 a := by
    exact Sum.inl.inj hq.symm
  subst q
  simpa only [Assertion931.liftOriginal_support,
    Assertion931.liftOriginal_start, Assertion931.liftOriginal_finish] using
      And.intro hqAC hqA

private theorem edge_real
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source) :
    (blueprint (kappa := kappa) hY hA0).IsEdgeReal := by
  intro e he
  simp only [edgeSet, Set.mem_iUnion] at he
  obtain ⟨p, ⟨a, rfl⟩, he⟩ := he
  rw [path_edgeSet hY hA0 a] at he
  exact (finiteMember hY hA0 a).edgeSet_subset_adj he

/-- Select the reference-linkage components starting in `A0` and reinterpret
them as an all-real linkage blueprint.  The untouched reference components
prove condition (2) of Definition 9.27 exactly. -/
theorem exists_initialReferenceBlueprint
    (hY : CardinalInduction.IsLinkageBetween
      Gamma Gamma.source T Y)
    (hA0 : A0 ⊆ Gamma.source)
    (hcard : #A0 ≤ kappa)
    {Z persistent : Set V}
    (hYroof : Gamma.vertexSet Y ⊆ Gamma.roof T)
    (hYZ : Gamma.vertexSet Y ⊆ Z) :
    ∃ W : LinkageBlueprint Gamma Y kappa,
      W.IsLinkageBlueprint T Z persistent ∧
        W.initialSet = A0 ∧ W.terminalSet ⊆ T ∧
        W.IsEdgeReal ∧
        (∀ p ∈ W.paths, W.IsPathBetween Gamma.source T p) := by
  let W := blueprint (kappa := kappa) hY hA0
  have hW : W.IsLinkageBlueprint T Z persistent := by
    refine
      { vertices_roofed := ?_
        covers_source := covers_source (kappa := kappa) hY hA0
        vertices_closed := ?_
        card_paths := ?_
        infinitely_many_strong := ?_
        terminals_popular := ?_ }
    · rintro x ⟨p, ⟨a, rfl⟩, hxp⟩
      apply hYroof
      refine ⟨Sum.inl (finiteMember hY hA0 a),
        finiteMember_mem hY hA0 a, ?_⟩
      change x ∈ (finiteMember hY hA0 a).support
      exact path_support hY hA0 a ▸ hxp
    · rintro x ⟨p, ⟨a, rfl⟩, hxp⟩
      apply hYZ
      refine ⟨Sum.inl (finiteMember hY hA0 a),
        finiteMember_mem hY hA0 a, ?_⟩
      change x ∈ (finiteMember hY hA0 a).support
      exact path_support hY hA0 a ▸ hxp
    · exact Cardinal.mk_range_le.trans hcard
    · intro r hr
      obtain ⟨a, ha⟩ := hr
      simp only [path] at ha
      cases ha
    · exact (terminalSet_subset (kappa := kappa) hY hA0).trans
        Set.subset_union_right
  exact ⟨W, hW, initialSet_eq (kappa := kappa) hY hA0,
    terminalSet_subset (kappa := kappa) hY hA0,
    edge_real (kappa := kappa) hY hA0,
    endpointPure (kappa := kappa) hY hA0⟩

end InitialReference

namespace InitialSingleton

variable {T A0 : Set V}

private noncomputable def path (A0 : Set V) (a : A0) :
    Path (imaginaryGraph Gamma Y kappa) :=
  DirectedPath.Path.trivial (imaginaryGraph Gamma Y kappa) a.1

private noncomputable def blueprint (S : Set V) :
    LinkageBlueprint Gamma Y kappa where
  paths := Set.range (path (Gamma := Gamma) (Y := Y) (kappa := kappa) S)
  isWarp := by
    rintro p ⟨a, rfl⟩ q ⟨b, rfl⟩ hpq
    have hab : a.1 ≠ b.1 := by
      intro hab
      apply hpq
      have hab' : a = b := Subtype.ext hab
      subst b
      rfl
    change Disjoint
      ((imaginaryWeb Gamma Y kappa).trivialPath a.1).support
      ((imaginaryWeb Gamma Y kappa).trivialPath b.1).support
    rw [(imaginaryWeb Gamma Y kappa).support_trivialPath,
      (imaginaryWeb Gamma Y kappa).support_trivialPath]
    exact Set.disjoint_singleton.2 hab

private theorem vertexSet_eq (A0 : Set V) :
    (blueprint (Gamma := Gamma) (Y := Y) (kappa := kappa) A0).vertexSet =
      A0 := by
  ext x
  constructor
  · rintro ⟨p, ⟨a, rfl⟩, hxp⟩
    change x ∈
      ((imaginaryWeb Gamma Y kappa).trivialPath a.1).support at hxp
    rw [(imaginaryWeb Gamma Y kappa).support_trivialPath] at hxp
    exact hxp.symm ▸ a.2
  · intro hx
    let a : A0 := ⟨x, hx⟩
    refine ⟨path (Gamma := Gamma) (Y := Y) (kappa := kappa) A0 a,
      ⟨a, rfl⟩, ?_⟩
    change x ∈
      ((imaginaryWeb Gamma Y kappa).trivialPath a.1).support
    rw [(imaginaryWeb Gamma Y kappa).support_trivialPath]
    exact Set.mem_singleton x

private theorem initialSet_eq (A0 : Set V) :
    (blueprint (Gamma := Gamma) (Y := Y) (kappa := kappa) A0).initialSet =
      A0 := by
  ext x
  constructor
  · rintro ⟨p, ⟨a, rfl⟩, hp⟩
    change a.1 = x at hp
    exact hp ▸ a.2
  · intro hx
    let a : A0 := ⟨x, hx⟩
    exact ⟨path (Gamma := Gamma) (Y := Y) (kappa := kappa) A0 a,
      ⟨a, rfl⟩, rfl⟩

private theorem terminalSet_eq (A0 : Set V) :
    (blueprint (Gamma := Gamma) (Y := Y) (kappa := kappa) A0).terminalSet =
      A0 := by
  ext x
  constructor
  · rintro ⟨p, ⟨a, rfl⟩, hp⟩
    change some a.1 = some x at hp
    exact Option.some.inj hp ▸ a.2
  · intro hx
    let a : A0 := ⟨x, hx⟩
    refine ⟨path (Gamma := Gamma) (Y := Y) (kappa := kappa) A0 a,
      ⟨a, rfl⟩, ?_⟩
    rfl

private theorem covers_source
    (hGamma : Gamma.IsNormalized)
    (hYinitial : Gamma.source ⊆ Gamma.initialSet Y)
    (hA0source : A0 ⊆ Gamma.source) (hsourceT : Gamma.source ⊆ T) :
    Gamma.source ⊆
      (blueprint (Gamma := Gamma) (Y := Y) (kappa := kappa) A0).initialSet ∪
        (blueprint (Gamma := Gamma) (Y := Y) (kappa := kappa) A0).retainedReferenceInitials T := by
  intro x hxsource
  by_cases hxA0 : x ∈ A0
  · left
    simpa only [initialSet_eq] using hxA0
  · right
    have hxInitial : x ∈ Gamma.initialSet Y := hYinitial hxsource
    obtain ⟨p, hpY, hpstart⟩ := hxInitial
    refine ⟨p, ⟨?_, ?_⟩, hpstart⟩
    · refine ⟨hpY, x, ?_, hsourceT hxsource⟩
      rw [← hpstart]
      exact p.initial_mem_support
    · rintro ⟨_hpY, z, hzp, hzblue⟩
      have hzA0 : z ∈ A0 :=
        (vertexSet_eq (Gamma := Gamma) (Y := Y) (kappa := kappa) A0) ▸
          hzblue
      have hzinitial : z = p.initial :=
        hGamma.eq_initial_of_mem_path p hzp (hA0source hzA0)
      apply hxA0
      exact hpstart.symm ▸ hzinitial.symm ▸ hzA0

private theorem endpointPure (hA0source : A0 ⊆ Gamma.source) :
    ∀ p ∈
      (blueprint (Gamma := Gamma) (Y := Y) (kappa := kappa) A0).paths,
      (blueprint (Gamma := Gamma) (Y := Y) (kappa := kappa) A0)
        |>.IsPathBetween Gamma.source T p := by
  rintro p ⟨a, rfl⟩
  let q := DirectedPath.FinitePath.trivial
    (imaginaryGraph Gamma Y kappa) a.1
  refine ⟨q, rfl, ?_, ?_⟩
  · simp [q, hA0source a.2]
  · simp [q, hA0source a.2]

private theorem edge_real (A0 : Set V) :
    (blueprint (Gamma := Gamma) (Y := Y) (kappa := kappa) A0).IsEdgeReal := by
  intro e he
  simp only [edgeSet, Set.mem_iUnion] at he
  obtain ⟨p, ⟨a, rfl⟩, he⟩ := he
  simpa [path, DirectedPath.Path.trivial,
    DirectedPath.FinitePath.trivial, DirectedPath.FinitePath.edgeSet] using he

/-- The source-faithful initial state of the terminal scheduler: use the
trivial blueprint on `A0` and let the untouched reference warp cover every
other source.  Normalization is used only to show that a reference member
starting outside `A0` cannot later meet a vertex of `A0`. -/
theorem exists_initialSingletonBlueprint
    {Z persistent : Set V}
    (hGamma : Gamma.IsNormalized)
    (hYinitial : Gamma.source ⊆ Gamma.initialSet Y)
    (hA0source : A0 ⊆ Gamma.source) (hsourceT : Gamma.source ⊆ T)
    (hA0Z : A0 ⊆ Z) (hcard : #A0 ≤ kappa) :
    ∃ W : LinkageBlueprint Gamma Y kappa,
      W.IsLinkageBlueprint T Z persistent ∧
        W.initialSet = A0 ∧ W.terminalSet = A0 ∧
        W.IsEdgeReal ∧
        (∀ p ∈ W.paths, W.IsPathBetween Gamma.source T p) := by
  let W := blueprint (Gamma := Gamma) (Y := Y) (kappa := kappa) A0
  have hW : W.IsLinkageBlueprint T Z persistent := by
    refine
      { vertices_roofed := ?_
        covers_source := covers_source hGamma hYinitial hA0source hsourceT
        vertices_closed := ?_
        card_paths := ?_
        infinitely_many_strong := ?_
        terminals_popular := ?_ }
    · rw [vertexSet_eq]
      exact hA0source.trans hsourceT |>.trans (Gamma.subset_roof T)
    · change
        (blueprint (Gamma := Gamma) (Y := Y) (kappa := kappa) A0).vertexSet
          ⊆ Z
      rw [vertexSet_eq]
      exact hA0Z
    · exact Cardinal.mk_range_le.trans hcard
    · intro r hr
      obtain ⟨a, ha⟩ := hr
      simp only [path] at ha
      cases ha
    · rw [terminalSet_eq]
      exact hA0source.trans hsourceT |>.trans Set.subset_union_right
  exact ⟨W, hW,
    initialSet_eq (Gamma := Gamma) (Y := Y) (kappa := kappa) A0,
    terminalSet_eq (Gamma := Gamma) (Y := Y) (kappa := kappa) A0,
    edge_real (Gamma := Gamma) (Y := Y) (kappa := kappa) A0,
    endpointPure (Gamma := Gamma) (Y := Y) (kappa := kappa) hA0source⟩

end InitialSingleton

end LinkageBlueprint
end Blueprint
end Erdos599

namespace Erdos599.DWeb.KappaLadder

open Cardinal Set

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Every original source still starts a member of the final legal-ladder
warp.  Fresh time-stamp components may add other initials, so inclusion is
the exact statement needed by the initial blueprint. -/
theorem IsLegal.source_subset_initialSet_limitWarp
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal) :
    Gamma.source ⊆ Gamma.initialSet L.limitWarp := by
  have hlimitOrd : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨C, hstage, hlimit⟩ :=
    hL.limitStages (Ladder.finalStage kappa) hlimitOrd
  let i : Set.Iio kappa.ord := ⟨0, hL.regular.ord_pos⟩
  intro x hx
  have hxi : x ∈ Gamma.initialSet (C.stage i) := by
    rw [hstage i]
    change x ∈
      Gamma.initialSet (L.accumulated (Ladder.zeroStage kappa))
    rw [hL.initialStage, Gamma.initialSet_trivialWave]
    exact hx
  change x ∈ Gamma.initialSet (L.accumulated (Ladder.finalStage kappa))
  rw [hlimit, C.initialSet_limitPaths Gamma]
  exact Set.mem_iUnion.2 ⟨i, hxi⟩

end Erdos599.DWeb.KappaLadder

namespace Erdos599.Blueprint.LinkageBlueprint.InitialSingleton

open Cardinal Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Instantiate the singleton scheduler entry with the final warp of a
legal ladder.  The reference-source coverage is now derived, not supplied
as a construction premise. -/
theorem exists_initialSingletonBlueprint_of_legalLadder
    {L : Gamma.KappaLadder kappa} (hGamma : Gamma.IsNormalized)
    (hL : L.IsLegal) {A0 Z persistent : Set V}
    (hA0source : A0 ⊆ Gamma.source) (hA0Z : A0 ⊆ Z)
    (hcard : #A0 ≤ kappa) :
    ∃ W : LinkageBlueprint Gamma L.limitWarp kappa,
      W.IsLinkageBlueprint Gamma.source Z persistent ∧
        W.initialSet = A0 ∧ W.terminalSet = A0 ∧
        W.IsEdgeReal ∧
        (∀ p ∈ W.paths,
          W.IsPathBetween Gamma.source Gamma.source p) := by
  exact exists_initialSingletonBlueprint hGamma
    hL.source_subset_initialSet_limitWarp hA0source Subset.rfl
    hA0Z hcard

end Erdos599.Blueprint.LinkageBlueprint.InitialSingleton
