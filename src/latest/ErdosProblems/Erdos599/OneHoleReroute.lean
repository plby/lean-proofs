/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteDeletion
import ErdosProblems.Erdos599.ReducingBoundary

/-!
# Endpoint bookkeeping for finite augmenting switches

The finite alternating-trace decomposition produces a cyclowarp.  Its cycle
components have no oriented boundary, so the path part has the same initial
and terminal boundary as the full switched relation.  This file records the
augmenting counterpart of `pathPart_frontiers_eq_sdiff_of_finite_reducing`:
when both ends of the trace are outside the old warp, switching adds precisely
the initial end to the initial set and the terminal end to the terminal
frontier.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Plain alternation is bracket alternation with the universal forward
family.  This lets collision-trimming lemmas stated for bracket alternation
be used by the residual search without imposing a second reference warp. -/
theorem isBracketAlternating_univ_iff
    {Q : AltPath Gamma.graph} {Z : Set Gamma.DPath} :
    IsBracketAlternating (Set.univ : Set Gamma.DPath) Z Q ↔
      IsAlternating Z Q := by
  constructor
  · exact fun h ↦ h.1
  · intro hQ
    refine ⟨hQ, ?_⟩
    intro l _hl _hdir
    exact ⟨Sum.inl l.path, Set.mem_univ _, l.path.isSubpathOf_self⟩

/-- If the unique missing target is itself an uncovered source, the trivial
path at that vertex is already the required augmentation. -/
theorem DWeb.oneHoleDichotomy_of_common_gap
    {Z : Set Gamma.DPath} (hZ : Gamma.IsCleanFiniteWarp Z)
    {x : V} (hxA : x ∈ Gamma.source \ Gamma.initialSet Z)
    (hxB : x ∈ Gamma.target \ Gamma.terminalFrontier Z) :
    Gamma.OneHoleDichotomy Z := by
  let q := FinitePath.trivial Gamma.graph x
  apply Gamma.oneHoleDichotomy_of_disjoint_gap_path hZ q
  · simpa [q] using hxA
  · simpa [q] using hxB
  · rw [Set.disjoint_left]
    intro y hyq hyZ
    have hyx : y = x := by simpa [q] using hyq
    subst y
    exact Set.disjoint_left.1 hZ.source_gap_disjoint_vertexSet hxA hyZ

/-- A vertex which is simultaneously an uncovered source and an uncovered
target gives an actual one-point augmentation, not merely the disjunctive
one-hole conclusion. -/
theorem DWeb.exists_onePointAugmentation_of_common_gap
    {Z : Set Gamma.DPath} (hZ : Gamma.IsCleanFiniteWarp Z)
    {x : V} (hxA : x ∈ Gamma.source \ Gamma.initialSet Z)
    (hxB : x ∈ Gamma.target \ Gamma.terminalFrontier Z) :
    ∃ Zplus, Gamma.IsOnePointAugmentation Z Zplus := by
  let q := FinitePath.trivial Gamma.graph x
  let Zplus : Set Gamma.DPath := insert (.inl q : Gamma.DPath) Z
  have hdisjoint : Disjoint q.support (Gamma.vertexSet Z) := by
    rw [Set.disjoint_left]
    intro y hyq hyZ
    have hyx : y = x := by simpa [q] using hyq
    subst y
    exact Set.disjoint_left.1 hZ.source_gap_disjoint_vertexSet hxA hyZ
  refine ⟨Zplus, x, hxA, x, hxB, ?_, ?_, ?_, ?_⟩
  · exact DWeb.IsWarp.insert_finite_of_disjoint Gamma hZ.isWarp q hdisjoint
  · exact Gamma.hasFiniteCharacter_insert_finite hZ.hasFiniteCharacter q
  · exact Gamma.initialSet_insert_finite Z q
  · exact Gamma.terminalFrontier_insert_finite Z q

/-- If the clean finite warp already covers the whole target, it is itself
a hindrance as soon as one source remains uncovered.  This is the terminal
base case of the residual search. -/
theorem DWeb.oneHoleDichotomy_of_terminalFrontier_eq_target
    {Z : Set Gamma.DPath} (hZ : Gamma.IsCleanFiniteWarp Z)
    (hgap : (Gamma.source \ Gamma.initialSet Z).Nonempty)
    (hterminal : Gamma.terminalFrontier Z = Gamma.target) :
    Gamma.OneHoleDichotomy Z := by
  right
  refine ⟨Z, ⟨hZ.isWarp, hZ.initialSet_subset_source, ?_⟩, ?_⟩
  · rw [hterminal]
    intro a _ha q hq
    exact ⟨q.finish, q.finish_mem_support, hq.2⟩
  · exact DWeb.IsCleanFiniteWarp.initialSet_ne_source_of_gap_nonempty
      Gamma hZ hgap

private theorem not_hasOutgoing_familyEdges_of_not_mem_vertexSet
    {Z : Set Gamma.DPath} {x : V} (hx : x ∉ Gamma.vertexSet Z) :
    ¬ HasOutgoing (familyEdges Z) x := by
  rintro ⟨y, hxy⟩
  simp only [familyEdges, Set.mem_iUnion] at hxy
  rcases hxy with ⟨p, hpZ, hpedge⟩
  exact hx ⟨p, hpZ, (p.edgeSet_subset_support_prod hpedge).1⟩

private theorem not_hasIncoming_familyEdges_of_not_mem_vertexSet
    {Z : Set Gamma.DPath} {x : V} (hx : x ∉ Gamma.vertexSet Z) :
    ¬ HasIncoming (familyEdges Z) x := by
  rintro ⟨y, hyx⟩
  simp only [familyEdges, Set.mem_iUnion] at hyx
  rcases hyx with ⟨p, hpZ, hpedge⟩
  exact hx ⟨p, hpZ, (p.edgeSet_subset_support_prod hpedge).2⟩

private theorem edgeBalance_familyEdges_eq_zero_of_not_mem_vertexSet
    {Z : Set Gamma.DPath} {x : V} (hx : x ∉ Gamma.vertexSet Z) :
    edgeBalance (familyEdges Z) x = 0 := by
  have hout := not_hasOutgoing_familyEdges_of_not_mem_vertexSet hx
  have hin := not_hasIncoming_familyEdges_of_not_mem_vertexSet hx
  simp [edgeBalance, propInt, hout, hin]

/-- Exact boundary delta for the path part of a concrete finite augmenting
switch.  The hypotheses that `a` and `b` lie outside the old vertex set are
the residual-search endpoint conditions. -/
theorem Cyclowarp.pathPart_frontiers_eq_insert_of_finite_augmenting
    {Z : Set Gamma.DPath} (hZfin : Gamma.HasFiniteCharacter Z)
    (Q : FiniteTrace Gamma.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q))
    {a b : V} (hab : a ≠ b)
    (ha : a ∉ Gamma.vertexSet Z) (hb : b ∉ Gamma.vertexSet Z)
    (hQi : (AltPath.finite Q).initial = a)
    (hQt : (AltPath.finite Q).terminal? = some b)
    (C : Cyclowarp Gamma)
    (hEdges : C.edges = (Cyclowarp.application Z (.finite Q)).edges)
    (hIso : C.isolated = (Cyclowarp.application Z (.finite Q)).isolated)
    (hCfin : Gamma.HasFiniteCharacter C.pathPart) :
    Gamma.initialSet C.pathPart = insert a (Gamma.initialSet Z) ∧
      Gamma.terminalFrontier C.pathPart =
        insert b (Gamma.terminalFrontier Z) := by
  classical
  have hba : b ≠ a := hab.symm
  have habal : edgeBalance (familyEdges Z) a = 0 :=
    edgeBalance_familyEdges_eq_zero_of_not_mem_vertexSet ha
  have hbbal : edgeBalance (familyEdges Z) b = 0 :=
    edgeBalance_familyEdges_eq_zero_of_not_mem_vertexSet hb
  have haniso : a ∉ isolatedVertices Z :=
    fun h ↦ ha (isolatedVertices_subset_vertexSet Z h)
  have hbniso : b ∉ isolatedVertices Z :=
    fun h ↦ hb (isolatedVertices_subset_vertexSet Z h)
  have hinitial : Q.initial = a := hQi
  have hterminal : Q.terminal = b := by
    simpa [AltPath.terminal?] using Option.some.inj hQt
  have hbalance : ∀ x,
      edgeBalance C.edges x = edgeBalance (familyEdges Z) x +
        propInt (x = a) - propInt (x = b) := by
    intro x
    rw [hEdges, Cyclowarp.application_edges,
      Q.hasReducingBalanceDelta hQ, hinitial, hterminal]
  have hIso' : C.isolated = isolatedVertices Z := by
    simpa [Cyclowarp.application_isolated] using hIso
  constructor
  · ext x
    rw [C.mem_initialSet_pathPart_iff_isolated_or_edgeBalance_eq_one hCfin]
    simp only [Set.mem_insert_iff]
    rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one hQ.1.1 hZfin,
      hIso', hbalance]
    by_cases hxa : x = a
    · subst x
      simp [propInt, haniso, habal, hab]
    · by_cases hxb : x = b
      · subst x
        simp [propInt, hbniso, hbbal, hba]
      · simp [propInt, hxa, hxb]
  · ext x
    rw [C.mem_terminalFrontier_pathPart_iff_isolated_or_edgeBalance_eq_neg_one
      hCfin]
    simp only [Set.mem_insert_iff]
    rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
      hQ.1.1 hZfin, hIso', hbalance]
    by_cases hxa : x = a
    · subst x
      simp [propInt, haniso, habal, hab]
    · by_cases hxb : x = b
      · subst x
        simp [propInt, hbniso, hbbal, hba]
      · simp [propInt, hxa, hxb]

/-- A finite alternating trace from a fresh vertex `a` to a fresh vertex
`b` realizes an exact one-point augmentation of the reference warp. -/
theorem FiniteTrace.exists_onePointAugmentation_of_augmenting
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q))
    (hZfin : Gamma.HasFiniteCharacter Z)
    {a b : V} (hab : a ≠ b)
    (ha : a ∉ Gamma.vertexSet Z) (hb : b ∉ Gamma.vertexSet Z)
    (hQi : (AltPath.finite Q).initial = a)
    (hQt : (AltPath.finite Q).terminal? = some b) :
    ∃ Zplus : Set Gamma.DPath,
      Gamma.IsWarp Zplus ∧ Gamma.HasFiniteCharacter Zplus ∧
        Gamma.initialSet Zplus = insert a (Gamma.initialSet Z) ∧
        Gamma.terminalFrontier Zplus =
          insert b (Gamma.terminalFrontier Z) := by
  obtain ⟨C, hEdges, hIso, hCfin⟩ :=
    Q.exists_application_cyclowarp hQ hZfin
  obtain ⟨hinit, hterm⟩ :=
    C.pathPart_frontiers_eq_insert_of_finite_augmenting hZfin Q hQ
      hab ha hb hQi hQt hEdges hIso hCfin
  exact ⟨C.pathPart, C.pathPart_isWarp, hCfin, hinit, hterm⟩

/-- Package an augmenting trace directly as the one-point augmentation
alternative used by the finite-deletion dichotomy.  Cleanliness supplies
freshness of the two gap endpoints. -/
theorem FiniteTrace.exists_isOnePointAugmentation_of_augmenting
    {Z : Set Gamma.DPath} (hZ : Gamma.IsCleanFiniteWarp Z)
    (Q : FiniteTrace Gamma.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q))
    {a b : V} (ha : a ∈ Gamma.source \ Gamma.initialSet Z)
    (hb : b ∈ Gamma.target \ Gamma.terminalFrontier Z)
    (hab : a ≠ b)
    (hQi : (AltPath.finite Q).initial = a)
    (hQt : (AltPath.finite Q).terminal? = some b) :
    ∃ Zplus, Gamma.IsOnePointAugmentation Z Zplus := by
  have haFresh : a ∉ Gamma.vertexSet Z := by
    intro haZ
    exact Set.disjoint_left.1 hZ.source_gap_disjoint_vertexSet ha haZ
  have hbFresh : b ∉ Gamma.vertexSet Z := by
    intro hbZ
    exact Set.disjoint_left.1 hZ.target_gap_disjoint_vertexSet hb hbZ
  obtain ⟨Zplus, hwarp, hfin, hinit, hterm⟩ :=
    Q.exists_onePointAugmentation_of_augmenting hQ hZ.hasFiniteCharacter
      hab haFresh hbFresh hQi hQt
  exact ⟨Zplus, a, ha, b, hb, hwarp, hfin, hinit, hterm⟩

end Alternating

namespace DWeb

open Set DirectedPath

universe u

variable {V : Type u}

/-- The one-hole augmentation principle, isolated as an interface while the
residual alternating search is developed below.  The quantification over all
webs is important: Lemma 3.31 applies it after both deletion and retargeting. -/
def OneHolePrinciple (V : Type u) : Prop :=
  ∀ (G : DWeb V) (J : Set G.DPath), G.IsCleanFiniteWarp J →
    (G.source \ G.initialSet J).Nonempty → G.OneHoleDichotomy J

/-- A finite directed walk which starts in `R`, ends in `B`, and can leave
`R` only through `S` must meet `S`, provided target vertices of `R` already
belong to `S`.  This is the elementary boundary argument behind the blocking
branch of the residual search. -/
private theorem Walk.exists_mem_of_forwardBoundary
    (G : DWeb V) {R S : Set V}
    (hexit : ∀ {x y}, G.graph.Adj x y → x ∈ R → y ∉ R → x ∈ S)
    (htarget : G.target ∩ R ⊆ S)
    {a b : V} (p : Walk G.graph a b) (ha : a ∈ R)
    (hb : b ∈ G.target) :
    ∃ x, x ∈ p.support ∧ x ∈ S := by
  induction p with
  | @nil a =>
      exact ⟨a, by simp, htarget ⟨hb, ha⟩⟩
  | @cons a c b hac p ih =>
      by_cases haS : a ∈ S
      · exact ⟨a, by simp, haS⟩
      · by_cases hcR : c ∈ R
        · obtain ⟨x, hxp, hxS⟩ := ih hcR hb
          exact ⟨x, by simp [hxp], hxS⟩
        · exact False.elim (haS (hexit hac ha hcR))

/-- Oriented-boundary form of the separator argument: if sources start in
`R` or on `S`, every edge leaving `R` leaves through `S`, and every target in
`R` lies on `S`, then `S` separates the source from the target. -/
theorem roof_of_forwardBoundary (G : DWeb V) {R S : Set V}
    (hsource : G.source ⊆ R ∪ S)
    (hexit : ∀ {x y}, G.graph.Adj x y → x ∈ R → y ∉ R → x ∈ S)
    (htarget : G.target ∩ R ⊆ S) :
    G.source ⊆ G.roof S := by
  intro a ha q hq
  have hstart : q.start ∈ R ∪ S := by
    rw [hq.1]
    exact hsource ha
  rcases hstart with hstart | hstart
  · obtain ⟨x, hxq, hxS⟩ :=
      Walk.exists_mem_of_forwardBoundary G hexit htarget q.walk hstart hq.2
    exact ⟨x, hxq, hxS⟩
  · exact ⟨q.start, q.start_mem_support, hstart⟩

/-- A residual blocking certificate for `J`.  The actual residual search
constructs `reachable`; this interface records exactly the three facts used
by the last-hit separator proof. -/
def IsOneHoleBlockingSet (G : DWeb V) (J : Set G.DPath)
    (hfin : G.HasFiniteCharacter J) (reachable : Set V) : Prop :=
  let boundary := Set.range (G.lastHitCut J hfin reachable)
  G.source ⊆ reachable ∪ boundary ∧
    (∀ {x y}, G.graph.Adj x y → x ∈ reachable →
      y ∉ reachable → x ∈ boundary) ∧
    G.target ∩ reachable ⊆ boundary

/-- The blocking output of a residual search is a genuine hindrance, hence
the second alternative of the one-hole dichotomy. -/
theorem oneHoleDichotomy_of_blockingSet
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    (hgap : (G.source \ G.initialSet J).Nonempty)
    {reachable : Set V}
    (hblock : G.IsOneHoleBlockingSet J hJ.hasFiniteCharacter reachable) :
    G.OneHoleDichotomy J := by
  right
  refine ⟨G.lastHitPrefixFamily J hJ.hasFiniteCharacter reachable, ?_⟩
  apply DWeb.IsWarp.isHindrance_lastHitPrefixFamily G hJ.isWarp
    hJ.hasFiniteCharacter hJ.initialSet_subset_source
    (DWeb.IsCleanFiniteWarp.initialSet_ne_source_of_gap_nonempty G hJ hgap)
    reachable
  exact G.roof_of_forwardBoundary hblock.1 hblock.2.1 hblock.2.2

/-- Exact residual-search output needed for the one-hole theorem. -/
def OneHoleSearchStatement (V : Type u) : Prop :=
  ∀ (G : DWeb V) (J : Set G.DPath), (hJ : G.IsCleanFiniteWarp J) →
    (G.source \ G.initialSet J).Nonempty →
      (∃ Jplus, G.IsOnePointAugmentation J Jplus) ∨
        ∃ reachable, G.IsOneHoleBlockingSet J hJ.hasFiniteCharacter reachable

/-- A complete residual search immediately supplies the one-hole principle. -/
theorem oneHolePrinciple_of_search
    (hsearch : OneHoleSearchStatement V) : OneHolePrinciple V := by
  intro G J hJ hgap
  rcases hsearch G J hJ hgap with haug | ⟨reachable, hblock⟩
  · exact Or.inl haug
  · exact G.oneHoleDichotomy_of_blockingSet hJ hgap hblock

private theorem terminalFrontier_eq_insert_sdiff_singleton
    (G : DWeb V) {W : Set G.DPath} {p : G.DPath} {t : V}
    (ht : G.terminal? p = some t) (hp : p ∈ W) :
    G.terminalFrontier W = insert t (G.terminalFrontier W \ {t}) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxt : x = t
    · exact Set.mem_insert_iff.2 (Or.inl hxt)
    · exact Set.mem_insert_of_mem t ⟨hx, by simpa using hxt⟩
  · exact Set.insert_subset ⟨p, hp, ht⟩ Set.sdiff_subset

/-- Singleton case of Lemma 3.31, assuming the one-hole augmentation
principle.  This theorem contains all normalization, endpoint, and separator
transport bookkeeping; the only missing ingredient is the residual search
itself. -/
theorem isHindered_delete_singleton_of_oneHolePrinciple
    (hone : OneHolePrinciple V) (G : DWeb V) {v : V}
    (hG : G.IsHindered) (hvA : v ∉ G.source) :
    (G.delete {v}).IsHindered := by
  obtain ⟨U, hU, hUfin, hUsource⟩ := G.exists_source_normalized_hindrance hG
  by_cases hvU : v ∈ G.vertexSet U
  · obtain ⟨p, hpU, hvp⟩ := hvU
    let pU : U := ⟨p, hpU⟩
    obtain ⟨q, hpq⟩ := hUfin hpU
    subst p
    let t : V := q.finish
    have hqt : G.terminal? (Sum.inl q : G.DPath) = some t := rfl
    have havoid : Disjoint (G.vertexSet (U \ {pU.1})) ({v} : Set V) :=
      DWeb.IsWarp.vertexSet_sdiff_singleton_disjoint_singleton
        G hU.1.1 pU.2 hvp
    let J : Set (G.delete {v}).DPath :=
      G.restrictDeleteFamily {v} (U \ {pU.1}) havoid
    let H : DWeb V := (G.delete {v}).retarget (G.terminalFrontier U)
    have hJwarp : H.IsWarp J := by
      change (G.delete {v}).IsWarp J
      exact DWeb.IsWarp.restrictDeleteFamily G
        (DWeb.IsWarp.sdiff_singleton G hU.1.1 pU.1) havoid
    have hJfin : H.HasFiniteCharacter J := by
      change (G.delete {v}).HasFiniteCharacter J
      exact G.fd_hasFiniteCharacter_restrictDeleteFamily
        (G.hasFiniteCharacter_sdiff_singleton hUfin pU.1) havoid
    have hJinit : H.initialSet J ⊆ H.source := by
      change (G.delete {v}).initialSet J ⊆ (G.delete {v}).source
      rw [G.initialSet_restrictDeleteFamily,
        DWeb.IsWarp.initialSet_sdiff_singleton G hU.1.1 pU.2]
      intro a ha
      exact ⟨hU.1.2.1 ha.1, fun hav ↦ hvA (by simpa using hav ▸ hU.1.2.1 ha.1)⟩
    have hJsource : ∀ r ∈ J,
        r.support ∩ H.source ⊆ {r.initial} := by
      change ∀ r ∈ J,
        r.support ∩ (G.delete {v}).source ⊆ {r.initial}
      apply G.fd_source_clean_restrictDeleteFamily havoid
        (by
          intro x hx
          exact fun hxA ↦ hvA (by simpa using hx ▸ hxA))
      intro r hr
      exact hUsource r hr.1
    have htFront : t ∈ G.terminalFrontier U := ⟨pU.1, pU.2, hqt⟩
    have htJ : t ∉ H.vertexSet J := by
      change t ∉ (G.delete {v}).vertexSet J
      intro ht
      rcases ht with ⟨r, hrJ, htr⟩
      change r ∈ G.restrictDeleteFamily {v} (U \ {pU.1}) havoid at hrJ
      obtain ⟨s, _hs, hrs⟩ := hrJ
      have htr' : t ∈ s.1.support := by
        subst r
        simpa using htr
      have hsp : s.1 = pU.1 := by
        by_contra hne
        exact Set.disjoint_left.1 (hU.1.1 s.2.1 pU.2 hne)
          htr' (G.terminal_mem_support hqt)
      exact s.2.2 (by simpa [hsp])
    have hJterm : (G.delete {v}).terminalFrontier J =
        G.terminalFrontier U \ {t} := by
      rw [G.terminalFrontier_restrictDeleteFamily]
      exact DWeb.IsWarp.terminalFrontier_sdiff_singleton
        G hU.1.1 pU.2 hqt
    have hHtarget : H.target = insert t (H.terminalFrontier J) := by
      change G.terminalFrontier U = insert t ((G.delete {v}).terminalFrontier J)
      rw [hJterm]
      exact terminalFrontier_eq_insert_sdiff_singleton G hqt pU.2
    have hJclean : H.IsCleanFiniteWarp J := by
      apply H.fd_isCleanFiniteWarp_of_single_target_gap
        hJwarp hJfin hJinit hJsource htJ hHtarget
    have htargetGap : (H.target \ H.terminalFrontier J).Subsingleton := by
      rw [hHtarget]
      intro x hx y hy
      rcases hx.1 with rfl | hxmem
      · rcases hy.1 with rfl | hymem
        · rfl
        · exact False.elim (hy.2 hymem)
      · exact False.elim (hx.2 hxmem)
    obtain ⟨aMissing, haMissing⟩ :
        (G.source \ G.initialSet U).Nonempty := by
      rw [Set.nonempty_def]
      by_contra hempty
      apply hU.2
      apply Set.Subset.antisymm hU.1.2.1
      intro a ha
      by_contra haU
      exact hempty ⟨a, ha, haU⟩
    have hpInit : pU.1.initial ∈ G.initialSet U :=
      ⟨pU.1, pU.2, rfl⟩
    have hsourceEq : H.source = G.source := by
      change (G.delete {v}).source = G.source
      exact G.fd_delete_source_eq_of_not_mem hvA
    have hJinitial : H.initialSet J =
        G.initialSet U \ {pU.1.initial} := by
      change (G.delete {v}).initialSet J = _
      rw [G.initialSet_restrictDeleteFamily]
      exact DWeb.IsWarp.initialSet_sdiff_singleton G hU.1.1 pU.2
    have haGap : aMissing ∈ H.source \ H.initialSet J := by
      rw [hsourceEq, hJinitial]
      exact ⟨haMissing.1, fun ha ↦ haMissing.2 ha.1⟩
    have hpGap : pU.1.initial ∈ H.source \ H.initialSet J := by
      rw [hsourceEq, hJinitial]
      exact ⟨hU.1.2.1 hpInit, fun hp ↦ hp.2 (Set.mem_singleton _)⟩
    have hne : aMissing ≠ pU.1.initial := by
      intro h
      apply haMissing.2
      rw [h]
      exact hpInit
    have hHdichotomy : H.OneHoleDichotomy J :=
      hone H J hJclean ⟨aMissing, haGap⟩
    have hHhindered : H.IsHindered :=
      H.isHindered_of_oneHoleDichotomy_of_two_source_gaps
        hJclean htargetGap haGap hpGap hne.symm hHdichotomy
    obtain ⟨W, hW⟩ := hHhindered
    refine ⟨W, ?_⟩
    apply DWeb.IsHindrance.of_retarget (G.delete {v}) hW
    exact (G.fd_delete_roof_frontier_sdiff (X := {v}) hU.1).trans
      ((G.delete {v}).roof_mono Set.sdiff_subset)
  · let havoid : Disjoint (G.vertexSet U) ({v} : Set V) :=
      Set.disjoint_left.2 fun x hxU hxv ↦ by
        have hxv' : x = v := Set.mem_singleton_iff.mp hxv
        subst x
        exact hvU hxU
    have hXA : ({v} : Set V) ⊆ G.sourceᶜ := by
      intro x hx
      have hxv : x = v := Set.mem_singleton_iff.mp hx
      subst x
      exact hvA
    refine ⟨G.restrictDeleteFamily {v} U havoid, ?_⟩
    exact DWeb.IsHindrance.restrictDeleteFamily G hU havoid hXA

/-- Finite form of Lemma 3.31, reduced to its singleton case. -/
theorem isHindered_delete_finite_of_oneHolePrinciple
    (hone : OneHolePrinciple V) (G : DWeb V) {F : Set V}
    (hG : G.IsHindered) (hF : F.Finite) (hFA : F ⊆ G.sourceᶜ) :
    (G.delete F).IsHindered := by
  induction F, hF using Set.Finite.induction_on with
  | empty => simpa using hG
  | @insert v F hvF hF ih =>
      have hFsub : F ⊆ G.sourceᶜ :=
        fun x hx ↦ hFA (Set.mem_insert_of_mem v hx)
      have hdelF : (G.delete F).IsHindered := ih hFsub
      have hvSource : v ∉ (G.delete F).source := by
        intro hv
        exact hFA (Set.mem_insert v F) hv.1
      have hstep := isHindered_delete_singleton_of_oneHolePrinciple
        hone (G.delete F) hdelF hvSource
      simpa only [G.delete_delete_singleton, Set.insert_comm] using hstep

/-- Lemma 3.32, assuming the one-hole principle.  A normalized hindrance in
the deleted web is lifted and viewed as an almost-complete wave in the web
retargeted to its old frontier together with the restored vertex. -/
theorem exists_wave_terminalFrontier_of_delete_isHindered_of_oneHolePrinciple
    (hone : OneHolePrinciple V) (G : DWeb V) {v : V}
    (hG : G.IsUnhindered) (hvA : v ∉ G.source)
    (hdel : (G.delete {v}).IsHindered) :
    ∃ W : Set G.DPath, G.IsWave W ∧ v ∈ G.terminalFrontier W := by
  let D := G.delete {v}
  obtain ⟨U, hU, hUfin, hUsource⟩ := D.exists_source_normalized_hindrance hdel
  let Z : Set G.DPath := G.liftDeleteFamily {v} U
  let C : Set V := D.terminalFrontier U ∪ {v}
  let H : DWeb V := G.retarget C
  have hZwarp : H.IsWarp Z := by
    change G.IsWarp Z
    exact hU.1.1.liftDeleteFamily
  have hZfin : H.HasFiniteCharacter Z := by
    change G.HasFiniteCharacter Z
    exact G.fd_hasFiniteCharacter_liftDeleteFamily hUfin
  have hZinit : H.initialSet Z ⊆ H.source := by
    change G.initialSet Z ⊆ G.source
    simpa [Z, D] using hU.1.2.1.trans Set.sdiff_subset
  have hZsource : ∀ p ∈ Z, p.support ∩ H.source ⊆ {p.initial} := by
    change ∀ p ∈ Z, p.support ∩ G.source ⊆ {p.initial}
    apply G.fd_source_clean_liftDeleteFamily hUsource
    intro x hx
    exact fun hxA ↦ hvA (by simpa using hx ▸ hxA)
  have hvZ : v ∉ H.vertexSet Z := by
    change v ∉ G.vertexSet Z
    intro hv
    rcases hv with ⟨p, hpZ, hvp⟩
    obtain ⟨q, hq, rfl⟩ := hpZ
    have hpinit : q.initial ∉ ({v} : Set V) :=
      (hU.1.2.1 ⟨q, hq, rfl⟩).2
    exact Set.disjoint_left.1
      (G.liftDeleteFamily_member_avoids ⟨q, hq, rfl⟩ (by simpa using hpinit))
      hvp (Set.mem_singleton v)
  have hHtarget : H.target = insert v (H.terminalFrontier Z) := by
    change D.terminalFrontier U ∪ {v} = insert v (G.terminalFrontier Z)
    rw [G.terminalFrontier_liftDeleteFamily]
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto
  have hZclean : H.IsCleanFiniteWarp Z := by
    apply H.fd_isCleanFiniteWarp_of_single_target_gap
      hZwarp hZfin hZinit hZsource hvZ hHtarget
  have hroof : G.source ⊆ G.roof C := by
    simpa [C, D, Set.union_comm] using
      G.roof_terminalFrontier_union_singleton_of_delete_wave hU.1 hvA
  have hHunhindered : H.IsUnhindered := by
    rw [H.isUnhindered_iff_not_isHindered]
    intro hH
    exact (G.isUnhindered_iff_not_isHindered.1 hG)
      ⟨hH.choose, DWeb.IsHindrance.of_retarget G hH.choose_spec hroof⟩
  obtain ⟨aMissing, haMissing⟩ :
      (D.source \ D.initialSet U).Nonempty := by
    rw [Set.nonempty_def]
    by_contra hempty
    apply hU.2
    apply Set.Subset.antisymm hU.1.2.1
    intro a ha
    by_contra haU
    exact hempty ⟨a, ha, haU⟩
  have haGap : aMissing ∈ H.source \ H.initialSet Z := by
    constructor
    · exact haMissing.1.1
    · change aMissing ∉ G.initialSet Z
      rw [G.initialSet_liftDeleteFamily]
      exact haMissing.2
  rcases hone H Z hZclean ⟨aMissing, haGap⟩ with haug | hhind
  · obtain ⟨Zplus, a, ha, b, hb, hwarp, _hfin, hinit, hterm⟩ := haug
    have hbv : b = v := by
      rw [hHtarget] at hb
      rcases hb.1 with h | h
      · exact h
      · exact False.elim (hb.2 h)
    subst b
    have hinitSub : H.initialSet Zplus ⊆ H.source := by
      rw [hinit]
      exact Set.insert_subset ha.1 hZclean.initialSet_subset_source
    have htermC : H.terminalFrontier Zplus = C := by
      rw [hterm, ← hHtarget]
      rfl
    have hWaveH : H.IsWave Zplus :=
      H.isWave_retarget_of_terminalFrontier_eq hwarp hinitSub htermC
    have hWaveG : G.IsWave Zplus := by
      exact DWeb.IsWave.of_retarget G hWaveH hroof
    refine ⟨Zplus, hWaveG, ?_⟩
    change v ∈ H.terminalFrontier Zplus
    rw [hterm]
    exact Set.mem_insert v _
  · exact False.elim
      (H.isUnhindered_iff_not_isHindered.1 hHunhindered hhind)

end DWeb
end Erdos599
