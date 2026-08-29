/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating
import ErdosProblems.Erdos599.AlternatingSourceAssertions
import ErdosProblems.Erdos599.AlternatingTraceOps
import ErdosProblems.Erdos599.SafeSwitching

/-!
# The endpoint-pure safe alternating-path dichotomy

This file develops the maximal safe-path construction underlying
Aharoni--Berger Lemma 4.13 for the endpoint-pure normalized interface used
by the application.  `SourceSafeAlternatingDichotomyStatement` in
`Alternating.lean` records the unnormalized printed interface, but that
interface is not asserted here: without the paper's suppressed/duplicated
occurrence model it has a four-vertex counterexample.  Endpoint purity is the
valid relation-level target.  The zero-link case is split off first.
-/

namespace Erdos599
namespace Alternating

open Set
open DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

/-- The endpoint-pure statement used by the application is an immediate
specialization of the literal source statement.  This keeps the two theorem
interfaces separate: a proof of the source lemma may ignore the ambient web
sides, while the recursive application records normalization explicitly. -/
theorem safeAlternatingDichotomyStatement_of_source
    (h : SourceSafeAlternatingDichotomyStatement Γ) :
    SafeAlternatingDichotomyStatement Γ := by
  intro _hΓ Z Y _hZA _hZB hZ hY hZfin hYfin hinit u hu
  exact h Z Y hZ hY hZfin hYfin hinit u hu

/-! ## Extending finite traces and taking an ω-limit -/

namespace FiniteTrace

/-- Append one link, with the three exact obligations imposed by the global
collision rules of `FiniteTrace`. -/
def extend {D : Digraph V} (Q : FiniteTrace D) (l : Link D)
    (hjoin : Q.lastLink.exit = l.entry)
    (halternates : Q.lastLink.direction ≠ l.direction)
    (hcompatible : ∀ i : Fin (Q.lastIndex + 1),
      CompatibleInOrder (Q.lastIndex + 1 = i.1 + 1) (Q.link i) l) :
    FiniteTrace D where
  lastIndex := Q.lastIndex + 1
  link := Fin.lastCases l Q.link
  joins := by
    intro i
    obtain ⟨j, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · rw [Fin.lastCases_castSucc, Fin.succ_castSucc, Fin.lastCases_castSucc]
      exact Q.joins j
    · have hlast : Q.link (Fin.last Q.lastIndex) = Q.lastLink := by congr
      simpa [hlast] using hjoin
  alternates := by
    intro i
    obtain ⟨j, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · rw [Fin.lastCases_castSucc, Fin.succ_castSucc, Fin.lastCases_castSucc]
      exact Q.alternates j
    · have hlast : Q.link (Fin.last Q.lastIndex) = Q.lastLink := by congr
      simpa [hlast] using halternates
  compatible := by
    intro i j hij
    obtain ⟨j₀, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
    · obtain ⟨i₀, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
      · simpa using Q.compatible i₀ j₀ (by simpa using hij)
      · exact (not_lt_of_ge (Fin.le_last j₀.castSucc) hij).elim
    · obtain ⟨i₀, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
      · simpa using hcompatible i₀
      · exact (lt_irrefl _ hij).elim

@[simp]
theorem firstLink_extend {D : Digraph V} (Q : FiniteTrace D) (l : Link D)
    (hjoin) (halternates) (hcompatible) :
    (Q.extend l hjoin halternates hcompatible).firstLink = Q.firstLink := by
  change Fin.lastCases l Q.link (0 : Fin (Q.lastIndex + 2)) = Q.link 0
  rw [show (0 : Fin (Q.lastIndex + 2)) =
      (0 : Fin (Q.lastIndex + 1)).castSucc by rfl]
  exact Fin.lastCases_castSucc _

@[simp]
theorem lastLink_extend {D : Digraph V} (Q : FiniteTrace D) (l : Link D)
    (hjoin) (halternates) (hcompatible) :
    (Q.extend l hjoin halternates hcompatible).lastLink = l := by
  change Fin.lastCases l Q.link
    (⟨Q.lastIndex + 1, Nat.lt_succ_self _⟩ : Fin (Q.lastIndex + 2)) = l
  rw [show (⟨Q.lastIndex + 1, Nat.lt_succ_self _⟩ : Fin (Q.lastIndex + 2)) =
      Fin.last (Q.lastIndex + 1) by rfl]
  simp

@[simp]
theorem initial_extend {D : Digraph V} (Q : FiniteTrace D) (l : Link D)
    (hjoin) (halternates) (hcompatible) :
    (Q.extend l hjoin halternates hcompatible).initial = Q.initial := by
  simp [FiniteTrace.initial]

@[simp]
theorem terminal_extend {D : Digraph V} (Q : FiniteTrace D) (l : Link D)
    (hjoin) (halternates) (hcompatible) :
    (Q.extend l hjoin halternates hcompatible).terminal = l.exit := by
  simp [FiniteTrace.terminal]

end FiniteTrace

/-! ## The safely reachable and reverse-reachable sets -/

/-- `SR` in the proof of Lemma 4.13: uncovered `Z`-terminals reached by a
safe `[Z,Y]`-alternating path from `u`. -/
def SafelyReachable (Z Y : Set Γ.DPath) (u : V) : Set V :=
  {v | v ∈ Γ.terminalFrontier Z \ Γ.vertexSet Y ∧
    ∃ Q : AltPath Γ.graph,
      IsBracketSafe Z Y Q ∧ Q.initial = u ∧ Q.terminal? = some v}

/-- `C` in the proof of Lemma 4.13: vertices reverse-reachable from `SR` by
a `[Y,Z]`-alternating path. -/
def ReverseReachable (Z Y : Set Γ.DPath) (u : V) : Set V :=
  {x | ∃ v ∈ SafelyReachable Z Y u,
    ∃ T : AltPath Γ.graph,
      IsBracketAlternating Y Z T ∧ T.initial = v ∧ T.terminal? = some x}

/-- The reverse-reachable set used by the repaired application-level
dichotomy.  Unlike the literal source set above, its reducing witness records
all forward contacts with `Z`, so it can be switched if the search reaches
back to `u`. -/
def ContactMarkedReverseReachable (Z Y : Set Γ.DPath) (u : V) : Set V :=
  {x | ∃ v ∈ SafelyReachable Z Y u,
    ∃ T : AltPath Γ.graph,
      IsBracketSwitchingAlternating Y Z T ∧
        T.initial = v ∧ T.terminal? = some x}

theorem safeAlternatingDichotomy_of_mem_reverseReachable
    {Z Y : Set Γ.DPath} {u : V}
    (hu : u ∈ ReverseReachable Z Y u) :
    SafeAlternatingDichotomy Z Y u := by
  right
  rcases hu with ⟨v, hvSR, T, hTsafe, hTinit, hTterm⟩
  rcases hvSR with ⟨hv, Q, hQsafe, hQinit, hQterm⟩
  exact ⟨v, hv, Q, hQsafe, hQinit, hQterm, T, hTsafe, hTinit, hTterm⟩

theorem not_mem_reverseReachable_of_not_dichotomy
    {Z Y : Set Γ.DPath} {u : V}
    (h : ¬ SafeAlternatingDichotomy Z Y u) :
    u ∉ ReverseReachable Z Y u :=
  fun hu ↦ h (safeAlternatingDichotomy_of_mem_reverseReachable hu)

theorem contactMarkedSafeAlternatingDichotomy_of_mem_reverseReachable
    {Z Y : Set Γ.DPath} {u : V}
    (hu : u ∈ ContactMarkedReverseReachable Z Y u) :
    ContactMarkedSafeAlternatingDichotomy Z Y u := by
  right
  rcases hu with ⟨v, hvSR, T, hTmarked, hTinit, hTterm⟩
  rcases hvSR with ⟨hv, Q, hQsafe, hQinit, hQterm⟩
  exact ⟨v, hv, Q, hQsafe, hQinit, hQterm, T, hTmarked, hTinit, hTterm⟩

theorem not_mem_contactMarkedReverseReachable_of_not_dichotomy
    {Z Y : Set Γ.DPath} {u : V}
    (h : ¬ ContactMarkedSafeAlternatingDichotomy Z Y u) :
    u ∉ ContactMarkedReverseReachable Z Y u :=
  fun hu ↦ h (contactMarkedSafeAlternatingDichotomy_of_mem_reverseReachable hu)

/-! ## Collision-trimmed reverse extensions -/

/-- A finite alternating trace whose terminal lies on its reference warp
cannot end forward.  Thus the reverse-reachability extensions in Assertions
4.15--4.18 replace the last backward link rather than appending another
backward link. -/
theorem lastDirection_eq_backward_of_terminal_mem_reference
    {Y Z : Set Γ.DPath} (T : FiniteTrace Γ.graph)
    (hT : IsBracketAlternating Y Z (.finite T))
    (hterminal : T.terminal ∈ Γ.vertexSet Z) :
    T.lastLink.direction = .backward := by
  rcases hT.1 with ⟨_, _, _, hlastOutside⟩
  cases hdir : T.lastLink.direction with
  | backward => rfl
  | forward =>
      exact False.elim ((hlastOutside T.terminal rfl (by
        change some T.lastLink.direction = some .forward
        simp [hdir])) hterminal)

/-- Replacing the final backward link by a longer collision-compatible
backward link preserves bracket alternation.  The genuine shortening step
chooses `new` at the last collision and discharges `hnewCompat`; this lemma
contains the invariant bookkeeping after that choice. -/
theorem exists_isBracketAlternating_replaceLastBackward
    {Y Z : Set Γ.DPath} (P : FiniteTrace Γ.graph)
    (old new : Link Γ.graph)
    (holdDir : old.direction = .backward)
    (hnewDir : new.direction = .backward)
    (holdJoin : P.terminal = old.entry)
    (holdAlt : P.lastLink.direction ≠ old.direction)
    (holdCompat : P.SnocCompatible old)
    (hnewJoin : P.terminal = new.entry)
    (hnewAlt : P.lastLink.direction ≠ new.direction)
    (hnewCompat : P.SnocCompatible new)
    (holdnew : old.path.support ⊆ new.path.support)
    (hnewZ : IsFragmentOf new.path Z)
    (hT : IsBracketAlternating Y Z
      (.finite (P.snoc old holdJoin holdAlt holdCompat))) :
    ∃ T' : FiniteTrace Γ.graph,
      IsBracketAlternating Y Z (.finite T') ∧
        T'.initial = (P.snoc old holdJoin holdAlt holdCompat).initial ∧
        T'.terminal = new.exit := by
  let Told := P.snoc old holdJoin holdAlt holdCompat
  let Tnew := P.snoc new hnewJoin hnewAlt hnewCompat
  rcases hT with ⟨hA, hFY⟩
  rcases hA with ⟨hZWarp, hBZ, hIni, hTer⟩
  have hlinksOld : Told.links = P.links ∪ {old} := by
    simpa [Told] using FiniteTrace.links_snoc P old holdJoin holdAlt holdCompat
  have hlinksNew : Tnew.links = P.links ∪ {new} := by
    simpa [Tnew] using FiniteTrace.links_snoc P new hnewJoin hnewAlt hnewCompat
  have hfirstOld : Told.firstLink = P.firstLink := by
    simpa [Told] using FiniteTrace.firstLink_snoc P old holdJoin holdAlt holdCompat
  have hfirstNew : Tnew.firstLink = P.firstLink := by
    simpa [Tnew] using FiniteTrace.firstLink_snoc P new hnewJoin hnewAlt hnewCompat
  have hinit : Tnew.initial = Told.initial := by
    rw [show Tnew.initial = P.initial by
      simpa [Tnew] using FiniteTrace.initial_snoc P new hnewJoin hnewAlt hnewCompat]
    symm
    simpa [Told] using FiniteTrace.initial_snoc P old holdJoin holdAlt holdCompat
  have hlastNew : Tnew.lastLink = new := by
    simpa [Tnew] using FiniteTrace.lastLink_snoc P new hnewJoin hnewAlt hnewCompat
  have hterminal : Tnew.terminal = new.exit := by
    simpa [Tnew] using FiniteTrace.terminal_snoc P new hnewJoin hnewAlt hnewCompat
  refine ⟨Tnew, ⟨⟨hZWarp, ?_, ?_, ?_⟩, ?_⟩, hinit, hterminal⟩
  · intro k hk hkback
    change k ∈ Tnew.links at hk
    rw [hlinksNew] at hk
    rcases hk with hkP | hknew
    · apply hBZ k
      · change k ∈ Told.links
        rw [hlinksOld]
        exact Or.inl hkP
      · exact hkback
    · have hkn : k = new := by simpa using hknew
      subst k
      exact hnewZ
  · intro hdir
    apply hIni
    change some Tnew.firstLink.direction = some .forward at hdir
    change some Told.firstLink.direction = some .forward
    simpa [hfirstOld, hfirstNew] using hdir
  · intro t ht hdir
    change some Tnew.lastLink.direction = some .forward at hdir
    rw [hlastNew, hnewDir] at hdir
    simp at hdir
  · intro k hk hkforward
    change k ∈ Tnew.links at hk
    rw [hlinksNew] at hk
    rcases hk with hkP | hknew
    · apply hFY k
      · change k ∈ Told.links
        rw [hlinksOld]
        exact Or.inl hkP
      · exact hkforward
    · have hkn : k = new := by simpa using hknew
      subst k
      simp [hnewDir] at hkforward

/-! ## Finite stages of the maximal construction -/

/-- The union of the interiors of the backward links already used by an
alternating path (`B_i` in the source proof). -/
def backwardInterior (Q : AltPath Γ.graph) : Set V :=
  ⋃ l ∈ Q.links, ⋃ (_ : l.direction = .backward), l.interior

/-- The invariant carried by the finite stages `S_i` in Lemma 4.13.  In the
unreduced concrete web the terminal is recorded explicitly as lying on `Z`;
this replaces the source's preliminary suppression assumption
`V[Y] ⊆ V[Z]`. -/
structure SafeStage (Z Y : Set Γ.DPath) (u : V) (C : Set V) where
  trace : FiniteTrace Γ.graph
  bracketSafe : IsBracketSafe Z Y (.finite trace)
  initial_eq : trace.initial = u
  first_forward : trace.firstLink.direction = .forward
  last_backward : trace.lastLink.direction = .backward
  terminal_mem_Z : trace.terminal ∈ Γ.vertexSet Z
  terminal_not_mem_C : trace.terminal ∉ C

namespace SafeStage

def path {Z Y : Set Γ.DPath} {u : V} {C : Set V}
    (S : SafeStage Z Y u C) : AltPath Γ.graph :=
  .finite S.trace

@[simp]
theorem path_initial {Z Y : Set Γ.DPath} {u : V} {C : Set V}
    (S : SafeStage Z Y u C) : S.path.initial = u :=
  S.initial_eq

@[simp]
theorem path_terminal {Z Y : Set Γ.DPath} {u : V} {C : Set V}
    (S : SafeStage Z Y u C) :
    S.path.terminal? = some S.trace.terminal :=
  rfl

end SafeStage

/-! ## The zero-link endpoint case -/

theorem isAlternating_trivial {Y : Set Γ.DPath} (hY : Γ.IsWarp Y) (u : V) :
    IsAlternating Y (.trivial u) := by
  refine ⟨hY, ?_, ?_, ?_⟩
  · simp [BackwardLinksOn]
  · simp
  · simp

theorem isBracketAlternating_trivial {U Y : Set Γ.DPath}
    (hY : Γ.IsWarp Y) (u : V) :
    IsBracketAlternating U Y (.trivial u) := by
  exact ⟨isAlternating_trivial hY u, by simp⟩

theorem isSafe_trivial {Y : Set Γ.DPath} (hY : Γ.IsWarp Y) (u : V) :
    IsSafe Y (.trivial u) := by
  refine ⟨isAlternating_trivial hY u, ?_, ?_, ?_⟩
  · intro p hp
    exact Or.inl (by simp [AltPath.directionEdges])
  · simp only [AltPath.edgeSet_trivial, Set.empty_sdiff]
    change ¬ ∃ R : DirectedRay V, R.EdgeSet ⊆ ∅
    rintro ⟨R, hR⟩
    exact hR ⟨0, rfl⟩
  · simp only [AltPath.edgeSet_trivial, Set.empty_sdiff]
    change ¬ ∃ C : DirectedCycle V, C.EdgeSet ⊆ ∅
    rintro ⟨C, hC⟩
    exact hC ⟨⟨0, C.positive⟩, rfl⟩

theorem isBracketSafe_trivial {U Y : Set Γ.DPath}
    (hY : Γ.IsWarp Y) (u : V) :
    IsBracketSafe U Y (.trivial u) := by
  exact ⟨isSafe_trivial hY u, isBracketAlternating_trivial hY u⟩

/-! ## The first forward/backward stage -/

/-- The edges of one finite fragment of a member of a warp form one interval
on every member of that warp.  This is the interval bookkeeping needed for
the first backward link of the source construction. -/
theorem fragment_inter_isEdgeInterval
    {Y : Set Γ.DPath} (hY : Γ.IsWarp Y)
    (r : FinitePath Γ.graph) (hr : IsFragmentOf r Y) :
    ∀ p ∈ Y, IsEdgeInterval (r.edgeSet ∩ p.edgeSet) p := by
  rcases hr with ⟨p₀, hp₀Y, hrp₀⟩
  intro p hpY
  by_cases hpp₀ : p = p₀
  · subst p
    right
    refine ⟨.inl r, hrp₀, ?_⟩
    exact Set.inter_eq_left.2 hrp₀.2
  · left
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨e, he⟩
    have hdisj : Disjoint p.support p₀.support :=
      DWeb.IsWarp.disjoint (Γ := Γ) hY hpY hp₀Y hpp₀
    have her := r.edgeSet_subset_support_prod he.1
    have hep := p.edgeSet_subset_support_prod he.2
    have herp₀ : e.1 ∈ p₀.support := hrp₀.1 her.1
    exact Set.disjoint_left.1 hdisj hep.1 herp₀

theorem safeAlternatingDichotomy_of_mem_terminalFrontier
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    {u : V} (huT : u ∈ Γ.terminalFrontier Z) (huY : u ∉ Γ.vertexSet Y) :
    SafeAlternatingDichotomy Z Y u := by
  right
  refine ⟨u, ⟨huT, huY⟩, .trivial u, isBracketSafe_trivial hY u, rfl, rfl,
    .trivial u, isBracketAlternating_trivial hZ u, rfl, rfl⟩

theorem contactMarkedSafeAlternatingDichotomy_of_mem_terminalFrontier
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    {u : V} (huT : u ∈ Γ.terminalFrontier Z) (huY : u ∉ Γ.vertexSet Y) :
    ContactMarkedSafeAlternatingDichotomy Z Y u := by
  right
  refine ⟨u, ⟨huT, huY⟩, .trivial u, isBracketSafe_trivial hY u, rfl, rfl,
    .trivial u, ⟨isBracketAlternating_trivial hZ u, ?_, ?_⟩, rfl, rfl⟩
  · simp [ForwardLinksOff]
  · simp [ForwardVertexContactsCovered, AltPath.directionVertices]

/-! ## A first maximality case: a reference path avoiding the other warp -/

theorem finitePath_edgeSet_disjoint_familyEdges_of_support_disjoint
    {Y : Set Γ.DPath} (q : FinitePath Γ.graph)
    (hdisj : Disjoint q.support (Γ.vertexSet Y)) :
    Disjoint q.edgeSet (familyEdges Y) := by
  rw [Set.disjoint_left]
  intro e heq heY
  have heqv := q.edgeSet_subset_support_prod heq
  simp only [familyEdges, Set.mem_iUnion] at heY
  rcases heY with ⟨p, hpY, hep⟩
  have hepv := p.edgeSet_subset_support_prod hep
  exact Set.disjoint_left.1 hdisj heqv.1 ⟨p, hpY, hepv.1⟩

theorem finitePath_finish_not_mem_vertexSet_of_support_disjoint
    {Y : Set Γ.DPath} (q : FinitePath Γ.graph)
    (hdisj : Disjoint q.support (Γ.vertexSet Y)) :
    q.finish ∉ Γ.vertexSet Y := by
  exact fun h ↦ Set.disjoint_left.1 hdisj q.finish_mem_support h

/-! ## Finite-character warps contain no ray or cycle in their edge union -/

theorem familyEdges_not_containsDirectedRay
    {W : Set Γ.DPath} (hW : Γ.IsWarp W)
    (hfin : Γ.HasFiniteCharacter W) :
    ¬ ContainsDirectedRay (familyEdges W) := by
  rintro ⟨R, hR⟩
  obtain ⟨p₀, hp₀W, hp₀edge⟩ :
      ∃ p₀ ∈ W, (R.vertex 0, R.vertex 1) ∈ p₀.edgeSet := by
    have hm := hR ⟨0, rfl⟩
    simp only [familyEdges, Set.mem_iUnion] at hm
    rcases hm with ⟨p₀, hp₀W, hp₀edge⟩
    exact ⟨p₀, hp₀W, by simpa using hp₀edge⟩
  have hedge : ∀ n : ℕ, (R.vertex n, R.vertex (n + 1)) ∈ p₀.edgeSet := by
    intro n
    induction n with
    | zero => simpa using hp₀edge
    | succ n ih =>
        obtain ⟨p, hpW, hpedge⟩ :
            ∃ p ∈ W, (R.vertex (n + 1), R.vertex (n + 1 + 1)) ∈ p.edgeSet := by
          have hm := hR ⟨n + 1, rfl⟩
          simp only [familyEdges, Set.mem_iUnion] at hm
          rcases hm with ⟨p, hpW, hpedge⟩
          exact ⟨p, hpW, hpedge⟩
        have hprev : R.vertex (n + 1) ∈ p₀.support :=
          (p₀.edgeSet_subset_support_prod ih).2
        have hnext : R.vertex (n + 1) ∈ p.support :=
          (p.edgeSet_subset_support_prod hpedge).1
        have hp : p = p₀ :=
          DWeb.IsWarp.eq_of_mem_support hW hpW hp₀W hnext hprev
        exact hp ▸ hpedge
  obtain ⟨q, hp₀⟩ := hfin hp₀W
  subst p₀
  have hall : ∀ n : ℕ, R.vertex n ∈ q.support := by
    intro n
    cases n with
    | zero => exact (q.edgeSet_subset_support_prod (hedge 0)).1
    | succ n => exact (q.edgeSet_subset_support_prod (hedge n)).2
  exact q.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem R.injective hall)

theorem familyEdges_not_containsDirectedCycle
    {W : Set Γ.DPath} (hW : Γ.IsWarp W)
    (hfin : Γ.HasFiniteCharacter W) :
    ¬ ContainsDirectedCycle (familyEdges W) := by
  rintro ⟨C, hC⟩
  let i₀ : Fin C.length := ⟨0, C.positive⟩
  obtain ⟨p₀, hp₀W, hp₀edge⟩ :
      ∃ p₀ ∈ W, (C.vertex i₀, C.vertex (C.next i₀)) ∈ p₀.edgeSet := by
    have hm := hC ⟨i₀, rfl⟩
    simp only [familyEdges, Set.mem_iUnion] at hm
    rcases hm with ⟨p₀, hp₀W, hp₀edge⟩
    exact ⟨p₀, hp₀W, hp₀edge⟩
  have hedgeNat : ∀ n : ℕ, ∀ hn : n < C.length,
      (C.vertex ⟨n, hn⟩, C.vertex (C.next ⟨n, hn⟩)) ∈ p₀.edgeSet := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa [i₀] using hp₀edge
    | succ n ih =>
        intro hn
        have hn' : n < C.length := Nat.lt_trans (Nat.lt_succ_self n) hn
        have hnext : C.next (⟨n, hn'⟩ : Fin C.length) = ⟨n + 1, hn⟩ := by
          ext
          exact Nat.mod_eq_of_lt hn
        obtain ⟨p, hpW, hpedge⟩ : ∃ p ∈ W,
            (C.vertex ⟨n + 1, hn⟩, C.vertex (C.next ⟨n + 1, hn⟩)) ∈
              p.edgeSet := by
          have hm := hC ⟨⟨n + 1, hn⟩, rfl⟩
          simp only [familyEdges, Set.mem_iUnion] at hm
          rcases hm with ⟨p, hpW, hpedge⟩
          exact ⟨p, hpW, hpedge⟩
        have hprev : C.vertex ⟨n + 1, hn⟩ ∈ p₀.support := by
          rw [← hnext]
          exact (p₀.edgeSet_subset_support_prod (ih hn')).2
        have hcur : C.vertex ⟨n + 1, hn⟩ ∈ p.support :=
          (p.edgeSet_subset_support_prod hpedge).1
        have hp : p = p₀ :=
          DWeb.IsWarp.eq_of_mem_support hW hpW hp₀W hcur hprev
        exact hp ▸ hpedge
  have hCp₀ : C.EdgeSet ⊆ p₀.edgeSet := by
    rintro e ⟨i, rfl⟩
    exact hedgeNat i.1 i.2
  obtain ⟨q, hp₀⟩ := hfin hp₀W
  subst p₀
  exact FinitePath.edgeSet_not_containsDirectedCycle q ⟨C, hCp₀⟩

/-- The reusable final safety check in the maximal construction.  Once the
backward pieces form one interval on each member of `Y`, all remaining edges
lie in the finite-character warp `Z`; the two forbidden infinite/cyclic
configurations therefore cannot occur. -/
theorem isSafe_of_outside_subset_familyEdges
    {Z Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hAlt : IsAlternating Y Q)
    (hIntervals : ∀ p ∈ Y,
      IsEdgeInterval (Q.directionEdges .backward ∩ p.edgeSet) p)
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (hOutside : Q.edgeSet \ familyEdges Y ⊆ familyEdges Z) :
    IsSafe Y Q := by
  refine ⟨hAlt, hIntervals, ?_, ?_⟩
  · rintro ⟨R, hR⟩
    exact familyEdges_not_containsDirectedRay hZ hZfin ⟨R, hR.trans hOutside⟩
  · rintro ⟨C, hC⟩
    exact familyEdges_not_containsDirectedCycle hZ hZfin ⟨C, hC.trans hOutside⟩

/-- For a bracket-alternating path, every edge outside the reference warp
comes from a forward link and hence from the forward warp. -/
theorem IsBracketAlternating.outside_subset_familyEdges
    {Z Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hQ : IsBracketAlternating Z Y Q) :
    Q.edgeSet \ familyEdges Y ⊆ familyEdges Z := by
  rintro e ⟨heQ, heY⟩
  rw [Q.edgeSet_eq_iUnion_links] at heQ
  simp only [Set.mem_iUnion] at heQ
  rcases heQ with ⟨l, hlQ, hel⟩
  cases hdir : l.direction with
  | forward =>
      rcases hQ.2 l hlQ hdir with ⟨p, hpZ, hsub⟩
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨p, hpZ, hsub.2 hel⟩
  | backward =>
      exfalso
      apply heY
      rcases hQ.1.2.1 l hlQ hdir with ⟨p, hpY, hsub⟩
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨p, hpY, hsub.2 hel⟩

/-- In a finite-character bracket, the interval condition is the only
additional safety obligation: ray- and cycle-freeness follow from the
finite-character forward warp. -/
theorem isBracketSafe_of_intervals
    {Z Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (hQ : IsBracketAlternating Z Y Q)
    (hIntervals : ∀ p ∈ Y,
      IsEdgeInterval (Q.directionEdges .backward ∩ p.edgeSet) p) :
    IsBracketSafe Z Y Q := by
  exact ⟨isSafe_of_outside_subset_familyEdges hQ.1 hIntervals hZ hZfin
    hQ.outside_subset_familyEdges, hQ⟩

/-- Assemble the initial two-link safe stage once the source assertions have
chosen its forward fragment and its first backward fragment.  The theorem is
deliberately certificate-based: all path-order choices remain outside this
pure trace constructor. -/
theorem exists_isBracketSafe_forward_backward
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z)
    (F R : Link Γ.graph)
    (hFdir : F.direction = .forward)
    (hRdir : R.direction = .backward)
    (hjoin : F.exit = R.entry)
    (hcompat : CompatibleInOrder True F R)
    (hFZ : IsFragmentOf F.path Z)
    (hRY : IsFragmentOf R.path Y)
    (hFoff : Disjoint F.path.edgeSet (familyEdges Y))
    (hFinitial : F.entry ∉ Γ.vertexSet Y) :
    ∃ T : FiniteTrace Γ.graph,
      IsBracketSafe Z Y (.finite T) ∧
        T.initial = F.entry ∧ T.terminal = R.exit ∧
        T.firstLink = F ∧ T.lastLink = R := by
  let T₀ : FiniteTrace Γ.graph := .singleton F
  have hjoin₀ : T₀.terminal = R.entry := by
    simpa [T₀] using hjoin
  have halt₀ : T₀.lastLink.direction ≠ R.direction := by
    simpa [T₀, hFdir, hRdir]
  have hcompat₀ : T₀.SnocCompatible R := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change CompatibleInOrder (0 + 1 = 0 + 1) F R
    simpa using hcompat
  let T := T₀.snoc R hjoin₀ halt₀ hcompat₀
  have hlinks₀ : T₀.links = {F} := by
    ext l
    constructor
    · rintro ⟨i, rfl⟩
      simp [T₀, FiniteTrace.singleton]
    · intro hl
      have hlf : l = F := by simpa using hl
      subst l
      exact ⟨0, by simp [T₀, FiniteTrace.singleton]⟩
  have hlinks : T.links = {F, R} := by
    rw [show T.links = T₀.links ∪ {R} by
      simpa [T] using FiniteTrace.links_snoc T₀ R hjoin₀ halt₀ hcompat₀]
    rw [hlinks₀]
    ext l
    simp [or_comm]
  have hAlt : IsBracketAlternating Z Y (.finite T) := by
    refine ⟨⟨hY, ?_, ?_, ?_⟩, ?_⟩
    · intro l hl hldir
      change l ∈ T.links at hl
      rw [hlinks] at hl
      rcases hl with hl | hl
      · have hlF : l = F := by simpa using hl
        subst l
        rw [hFdir] at hldir
        cases hldir
      · have hlR : l = R := by simpa using hl
        subst l
        exact hRY
    · intro _
      change T.initial ∉ Γ.vertexSet Y
      simpa [T, T₀] using hFinitial
    · intro t ht hlast
      have hlastR : T.lastLink = R := by
        simpa [T] using FiniteTrace.lastLink_snoc T₀ R hjoin₀ halt₀ hcompat₀
      change some T.lastLink.direction = some .forward at hlast
      rw [hlastR, hRdir] at hlast
      simp at hlast
    · intro l hl hldir
      change l ∈ T.links at hl
      rw [hlinks] at hl
      rcases hl with hl | hl
      · have hlF : l = F := by simpa using hl
        subst l
        exact hFZ
      · have hlR : l = R := by simpa using hl
        subst l
        rw [hRdir] at hldir
        cases hldir
  have hbackedges : (AltPath.finite T).directionEdges .backward =
      R.path.edgeSet := by
    ext e
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    constructor
    · rintro ⟨l, hl, hldir, hel⟩
      change l ∈ T.links at hl
      rw [hlinks] at hl
      rcases hl with hl | hl
      · have hlF : l = F := by simpa using hl
        subst l
        simp [hFdir] at hldir
      · have hlR : l = R := by simpa using hl
        subst l
        exact hel
    · intro he
      exact ⟨R, by
        change R ∈ T.links
        rw [hlinks]
        simp, hRdir, he⟩
  have hIntervals : ∀ p ∈ Y,
      IsEdgeInterval ((AltPath.finite T).directionEdges .backward ∩
        p.edgeSet) p := by
    intro p hpY
    rw [hbackedges]
    exact fragment_inter_isEdgeInterval hY R.path hRY p hpY
  refine ⟨T, isBracketSafe_of_intervals hZ hZfin hAlt hIntervals, ?_, ?_, ?_, ?_⟩
  · simp [T, T₀]
  · simp [T, T₀]
  · simp [T, T₀]
  · simp [T, T₀]

/-! ## Preservation under one forward/backward construction step -/

/-- Appending a forward `Z`-fragment and then a backward `Y`-fragment
preserves bracket alternation, provided every new forward contact with `Y`
is covered either by an old backward link or by the new backward link. -/
theorem isBracketAlternating_snoc_forward_backward
    {Z Y : Set Γ.DPath} (T : FiniteTrace Γ.graph)
    (F R : Link Γ.graph)
    (hTFjoin : T.terminal = F.entry)
    (hTFalt : T.lastLink.direction ≠ F.direction)
    (hTFcompat : T.SnocCompatible F)
    (hFRjoin : (T.snoc F hTFjoin hTFalt hTFcompat).terminal = R.entry)
    (hFRalt : (T.snoc F hTFjoin hTFalt hTFcompat).lastLink.direction ≠
      R.direction)
    (hFRcompat : (T.snoc F hTFjoin hTFalt hTFcompat).SnocCompatible R)
    (hT : IsBracketSafe Z Y (.finite T))
    (hFdir : F.direction = .forward)
    (hRdir : R.direction = .backward)
    (hFZ : IsFragmentOf F.path Z)
    (hRY : IsFragmentOf R.path Y)
    (hFoff : Disjoint F.path.edgeSet (familyEdges Y))
    (hcontacts : F.path.support ∩ Γ.vertexSet Y ⊆
      (AltPath.finite T).directionVertices .backward ∪ R.path.support) :
    IsBracketAlternating Z Y
      (.finite ((T.snoc F hTFjoin hTFalt hTFcompat).snoc R
        hFRjoin hFRalt hFRcompat)) := by
  let TF := T.snoc F hTFjoin hTFalt hTFcompat
  let TFR := TF.snoc R hFRjoin hFRalt hFRcompat
  have hlinksTF : TF.links = T.links ∪ {F} := by
    simpa [TF] using FiniteTrace.links_snoc T F hTFjoin hTFalt hTFcompat
  have hlinksTFR : TFR.links = TF.links ∪ {R} := by
    simpa [TFR] using FiniteTrace.links_snoc TF R hFRjoin hFRalt hFRcompat
  have hfirstTF : TF.firstLink = T.firstLink := by
    simpa [TF] using FiniteTrace.firstLink_snoc T F hTFjoin hTFalt hTFcompat
  have hfirstTFR : TFR.firstLink = TF.firstLink := by
    simpa [TFR] using FiniteTrace.firstLink_snoc TF R hFRjoin hFRalt hFRcompat
  have hlastTFR : TFR.lastLink = R := by
    simpa [TFR] using FiniteTrace.lastLink_snoc TF R hFRjoin hFRalt hFRcompat
  rcases hT.isBracketAlternating with ⟨hAlt, hforwardZ⟩
  rcases hAlt with ⟨hYWarp, hbackY, hfirstOutside, hlastOutside⟩
  change IsBracketAlternating Z Y (.finite TFR)
  refine ⟨⟨hYWarp, ?_, ?_, ?_⟩, ?_⟩
  · intro l hl hldir
    change l ∈ TFR.links at hl
    rw [hlinksTFR, hlinksTF] at hl
    rcases hl with (hlT | hlF) | hlR
    · exact hbackY l hlT hldir
    · have hlF' : l = F := by simpa using hlF
      subst l
      rw [hFdir] at hldir
      cases hldir
    · have hlR' : l = R := by simpa using hlR
      subst l
      exact hRY
  · intro hdir
    apply hfirstOutside
    change some TFR.firstLink.direction = some .forward at hdir
    change some T.firstLink.direction = some .forward
    simpa [hfirstTFR, hfirstTF] using hdir
  · intro t ht hdir
    change some TFR.lastLink.direction = some .forward at hdir
    rw [hlastTFR, hRdir] at hdir
    simp at hdir
  · intro l hl hldir
    change l ∈ TFR.links at hl
    rw [hlinksTFR, hlinksTF] at hl
    rcases hl with (hlT | hlF) | hlR
    · exact hforwardZ l hlT hldir
    · have hlF' : l = F := by simpa using hlF
      subst l
      exact hFZ
    · have hlR' : l = R := by simpa using hlR
      subst l
      rw [hRdir] at hldir
      cases hldir

/-- The complete two-link stage-extension rule.  The source assertions
provide the collision and interval hypotheses; all alternating and safety
bookkeeping is discharged here. -/
theorem isBracketSafe_snoc_forward_backward
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z)
    (hZfin : Γ.HasFiniteCharacter Z)
    (T : FiniteTrace Γ.graph) (F R : Link Γ.graph)
    (hTFjoin : T.terminal = F.entry)
    (hTFalt : T.lastLink.direction ≠ F.direction)
    (hTFcompat : T.SnocCompatible F)
    (hFRjoin : (T.snoc F hTFjoin hTFalt hTFcompat).terminal = R.entry)
    (hFRalt : (T.snoc F hTFjoin hTFalt hTFcompat).lastLink.direction ≠
      R.direction)
    (hFRcompat : (T.snoc F hTFjoin hTFalt hTFcompat).SnocCompatible R)
    (hT : IsBracketSafe Z Y (.finite T))
    (hFdir : F.direction = .forward)
    (hRdir : R.direction = .backward)
    (hFZ : IsFragmentOf F.path Z)
    (hRY : IsFragmentOf R.path Y)
    (hFoff : Disjoint F.path.edgeSet (familyEdges Y))
    (hcontacts : F.path.support ∩ Γ.vertexSet Y ⊆
      (AltPath.finite T).directionVertices .backward ∪ R.path.support)
    (hIntervals : ∀ p ∈ Y,
      IsEdgeInterval
        ((AltPath.finite ((T.snoc F hTFjoin hTFalt hTFcompat).snoc R
          hFRjoin hFRalt hFRcompat)).directionEdges .backward ∩
            p.edgeSet) p) :
    IsBracketSafe Z Y
      (.finite ((T.snoc F hTFjoin hTFalt hTFcompat).snoc R
        hFRjoin hFRalt hFRcompat)) := by
  apply isBracketSafe_of_intervals hZ hZfin
  · exact isBracketAlternating_snoc_forward_backward T F R
      hTFjoin hTFalt hTFcompat hFRjoin hFRalt hFRcompat hT
      hFdir hRdir hFZ hRY hFoff hcontacts
  · exact hIntervals

/-! ## Passing coherent finite construction data to the infinite limit -/

/-- Global link invariants are enough to turn the ω-sequence produced by
the maximal recursion into the safe infinite alternative.  Keeping this
lemma independent of the particular successor rule makes the final limit
step purely structural: the five source assertions are used only to build
`f` and discharge the hypotheses below. -/
theorem contactMarkedSafeAlternatingDichotomy_of_infiniteLinks
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) {u : V}
    (f : ℕ → Link Γ.graph)
    (hjoins : ∀ n, (f n).exit = (f (n + 1)).entry)
    (halts : ∀ n, (f n).direction ≠ (f (n + 1)).direction)
    (hcompat : ∀ i j, i < j →
      CompatibleInOrder (j = i + 1) (f i) (f j))
    (hinitial : (f 0).entry = u)
    (hback : ∀ n, (f n).direction = .backward →
      IsFragmentOf (f n).path Y)
    (hforwardOff : ∀ n, (f n).direction = .forward →
      Disjoint (f n).path.edgeSet (familyEdges Y))
    (hcontacts :
      (⋃ n, ⋃ (_ : (f n).direction = .forward), (f n).path.support) ∩
          Γ.vertexSet Y ⊆
        ⋃ n, ⋃ (_ : (f n).direction = .backward), (f n).path.support)
    (hfirst : (f 0).direction = .forward)
    (hforwardZ : ∀ n, (f n).direction = .forward →
      IsFragmentOf (f n).path Z)
    (hIntervals : ∀ p ∈ Y,
      IsEdgeInterval
        ((⋃ n, ⋃ (_ : (f n).direction = .backward),
          (f n).path.edgeSet) ∩ p.edgeSet) p) :
    ContactMarkedSafeAlternatingDichotomy Z Y u := by
  let T : InfiniteTrace Γ.graph :=
    InfiniteTrace.ofLinks f hjoins halts hcompat
  let Q : AltPath Γ.graph := .infinite T
  have hlinks : Q.links = Set.range f := by
    rfl
  have hvertices :
      Q.directionVertices .forward =
        ⋃ n, ⋃ (_ : (f n).direction = .forward), (f n).path.support := by
    ext x
    simp only [AltPath.directionVertices, hlinks, Set.mem_iUnion,
      Set.mem_range]
    constructor
    · rintro ⟨l, ⟨n, rfl⟩, hdir, hx⟩
      exact ⟨n, hdir, hx⟩
    · rintro ⟨n, hdir, hx⟩
      exact ⟨f n, ⟨n, rfl⟩, hdir, hx⟩
  have hverticesBack :
      Q.directionVertices .backward =
        ⋃ n, ⋃ (_ : (f n).direction = .backward), (f n).path.support := by
    ext x
    simp only [AltPath.directionVertices, hlinks, Set.mem_iUnion,
      Set.mem_range]
    constructor
    · rintro ⟨l, ⟨n, rfl⟩, hdir, hx⟩
      exact ⟨n, hdir, hx⟩
    · rintro ⟨n, hdir, hx⟩
      exact ⟨f n, ⟨n, rfl⟩, hdir, hx⟩
  have hEdgesBack : Q.directionEdges .backward =
      ⋃ n, ⋃ (_ : (f n).direction = .backward), (f n).path.edgeSet := by
    ext e
    simp only [AltPath.directionEdges, hlinks, Set.mem_iUnion,
      Set.mem_range]
    constructor
    · rintro ⟨l, ⟨n, rfl⟩, hdir, he⟩
      exact ⟨n, hdir, he⟩
    · rintro ⟨n, hdir, he⟩
      exact ⟨f n, ⟨n, rfl⟩, hdir, he⟩
  have hAlt : IsBracketAlternating Z Y Q := by
    refine ⟨⟨hY, ?_, ?_, ?_⟩, ?_⟩
    · intro l hl hdir
      rw [hlinks] at hl
      rcases hl with ⟨n, rfl⟩
      exact hback n hdir
    · intro _
      have huY : (f 0).entry ∉ Γ.vertexSet Y := by
        intro hu
        have huF : (f 0).entry ∈ Q.directionVertices .forward := by
          rw [hvertices]
          exact Set.mem_iUnion_of_mem 0
            (Set.mem_iUnion_of_mem hfirst (f 0).entry_mem_support)
        have huB := hcontacts ⟨by simpa [hvertices] using huF, hu⟩
        rcases Set.mem_iUnion.1 huB with ⟨m, huB⟩
        rcases Set.mem_iUnion.1 huB with ⟨hldir, hul⟩
        have hc := hcompat 0 m
        rcases Nat.eq_zero_or_pos m with rfl | hn
        · simp [hfirst] at hldir
        · have hc' := hc hn
          simp only [hfirst, hldir, CompatibleInOrder] at hc'
          by_cases hadj : m = 1
          · have hi : (f 0).entry ∈
                (f 0).path.support ∩ (f m).path.support :=
              ⟨(f 0).entry_mem_support, hul⟩
            rw [hc'.1 (by omega)] at hi
            exact (f 0).entry_ne_exit (by simpa using hi)
          · exact Set.disjoint_left.1 (hc'.2 (by omega))
              (f 0).entry_mem_support hul
      change (f 0).entry ∉ Γ.vertexSet Y
      exact huY
    · intro t ht
      simp [Q, AltPath.terminal?] at ht
    · intro l hl hdir
      rw [hlinks] at hl
      rcases hl with ⟨n, rfl⟩
      exact hforwardZ n hdir
  left
  refine ⟨Q, isBracketSafe_of_intervals hZ hZfin hAlt ?_, ?_, ?_⟩
  · intro p hp
    rw [hEdgesBack]
    exact hIntervals p hp
  · change (f 0).entry = u
    exact hinitial
  · simp [Q, AltPath.IsInfinite]

theorem safeAlternatingDichotomy_of_infiniteLinks
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) {u : V}
    (f : ℕ → Link Γ.graph)
    (hjoins : ∀ n, (f n).exit = (f (n + 1)).entry)
    (halts : ∀ n, (f n).direction ≠ (f (n + 1)).direction)
    (hcompat : ∀ i j, i < j →
      CompatibleInOrder (j = i + 1) (f i) (f j))
    (hinitial : (f 0).entry = u)
    (hback : ∀ n, (f n).direction = .backward →
      IsFragmentOf (f n).path Y)
    (hforwardOff : ∀ n, (f n).direction = .forward →
      Disjoint (f n).path.edgeSet (familyEdges Y))
    (hcontacts :
      (⋃ n, ⋃ (_ : (f n).direction = .forward), (f n).path.support) ∩
          Γ.vertexSet Y ⊆
        ⋃ n, ⋃ (_ : (f n).direction = .backward), (f n).path.support)
    (hfirst : (f 0).direction = .forward)
    (hforwardZ : ∀ n, (f n).direction = .forward →
      IsFragmentOf (f n).path Z)
    (hIntervals : ∀ p ∈ Y,
      IsEdgeInterval ((⋃ n, ⋃ (_ : (f n).direction = .backward),
        (f n).path.edgeSet) ∩ p.edgeSet) p) :
    SafeAlternatingDichotomy Z Y u :=
  (contactMarkedSafeAlternatingDichotomy_of_infiniteLinks hZ hY hZfin f
    hjoins halts hcompat hinitial hback hforwardOff hcontacts hfirst hforwardZ
    hIntervals).toSafeAlternatingDichotomy

/-- A finite safe path with the symmetric vertex-contact invariant supplies
the literal reducing path in alternative (2) simply by reversal. -/
theorem safeAlternatingDichotomy_of_finite_symmetric
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z)
    {u v : V} (T : FiniteTrace Γ.graph)
    (hv : v ∈ Γ.terminalFrontier Z \ Γ.vertexSet Y)
    (hT : IsBracketSafe Z Y (.finite T))
    (hinit : T.initial = u) (hterminal : T.terminal = v)
    (hcover : (AltPath.finite T).directionVertices .backward ∩
        Γ.vertexSet Z ⊆
      (AltPath.finite T).directionVertices .forward) :
    SafeAlternatingDichotomy Z Y u := by
  right
  refine ⟨v, hv, .finite T, hT, hinit, ?_, .finite T.reverse, ?_, ?_, ?_⟩
  · simpa using congrArg some hterminal
  · exact IsBracketAlternating.reverse_finite hZ hT.2 hcover
  · simpa using hterminal
  · simpa using congrArg some hinit

theorem isBracketSafe_single_forward
    {Z Y : Set Γ.DPath} (hY : Γ.IsWarp Y)
    (q : FinitePath Γ.graph) (hqZ : (Sum.inl q : Γ.DPath) ∈ Z)
    (hneq : q.start ≠ q.finish)
    (hdisj : Disjoint q.support (Γ.vertexSet Y)) :
    IsBracketSafe Z Y
      (AltPath.single ⟨q, .forward, hneq⟩) := by
  let l : Link Γ.graph := ⟨q, .forward, hneq⟩
  have hedge : Disjoint q.edgeSet (familyEdges Y) :=
    finitePath_edgeSet_disjoint_familyEdges_of_support_disjoint q hdisj
  have hstart : q.start ∉ Γ.vertexSet Y :=
    fun h ↦ Set.disjoint_left.1 hdisj q.start_mem_support h
  have hfinish : q.finish ∉ Γ.vertexSet Y :=
    finitePath_finish_not_mem_vertexSet_of_support_disjoint q hdisj
  have halt : IsAlternating Y (AltPath.single l) := by
    refine ⟨hY, ?_, ?_, ?_⟩
    · intro k hk hback
      have hk' : k = l := by simpa [l] using hk
      subst k
      simp [l] at hback
    · simpa [l, Link.entry] using hstart
    · intro t ht _
      have ht' : q.finish = t := by simpa [l, Link.exit] using ht
      exact ht' ▸ hfinish
  have hsafe : IsSafe Y (AltPath.single l) := by
    refine ⟨halt, ?_, ?_, ?_⟩
    · intro p hpY
      left
      apply Set.eq_empty_iff_forall_notMem.2
      intro e he
      simp [AltPath.directionEdges, l] at he
    · apply FinitePath.not_containsDirectedRay_of_subset q
      intro e he
      simpa [l] using he.1
    · apply FinitePath.not_containsDirectedCycle_of_subset q
      intro e he
      simpa [l] using he.1
  refine ⟨hsafe, halt, ?_⟩
  intro k hk hforward
  have hk' : k = l := by simpa [l] using hk
  subst k
  exact ⟨Sum.inl q, hqZ, q.isSubpathOf_self⟩

theorem isBracketAlternating_single_backward
    {U Z : Set Γ.DPath} (hZ : Γ.IsWarp Z)
    (q : FinitePath Γ.graph) (hqZ : (Sum.inl q : Γ.DPath) ∈ Z)
    (hneq : q.start ≠ q.finish) :
    IsBracketAlternating U Z
      (AltPath.single ⟨q, .backward, hneq⟩) := by
  let l : Link Γ.graph := ⟨q, .backward, hneq⟩
  refine ⟨⟨hZ, ?_, ?_, ?_⟩, ?_⟩
  · intro k hk hback
    have hk' : k = l := by simpa [l] using hk
    subst k
    exact ⟨Sum.inl q, hqZ, q.isSubpathOf_self⟩
  · simp
  · intro t ht hlast
    simp at hlast
  · intro k hk hforward
    have hk' : k = l := by simpa [l] using hk
    subst k
    simp [l] at hforward

theorem isBracketSwitchingAlternating_single_backward
    {U Z : Set Γ.DPath} (hZ : Γ.IsWarp Z)
    (q : FinitePath Γ.graph) (hqZ : (Sum.inl q : Γ.DPath) ∈ Z)
    (hneq : q.start ≠ q.finish) :
    IsBracketSwitchingAlternating U Z
      (AltPath.single ⟨q, .backward, hneq⟩) := by
  refine ⟨isBracketAlternating_single_backward hZ q hqZ hneq, ?_, ?_⟩
  · simp [ForwardLinksOff, AltPath.directionEdges]
  · simp [ForwardVertexContactsCovered, AltPath.directionVertices]

theorem safeAlternatingDichotomy_of_disjoint_path
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (q : FinitePath Γ.graph) (hqZ : (Sum.inl q : Γ.DPath) ∈ Z)
    {u : V} (hstart : q.start = u)
    (hdisj : Disjoint q.support (Γ.vertexSet Y)) :
    SafeAlternatingDichotomy Z Y u := by
  by_cases htriv : q.start = q.finish
  · apply safeAlternatingDichotomy_of_mem_terminalFrontier hZ hY
    · exact ⟨Sum.inl q, hqZ, by simpa [hstart] using congrArg some htriv.symm⟩
    · exact hstart ▸ fun h ↦ Set.disjoint_left.1 hdisj q.start_mem_support h
  · right
    let F : Link Γ.graph := ⟨q, .forward, htriv⟩
    let R : Link Γ.graph := ⟨q, .backward, htriv⟩
    refine ⟨q.finish, ⟨⟨Sum.inl q, hqZ, rfl⟩,
      finitePath_finish_not_mem_vertexSet_of_support_disjoint q hdisj⟩,
      AltPath.single F, ?_, ?_, rfl, AltPath.single R, ?_, ?_, ?_⟩
    · simpa [F] using isBracketSafe_single_forward hY q hqZ htriv hdisj
    · simpa [F, hstart]
    · simpa [R] using
        (isBracketAlternating_single_backward (U := Y) hZ q hqZ htriv)
    · simp [R, Link.entry]
    · simp [R, Link.exit, hstart]

theorem contactMarkedSafeAlternatingDichotomy_of_disjoint_path
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (q : FinitePath Γ.graph) (hqZ : (Sum.inl q : Γ.DPath) ∈ Z)
    {u : V} (hstart : q.start = u)
    (hdisj : Disjoint q.support (Γ.vertexSet Y)) :
    ContactMarkedSafeAlternatingDichotomy Z Y u := by
  by_cases htriv : q.start = q.finish
  · apply contactMarkedSafeAlternatingDichotomy_of_mem_terminalFrontier hZ hY
    · exact ⟨Sum.inl q, hqZ, by simpa [hstart] using congrArg some htriv.symm⟩
    · exact hstart ▸ fun h ↦ Set.disjoint_left.1 hdisj q.start_mem_support h
  · right
    let F : Link Γ.graph := ⟨q, .forward, htriv⟩
    let R : Link Γ.graph := ⟨q, .backward, htriv⟩
    refine ⟨q.finish, ⟨⟨Sum.inl q, hqZ, rfl⟩,
      finitePath_finish_not_mem_vertexSet_of_support_disjoint q hdisj⟩,
      AltPath.single F, ?_, ?_, rfl, AltPath.single R, ?_, ?_, ?_⟩
    · simpa [F] using isBracketSafe_single_forward hY q hqZ htriv hdisj
    · simpa [F, hstart]
    · simpa [R] using
        (isBracketSwitchingAlternating_single_backward (U := Y) hZ q hqZ htriv)
    · simp [R, Link.entry]
    · simp [R, Link.exit, hstart]

/-- Finite character turns a covered initial vertex into a concrete finite
reference path starting there. -/
theorem exists_finitePath_start_of_mem_initialSet
    {W : Set Γ.DPath} (hfin : Γ.HasFiniteCharacter W)
    {u : V} (hu : u ∈ Γ.initialSet W) :
    ∃ q : FinitePath Γ.graph, (Sum.inl q : Γ.DPath) ∈ W ∧ q.start = u := by
  rcases hu with ⟨p, hpW, hpinit⟩
  rcases hfin hpW with ⟨q, rfl⟩
  exact ⟨q, hpW, hpinit⟩

/-- The first, terminal branch of the maximal construction: if the reference
path from the uncovered source avoids `Y`, it itself supplies both directions
of alternative (2). -/
theorem safeAlternatingDichotomy_of_initial_path_disjoint
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) {u : V}
    (hu : u ∈ Γ.initialSet Z)
    (havoid : ∀ q : FinitePath Γ.graph,
      (Sum.inl q : Γ.DPath) ∈ Z → q.start = u →
        Disjoint q.support (Γ.vertexSet Y)) :
    SafeAlternatingDichotomy Z Y u := by
  obtain ⟨q, hqZ, hqu⟩ := exists_finitePath_start_of_mem_initialSet hZfin hu
  exact safeAlternatingDichotomy_of_disjoint_path hZ hY q hqZ hqu
    (havoid q hqZ hqu)

theorem contactMarkedSafeAlternatingDichotomy_of_initial_path_disjoint
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z) {u : V}
    (hu : u ∈ Γ.initialSet Z)
    (havoid : ∀ q : FinitePath Γ.graph,
      (Sum.inl q : Γ.DPath) ∈ Z → q.start = u →
        Disjoint q.support (Γ.vertexSet Y)) :
    ContactMarkedSafeAlternatingDichotomy Z Y u := by
  obtain ⟨q, hqZ, hqu⟩ := exists_finitePath_start_of_mem_initialSet hZfin hu
  exact contactMarkedSafeAlternatingDichotomy_of_disjoint_path hZ hY q hqZ hqu
    (havoid q hqZ hqu)

/-! ## Contact facts used by Assertions 4.15--4.19 -/

/-- A path of `Y` cannot begin where it first (or later) meets the `Z`-path
whose initial vertex is uncovered by `Y`.  This is the short uniqueness
argument used immediately before Assertion 4.15. -/
theorem contact_ne_initial_of_initial_uncovered
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z)
    (hinit : Γ.initialSet Y ⊆ Γ.initialSet Z)
    {q : FinitePath Γ.graph} (hqZ : (Sum.inl q : Γ.DPath) ∈ Z)
    {u w : V} (hqu : q.start = u) (huY : u ∉ Γ.vertexSet Y)
    {p : Γ.DPath} (hpY : p ∈ Y) (hwp : w ∈ p.support)
    (hwq : w ∈ q.support) : w ≠ p.initial := by
  intro hwi
  have hpinit : p.initial ∈ Γ.initialSet Y := ⟨p, hpY, rfl⟩
  rcases hinit hpinit with ⟨z, hzZ, hzinit⟩
  have hwz : w ∈ z.support := by
    rw [hwi]
    rw [← hzinit]
    exact z.initial_mem_support
  have hzq : z = (Sum.inl q : Γ.DPath) :=
    DWeb.IsWarp.eq_of_mem_support hZ hzZ hqZ hwz hwq
  have hwu : w = u := by
    calc
      w = p.initial := hwi
      _ = z.initial := hzinit.symm
      _ = q.start := congrArg Path.initial hzq
      _ = u := hqu
  apply huY
  exact ⟨p, hpY, hwu ▸ hwp⟩

/-- The initial endpoint of an edge of a finite walk occurs before the
walk's final vertex. -/
theorem Walk.edge_fst_mem_support_dropLast {D : Digraph V} {a b x y : V}
    (p : Walk D a b) (he : (x, y) ∈ p.edgeSet) :
    x ∈ p.support.dropLast := by
  induction p with
  | nil => simp at he
  | @cons a z b h p ih =>
      simp only [Walk.edgeSet_cons, Set.mem_union, Set.mem_singleton_iff] at he
      rw [Walk.support_cons, List.dropLast_cons_of_ne_nil p.support_ne_nil]
      rcases he with he | he
      · have hxa : x = a := congrArg Prod.fst he
        exact hxa ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih he)

/-- The first `Y`-contact on the `Z`-path from an uncovered initial vertex
is a nontrivial forward link.  Its only vertex on `Y` is its exit, and none
of its edges is a `Y`-edge.  This is the concrete first-link payload used in
Assertion 4.15. -/
theorem exists_initialForwardLink_to_firstContact
    {Z Y : Set Γ.DPath} (q : FinitePath Γ.graph)
    (hqZ : (Sum.inl q : Γ.DPath) ∈ Z) {u : V}
    (hqu : q.start = u) (huY : u ∉ Γ.vertexSet Y)
    (hmeet : q.walk.Meets (Γ.vertexSet Y)) :
    ∃ F : Link Γ.graph,
      F.direction = .forward ∧ F.entry = u ∧
      F.exit ∈ Γ.vertexSet Y ∧ IsFragmentOf F.path Z ∧
      Disjoint F.path.edgeSet (familyEdges Y) ∧
      F.path.support ∩ Γ.vertexSet Y = {F.exit} := by
  let r := q.firstHit (Γ.vertexSet Y) hmeet
  have hrstart : r.start = u := by
    change q.start = u
    exact hqu
  have hrfinish : r.finish ∈ Γ.vertexSet Y :=
    q.firstHit_finish_mem (Γ.vertexSet Y) hmeet
  have hrne : r.start ≠ r.finish := by
    intro h
    apply huY
    rw [← hrstart, h]
    exact hrfinish
  let F : Link Γ.graph := ⟨r, .forward, hrne⟩
  refine ⟨F, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [F, Link.entry] using hrstart
  · simpa [F, Link.exit] using hrfinish
  · exact ⟨Sum.inl q, hqZ, q.firstHit_isSubpathOf (Γ.vertexSet Y) hmeet⟩
  · rw [Set.disjoint_left]
    intro e her heYedge
    have hbefore : e.1 ∈ r.walk.support.dropLast :=
      Walk.edge_fst_mem_support_dropLast r.walk her
    have hnotY : e.1 ∉ Γ.vertexSet Y :=
      q.firstHit_no_mem_before (Γ.vertexSet Y) hmeet hbefore
    apply hnotY
    simp only [familyEdges, Set.mem_iUnion] at heYedge
    rcases heYedge with ⟨p, hpY, hep⟩
    exact ⟨p, hpY, (p.edgeSet_subset_support_prod hep).1⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxr, hxY⟩
      have hxf : x = r.finish := by
        by_contra hne
        have hlast : r.walk.support.getLast r.walk.support_ne_nil = r.finish :=
          r.walk.getLast_support
        have hxlast : x ≠ r.walk.support.getLast r.walk.support_ne_nil := by
          simpa only [hlast] using hne
        exact q.firstHit_no_mem_before (Γ.vertexSet Y) hmeet
          (List.mem_dropLast_of_mem_of_ne_getLast hxr hxlast) hxY
      simpa [F, Link.exit] using hxf
    · intro x hx
      have hxF : x = r.finish := by simpa [F, Link.exit] using hx
      subst x
      exact ⟨r.finish_mem_support, hrfinish⟩

end Alternating
end Erdos599
