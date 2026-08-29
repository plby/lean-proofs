/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingTraceOps

/-!
# Logical closure lemmas for Assertions 4.15--4.19

The proof of Aharoni--Berger Lemma 4.13 repeatedly extends a reverse
`[Y,Z]`-alternating trace.  The graph-theoretic part of each assertion is the
construction (and, when necessary, collision trimming) of that extension.
This file separates that construction from the common logical argument:
reverse reachability is closed under every extension which preserves the
initial vertex and bracket alternation.

The final section records the elementary linear-order fact on a finite path
used in Assertion 4.19.  It avoids imposing a decidable equality on the
vertex type.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

/-- The safely reachable terminal set, factored out here so the source
assertions can be checked independently of the eventual maximal-recursion
module. -/
def SourceSafelyReachable (Z Y : Set Γ.DPath) (u : V) : Set V :=
  {v | v ∈ Γ.terminalFrontier Z \ Γ.vertexSet Y ∧
    ∃ Q : AltPath Γ.graph,
      IsBracketSafe Z Y Q ∧ Q.initial = u ∧ Q.terminal? = some v}

/-- The reverse-reachable set `C` of the source proof. -/
def SourceReverseReachable (Z Y : Set Γ.DPath) (u : V) : Set V :=
  {x | ∃ v ∈ SourceSafelyReachable Z Y u,
    ∃ T : AltPath Γ.graph,
      IsBracketAlternating Y Z T ∧ T.initial = v ∧ T.terminal? = some x}

/-- A collision-resolved continuation of every finite-or-trivial reverse
trace from `x` to `y`.  This is the precise local certificate constructed in
Assertions 4.15, 4.17, and 4.18 after merging or trimming the final link.
The initial vertex is universally quantified because it is the uncovered
terminal in `SafelyReachable`. -/
def ReverseTraceExtension (Y Z : Set Γ.DPath) (x y : V) : Prop :=
  ∀ (a : V) (T : AltPath Γ.graph),
    IsBracketAlternating Y Z T →
    T.initial = a → T.terminal? = some x →
      ∃ T' : AltPath Γ.graph,
        IsBracketAlternating Y Z T' ∧
          T'.initial = a ∧ T'.terminal? = some y

namespace ReverseTraceExtension

theorem refl (Y Z : Set Γ.DPath) (x : V) :
    ReverseTraceExtension Y Z x x := by
  intro a T hT hinit hterm
  exact ⟨T, hT, hinit, hterm⟩

theorem trans {Y Z : Set Γ.DPath} {x y z : V}
    (hxy : ReverseTraceExtension Y Z x y)
    (hyz : ReverseTraceExtension Y Z y z) :
    ReverseTraceExtension Y Z x z := by
  intro a T hT hinit hterm
  rcases hxy a T hT hinit hterm with ⟨T', hT', hinit', hterm'⟩
  exact hyz a T' hT' hinit' hterm'

end ReverseTraceExtension

/-! ## Collision-compatible continuation constructors -/

/-- Appending one backward reference fragment preserves literal bracket
alternation.  This is the separate-link case in the source proof (the case
where the old final link is forward).  All collision work is concentrated in
`hcompat`; no vertex-contact normalization is assumed. -/
theorem IsBracketAlternating.snoc_backward
    {U Y : Set Γ.DPath} (T : FiniteTrace Γ.graph) (R : Link Γ.graph)
    (hjoin : T.terminal = R.entry)
    (halt : T.lastLink.direction ≠ R.direction)
    (hcompat : T.SnocCompatible R)
    (hT : IsBracketAlternating U Y (.finite T))
    (hRdir : R.direction = .backward)
    (hRY : IsFragmentOf R.path Y) :
    IsBracketAlternating U Y (.finite (T.snoc R hjoin halt hcompat)) := by
  let TR := T.snoc R hjoin halt hcompat
  have hlinks : TR.links = T.links ∪ {R} := by
    simpa [TR] using FiniteTrace.links_snoc T R hjoin halt hcompat
  have hfirst : TR.firstLink = T.firstLink := by
    simpa [TR] using FiniteTrace.firstLink_snoc T R hjoin halt hcompat
  have hlast : TR.lastLink = R := by
    simpa [TR] using FiniteTrace.lastLink_snoc T R hjoin halt hcompat
  rcases hT with ⟨hAlt, hforwardU⟩
  rcases hAlt with ⟨hYWarp, hbackY, hinitial, hterminal⟩
  refine ⟨⟨hYWarp, ?_, ?_, ?_⟩, ?_⟩
  · intro l hl hldir
    change l ∈ TR.links at hl
    rw [hlinks] at hl
    rcases hl with hlT | hlR
    · exact hbackY l hlT hldir
    · have hl : l = R := by simpa using hlR
      subst l
      exact hRY
  · intro hdir
    apply hinitial
    change some TR.firstLink.direction = some .forward at hdir
    change some T.firstLink.direction = some .forward
    simpa [hfirst] using hdir
  · intro t ht hdir
    change some TR.lastLink.direction = some .forward at hdir
    rw [hlast, hRdir] at hdir
    simp at hdir
  · intro l hl hldir
    change l ∈ TR.links at hl
    rw [hlinks] at hl
    rcases hl with hlT | hlR
    · exact hforwardU l hlT hldir
    · have hl : l = R := by simpa using hlR
      subst l
      rw [hRdir] at hldir
      cases hldir

/-- Package the preceding preservation theorem with its endpoint equations.
This is the witness actually consumed by `ReverseTraceExtension`. -/
theorem exists_bracketContinuation_snoc_backward
    {U Y : Set Γ.DPath} (T : FiniteTrace Γ.graph) (R : Link Γ.graph)
    (hjoin : T.terminal = R.entry)
    (halt : T.lastLink.direction ≠ R.direction)
    (hcompat : T.SnocCompatible R)
    (hT : IsBracketAlternating U Y (.finite T))
    (hRdir : R.direction = .backward)
    (hRY : IsFragmentOf R.path Y) :
    ∃ T' : AltPath Γ.graph,
      IsBracketAlternating U Y T' ∧
        T'.initial = T.initial ∧ T'.terminal? = some R.exit := by
  let TR := T.snoc R hjoin halt hcompat
  refine ⟨.finite TR, hT.snoc_backward T R hjoin halt hcompat hRdir hRY,
    ?_, ?_⟩
  · change TR.initial = T.initial
    simpa [TR] using FiniteTrace.initial_snoc T R hjoin halt hcompat
  · change some TR.terminal = some R.exit
    congr 1
    simpa [TR] using FiniteTrace.terminal_snoc T R hjoin halt hcompat

/-- Reverse reachability is closed under a collision-resolved reverse-trace
extension.  This is the common inference in Assertions 4.15, 4.17, and
4.18. -/
theorem SourceReverseReachable.closed_under_extension
    {Z Y : Set Γ.DPath} {u x y : V}
    (hxy : ReverseTraceExtension Y Z x y)
    (hx : x ∈ SourceReverseReachable Z Y u) :
    y ∈ SourceReverseReachable Z Y u := by
  rcases hx with ⟨v, hv, T, hT, hinit, hterm⟩
  rcases hxy v T hT hinit hterm with ⟨T', hT', hinit', hterm'⟩
  exact ⟨v, hv, T', hT', hinit', hterm'⟩

/-- Contrapositive form used verbatim in the source assertions: if `y` is
outside `C`, then every point from which reverse traces can be continued to
`y` is outside `C` as well. -/
theorem not_mem_reverseReachable_of_extension
    {Z Y : Set Γ.DPath} {u x y : V}
    (hy : y ∉ SourceReverseReachable Z Y u)
    (hxy : ReverseTraceExtension Y Z x y) :
    x ∉ SourceReverseReachable Z Y u := by
  intro hx
  exact hy (SourceReverseReachable.closed_under_extension hxy hx)

/-- Assertion 4.15 after its two collision-resolved continuation
certificates have been constructed. -/
theorem assertion415_outside
    {Z Y : Set Γ.DPath} {u w y : V}
    (hu : u ∉ SourceReverseReachable Z Y u)
    (hwu : ReverseTraceExtension Y Z w u)
    (hyu : ReverseTraceExtension Y Z y u) :
    w ∉ SourceReverseReachable Z Y u ∧
      y ∉ SourceReverseReachable Z Y u := by
  exact ⟨not_mem_reverseReachable_of_extension hu hwu,
    not_mem_reverseReachable_of_extension hu hyu⟩

/-- Assertion 4.17, with the collision-trimmed continuation along the new
`Z`-fragment made explicit. -/
theorem assertion417_firstContact_outside
    {Z Y : Set Γ.DPath} {u ui w : V}
    (hui : ui ∉ SourceReverseReachable Z Y u)
    (hwui : ReverseTraceExtension Y Z w ui) :
    w ∉ SourceReverseReachable Z Y u :=
  not_mem_reverseReachable_of_extension hui hwui

/-- Assertion 4.18, with the continuation consisting of the predecessor
edge followed by the new reverse `Z`-fragment made explicit. -/
theorem assertion418_predecessor_outside
    {Z Y : Set Γ.DPath} {u ui y : V}
    (hui : ui ∉ SourceReverseReachable Z Y u)
    (hyui : ReverseTraceExtension Y Z y ui) :
    y ∉ SourceReverseReachable Z Y u :=
  not_mem_reverseReachable_of_extension hui hyui

/-- The finite alternative follows as soon as a safe outward trace and a
reverse trace have the required endpoints.  In Assertion 4.16 this is the
contradiction obtained when the remaining reference segment has no new
`Y`-contact. -/
theorem mem_reverseReachable_of_safe_outward_and_return
    {Z Y : Set Γ.DPath} {u v x : V}
    (hv : v ∈ Γ.terminalFrontier Z \ Γ.vertexSet Y)
    (Q : AltPath Γ.graph) (hQ : IsBracketSafe Z Y Q)
    (hQinit : Q.initial = u) (hQterm : Q.terminal? = some v)
    (T : AltPath Γ.graph) (hT : IsBracketAlternating Y Z T)
    (hTinit : T.initial = v) (hTterm : T.terminal? = some x) :
    x ∈ SourceReverseReachable Z Y u := by
  refine ⟨v, ?_, T, hT, hTinit, hTterm⟩
  exact ⟨hv, Q, hQ, hQinit, hQterm⟩

/-- Assertion 4.16 in its contradiction form.  The geometric branch of the
argument supplies `Q` by appending the unused `Z`-tail and supplies `T` by
reversing that tail. -/
theorem assertion416_contradiction
    {Z Y : Set Γ.DPath} {u ui v : V}
    (hui : ui ∉ SourceReverseReachable Z Y u)
    (hv : v ∈ Γ.terminalFrontier Z \ Γ.vertexSet Y)
    (Q : AltPath Γ.graph) (hQ : IsBracketSafe Z Y Q)
    (hQinit : Q.initial = u) (hQterm : Q.terminal? = some v)
    (T : AltPath Γ.graph) (hT : IsBracketAlternating Y Z T)
    (hTinit : T.initial = v) (hTterm : T.terminal? = some ui) :
    False := by
  exact hui (mem_reverseReachable_of_safe_outward_and_return hv Q hQ
    hQinit hQterm T hT hTinit hTterm)

end Alternating

namespace DirectedPath

open Set

universe u

variable {V : Type u} {D : Digraph V}

namespace FinitePath

/-- Two distinct vertices of a finite directed path occur in one of the two
strict orders.  The proof uses only list decomposition and path nodupness, so
no decidable equality on vertices is required. -/
theorem orderedOccurrence_or_reverse (p : FinitePath D) {x y : V}
    (hx : x ∈ p.support) (hy : y ∈ p.support) (hxy : x ≠ y) :
    Nonempty (OrderedOccurrence p x y) ∨
      Nonempty (OrderedOccurrence p y x) := by
  change x ∈ p.walk.support at hx
  change y ∈ p.walk.support at hy
  rcases List.mem_iff_append.mp hx with ⟨before, suffix, hsupp⟩
  have hy' : y ∈ before ∨ y = x ∨ y ∈ suffix := by
    rw [hsupp] at hy
    simpa only [List.mem_append, List.mem_cons] using hy
  rcases hy' with hybefore | hyx | hysuffix
  · rcases List.mem_iff_append.mp hybefore with ⟨pre, after, hbefore⟩
    right
    refine ⟨{
      before := pre
      middle := after
      after := suffix
      support_eq := ?_ }⟩
    rw [hsupp, hbefore]
  · exact (hxy hyx.symm).elim
  · left
    exact OrderedOccurrence.nonempty_of_mem_suffix before suffix hsupp hysuffix

/-- If the reverse order has been excluded by the backward-interior and
first-outside invariants, the new contact lies strictly after the old one.
This is the order-theoretic final step of Assertion 4.19. -/
theorem orderedOccurrence_of_not_reverse (p : FinitePath D) {old new : V}
    (hold : old ∈ p.support) (hnew : new ∈ p.support)
    (hne : old ≠ new)
    (hnotReverse : ¬ Nonempty (OrderedOccurrence p new old)) :
    Nonempty (OrderedOccurrence p old new) := by
  rcases p.orderedOccurrence_or_reverse hold hnew hne with h | h
  · exact h
  · exact (hnotReverse h).elim

/-- Non-strict form of the same linearity fact, convenient when selecting a
first contact from a suffix. -/
theorem atOrAfter_or_reverse (p : FinitePath D) {x y : V}
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    p.AtOrAfter x y ∨ p.AtOrAfter y x := by
  by_cases hxy : x = y
  · exact Or.inl (Or.inl hxy.symm)
  · rcases p.orderedOccurrence_or_reverse hx hy hxy with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

end FinitePath
end DirectedPath
end Erdos599
