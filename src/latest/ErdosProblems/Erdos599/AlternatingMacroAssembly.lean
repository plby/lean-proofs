/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RawAlternatingDichotomy
import ErdosProblems.Erdos599.AlternatingMacroSafety
import ErdosProblems.Erdos599.AlternatingDichotomy

/-!
# Assembling the macro orbit into the literal safe dichotomy

This file isolates the purely logical last step of the alternating-path
construction.  A finite macro route is compiled to an endpoint-exposed safe
finite trace whose first and last links point forwards.  An infinite macro
chain is compiled directly to a safe infinite trace.  The deterministic
macro-orbit theorem then gives exactly the two alternatives in
`SafeAlternatingDichotomy`.

The records below are deliberately phrased in the literal trace language.
They are the small interfaces which the finite and infinite edge-level
compilers have to implement; all orbit, endpoint, frontier, and reversal
bookkeeping is discharged here.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

/-- Indexed backward-run provenance is enough for the safeness assembly.
This is the form naturally emitted by a run compressor. -/
theorem IsBracketAlternating.isBracketSafe_of_indexedBackwardProvenance
    {Z Y : Set Γ.DPath} {Q : AltPath Γ.graph} {I : Type*}
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z)
    (hQ : IsBracketAlternating Z Y Q)
    (P : Q.IndexedBackwardProvenance Y I) :
    IsBracketSafe Z Y Q := by
  have houtside := hQ.outside_subset_familyEdges_literal
  refine ⟨⟨hQ.1, P.intervals hY, ?_, ?_⟩, hQ⟩
  · rintro ⟨R, hR⟩
    exact SwitchingCore.familyEdges_not_containsDirectedRay hZ hZfin
      ⟨R, hR.trans houtside⟩
  · rintro ⟨D, hD⟩
    exact SwitchingCore.familyEdges_not_containsDirectedCycle hZ hZfin
      ⟨D, hD.trans houtside⟩

namespace FiniteMacroRoute

/-- The exact edge-level output needed from a finite macro route.  Boundary
forwardness is what makes reversal a literal `[Y,Z]`-alternating trace. -/
structure Compilation {Z Y : Set Γ.DPath}
    (C : FiniteMacroRoute Γ Z Y) where
  trace : FiniteTrace Γ.graph
  safe : IsBracketSafe Z Y (.finite trace)
  initial_eq : trace.initial = (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial
  terminal_eq : trace.terminal = C.finalTerminal
  first_forward : trace.firstLink.direction = .forward
  last_forward : trace.lastLink.direction = .forward

/-- Package a compressed finite run walk and its certificates as the finite
macro compiler output. -/
def Compilation.ofRunWalk {Z Y : Set Γ.DPath}
    (C : FiniteMacroRoute Γ Z Y)
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z)
    (W : FiniteRunWalk Γ.graph)
    (hlabels : W.LiteralBracketLabels Z Y)
    (P : (AltPath.finite W.toFiniteTrace).IndexedBackwardProvenance
      Y (Fin (W.lastIndex + 1)))
    (hinitial : W.vertex 0 = (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial)
    (hterminal : W.vertex (W.run W.lastRunIndex).last = C.finalTerminal)
    (hfirst : (W.run ⟨0, Nat.zero_lt_succ _⟩).link.direction = .forward)
    (hlast : (W.run W.lastRunIndex).link.direction = .forward) :
    C.Compilation where
  trace := W.toFiniteTrace
  safe := (W.isLiteralBracketAlternating hlabels).isBracketSafe_of_indexedBackwardProvenance
    hZ hY hZfin P
  initial_eq := by simpa using W.toFiniteTrace_initial.trans hinitial
  terminal_eq := by simpa using W.toFiniteTrace_terminal.trans hterminal
  first_forward := by
    simpa [FiniteTrace.firstLink, FiniteRunWalk.toFiniteTrace] using hfirst
  last_forward := by
    simpa [FiniteTrace.lastLink, FiniteRunWalk.toFiniteTrace,
      FiniteRunWalk.lastRunIndex] using hlast

end FiniteMacroRoute

namespace MacroChain

/-- The exact edge-level output needed from an infinite macro chain. -/
structure Compilation {Z Y : Set Γ.DPath} (C : MacroChain Z Y) where
  trace : InfiniteTrace Γ.graph
  safe : IsBracketSafe Z Y (.infinite trace)
  initial_eq : trace.initial = (C.z 0).1.initial

/-- Package a compressed infinite run walk and its certificates as the
infinite macro compiler output. -/
def Compilation.ofRunWalk {Z Y : Set Γ.DPath} (C : MacroChain Z Y)
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z)
    (W : InfiniteRunWalk Γ.graph)
    (hlabels : W.LiteralBracketLabels Z Y)
    (P : (AltPath.infinite W.toInfiniteTrace).IndexedBackwardProvenance Y ℕ)
    (hinitial : W.vertex 0 = (C.z 0).1.initial) : C.Compilation where
  trace := W.toInfiniteTrace
  safe := (W.isLiteralBracketAlternating hlabels).isBracketSafe_of_indexedBackwardProvenance
    hZ hY hZfin P
  initial_eq := by simpa using W.toInfiniteTrace_initial.trans hinitial

end MacroChain

/-- Once the finite- and infinite-orbit compilers are available, the macro
orbit starting at a particular uncovered initial path gives the literal safe
alternating dichotomy. -/
theorem safeAlternatingDichotomy_of_macro_compilers
    (hΓ : Γ.IsNormalized) {Z Y : Set Γ.DPath}
    (hZB : Γ.terminalFrontier Z ⊆ Γ.target)
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfin : Γ.HasFiniteCharacter Z)
    (hinit : Γ.initialSet Y ⊆ Γ.initialSet Z)
    {u : V} (p₀ : Z) (hp₀ : p₀.1.initial = u)
    (huY : u ∉ Γ.vertexSet Y)
    (finiteCompiler : u ∉ Γ.terminalFrontier Z →
      ∀ C : FiniteMacroRoute Γ Z Y,
        C.z ⟨0, Nat.zero_lt_succ _⟩ = p₀ → C.Compilation)
    (infiniteCompiler : u ∉ Γ.terminalFrontier Z →
      ∀ C : MacroChain Z Y, C.z 0 = p₀ → C.Compilation) :
    SafeAlternatingDichotomy Z Y u := by
  by_cases huT : u ∈ Γ.terminalFrontier Z
  · exact safeAlternatingDichotomy_of_mem_terminalFrontier hZ hY huT huY
  rcases finiteMacroRoute_or_infiniteMacroChain hΓ hZB hZfin hinit p₀ with
    ⟨C, hC₀⟩ | ⟨C, hC₀⟩
  · right
    let K := finiteCompiler huT C hC₀
    have hfrontier : C.finalTerminal ∈ Γ.terminalFrontier Z := by
      exact ⟨(C.z ⟨C.lastIndex, Nat.lt_succ_self _⟩).1,
        (C.z ⟨C.lastIndex, Nat.lt_succ_self _⟩).2, C.final_terminal⟩
    have hQinitial : K.trace.initial = u := by
      rw [K.initial_eq, hC₀, hp₀]
    refine ⟨C.finalTerminal, ⟨hfrontier, C.final_uncovered⟩,
      .finite K.trace, K.safe, hQinitial, ?_,
      .finite K.trace.reverse, ?_, ?_, ?_⟩
    · simp [K.terminal_eq]
    · exact IsBracketAlternating.reverse_finite_of_boundary_forward hZ
        K.safe.2 K.first_forward K.last_forward
    · simp [K.terminal_eq]
    · simp [hQinitial]
  · left
    let K := infiniteCompiler huT C hC₀
    have hQinitial : K.trace.initial = u := by
      rw [K.initial_eq, hC₀, hp₀]
    exact ⟨.infinite K.trace, K.safe, hQinitial, by
      simp [AltPath.IsInfinite]⟩

/-- Global packaging of `safeAlternatingDichotomy_of_macro_compilers`.  The
two hypotheses are precisely the finite and infinite edge-level construction
theorems, with every standing assumption made explicit. -/
theorem safeAlternatingDichotomyStatement_of_macro_compilers
    (finiteCompiler :
      ∀ (Z Y : Set Γ.DPath),
        Γ.initialSet Z ⊆ Γ.source →
        Γ.terminalFrontier Z ⊆ Γ.target →
        Γ.IsWarp Z → Γ.IsWarp Y →
        Γ.HasFiniteCharacter Z → Γ.HasFiniteCharacter Y →
        Γ.initialSet Y ⊆ Γ.initialSet Z →
        ∀ (u : V) (_hu : u ∈ Γ.initialSet Z \ Γ.vertexSet Y)
          (p₀ : Z), p₀.1.initial = u →
          u ∉ Γ.terminalFrontier Z →
          ∀ C : FiniteMacroRoute Γ Z Y,
            C.z ⟨0, Nat.zero_lt_succ _⟩ = p₀ → C.Compilation)
    (infiniteCompiler :
      ∀ (Z Y : Set Γ.DPath),
        Γ.initialSet Z ⊆ Γ.source →
        Γ.terminalFrontier Z ⊆ Γ.target →
        Γ.IsWarp Z → Γ.IsWarp Y →
        Γ.HasFiniteCharacter Z → Γ.HasFiniteCharacter Y →
        Γ.initialSet Y ⊆ Γ.initialSet Z →
        ∀ (u : V) (_hu : u ∈ Γ.initialSet Z \ Γ.vertexSet Y)
          (p₀ : Z), p₀.1.initial = u →
          u ∉ Γ.terminalFrontier Z →
          ∀ C : MacroChain Z Y, C.z 0 = p₀ → C.Compilation) :
    SafeAlternatingDichotomyStatement Γ := by
  intro hΓ Z Y hZA hZB hZ hY hZfin hYfin hinit u hu
  rcases hu.1 with ⟨p₀, hp₀Z, hp₀⟩
  let p₀' : Z := ⟨p₀, hp₀Z⟩
  apply safeAlternatingDichotomy_of_macro_compilers hΓ hZB hZ hY hZfin hinit
    p₀' hp₀ hu.2
  · exact finiteCompiler Z Y hZA hZB hZ hY hZfin hYfin hinit u hu p₀' hp₀
  · exact infiniteCompiler Z Y hZA hZB hZ hY hZfin hYfin hinit u hu p₀' hp₀

end Alternating
end Erdos599
