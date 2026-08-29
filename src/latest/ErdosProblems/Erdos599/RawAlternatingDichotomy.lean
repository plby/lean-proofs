/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingMacroChain
import ErdosProblems.Erdos599.AlternatingTraceOps

/-!
# The literal endpoint-pure alternating dichotomy

This file contains the occurrence-walk construction used to prove the
normalized, endpoint-pure form of Aharoni--Berger Lemma 4.13.  The first
ingredient is chronological loop erasure for a sequence in which every
projected vertex occurs only finitely often.  In the macro chain each vertex
occurs on at most one `Z`-path and at most one `Y`-path, so this is exactly the
needed projection lemma.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u v

/-! ## Infinite chronological loop erasure -/

/-- The set of indices at which `f` assumes its value at `n`. -/
def occurrenceFiber {A : Type u} (f : ℕ → A) (n : ℕ) : Set ℕ :=
  {m | f m = f n}

theorem mem_occurrenceFiber_self {A : Type u} (f : ℕ → A) (n : ℕ) :
    n ∈ occurrenceFiber f n :=
  rfl

/-- The last occurrence of `f n`, when every fiber of `f` is finite. -/
noncomputable def lastOccurrence {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) (n : ℕ) : ℕ :=
  (hfinite n).toFinset.max' ⟨n, by
    simpa only [Set.Finite.mem_toFinset] using mem_occurrenceFiber_self f n⟩

theorem lastOccurrence_mem {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) (n : ℕ) :
    f (lastOccurrence f hfinite n) = f n := by
  have hmem : lastOccurrence f hfinite n ∈
      (hfinite n).toFinset := Finset.max'_mem _ _
  simpa only [Set.Finite.mem_toFinset, occurrenceFiber, Set.mem_setOf_eq]
    using hmem

theorem le_lastOccurrence {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) {n m : ℕ}
    (hm : f m = f n) :
    m ≤ lastOccurrence f hfinite n := by
  apply Finset.le_max'
  simpa only [Set.Finite.mem_toFinset, occurrenceFiber, Set.mem_setOf_eq]
    using hm

theorem le_lastOccurrence_self {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) (n : ℕ) :
    n ≤ lastOccurrence f hfinite n :=
  le_lastOccurrence f hfinite rfl

theorem lastOccurrence_is_last {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) {n m : ℕ}
    (hm : f m = f (lastOccurrence f hfinite n)) :
    m ≤ lastOccurrence f hfinite n := by
  apply le_lastOccurrence f hfinite
  exact hm.trans (lastOccurrence_mem f hfinite n)

/-- The retained raw indices of chronological loop erasure.  From a retained
index `k`, keep the edge starting at `k`, then jump its other endpoint to its
last occurrence in the raw sequence. -/
noncomputable def loopErasedIndex {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) : ℕ → ℕ
  | 0 => lastOccurrence f hfinite 0
  | n + 1 => lastOccurrence f hfinite (loopErasedIndex f hfinite n + 1)

@[simp]
theorem loopErasedIndex_zero {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) :
    loopErasedIndex f hfinite 0 = lastOccurrence f hfinite 0 :=
  rfl

@[simp]
theorem loopErasedIndex_succ {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) (n : ℕ) :
    loopErasedIndex f hfinite (n + 1) =
      lastOccurrence f hfinite (loopErasedIndex f hfinite n + 1) :=
  rfl

theorem loopErasedIndex_strictMono {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) :
    StrictMono (loopErasedIndex f hfinite) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [loopErasedIndex_succ]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    (le_lastOccurrence_self f hfinite _)

/-- The endpoint of the retained raw edge is the next retained projected
vertex. -/
theorem loopErasedIndex_join {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) (n : ℕ) :
    f (loopErasedIndex f hfinite n + 1) =
      f (loopErasedIndex f hfinite (n + 1)) := by
  rw [loopErasedIndex_succ]
  exact (lastOccurrence_mem f hfinite
    (loopErasedIndex f hfinite n + 1)).symm

theorem loopErasedIndex_is_last {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) (n m : ℕ)
    (hm : f m = f (loopErasedIndex f hfinite n)) :
    m ≤ loopErasedIndex f hfinite n := by
  cases n with
  | zero =>
      simpa using lastOccurrence_is_last f hfinite hm
  | succ n =>
      rw [loopErasedIndex_succ]
      exact lastOccurrence_is_last f hfinite hm

/-- Projected vertices retained by chronological loop erasure never repeat. -/
theorem injective_loopErasedVertex {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite) :
    Function.Injective (fun n ↦ f (loopErasedIndex f hfinite n)) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij' | hji'
  · have hindex := loopErasedIndex_strictMono f hfinite hij'
    have hle := loopErasedIndex_is_last f hfinite i
      (loopErasedIndex f hfinite j) hij.symm
    exact (Nat.not_lt_of_ge hle) hindex
  · have hindex := loopErasedIndex_strictMono f hfinite hji'
    have hle := loopErasedIndex_is_last f hfinite j
      (loopErasedIndex f hfinite i) hij
    exact (Nat.not_lt_of_ge hle) hindex

/-- If the root has no later occurrence, chronological loop erasure begins
at the literal root rather than merely at an equal projected vertex. -/
theorem loopErasedIndex_zero_eq_zero_of_root_unique {A : Type u} (f : ℕ → A)
    (hfinite : ∀ n, (occurrenceFiber f n).Finite)
    (hroot : ∀ m, f m = f 0 → m = 0) :
    loopErasedIndex f hfinite 0 = 0 := by
  rw [loopErasedIndex_zero]
  exact hroot _ (lastOccurrence_mem f hfinite 0)

/-! ## Literal reversal -/

/-- Reversal is automatic for a finite literal bracket-alternating trace
whose two exposed links are forward.  The extra contact/off-edge hypotheses
needed by exact switching play no role here: after reversal the original
forward links are backward fragments of `U`, and the original backward links
are forward fragments of `Y`. -/
theorem IsBracketAlternating.reverse_finite_of_boundary_forward
    {V : Type u} {Γ : DWeb V} {U Y : Set Γ.DPath}
    {Q : FiniteTrace Γ.graph}
    (hU : Γ.IsWarp U)
    (hQ : IsBracketAlternating U Y (.finite Q))
    (hfirst : Q.firstLink.direction = .forward)
    (hlast : Q.lastLink.direction = .forward) :
    IsBracketAlternating Y U (.finite Q.reverse) := by
  rcases hQ with ⟨⟨_hY, hbackY, _hinitial, _hterminal⟩, hforwardU⟩
  refine ⟨⟨hU, ?_, ?_, ?_⟩, ?_⟩
  · intro l hl hldir
    change l ∈ Q.reverse.links at hl
    rw [FiniteTrace.links_reverse] at hl
    rcases hl with ⟨k, hk, rfl⟩
    have hkdir : k.direction = .forward := by
      cases hd : k.direction <;> simp [Link.reverse, hd] at hldir ⊢
    simpa using hforwardU k hk hkdir
  · intro hreverseFirst
    have hcontra : Q.lastLink.direction = .backward := by
      cases hd : Q.lastLink.direction <;>
        simp [AltPath.firstDirection?_finite_reverse, hd] at hreverseFirst ⊢
    exact (by simpa [hlast] using hcontra)
  · intro t _hterm hreverseLast
    have hcontra : Q.firstLink.direction = .backward := by
      cases hd : Q.firstLink.direction <;>
        simp [AltPath.lastDirection?_finite_reverse, hd] at hreverseLast ⊢
    exact (by simpa [hfirst] using hcontra)
  · intro l hl hldir
    change l ∈ Q.reverse.links at hl
    rw [FiniteTrace.links_reverse] at hl
    rcases hl with ⟨k, hk, rfl⟩
    have hkdir : k.direction = .backward := by
      cases hd : k.direction <;> simp [Link.reverse, hd] at hldir ⊢
    simpa using hbackY k hk hkdir

/-! ## The deterministic macro orbit -/

/-- A finite initial macro orbit ending at the first `Z`-terminal which is
not covered by `Y`.  The intervening `Y` witnesses are stored explicitly for
the edge-level compiler. -/
structure FiniteMacroRoute {V : Type u} (Γ : DWeb V)
    (Z Y : Set Γ.DPath) where
  lastIndex : ℕ
  z : Fin (lastIndex + 1) → Z
  y : Fin lastIndex → Y
  terminal : Fin lastIndex → V
  z_terminal : ∀ i,
    Γ.terminal? (z ⟨i.1, by omega⟩).1 = some (terminal i)
  y_terminal : ∀ i, Γ.terminal? (y i).1 = some (terminal i)
  joins : ∀ i,
    (y i).1.initial = (z ⟨i.1 + 1, by omega⟩).1.initial
  finalTerminal : V
  final_terminal :
    Γ.terminal? (z ⟨lastIndex, Nat.lt_succ_self _⟩).1 = some finalTerminal
  final_uncovered : finalTerminal ∉ Γ.vertexSet Y

namespace FiniteMacroRoute

theorem step {V : Type u} {Γ : DWeb V} {Z Y : Set Γ.DPath}
    (C : FiniteMacroRoute Γ Z Y) (i : Fin C.lastIndex) :
    MacroStep Z Y (C.z ⟨i.1, by omega⟩) (C.z ⟨i.1 + 1, by omega⟩) :=
  ⟨C.y i, C.terminal i, C.z_terminal i, C.y_terminal i, C.joins i⟩

end FiniteMacroRoute

/-- Starting at any `Z`-path, deterministic path-level continuation either
reaches an uncovered terminal after finitely many steps or supplies an
infinite macro chain.  Only terminals on the actual orbit are required to be
covered; unrelated members of `Z` play no role. -/
theorem finiteMacroRoute_or_infiniteMacroChain
    {V : Type u} {Γ : DWeb V}
    (hΓ : Γ.IsNormalized) {Z Y : Set Γ.DPath}
    (hZB : Γ.terminalFrontier Z ⊆ Γ.target)
    (hZfin : Γ.HasFiniteCharacter Z)
    (hinit : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (p₀ : Z) :
    (∃ C : FiniteMacroRoute Γ Z Y,
      C.z ⟨0, Nat.zero_lt_succ _⟩ = p₀) ∨
    (∃ C : MacroChain Z Y, C.z 0 = p₀) := by
  classical
  let Covered : Z → Prop := fun p ↦
    ∀ t, Γ.terminal? p.1 = some t → t ∈ Γ.vertexSet Y
  have hstep (p : Z) (hp : Covered p) : ∃ r : Z, MacroStep Z Y p r :=
    MacroStep.exists_of_terminal_mem hΓ hZB hZfin hinit p hp
  let next : Z → Z := fun p ↦
    if hp : Covered p then Classical.choose (hstep p hp) else p
  have next_step {p : Z} (hp : Covered p) : MacroStep Z Y p (next p) := by
    simp only [next, dif_pos hp]
    exact Classical.choose_spec (hstep p hp)
  let z : ℕ → Z := fun n ↦ Nat.rec p₀ (fun _ p ↦ next p) n
  have z_zero : z 0 = p₀ := rfl
  have z_succ (n : ℕ) : z (n + 1) = next (z n) := by
    simp [z]
  by_cases hall : ∀ n, Covered (z n)
  · right
    have hzstep (n : ℕ) : MacroStep Z Y (z n) (z (n + 1)) := by
      rw [z_succ]
      exact next_step (hall n)
    let y : ℕ → Y := fun n ↦ Classical.choose (hzstep n)
    let terminal : ℕ → V := fun n ↦
      Classical.choose (Classical.choose_spec (hzstep n))
    have hspec (n : ℕ) :
        Γ.terminal? (z n).1 = some (terminal n) ∧
          Γ.terminal? (y n).1 = some (terminal n) ∧
            (y n).1.initial = (z (n + 1)).1.initial :=
      Classical.choose_spec (Classical.choose_spec (hzstep n))
    exact ⟨{
      z := z
      y := y
      terminal := terminal
      z_terminal := fun n ↦ (hspec n).1
      y_terminal := fun n ↦ (hspec n).2.1
      joins := fun n ↦ (hspec n).2.2
    }, z_zero⟩
  · left
    have hex : ∃ n, ¬ Covered (z n) := by
      simpa only [not_forall] using hall
    let N : ℕ := Nat.find hex
    have hN : ¬ Covered (z N) := Nat.find_spec hex
    have hbefore {n : ℕ} (hn : n < N) : Covered (z n) := by
      by_contra hncovered
      exact Nat.find_min hex hn hncovered
    have hzstep (n : Fin N) :
        MacroStep Z Y (z n.1) (z (n.1 + 1)) := by
      rw [z_succ]
      exact next_step (hbefore n.isLt)
    let y : Fin N → Y := fun n ↦ Classical.choose (hzstep n)
    let terminal : Fin N → V := fun n ↦
      Classical.choose (Classical.choose_spec (hzstep n))
    have hspec (n : Fin N) :
        Γ.terminal? (z n.1).1 = some (terminal n) ∧
          Γ.terminal? (y n).1 = some (terminal n) ∧
            (y n).1.initial = (z (n.1 + 1)).1.initial :=
      Classical.choose_spec (Classical.choose_spec (hzstep n))
    have hfinal : ∃ t,
        Γ.terminal? (z N).1 = some t ∧ t ∉ Γ.vertexSet Y := by
      dsimp only [Covered] at hN
      push_neg at hN
      rcases hN with ⟨t, ht, htY⟩
      exact ⟨t, ht, htY⟩
    let t : V := Classical.choose hfinal
    have ht := Classical.choose_spec hfinal
    refine ⟨{
      lastIndex := N
      z := fun i ↦ z i.1
      y := y
      terminal := terminal
      z_terminal := fun i ↦ (hspec i).1
      y_terminal := fun i ↦ (hspec i).2.1
      joins := fun i ↦ (hspec i).2.2
      finalTerminal := t
      final_terminal := ht.1
      final_uncovered := ht.2
    }, ?_⟩
    exact z_zero

end Alternating
end Erdos599
