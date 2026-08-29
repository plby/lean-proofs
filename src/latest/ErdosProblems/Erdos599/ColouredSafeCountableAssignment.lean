/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeIsolatedReduction
import Mathlib.Data.Set.Countable

/-!
# Countable successive coloured-safe assignment with weak provenance

The forward warp changes after every finite reducing switch.  Accordingly,
the occurrence word assigned to a source is indexed by the actual current
warp at its birth stage.  We retain that warp, its finite-character and warp
certificates, and containment of its edge relation in the union of the
original forward and fixed reference relations.  We deliberately do not
coerce these words to fixed-original bracketed words.
-/

noncomputable section

open Set

namespace Erdos599.ColouredSafeReverseReachability

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

abbrev UncoveredInitial (W Y : Set Gamma.DPath) :=
  {s : V // s ∈ Gamma.initialSet W \ Gamma.vertexSet Y}

/-- A finite or infinite interval-safe occurrence word over the actual
current forward warp. -/
inductive CurrentSafeOccurrence (current Y : Set Gamma.DPath) (s : V) : Type u
  | infinite (Q : InfiniteColouredOccurrenceWord current Y)
      (safe : Q.IsIntervalSafe) (first : Q.vertex 0 = s)
  | finite (t : V) (Q : FiniteColouredOccurrenceWord current Y)
      (safe : Q.IsIntervalSafe) (first : Q.vertex 0 = s)
      (last : Q.vertex (Fin.last Q.length) = t)

namespace CurrentSafeOccurrence

def forwardEdges {current Y : Set Gamma.DPath} {s : V}
    (A : CurrentSafeOccurrence current Y s) : Set (V × V) :=
  match A with
  | .infinite Q .. => Q.forwardEdges
  | .finite _ Q .. => Q.forwardEdges

def terminal? {current Y : Set Gamma.DPath} {s : V}
    (A : CurrentSafeOccurrence current Y s) : Option V :=
  match A with
  | .infinite .. => none
  | .finite t .. => some t

@[simp] theorem terminal?_infinite
    {current Y : Set Gamma.DPath} {s : V}
    (Q : InfiniteColouredOccurrenceWord current Y)
    (hQ : Q.IsIntervalSafe) (hfirst : Q.vertex 0 = s) :
    (CurrentSafeOccurrence.infinite Q hQ hfirst).terminal? = none := rfl

@[simp] theorem terminal?_finite
    {current Y : Set Gamma.DPath} {s t : V}
    (Q : FiniteColouredOccurrenceWord current Y)
    (hQ : Q.IsIntervalSafe) (hfirst : Q.vertex 0 = s)
    (hlast : Q.vertex (Fin.last Q.length) = t) :
    (CurrentSafeOccurrence.finite t Q hQ hfirst hlast).terminal? = some t := rfl

theorem forwardEdges_subset_current
    {current Y : Set Gamma.DPath} {s : V}
    (A : CurrentSafeOccurrence current Y s) :
    A.forwardEdges ⊆ familyEdges current := by
  cases A with
  | infinite Q => exact Q.forwardEdges_subset_familyEdges
  | finite t Q => exact Q.forwardEdges_subset_familyEdges

end CurrentSafeOccurrence

/-- Honest weak provenance for one assigned source. -/
structure WeakAssignedData (W Y : Set Gamma.DPath)
    (s : UncoveredInitial W Y) where
  current : Set Gamma.DPath
  current_isWarp : Gamma.IsWarp current
  current_finite : Gamma.HasFiniteCharacter current
  current_edges : familyEdges current ⊆ familyEdges W ∪ familyEdges Y
  current_initial_subset : Gamma.initialSet current ⊆ Gamma.initialSet W
  current_terminal_subset : Gamma.terminalFrontier current ⊆
    Gamma.terminalFrontier W
  occurrence : CurrentSafeOccurrence current Y s.1
  finite_terminal_original : ∀ {t : V}, occurrence.terminal? = some t →
    t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y

namespace WeakAssignedData

/-- Honest forward provenance: a forward edge of the birth-stage word which
is not a reference edge was already an edge of the original forward warp.
This is weaker, and more accurate, than indexing the word itself by the
original warp. -/
theorem forwardEdges_sdiff_reference_subset_original
    {W Y : Set Gamma.DPath} {s : UncoveredInitial W Y}
    (D : WeakAssignedData W Y s) :
    D.occurrence.forwardEdges \ familyEdges Y ⊆ familyEdges W := by
  intro e he
  rcases D.current_edges (D.occurrence.forwardEdges_subset_current he.1) with
    heW | heY
  · exact heW
  · exact (he.2 heY).elim

theorem forwardEdges_subset_original_union_reference
    {W Y : Set Gamma.DPath} {s : UncoveredInitial W Y}
    (D : WeakAssignedData W Y s) :
    D.occurrence.forwardEdges ⊆ familyEdges W ∪ familyEdges Y :=
  D.occurrence.forwardEdges_subset_current.trans D.current_edges

end WeakAssignedData

/-- A countable successive assignment.  Finite terminals are injective, but
the assigned words retain their actual current forward warps. -/
structure WeakSuccessiveAssignment (W Y : Set Gamma.DPath) where
  assigned : ∀ s : UncoveredInitial W Y, WeakAssignedData W Y s
  finite_terminals_injective : ∀ {s₁ s₂ : UncoveredInitial W Y} {t : V},
    (assigned s₁).occurrence.terminal? = some t →
    (assigned s₂).occurrence.terminal? = some t → s₁ = s₂

section Recursion

variable (Gamma)
variable (W Y : Set Gamma.DPath)

private structure AssignmentState
    (code : UncoveredInitial W Y → ℕ) (n : ℕ) where
  current : Set Gamma.DPath
  current_isWarp : Gamma.IsWarp current
  current_finite : Gamma.HasFiniteCharacter current
  current_edges : familyEdges current ⊆ familyEdges W ∪ familyEdges Y
  current_initial_subset : Gamma.initialSet current ⊆ Gamma.initialSet W
  current_terminal_subset : Gamma.terminalFrontier current ⊆
    Gamma.terminalFrontier W
  initialY_subset : Gamma.initialSet Y ⊆ Gamma.initialSet current
  initial_pure : Gamma.initialSet current ∩ Gamma.vertexSet Y ⊆
    Gamma.initialSet Y
  terminal_pure : Gamma.terminalFrontier current ∩ Gamma.vertexSet Y ⊆
    Gamma.terminalFrontier Y
  unprocessed_initial : ∀ s, n ≤ code s → s.1 ∈ Gamma.initialSet current
  used : Set V
  used_disjoint : Disjoint used (Gamma.terminalFrontier current)

namespace AssignmentState

variable {Gamma W Y}
variable {code : UncoveredInitial W Y → ℕ}

private def initial
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y) : AssignmentState Gamma W Y code 0 where
  current := W
  current_isWarp := hW
  current_finite := hWfin
  current_edges := Set.subset_union_left
  current_initial_subset := Subset.rfl
  current_terminal_subset := Subset.rfl
  initialY_subset := hsource
  initial_pure := hinitial
  terminal_pure := hterminal
  unprocessed_initial := fun s _ ↦ s.property.1
  used := ∅
  used_disjoint := by simp

private inductive ChosenAlternative
    (current : Set Gamma.DPath) (s : UncoveredInitial W Y) : Type u
  | infinite (Q : InfiniteColouredOccurrenceWord current Y)
      (safe : Q.IsIntervalSafe) (first : Q.vertex 0 = s.1)
  | finite (t : V)
      (terminal_mem : t ∈ Gamma.terminalFrontier current \ Gamma.vertexSet Y)
      (Q : FiniteColouredOccurrenceWord current Y)
      (safe : Q.IsIntervalSafe) (first : Q.vertex 0 = s.1)
      (last : Q.vertex (Fin.last Q.length) = t)
      (next : Set Gamma.DPath) (next_isWarp : Gamma.IsWarp next)
      (next_finite : Gamma.HasFiniteCharacter next)
      (next_edges : familyEdges next ⊆ familyEdges current ∪ familyEdges Y)
      (next_initial : Gamma.initialSet next = Gamma.initialSet current \ {s.1})
      (next_terminal : Gamma.terminalFrontier next =
        Gamma.terminalFrontier current \ {t})

private structure StepResult (n : ℕ)
    (S : AssignmentState Gamma W Y code n) where
  next : AssignmentState Gamma W Y code (n + 1)
  used_mono : S.used ⊆ next.used
  output : ∀ s, code s = n → WeakAssignedData W Y s
  finite_terminal_mem_current : ∀ s (hs : code s = n) t,
    ((output s hs).occurrence.terminal? = some t) →
      t ∈ Gamma.terminalFrontier S.current
  finite_terminal_mem_next_used : ∀ s (hs : code s = n) t,
    ((output s hs).occurrence.terminal? = some t) → t ∈ next.used

private noncomputable def step
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hcode : Function.Injective code) (n : ℕ)
    (S : AssignmentState Gamma W Y code n) : StepResult n S := by
  classical
  by_cases hn : ∃ s, code s = n
  · let s : UncoveredInitial W Y := Classical.choose hn
    have hscode : code s = n := Classical.choose_spec hn
    have hsCurrent : s.1 ∈ Gamma.initialSet S.current :=
      S.unprocessed_initial s (by omega)
    have hAlt := exists_safe_occurrence_dichotomy_total
      S.current_isWarp hY S.current_finite hYfin S.initialY_subset
      S.initial_pure S.terminal_pure hsCurrent s.property.2
    have hChosen : Nonempty (ChosenAlternative S.current s) := by
      rcases hAlt with hInfinite | hFinite
      · obtain ⟨Q, hsafe, hfirst, _U, _hU, _hUfin, _hUE, _hUI,
          _hUinitial, _hUterminal⟩ := hInfinite
        exact ⟨.infinite Q hsafe hfirst⟩
      · obtain ⟨t, ht, Q, hsafe, hfirst, hlast, U, hU, hUfin,
          hUE, _hUI, hUinitial, hUterminal⟩ := hFinite
        exact ⟨.finite t ht Q hsafe hfirst hlast U hU hUfin hUE
          hUinitial hUterminal⟩
    let chosen := Classical.choice hChosen
    cases chosen with
    | infinite Q hsafe hfirst =>
      let data : WeakAssignedData W Y s := {
        current := S.current
        current_isWarp := S.current_isWarp
        current_finite := S.current_finite
        current_edges := S.current_edges
        current_initial_subset := S.current_initial_subset
        current_terminal_subset := S.current_terminal_subset
        occurrence := .infinite Q hsafe hfirst
        finite_terminal_original := by simp }
      exact {
        next := {
          current := S.current
          current_isWarp := S.current_isWarp
          current_finite := S.current_finite
          current_edges := S.current_edges
          current_initial_subset := S.current_initial_subset
          current_terminal_subset := S.current_terminal_subset
          initialY_subset := S.initialY_subset
          initial_pure := S.initial_pure
          terminal_pure := S.terminal_pure
          unprocessed_initial := fun z hz ↦ S.unprocessed_initial z (by omega)
          used := S.used
          used_disjoint := S.used_disjoint }
        used_mono := Subset.rfl
        output := by
          intro z hz
          have hzs : z = s := hcode (hz.trans hscode.symm)
          subst z
          exact data
        finite_terminal_mem_current := by
          intro z hz t ht
          have hzs : z = s := hcode (hz.trans hscode.symm)
          subst z
          simp [data] at ht
        finite_terminal_mem_next_used := by
          intro z hz t ht
          have hzs : z = s := hcode (hz.trans hscode.symm)
          subst z
          simp [data] at ht }
    | finite t ht Q hsafe hfirst hlast U hU hUfin hUE hUinitial hUterminal =>
      have htOriginal : t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y :=
        ⟨S.current_terminal_subset ht.1, ht.2⟩
      have hUEOriginal : familyEdges U ⊆ familyEdges W ∪ familyEdges Y := by
        intro e he
        rcases hUE he with heCurrent | heY
        · exact S.current_edges heCurrent
        · exact Or.inr heY
      let data : WeakAssignedData W Y s := {
        current := S.current
        current_isWarp := S.current_isWarp
        current_finite := S.current_finite
        current_edges := S.current_edges
        current_initial_subset := S.current_initial_subset
        current_terminal_subset := S.current_terminal_subset
        occurrence := .finite t Q hsafe hfirst hlast
        finite_terminal_original := by
          intro x hx
          have htx : t = x := by
            apply Option.some.inj
            simpa using hx
          exact htx.symm ▸ htOriginal }
      exact {
        next := {
          current := U
          current_isWarp := hU
          current_finite := hUfin
          current_edges := hUEOriginal
          current_initial_subset := by
            rw [hUinitial]
            exact Set.sdiff_subset.trans S.current_initial_subset
          current_terminal_subset := by
            rw [hUterminal]
            exact Set.sdiff_subset.trans S.current_terminal_subset
          initialY_subset := by
            rw [hUinitial]
            intro x hx
            refine ⟨S.initialY_subset hx, ?_⟩
            intro hxs
            have hxVertex : x ∈ Gamma.vertexSet Y := by
              rcases hx with ⟨p, hpY, hpx⟩
              exact ⟨p, hpY, hpx ▸ p.initial_mem_support⟩
            exact s.property.2 (Set.mem_singleton_iff.mp hxs ▸ hxVertex)
          initial_pure := by
            rw [hUinitial]
            exact fun x hx ↦ S.initial_pure ⟨hx.1.1, hx.2⟩
          terminal_pure := by
            rw [hUterminal]
            exact fun x hx ↦ S.terminal_pure ⟨hx.1.1, hx.2⟩
          unprocessed_initial := by
            intro z hz
            rw [hUinitial]
            refine ⟨S.unprocessed_initial z (by omega), ?_⟩
            intro hzsval
            have hzs : z = s := Subtype.ext (Set.mem_singleton_iff.mp hzsval)
            subst z
            omega
          used := insert t S.used
          used_disjoint := by
            rw [Set.disjoint_left]
            intro x hxUsed hxTerminal
            rw [hUterminal] at hxTerminal
            rcases hxUsed with rfl | hxUsed
            · exact hxTerminal.2 rfl
            · exact Set.disjoint_left.1 S.used_disjoint hxUsed hxTerminal.1 }
        used_mono := subset_insert t S.used
        output := by
          intro z hz
          have hzs : z = s := hcode (hz.trans hscode.symm)
          subst z
          exact data
        finite_terminal_mem_current := by
          intro z hz x hx
          have hzs : z = s := hcode (hz.trans hscode.symm)
          subst z
          have htx : t = x := by
            apply Option.some.inj
            simpa [data] using hx
          exact htx.symm ▸ ht.1
        finite_terminal_mem_next_used := by
          intro z hz x hx
          have hzs : z = s := hcode (hz.trans hscode.symm)
          subst z
          have htx : t = x := by
            apply Option.some.inj
            simpa [data] using hx
          exact htx.symm ▸ Set.mem_insert t S.used }
  · exact {
      next := {
        current := S.current
        current_isWarp := S.current_isWarp
        current_finite := S.current_finite
        current_edges := S.current_edges
        current_initial_subset := S.current_initial_subset
        current_terminal_subset := S.current_terminal_subset
        initialY_subset := S.initialY_subset
        initial_pure := S.initial_pure
        terminal_pure := S.terminal_pure
        unprocessed_initial := fun z hz ↦ S.unprocessed_initial z (by omega)
        used := S.used
        used_disjoint := S.used_disjoint }
      used_mono := Subset.rfl
      output := fun z hz ↦ (hn ⟨z, hz⟩).elim
      finite_terminal_mem_current := fun z hz ↦ (hn ⟨z, hz⟩).elim
      finite_terminal_mem_next_used := fun z hz ↦ (hn ⟨z, hz⟩).elim }

end AssignmentState

open AssignmentState

private noncomputable def assignmentStates
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (code : UncoveredInitial W Y → ℕ) (hcode : Function.Injective code) :
    ∀ n, AssignmentState Gamma W Y code n
  | 0 => AssignmentState.initial hW hWfin hsource hinitial hterminal
  | n + 1 =>
      (AssignmentState.step hY hYfin hcode n
        (assignmentStates hW hWfin hY hYfin hsource hinitial hterminal
          code hcode n)).next

private theorem assignmentStates_used_mono
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (code : UncoveredInitial W Y → ℕ) (hcode : Function.Injective code)
    {n m : ℕ} (hnm : n ≤ m) :
    (assignmentStates Gamma W Y hW hWfin hY hYfin hsource hinitial hterminal
      code hcode n).used ⊆
    (assignmentStates Gamma W Y hW hWfin hY hYfin hsource hinitial hterminal
      code hcode m).used := by
  intro x hx
  induction m, hnm using Nat.le_induction with
  | base => exact hx
  | succ m hnm ih =>
      exact (AssignmentState.step hY hYfin hcode m
        (assignmentStates Gamma W Y hW hWfin hY hYfin hsource hinitial
          hterminal code hcode m)).used_mono ih

private noncomputable def assignmentData
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (code : UncoveredInitial W Y → ℕ) (hcode : Function.Injective code)
    (s : UncoveredInitial W Y) : WeakAssignedData W Y s :=
  (AssignmentState.step hY hYfin hcode (code s)
    (assignmentStates Gamma W Y hW hWfin hY hYfin hsource hinitial hterminal
      code hcode (code s))).output s rfl

private theorem assignmentData_finite_terminals_injective
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (code : UncoveredInitial W Y → ℕ) (hcode : Function.Injective code)
    {s₁ s₂ : UncoveredInitial W Y} {t : V}
    (hs₁ : (assignmentData Gamma W Y hW hWfin hY hYfin hsource hinitial
      hterminal code hcode s₁).occurrence.terminal? = some t)
    (hs₂ : (assignmentData Gamma W Y hW hWfin hY hYfin hsource hinitial
      hterminal code hcode s₂).occurrence.terminal? = some t) : s₁ = s₂ := by
  rcases lt_trichotomy (code s₁) (code s₂) with hlt | heq | hgt
  · let S₁ := assignmentStates Gamma W Y hW hWfin hY hYfin hsource
      hinitial hterminal code hcode (code s₁)
    let R₁ := AssignmentState.step hY hYfin hcode (code s₁) S₁
    let S₂ := assignmentStates Gamma W Y hW hWfin hY hYfin hsource
      hinitial hterminal code hcode (code s₂)
    let R₂ := AssignmentState.step hY hYfin hcode (code s₂) S₂
    have htUsedNext : t ∈ R₁.next.used :=
      R₁.finite_terminal_mem_next_used s₁ rfl t hs₁
    have htUsed : t ∈ S₂.used :=
      assignmentStates_used_mono Gamma W Y hW hWfin hY hYfin hsource
        hinitial hterminal code hcode (Nat.succ_le_iff.2 hlt) htUsedNext
    have htTerminal : t ∈ Gamma.terminalFrontier S₂.current :=
      R₂.finite_terminal_mem_current s₂ rfl t hs₂
    exact (Set.disjoint_left.1 S₂.used_disjoint htUsed htTerminal).elim
  · exact hcode heq
  · let S₂ := assignmentStates Gamma W Y hW hWfin hY hYfin hsource
      hinitial hterminal code hcode (code s₂)
    let R₂ := AssignmentState.step hY hYfin hcode (code s₂) S₂
    let S₁ := assignmentStates Gamma W Y hW hWfin hY hYfin hsource
      hinitial hterminal code hcode (code s₁)
    let R₁ := AssignmentState.step hY hYfin hcode (code s₁) S₁
    have htUsedNext : t ∈ R₂.next.used :=
      R₂.finite_terminal_mem_next_used s₂ rfl t hs₂
    have htUsed : t ∈ S₁.used :=
      assignmentStates_used_mono Gamma W Y hW hWfin hY hYfin hsource
        hinitial hterminal code hcode (Nat.succ_le_iff.2 hgt) htUsedNext
    have htTerminal : t ∈ Gamma.terminalFrontier S₁.current :=
      R₁.finite_terminal_mem_current s₁ rfl t hs₁
    exact (Set.disjoint_left.1 S₁.used_disjoint htUsed htTerminal).elim

private noncomputable def weakAssignmentOfCode
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (code : UncoveredInitial W Y → ℕ) (hcode : Function.Injective code) :
    WeakSuccessiveAssignment W Y where
  assigned s := assignmentData Gamma W Y hW hWfin hY hYfin hsource
    hinitial hterminal code hcode s
  finite_terminals_injective :=
    assignmentData_finite_terminals_injective Gamma W Y hW hWfin hY hYfin
      hsource hinitial hterminal code hcode

/-- Countable successive-switch assignment obtained from the proved total
single-source dichotomy.  The result intentionally retains current-warp
provenance rather than claiming fixed-original bracketedness. -/
theorem exists_weakSuccessiveAssignment_of_countable
    {W Y : Set Gamma.DPath}
    (hW : Gamma.IsWarp W) (hWfin : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (hcount : (Gamma.initialSet W \ Gamma.vertexSet Y).Countable) :
    Nonempty (WeakSuccessiveAssignment W Y) := by
  classical
  rcases Set.countable_iff_exists_injective.1 hcount with ⟨code, hcode⟩
  exact ⟨weakAssignmentOfCode Gamma W Y hW hWfin hY hYfin hsource
    hinitial hterminal code hcode⟩

#print axioms exists_weakSuccessiveAssignment_of_countable

end Recursion

end Erdos599.ColouredSafeReverseReachability
