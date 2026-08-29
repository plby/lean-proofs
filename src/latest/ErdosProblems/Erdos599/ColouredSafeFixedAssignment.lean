/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeInternalReferenceHall
import ErdosProblems.Erdos599.ColouredSafeCountableAssignment
import Mathlib.Combinatorics.Hall.Basic

/-!
# A simultaneous safe assignment over the fixed original forward warp

Only sources without an infinite original safe word use the finite-row
Hall matching. Every chosen word, including the infinite alternatives,
retains the literal original forward warp as its type parameter. The
internal-edge hypothesis is explicit; its fractured-family application
requires a separate geometric proof.
-/

noncomputable section

namespace Erdos599.Alternating.ColouredSafeFixedAssignment

open Set DirectedPath FiniteColouredOccurrenceWord ColouredSafeReverseReachability
open ColouredSafeInternalReferenceHall

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- Exposed sources which must receive a finite terminal. -/
abbrev FiniteOnlySource (W Y : Set Gamma.DPath) :=
  {s : ExposedInitial W Y // ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
    Q.IsIntervalSafe ∧ Q.vertex 0 = s.1}

/-- A simultaneous assignment with the same original forward warp for
every source. There is no pairwise disjointness assertion for the words. -/
structure FixedSafeAssignment (W Y : Set Gamma.DPath) where
  assigned : ∀ s : ExposedInitial W Y, CurrentSafeOccurrence W Y s.1
  finite_terminal : ∀ (s : ExposedInitial W Y) {t : V},
    (assigned s).terminal? = some t →
      t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y
  finite_terminals_injective : ∀ {s₁ s₂ : ExposedInitial W Y} {t : V},
    (assigned s₁).terminal? = some t →
    (assigned s₂).terminal? = some t → s₁ = s₂

/-- The finite-subset Hall inequalities give an injection on precisely
the sources with no infinite safe alternative. -/
theorem exists_finiteTerminalInjection_of_hall
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hHall : ∀ {J : Set (ExposedInitial W Y)}, J.Finite →
      (∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
        Q.IsIntervalSafe ∧ Q.vertex 0 = s.1) →
      J.ncard ≤ (safeTerminalUnion J).ncard) :
    ∃ f : FiniteOnlySource W Y → V, Function.Injective f ∧
      ∀ s, f s ∈ safelyReachable W Y s.1.1 := by
  classical
  have hrow (s : FiniteOnlySource W Y) :
      (safelyReachable W Y s.1.1).Finite :=
    safelyReachable_finite_of_no_safeInfinite hW hY hWfin hYfin
      s.1.2.1 s.1.2.2 s.2
  let row (s : FiniteOnlySource W Y) : Finset V := (hrow s).toFinset
  have hfiniteHall (J : Finset (FiniteOnlySource W Y)) :
      J.card ≤ (J.biUnion row).card := by
    let K : Set (ExposedInitial W Y) := Subtype.val '' (J : Set (FiniteOnlySource W Y))
    have hK : K.Finite := J.finite_toSet.image Subtype.val
    have hno : ∀ s ∈ K, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
        Q.IsIntervalSafe ∧ Q.vertex 0 = s.1 := by
      rintro _ ⟨s, _hs, rfl⟩
      exact s.2
    have hcard : K.ncard ≤ (safeTerminalUnion K).ncard := hHall hK hno
    have hKcard : K.ncard = J.card := by
      change (Subtype.val '' (J : Set (FiniteOnlySource W Y))).ncard = J.card
      rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
    have hUnion : safeTerminalUnion K = (J.biUnion row : Set V) := by
      ext t
      constructor
      · intro ht
        obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
        obtain ⟨hsK, htrow⟩ := Set.mem_iUnion.mp hs
        obtain ⟨r, hr, rfl⟩ := hsK
        exact Finset.mem_biUnion.mpr ⟨r, hr, (hrow r).mem_toFinset.mpr htrow⟩
      · intro ht
        obtain ⟨s, hs, hts⟩ := Finset.mem_biUnion.mp ht
        exact mem_safeTerminalUnion_of_mem_safelyReachable
          (J := K) (s := s.1) ⟨s, hs, rfl⟩ ((hrow s).mem_toFinset.mp hts)
    simpa only [hKcard, hUnion, Set.ncard_coe_finset] using hcard
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective row).mp hfiniteHall
  exact ⟨f, hf, fun s ↦ (hrow s).mem_toFinset.mp (hmem s)⟩

/-- Assemble actual finite and infinite safe witnesses after Hall selection. -/
theorem exists_fixedSafeAssignment_of_hall
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hHall : ∀ {J : Set (ExposedInitial W Y)}, J.Finite →
      (∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
        Q.IsIntervalSafe ∧ Q.vertex 0 = s.1) →
      J.ncard ≤ (safeTerminalUnion J).ncard) :
    Nonempty (FixedSafeAssignment W Y) := by
  classical
  obtain ⟨f, hf, hmem⟩ := exists_finiteTerminalInjection_of_hall hW hY hWfin hYfin hHall
  have hwitness (s : FiniteOnlySource W Y) :
      ∃ Q : FiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧
        Q.vertex 0 = s.1.1 ∧ Q.vertex (Fin.last Q.length) = f s := (hmem s).2
  choose q hsafe hfirst hlast using hwitness
  let assigned (s : ExposedInitial W Y) : CurrentSafeOccurrence W Y s.1 :=
    if hi : ∃ Q : InfiniteColouredOccurrenceWord W Y,
        Q.IsIntervalSafe ∧ Q.vertex 0 = s.1 then
      .infinite hi.choose hi.choose_spec.1 hi.choose_spec.2
    else
      .finite (f ⟨s, hi⟩) (q ⟨s, hi⟩) (hsafe ⟨s, hi⟩)
        (hfirst ⟨s, hi⟩) (hlast ⟨s, hi⟩)
  refine ⟨{ assigned := assigned, finite_terminal := ?_, finite_terminals_injective := ?_ }⟩
  · intro s t ht
    by_cases hi : ∃ Q : InfiniteColouredOccurrenceWord W Y,
        Q.IsIntervalSafe ∧ Q.vertex 0 = s.1
    · simp [assigned, hi] at ht
    · have heq : f ⟨s, hi⟩ = t := by simpa [assigned, hi] using ht
      rw [← heq]
      exact (hmem ⟨s, hi⟩).1
  · intro s₁ s₂ t ht₁ ht₂
    by_cases hi₁ : ∃ Q : InfiniteColouredOccurrenceWord W Y,
        Q.IsIntervalSafe ∧ Q.vertex 0 = s₁.1
    · simp [assigned, hi₁] at ht₁
    by_cases hi₂ : ∃ Q : InfiniteColouredOccurrenceWord W Y,
        Q.IsIntervalSafe ∧ Q.vertex 0 = s₂.1
    · simp [assigned, hi₂] at ht₂
    have heq₁ : f ⟨s₁, hi₁⟩ = t := by simpa [assigned, hi₁] using ht₁
    have heq₂ : f ⟨s₂, hi₂⟩ = t := by simpa [assigned, hi₂] using ht₂
    exact congrArg Subtype.val (hf (heq₁.trans heq₂.symm))

/-- The bounded-feedback argument supplies the Hall premise without
assuming finite ambient carriers. -/
theorem exists_fixedSafeAssignment
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (hinternal : InternalReferenceEdges W Y) :
    Nonempty (FixedSafeAssignment W Y) :=
  exists_fixedSafeAssignment_of_hall hW hY hWfin hYfin
    (fun hJ hno ↦ hall hW hY hWfin hYfin hsource hterminal hinternal hJ hno)

/-- A theorem for the real subdivided graph; no fractured-duplication
incidence is being assumed here. -/
theorem exists_fixedSafeAssignment_of_subdivision
    (hsub : Blueprint.HasHereditarySubdivisionIncidence Gamma.graph)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y) :
    Nonempty (FixedSafeAssignment W Y) :=
  exists_fixedSafeAssignment_of_hall hW hY hWfin hYfin
    (fun hJ hno ↦ hall_of_subdivision hsub hW hY hWfin hYfin hsource hterminal hJ hno)

#print axioms exists_finiteTerminalInjection_of_hall
#print axioms exists_fixedSafeAssignment_of_hall
#print axioms exists_fixedSafeAssignment
#print axioms exists_fixedSafeAssignment_of_subdivision

end Erdos599.Alternating.ColouredSafeFixedAssignment
