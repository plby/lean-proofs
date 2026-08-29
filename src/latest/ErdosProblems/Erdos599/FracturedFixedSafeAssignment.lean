/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedCanonicalInternalReference
import ErdosProblems.Erdos599.FracturedColouredDichotomy
import ErdosProblems.Erdos599.Blueprint931

/-!
# Simultaneous projection of the fixed canonical safe assignment

Finite terminals retain their incoming role, so projection does not identify
different selected terminals. Singleton fractured sources use empty words;
active paths avoid those singleton vertices. Every output word uses the
original fractured edge warp, with no successive replacement of its edges.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedFixedSafeAssignment

open Set DirectedPath Alternating FracturedDuplication FracturedAssignmentPeel
open FracturedCanonicalBoundary FracturedCanonicalSafeProjection
open FracturedCanonicalInternalReference ColouredSafeReverseReachability
open FiniteColouredOccurrenceWord

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

/-- Project one chosen canonical occurrence with its actual terminal legality. -/
def projectOccurrence
    (Z : FracturedWarp Gamma) (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction : NoJunctionOnReference Z (activeReference Z Y))
    (s : ExposedInitial (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y))
    (A : CurrentSafeOccurrence (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y) s.1)
    (hterminal : ∀ {t}, A.terminal? = some t →
      t ∈ (web Gamma Z).terminalFrontier (canonicalActiveLift Z) \
        (web Gamma Z).vertexSet (canonicalPeeledReferenceLift Z Y)) :
    CurrentSafeOccurrence Z.edgeWarp Y (project s.1) := by
  have hsNotInitial : s.1 ∉ (web Gamma Z).initialSet
      (canonicalPeeledReferenceLift Z Y) :=
    fun hs ↦ s.2.2 (initialSet_subset_vertexSet _ hs)
  cases A with
  | infinite Q hQ hfirst =>
      refine .infinite (infiniteSafeProjection Z hY hYfinite Q) ?_ ?_
      · apply infiniteSafeProjection_isIntervalSafe Z hboundary hY hYfinite
          hsource hnoJunction Q hQ
        · simpa only [hfirst] using s.2.1
        · simpa only [hfirst] using hsNotInitial
      · rw [infiniteSafeProjection_first, hfirst]
  | finite t Q hQ hfirst hlast =>
      have ht := hterminal (t := t) rfl
      refine .finite (project t) (finiteSafeProjection Z hYfinite Q) ?_ ?_ ?_
      · apply finiteSafeProjection_isIntervalSafe Z hboundary hY hYfinite
          hsource hnoJunction Q hQ
        · simpa only [hfirst] using s.2.1
        · simpa only [hfirst] using hsNotInitial
        · simpa only [hlast] using ht.1
        · simpa only [hlast] using ht.2
      · rw [finiteSafeProjection_first, hfirst]
      · rw [finiteSafeProjection_last, hlast]

@[simp] theorem projectOccurrence_terminal
    (Z : FracturedWarp Gamma) (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction : NoJunctionOnReference Z (activeReference Z Y))
    (s : ExposedInitial (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y))
    (A : CurrentSafeOccurrence (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y) s.1)
    (hterminal : ∀ {t}, A.terminal? = some t →
      t ∈ (web Gamma Z).terminalFrontier (canonicalActiveLift Z) \
        (web Gamma Z).vertexSet (canonicalPeeledReferenceLift Z Y)) :
    (projectOccurrence Z hboundary hY hYfinite hsource hnoJunction s A hterminal).terminal? =
      A.terminal?.map project := by
  cases A <;> rfl

theorem projectOccurrence_terminal_mem
    (Z : FracturedWarp Gamma) (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction : NoJunctionOnReference Z (activeReference Z Y))
    (s : ExposedInitial (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y))
    (A : CurrentSafeOccurrence (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y) s.1)
    (hterminal : ∀ {t}, A.terminal? = some t →
      t ∈ (web Gamma Z).terminalFrontier (canonicalActiveLift Z) \
        (web Gamma Z).vertexSet (canonicalPeeledReferenceLift Z Y))
    {t : V}
    (ht : (projectOccurrence Z hboundary hY hYfinite hsource hnoJunction s A
      hterminal).terminal? = some t) :
    t ∈ Gamma.terminalFrontier (activePaths Z) \ Gamma.vertexSet Y := by
  cases A with
  | infinite Q hQ hfirst => simp [projectOccurrence, CurrentSafeOccurrence.terminal?] at ht
  | finite v Q hQ hfirst hlast =>
      have hv := hterminal (t := v) rfl
      have hvt : project v = t := Option.some.inj ht
      have hmem := finiteSafeProjection_terminal_mem Z hboundary hY hYfinite
        hsource hnoJunction Q (by simpa only [hlast] using hv.1)
        (by simpa only [hlast] using hv.2)
      simpa only [finiteSafeProjection_last, hlast, hvt] using hmem

/-- A projected finite terminal determines its exact incoming-role lift. -/
theorem terminal_eq_incoming_of_projectOccurrence
    (Z : FracturedWarp Gamma) (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction : NoJunctionOnReference Z (activeReference Z Y))
    (s : ExposedInitial (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y))
    (A : CurrentSafeOccurrence (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y) s.1)
    (hterminal : ∀ {t}, A.terminal? = some t →
      t ∈ (web Gamma Z).terminalFrontier (canonicalActiveLift Z) \
        (web Gamma Z).vertexSet (canonicalPeeledReferenceLift Z Y))
    {t : V}
    (ht : (projectOccurrence Z hboundary hY hYfinite hsource hnoJunction s A
      hterminal).terminal? = some t) : A.terminal? = some (incoming t) := by
  rw [projectOccurrence_terminal] at ht
  cases hv : A.terminal? with
  | none => simp only [hv, Option.map_none] at ht; cases ht
  | some v =>
      have hvt : project v = t := by simpa only [hv, Option.map_some, Option.some.injEq] using ht
      obtain ⟨x, _hx, hvx⟩ := terminal_data_canonicalActiveLift Z (hterminal hv).1
      have hxt : x = t := by simpa only [hvx, project_incoming] using hvt
      rw [hvx, hxt]

abbrev Source (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) :=
  {s : V // s ∈ Gamma.initialSet Z.paths \ Gamma.initialSet Y}

structure Assignment (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) where
  assigned : ∀ s : Source Z Y, CurrentSafeOccurrence Z.edgeWarp Y s.1
  finite_terminal : ∀ (s : Source Z Y) {t : V}, (assigned s).terminal? = some t →
    t ∈ Gamma.terminalFrontier Z.paths \ Gamma.vertexSet Y
  finite_terminals_injective : ∀ {s₁ s₂ : Source Z Y} {t : V},
    (assigned s₁).terminal? = some t → (assigned s₂).terminal? = some t → s₁ = s₂

/-- Reuse the existing endpoint-only relation interface. This forgets the
words, but does not claim legacy alternating-path classification for them. -/
def Assignment.toCompressed {Z : FracturedWarp Gamma} (A : Assignment Z Y) :
    CompressedFracturedAssignment Z Y where
  outcome s := (A.assigned s).terminal?
  finite_exit_mem s _ ht := A.finite_terminal s ht
  finite_exits_injective _ _ _ h₁ h₂ := A.finite_terminals_injective h₁ h₂

/-- The actual outgoing-role source used for a nonsingleton assignment. -/
def liftedSource (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (s : Source Z Y) (hnot : s.1 ∉ singletonVertices Z) :
    ExposedInitial (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y) := by
  refine ⟨outgoing s.1, outgoing_mem_initialSet_canonicalActiveLift Z hZfinite
    (activeInitial_of_not_singleton Z hZfinite s.2.1 hnot), ?_⟩
  intro hmem
  obtain ⟨p, hp, hsp⟩ := project_mem_vertexSet_activeReference_of_mem_canonicalLift Z Y hmem
  exact hboundary.initial_outside s.2 ⟨p, activeReference_subset Z Y hp, hsp⟩

private theorem active_terminal_not_singleton (Z : FracturedWarp Gamma)
    {t : V} (ht : t ∈ Gamma.terminalFrontier (activePaths Z)) :
    t ∉ singletonVertices Z := by
  obtain ⟨p, hp, hpt⟩ := ht
  exact fun hs ↦ Set.disjoint_left.mp (activePath_avoids_singletonVertices Z hp)
    (p.terminal_mem_support t hpt) hs

/-- The actual simultaneous construction also retains any property proved
for its singleton words and its literal canonical projections. -/
theorem exists_assignment_with_property
    (Z : FracturedWarp Gamma)
    (hsub : Blueprint.HasHereditarySubdivisionIncidence Gamma.graph)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction : NoJunctionOnReference Z (activeReference Z Y))
    (Good : ∀ s : Source Z Y, CurrentSafeOccurrence Z.edgeWarp Y s.1 → Prop)
    (hgoodSingleton : ∀ (s : Source Z Y), s.1 ∈ singletonVertices Z →
      Good s (.finite s.1 (emptyAt s.1) (emptyAt_isIntervalSafe s.1) rfl rfl))
    (hgoodProjection : ∀ (s : Source Z Y) (hnot : s.1 ∉ singletonVertices Z)
        (A : CurrentSafeOccurrence (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y)
          (liftedSource Z hboundary hZfinite s hnot).1)
        (hterminal : ∀ {t}, A.terminal? = some t →
          t ∈ (web Gamma Z).terminalFrontier (canonicalActiveLift Z) \
            (web Gamma Z).vertexSet (canonicalPeeledReferenceLift Z Y)),
      Good s (projectOccurrence Z hboundary hY hYfinite hsource hnoJunction
        (liftedSource Z hboundary hZfinite s hnot) A hterminal)) :
    ∃ A : Assignment Z Y, ∀ s, Good s (A.assigned s) := by
  classical
  obtain ⟨A⟩ := exists_canonicalFixedSafeAssignment Z hsub hboundary hY hZfinite
    hYfinite hsource hnoJunction
  let liftSource (s : Source Z Y) (hnot : s.1 ∉ singletonVertices Z) :=
    liftedSource Z hboundary hZfinite s hnot
  let projected (s : Source Z Y) (hnot : s.1 ∉ singletonVertices Z) :
      CurrentSafeOccurrence Z.edgeWarp Y s.1 :=
    projectOccurrence Z hboundary hY hYfinite hsource hnoJunction
      (liftSource s hnot) (A.assigned (liftSource s hnot)) (A.finite_terminal _)
  have hprojected {s : Source Z Y} (hnot : s.1 ∉ singletonVertices Z) {t : V}
      (ht : (projected s hnot).terminal? = some t) :
      t ∈ Gamma.terminalFrontier (activePaths Z) \ Gamma.vertexSet Y :=
    projectOccurrence_terminal_mem Z hboundary hY hYfinite hsource hnoJunction _ _ _ ht
  have hlifted {s : Source Z Y} (hnot : s.1 ∉ singletonVertices Z) {t : V}
      (ht : (projected s hnot).terminal? = some t) :
      (A.assigned (liftSource s hnot)).terminal? = some (incoming t) :=
    terminal_eq_incoming_of_projectOccurrence Z hboundary hY hYfinite
      hsource hnoJunction _ _ _ ht
  let assigned (s : Source Z Y) : CurrentSafeOccurrence Z.edgeWarp Y s.1 :=
    if hs : s.1 ∈ singletonVertices Z then
      .finite s.1 (emptyAt s.1) (emptyAt_isIntervalSafe s.1) rfl rfl
    else projected s hs
  refine ⟨{ assigned := assigned, finite_terminal := ?_, finite_terminals_injective := ?_ }, ?_⟩
  · intro s t ht
    by_cases hs : s.1 ∈ singletonVertices Z
    · have hst : s.1 = t := by
        simpa [assigned, hs, CurrentSafeOccurrence.terminal?] using ht
      rw [← hst]
      exact ⟨⟨Gamma.trivialPath s.1, hs, Gamma.terminal?_trivialPath s.1⟩,
        hboundary.initial_outside s.2⟩
    · have hmem := hprojected hs (by simpa only [assigned, dif_neg hs] using ht)
      obtain ⟨p, hp, hpt⟩ := hmem.1
      exact ⟨⟨p, hp.1, hpt⟩, hmem.2⟩
  · intro s₁ s₂ t ht₁ ht₂
    by_cases hs₁ : s₁.1 ∈ singletonVertices Z
    · have hst₁ : s₁.1 = t := by
        simpa [assigned, hs₁, CurrentSafeOccurrence.terminal?] using ht₁
      by_cases hs₂ : s₂.1 ∈ singletonVertices Z
      · have hst₂ : s₂.1 = t := by
          simpa [assigned, hs₂, CurrentSafeOccurrence.terminal?] using ht₂
        exact Subtype.ext (hst₁.trans hst₂.symm)
      · have hmem := hprojected hs₂ (by simpa only [assigned, dif_neg hs₂] using ht₂)
        exact (active_terminal_not_singleton Z hmem.1 (hst₁ ▸ hs₁)).elim
    · by_cases hs₂ : s₂.1 ∈ singletonVertices Z
      · have hst₂ : s₂.1 = t := by
          simpa [assigned, hs₂, CurrentSafeOccurrence.terminal?] using ht₂
        have hmem := hprojected hs₁ (by simpa only [assigned, dif_neg hs₁] using ht₁)
        exact (active_terminal_not_singleton Z hmem.1 (hst₂ ▸ hs₂)).elim
      · have h₁ := hlifted hs₁ (by simpa only [assigned, dif_neg hs₁] using ht₁)
        have h₂ := hlifted hs₂ (by simpa only [assigned, dif_neg hs₂] using ht₂)
        have heq := A.finite_terminals_injective h₁ h₂
        exact Subtype.ext (congrArg (fun a : ExposedInitial (canonicalActiveLift Z)
          (canonicalPeeledReferenceLift Z Y) ↦ project a.1) heq)
  · intro s
    by_cases hs : s.1 ∈ singletonVertices Z
    · simpa only [assigned, dif_pos hs] using hgoodSingleton s hs
    · simpa only [assigned, dif_neg hs] using
        hgoodProjection s hs (A.assigned (liftSource s hs)) (A.finite_terminal _)

/-- The fixed-original assignment for the actual fractured family, including
the singleton sources excluded from the canonical active lift. -/
theorem exists_assignment
    (Z : FracturedWarp Gamma)
    (hsub : Blueprint.HasHereditarySubdivisionIncidence Gamma.graph)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction : NoJunctionOnReference Z (activeReference Z Y)) :
    Nonempty (Assignment Z Y) := by
  obtain ⟨A, _⟩ := exists_assignment_with_property Z hsub hboundary hY hZfinite
    hYfinite hsource hnoJunction (fun _ _ ↦ True)
    (fun _ _ ↦ True.intro) (fun _ _ _ _ ↦ True.intro)
  exact ⟨A⟩

/-- In the genuine outside cut the existing closing-set geometry supplies
the no-junction condition required by the canonical construction. -/
theorem exists_outside_assignment
    {W : Set Gamma.DPath} {X : Set V} (F : OutsideFracturedWarp W X)
    (hsub : Blueprint.HasHereditarySubdivisionIncidence Gamma.graph)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths)
    (hdisjoint : Disjoint X (Gamma.vertexSet Y)) :
    Nonempty (Assignment F.holes Y) :=
  exists_assignment F.holes hsub hboundary hY F.finiteCharacter hYfinite hsource
    (F.noJunctionOnPeeledReference hboundary hY hdisjoint)

#print axioms projectOccurrence
#print axioms projectOccurrence_terminal_mem
#print axioms terminal_eq_incoming_of_projectOccurrence
#print axioms Assignment.toCompressed
#print axioms exists_assignment_with_property
#print axioms exists_assignment
#print axioms exists_outside_assignment

end Erdos599.Blueprint.LinkageBlueprint.FracturedFixedSafeAssignment
