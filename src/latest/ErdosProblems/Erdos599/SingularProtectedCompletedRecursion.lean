/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProtectedCompletedState

/-!
# Countable recursion of protected completed states

This module performs only the simultaneous singular-matrix bookkeeping.  A
state-level selector may complete more sources than the current competitor
request, provided that it keeps the completed paths already installed and
does not exceed the column scale.  The canonical source layer and the
inflationary competitor step then force the selected source set to have
exactly the scale cardinality.

No residual-unhindered premise is added here: it is already internal to
`ProtectedCompletedState` in the form of its boundary quotient.  Likewise,
this file makes no universal lower-induction assumption.  The geometric
protected successor is expected to instantiate `BoundedProtectedSelection`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularProtectedCompletedRecursion

open SingularExtension SingularMatrix SingularEventualRows
  SingularCompletedDisplayEventualRows SingularProtectedCompletedState

universe u

variable {V : Type u}

/-- One admissible selected successor.  Its completed source set may strictly
contain the request, but is bounded by the same scale. -/
structure BoundedProtectedSuccessor
    (G : DWeb V) (rho : Cardinal.{u})
    (S : ProtectedCompletedState G) (requested : Set V) where
  state : ProtectedCompletedState G
  requested_subset : requested ⊆ state.sources
  sources_le : #state.sources ≤ rho
  completed_subset : S.completed ⊆ state.completed

namespace BoundedProtectedSuccessor

variable {G : DWeb V} {rho : Cardinal.{u}}
variable {S : ProtectedCompletedState G} {requested : Set V}

/-- A bounded successor containing an exact-scale request has exact scale. -/
theorem sources_card
    (T : BoundedProtectedSuccessor G rho S requested)
    (hrequested : #requested = rho) : #T.state.sources = rho := by
  apply le_antisymm T.sources_le
  calc
    rho = #requested := hrequested.symm
    _ ≤ #T.state.sources := Cardinal.mk_subtype_mono T.requested_subset

end BoundedProtectedSuccessor

/-- The provisional state-level input to the countable recursion.  The
geometric successor theorem supplies this selection from the protected
boundary quotient; the recursion below merely chooses and organizes it. -/
def BoundedProtectedSelection (G : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ (rho : Cardinal.{u}) (S : ProtectedCompletedState G)
    (requested : Set V),
    rho < kappa →
    aleph0 ≤ rho →
    S.sources ⊆ requested →
    requested ⊆ G.source →
    #requested ≤ rho →
    Nonempty (BoundedProtectedSuccessor G rho S requested)

/-- The successor chosen from the state-level selection theorem. -/
noncomputable def selectedSuccessor
    {G : DWeb V} {kappa : Cardinal.{u}}
    (hselect : BoundedProtectedSelection G kappa)
    (rho : Cardinal.{u}) (hbelow : rho < kappa)
    (S : ProtectedCompletedState G)
    (requested : Set V) (hinfinite : aleph0 ≤ rho)
    (hcurrent : S.sources ⊆ requested)
    (hsource : requested ⊆ G.source) (hcard : #requested ≤ rho) :
    BoundedProtectedSuccessor G rho S requested :=
  Classical.choice
    (hselect rho S requested hbelow hinfinite hcurrent hsource hcard)

/-- One simultaneous protected state, with exact scale in every column. -/
structure SimultaneousState
    (G : DWeb V) (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) where
  column : ∀ _i : Index kappa, ProtectedCompletedState G
  sources_card : ∀ i,
    #(column i).sources = scale kappa huncountable hsingular i

namespace SimultaneousState

variable {G : DWeb V} {kappa : Cardinal.{u}}
variable {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}

/-- The trivially padded target row displayed by a simultaneous protected
state. -/
def row (S : SimultaneousState G kappa huncountable hsingular)
    (hNorm : G.IsNormalized) : TargetRowStage G (Index kappa) where
  sources i := (S.column i).sources
  paths i := (S.column i).toCompletedDisplayState.displayed
  isWarp i := (S.column i).toCompletedDisplayState.displayed_isWarp hNorm
  finiteCharacter i :=
    (S.column i).toCompletedDisplayState.displayed_finiteCharacter
  initialSet i :=
    (S.column i).toCompletedDisplayState.displayed_initialSet
  links i := (S.column i).toCompletedDisplayState.displayed_links

@[simp] theorem row_sources
    (S : SimultaneousState G kappa huncountable hsingular)
    (hNorm : G.IsNormalized) (i : Index kappa) :
    (S.row hNorm).sources i = (S.column i).sources := rfl

@[simp] theorem row_paths
    (S : SimultaneousState G kappa huncountable hsingular)
    (hNorm : G.IsNormalized) (i : Index kappa) :
    (S.row hNorm).paths i =
      (S.column i).toCompletedDisplayState.displayed := rfl

end SimultaneousState

/-! ## One simultaneous competitor step -/

/-- The competitor step of an exact-scale displayed row stays in the ambient
source. -/
theorem nextTargetSources_subset_source_of_completed
    {G : DWeb V} {fixed : Set G.DPath}
    (hfixed : G.initialSet fixed ⊆ G.source)
    {kappa : Cardinal.{u}} {huncountable : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (S : SimultaneousState G kappa huncountable hsingular)
    (hNorm : G.IsNormalized) (i : Index kappa) :
    nextTargetSources G fixed (S.row hNorm) i ⊆ G.source := by
  rintro x (hx | hx)
  · exact (S.column i).sources_subset hx
  · obtain ⟨a, _ha, p, hpAll, _hpa, q, hqAll, hqx, _hpq⟩ := hx
    rcases hqAll with hqFixed | hqRows
    · apply hfixed
      exact ⟨q, hqFixed, hqx⟩
    · obtain ⟨j, hqj⟩ := Set.mem_iUnion.1 hqRows
      rw [← (S.row hNorm).initialSet j]
      exact ⟨q, hqj, hqx⟩

/-- One displayed competitor step has exactly the scale cardinality. -/
theorem mk_nextTargetSources_eq_of_completed
    {G : DWeb V} {fixed : Set G.DPath} (hfixed : G.IsWarp fixed)
    {kappa : Cardinal.{u}} {huncountable : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (S : SimultaneousState G kappa huncountable hsingular)
    (hNorm : G.IsNormalized) (i : Index kappa) :
    #(nextTargetSources G fixed (S.row hNorm) i) =
      scale kappa huncountable hsingular i := by
  let rho := scale kappa huncountable hsingular i
  have hrho : aleph0 ≤ rho :=
    scale_infinite kappa huncountable hsingular i
  have hI : #(Index kappa) ≤ rho :=
    scale_index_le kappa huncountable hsingular i
  apply le_antisymm
  · unfold nextTargetSources DWeb.competitorStep
    refine (Cardinal.mk_union_le _ _).trans ?_
    exact Cardinal.add_le_of_le hrho (S.sources_card i).le
      (G.mk_competitorClosure_fixed_iUnion_le fixed (S.row hNorm).paths
        ((S.row hNorm).sources i) hfixed (S.row hNorm).isWarp
        hrho hI (S.sources_card i).le)
  · rw [← S.sources_card i]
    apply Cardinal.mk_le_mk_of_subset
    exact fun _ hx ↦ Or.inl hx

section Initial

variable {G : DWeb V} {A₀ : Set V} {kappa : Cardinal.{u}}
variable {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
variable {hcard : #A₀ = kappa}

/-- The selected protected state containing one canonical source layer. -/
noncomputable def initialSuccessor
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hA₀ : A₀ ⊆ G.source) (i : Index kappa) :
    BoundedProtectedSuccessor G
      (scale kappa huncountable hsingular i)
      (emptyState G hNorm hG)
      (sourceLayer A₀ kappa hcard huncountable hsingular i) :=
  selectedSuccessor hselect _
    (scale_below kappa huncountable hsingular i) _ _
    (scale_infinite kappa huncountable hsingular i)
    (by simp)
    ((sourceLayer_subset A₀ kappa hcard huncountable hsingular i).trans hA₀)
    (sourceLayer_card A₀ kappa hcard huncountable hsingular i).le

/-- Simultaneously choose the exact-scale initial protected state in every
column. -/
noncomputable def initialState
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hA₀ : A₀ ⊆ G.source) :
    SimultaneousState G kappa huncountable hsingular where
  column i := (initialSuccessor hselect hNorm hG hA₀ i).state
  sources_card i :=
    (initialSuccessor hselect hNorm hG hA₀ i).sources_card
      (sourceLayer_card A₀ kappa hcard huncountable hsingular i)

theorem sourceLayer_subset_initialState
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hA₀ : A₀ ⊆ G.source) (i : Index kappa) :
    sourceLayer A₀ kappa hcard huncountable hsingular i ⊆
      ((initialState (kappa := kappa) (huncountable := huncountable)
        (hsingular := hsingular) (hcard := hcard)
        hselect hNorm hG hA₀).column i).sources :=
  (initialSuccessor hselect hNorm hG hA₀ i).requested_subset

end Initial

section Step

variable {G : DWeb V} {fixed : Set G.DPath} {kappa : Cardinal.{u}}
variable {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}

/-- The selected successor in one column after the whole displayed row has
been used to compute competitors. -/
noncomputable def stepSuccessor
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source)
    (S : SimultaneousState G kappa huncountable hsingular)
    (i : Index kappa) :
    BoundedProtectedSuccessor G
      (scale kappa huncountable hsingular i) (S.column i)
      (nextTargetSources G fixed (S.row hNorm) i) :=
  selectedSuccessor hselect _
    (scale_below kappa huncountable hsingular i) _ _
    (scale_infinite kappa huncountable hsingular i)
    (fun _ hx ↦ Or.inl hx)
    (nextTargetSources_subset_source_of_completed
      hfixedSource S hNorm i)
    (mk_nextTargetSources_eq_of_completed hfixedWarp S hNorm i).le

/-- Advance all columns simultaneously. -/
noncomputable def step
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source)
    (S : SimultaneousState G kappa huncountable hsingular) :
    SimultaneousState G kappa huncountable hsingular where
  column i :=
    (stepSuccessor hselect hNorm hfixedWarp hfixedSource S i).state
  sources_card i :=
    (stepSuccessor hselect hNorm hfixedWarp hfixedSource S i).sources_card
      (mk_nextTargetSources_eq_of_completed hfixedWarp S hNorm i)

theorem requested_subset_step_sources
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source)
    (S : SimultaneousState G kappa huncountable hsingular)
    (i : Index kappa) :
    nextTargetSources G fixed (S.row hNorm) i ⊆
      ((step hselect hNorm hfixedWarp hfixedSource S).column i).sources :=
  (stepSuccessor hselect hNorm hfixedWarp hfixedSource S i).requested_subset

theorem sources_subset_step_sources
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source)
    (S : SimultaneousState G kappa huncountable hsingular)
    (i : Index kappa) :
    (S.column i).sources ⊆
      ((step hselect hNorm hfixedWarp hfixedSource S).column i).sources :=
  (fun _ hx ↦ requested_subset_step_sources hselect hNorm hfixedWarp
    hfixedSource S i (Or.inl hx))

theorem completed_subset_step_completed
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source)
    (S : SimultaneousState G kappa huncountable hsingular)
    (i : Index kappa) :
    (S.column i).completed ⊆
      ((step hselect hNorm hfixedWarp hfixedSource S).column i).completed :=
  (stepSuccessor hselect hNorm hfixedWarp hfixedSource S i).completed_subset

end Step

section Recursion

variable {G : DWeb V} {fixed : Set G.DPath}
variable {A₀ : Set V} {kappa : Cardinal.{u}}
variable {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
variable {hcard : #A₀ = kappa}

/-- The simultaneous omega recursion of protected completed states. -/
noncomputable def stateAt
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hA₀ : A₀ ⊆ G.source)
    (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source) :
    ℕ → SimultaneousState G kappa huncountable hsingular
  | 0 => initialState (kappa := kappa) (huncountable := huncountable)
      (hsingular := hsingular) (hcard := hcard) hselect hNorm hG hA₀
  | n + 1 => step (kappa := kappa) (huncountable := huncountable)
      (hsingular := hsingular) hselect hNorm hfixedWarp hfixedSource
      (stateAt hselect hNorm hG hA₀ hfixedWarp hfixedSource n)

@[simp] theorem stateAt_zero
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hA₀ : A₀ ⊆ G.source)
    (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source) :
    stateAt (kappa := kappa) (huncountable := huncountable)
        (hsingular := hsingular) (hcard := hcard)
        hselect hNorm hG hA₀ hfixedWarp hfixedSource 0 =
      initialState (kappa := kappa) (huncountable := huncountable)
        (hsingular := hsingular) (hcard := hcard)
        hselect hNorm hG hA₀ := rfl

@[simp] theorem stateAt_succ
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hA₀ : A₀ ⊆ G.source)
    (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source) (n : ℕ) :
    stateAt (kappa := kappa) (huncountable := huncountable)
        (hsingular := hsingular) (hcard := hcard)
        hselect hNorm hG hA₀ hfixedWarp hfixedSource (n + 1) =
      step (kappa := kappa) (huncountable := huncountable)
        (hsingular := hsingular) hselect hNorm hfixedWarp hfixedSource
        (stateAt (kappa := kappa) (huncountable := huncountable)
          (hsingular := hsingular) (hcard := hcard)
          hselect hNorm hG hA₀ hfixedWarp hfixedSource n) := rfl

theorem stateAt_sources_subset_succ
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hA₀ : A₀ ⊆ G.source)
    (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source)
    (n : ℕ) (i : Index kappa) :
    ((stateAt (kappa := kappa) (huncountable := huncountable)
      (hsingular := hsingular) (hcard := hcard)
      hselect hNorm hG hA₀ hfixedWarp hfixedSource n).column i).sources ⊆
      ((stateAt (kappa := kappa) (huncountable := huncountable)
        (hsingular := hsingular) (hcard := hcard)
        hselect hNorm hG hA₀ hfixedWarp hfixedSource (n + 1)).column i).sources := by
  rw [stateAt_succ (kappa := kappa) (huncountable := huncountable)
    (hsingular := hsingular) (hcard := hcard)]
  exact sources_subset_step_sources hselect hNorm hfixedWarp hfixedSource _ i

theorem stateAt_completed_subset_succ
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hA₀ : A₀ ⊆ G.source)
    (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source)
    (n : ℕ) (i : Index kappa) :
    ((stateAt (kappa := kappa) (huncountable := huncountable)
      (hsingular := hsingular) (hcard := hcard)
      hselect hNorm hG hA₀ hfixedWarp hfixedSource n).column i).completed ⊆
      ((stateAt (kappa := kappa) (huncountable := huncountable)
        (hsingular := hsingular) (hcard := hcard)
        hselect hNorm hG hA₀ hfixedWarp hfixedSource (n + 1)).column i).completed := by
  rw [stateAt_succ (kappa := kappa) (huncountable := huncountable)
    (hsingular := hsingular) (hcard := hcard)]
  exact completed_subset_step_completed hselect hNorm hfixedWarp hfixedSource _ i

/-- The selected protected recursion, forgetting its private boundaries and
pending rows, is exactly a completed display schedule. -/
noncomputable def toCompletedDisplaySchedule
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hA₀ : A₀ ⊆ G.source)
    (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source) :
    CompletedDisplaySchedule G fixed A₀ kappa
      huncountable hsingular hcard where
  state i n :=
    (stateAt (kappa := kappa) (huncountable := huncountable)
      (hsingular := hsingular) (hcard := hcard)
      hselect hNorm hG hA₀ hfixedWarp hfixedSource n).column i
      |>.toCompletedDisplayState
  seed i := by
    change sourceLayer A₀ kappa hcard huncountable hsingular i ⊆
      ((initialState (kappa := kappa) (huncountable := huncountable)
        (hsingular := hsingular) (hcard := hcard)
        hselect hNorm hG hA₀).column i).sources
    exact sourceLayer_subset_initialState (kappa := kappa)
      (huncountable := huncountable) (hsingular := hsingular)
      (hcard := hcard) hselect hNorm hG hA₀ i
  sources_card i n :=
    (stateAt (kappa := kappa) (huncountable := huncountable)
      (hsingular := hsingular) (hcard := hcard)
      hselect hNorm hG hA₀ hfixedWarp hfixedSource n).sources_card i
  sources_mono i := by
    apply monotone_nat_of_le_succ
    intro n
    exact stateAt_sources_subset_succ (kappa := kappa)
      (huncountable := huncountable) (hsingular := hsingular)
      (hcard := hcard) hselect hNorm hG hA₀ hfixedWarp hfixedSource n i
  completed_mono i := by
    apply monotone_nat_of_le_succ
    intro n
    exact stateAt_completed_subset_succ (kappa := kappa)
      (huncountable := huncountable) (hsingular := hsingular)
      (hcard := hcard) hselect hNorm hG hA₀ hfixedWarp hfixedSource n i
  close i n := by
    intro x hx
    rw [stateAt_succ (kappa := kappa) (huncountable := huncountable)
      (hsingular := hsingular) (hcard := hcard)]
    apply requested_subset_step_sources hselect hNorm hfixedWarp
      hfixedSource _ i
    exact Or.inr hx

/-- The final adapter to the eventual-row interface used by the singular
least-column theorem. -/
noncomputable def toEventualRows
    (hselect : BoundedProtectedSelection G kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hA₀ : A₀ ⊆ G.source)
    (hfixedWarp : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source) :
    EventualRows G fixed A₀ kappa huncountable hsingular hcard :=
  (toCompletedDisplaySchedule (kappa := kappa)
    (huncountable := huncountable) (hsingular := hsingular)
    (hcard := hcard) hselect hNorm hG hA₀
    hfixedWarp hfixedSource).toEventualRows hNorm

/-- A bounded protected selector in a normalized unhindered web supplies the
actual singular extension clause.  The fixed complementary linkage is used
only through its warp and source-initial certificates. -/
theorem extensionClauseAt_of_boundedProtectedSelection
    (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (G : DWeb V) (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hselect : BoundedProtectedSelection G kappa) :
    ExtensionClauseAt G kappa := by
  apply singularExtensionClauseAt_of_targetRows
    kappa huncountable hsingular G
  intro A₀ hA₀ hcard fixed hfixed
  have hfixedSource : G.initialSet fixed ⊆ G.source := by
    rw [hfixed.initialSet_eq]
    exact Set.sdiff_subset
  exact (toEventualRows (huncountable := huncountable)
    (hsingular := hsingular) (hcard := hcard)
    hselect hNorm hG hA₀ hfixed.isWarp hfixedSource).toTargetRows

/-- Induction-facing normalized form.  The selector is needed only for the
normalized web and only below the current singular cardinal. -/
theorem extensionClauseAt_of_normalizedBoundedProtectedSelection
    (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (G : DWeb V) (hG : G.IsUnhindered)
    (hselect : BoundedProtectedSelection G.normalized kappa) :
    ExtensionClauseAt G kappa := by
  apply singularExtensionClauseAt_of_normalizedEventualRows
    kappa huncountable hsingular G
  intro A₀ hA₀ hcard fixed hfixed
  have hfixedSource : G.normalized.initialSet fixed ⊆
      G.normalized.source := by
    rw [hfixed.initialSet_eq]
    exact Set.sdiff_subset
  exact toEventualRows (huncountable := huncountable)
    (hsingular := hsingular) (hcard := hcard) hselect
    G.normalized_isNormalized hG.normalized hA₀ hfixed.isWarp hfixedSource

#print axioms BoundedProtectedSuccessor.sources_card
#print axioms toCompletedDisplaySchedule
#print axioms toEventualRows
#print axioms extensionClauseAt_of_boundedProtectedSelection
#print axioms extensionClauseAt_of_normalizedBoundedProtectedSelection

end Recursion
end SingularProtectedCompletedRecursion
end CardinalInduction
end Erdos599
