/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularEventualRows

/-!
# Completed-path displays for the singular matrix

At a singular successor stage only the paths which have already reached the
ambient target have to persist literally.  All other sources may be displayed
by their trivial paths.  This module isolates that elementary bookkeeping
from the geometric state used to construct the next completed batch.

In particular, `CompletedDisplayState` contains no residual-unhindered
hypothesis.  If completed paths and their source sets are monotone, then the
corresponding full-source displays are forward monotone.  A countable family
of such states therefore gives the `EventualRows` consumed by the singular
least-column construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularCompletedDisplayEventualRows

open SingularExtension SingularMatrix SingularEventualRows

universe u

variable {V : Type u}

/-- A target linkage recording exactly the sources completed so far.  The
geometric data used to produce later completed paths deliberately does not
belong to this display-only record. -/
structure CompletedDisplayState (G : DWeb V) where
  sources : Set V
  sources_subset : sources ⊆ G.source
  completed : Set G.DPath
  linkage : IsLinkageBetween G sources G.target completed

namespace CompletedDisplayState

variable {G : DWeb V}

/-- Fill every source which is not yet completed with its trivial path. -/
def displayed (S : CompletedDisplayState G) : Set G.DPath :=
  S.completed ∪ G.trivialPath '' (G.source \ S.sources)

/-- The completed linkage is disjoint from the trivial padding in a
normalized web. -/
theorem displayed_isWarp (hNorm : G.IsNormalized)
    (S : CompletedDisplayState G) : G.IsWarp S.displayed := by
  apply Set.PairwiseDisjoint.union S.linkage.isWarp
    (G.isWarp_trivialPaths (G.source \ S.sources))
  intro p hp q hq _hpq
  obtain ⟨x, hx, rfl⟩ := hq
  rw [G.support_trivialPath]
  apply Set.disjoint_singleton_right.2
  intro hxp
  have hxeq : x = p.initial :=
    hNorm.eq_initial_of_mem_path p hxp hx.1
  have hpinitial : p.initial ∈ S.sources := by
    rw [← S.linkage.initialSet_eq]
    exact ⟨p, hp, rfl⟩
  exact hx.2 (hxeq.symm ▸ hpinitial)

theorem displayed_finiteCharacter (S : CompletedDisplayState G) :
    G.HasFiniteCharacter S.displayed := by
  apply SingularContinuation.finiteCharacter_union G
    S.linkage.finiteCharacter
  rintro p ⟨x, _hx, rfl⟩
  exact ⟨DirectedPath.FinitePath.trivial G.graph x, rfl⟩

theorem displayed_initialSet (S : CompletedDisplayState G) :
    G.initialSet S.displayed = G.source := by
  unfold displayed
  rw [G.initialSet_union, G.initialSet_trivialPaths,
    S.linkage.initialSet_eq, Set.union_comm,
    Set.sdiff_union_of_subset S.sources_subset]

theorem displayed_links (S : CompletedDisplayState G) :
    LinksToTarget G S.displayed S.sources := by
  have hlinks := linksToTarget_of_linkageToTarget S.linkage
  intro a ha
  obtain ⟨p, hp, hpa⟩ := hlinks a ha
  exact ⟨p, Or.inl hp, hpa⟩

/-- Every path with initial vertex `a` extends the trivial path at `a`. -/
private theorem extends_trivialPath_of_initial_eq
    (G : DWeb V) {a : V} {q : G.DPath} (hq : q.initial = a) :
    G.Extends (G.trivialPath a) q := by
  rcases q with f | r
  · change [a] <+: f.walk.support
    rw [List.singleton_prefix_iff_head?_eq_some,
      List.head?_eq_some_head f.walk.support_ne_nil, f.walk.head_support]
    exact congrArg some hq
  · change (DirectedPath.FinitePath.trivial G.graph a).IsInitialSegmentOf r
    intro n hn
    simp only [DirectedPath.FinitePath.trivial_walk] at hn ⊢
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn)
    subst n
    change r.initial = a at hq
    exact hq.symm

/-- Literal persistence of completed paths, together with monotonicity of
their source sets, is exactly what is needed for forward extension of the
trivially padded displays. -/
theorem forward_displayed_of_mono
    (S T : CompletedDisplayState G)
    (hsources : S.sources ⊆ T.sources)
    (hcompleted : S.completed ⊆ T.completed) :
    G.ForwardExtension S.displayed T.displayed := by
  constructor
  · intro p hp
    rcases hp with hpCompleted | hpTrivial
    · exact ⟨p, Or.inl (hcompleted hpCompleted), G.extends_refl p⟩
    · obtain ⟨x, hx, rfl⟩ := hpTrivial
      by_cases hxT : x ∈ T.sources
      · have hxInitial : x ∈ G.initialSet T.completed := by
          rw [T.linkage.initialSet_eq]
          exact hxT
        obtain ⟨q, hq, hqx⟩ := hxInitial
        exact ⟨q, Or.inl hq, extends_trivialPath_of_initial_eq G hqx⟩
      · exact ⟨G.trivialPath x, Or.inr ⟨x, ⟨hx.1, hxT⟩, rfl⟩,
          G.extends_refl _⟩
  · intro q hq
    rcases hq with hqCompleted | hqTrivial
    · by_cases hqS : q.initial ∈ S.sources
      · have hqInitial : q.initial ∈ G.initialSet S.completed := by
          rw [S.linkage.initialSet_eq]
          exact hqS
        obtain ⟨p, hp, hpqInitial⟩ := hqInitial
        have hpq : p = q :=
          DWeb.IsWarp.eq_of_initial_eq G T.linkage.isWarp
            (hcompleted hp) hqCompleted hpqInitial
        subst q
        exact ⟨p, Or.inl hp, G.extends_refl p⟩
      · have hqT : q.initial ∈ T.sources := by
          rw [← T.linkage.initialSet_eq]
          exact ⟨q, hqCompleted, rfl⟩
        exact ⟨G.trivialPath q.initial,
          Or.inr ⟨q.initial, ⟨T.sources_subset hqT, hqS⟩, rfl⟩,
          extends_trivialPath_of_initial_eq G rfl⟩
    · obtain ⟨x, hx, rfl⟩ := hqTrivial
      exact ⟨G.trivialPath x,
        Or.inr ⟨x, ⟨hx.1, fun hxS ↦ hx.2 (hsources hxS)⟩, rfl⟩,
        G.extends_refl _⟩

end CompletedDisplayState

/-- A simultaneous countable schedule of completed linkages.  The source
sets absorb their own competitor closures, while literal completed paths
persist from one stage to the next. -/
structure CompletedDisplaySchedule
    (G : DWeb V) (fixed : Set G.DPath)
    (A₀ : Set V) (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hcard : #A₀ = kappa) where
  state : Index kappa → ℕ → CompletedDisplayState G
  seed : ∀ i,
    sourceLayer A₀ kappa hcard huncountable hsingular i ⊆
      (state i 0).sources
  sources_card : ∀ i n,
    #((state i n).sources) = scale kappa huncountable hsingular i
  sources_mono : ∀ i, Monotone (fun n ↦ (state i n).sources)
  completed_mono : ∀ i, Monotone (fun n ↦ (state i n).completed)
  close : ∀ i n,
    G.competitorClosure
        (G.matrixStageFamily fixed (fun j m ↦ (state j m).displayed) n)
        (state i n).sources ⊆
      (state i (n + 1)).sources

namespace CompletedDisplaySchedule

variable {G : DWeb V} {fixed : Set G.DPath}
variable {A₀ : Set V} {kappa : Cardinal.{u}}
variable {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
variable {hcard : #A₀ = kappa}

/-- Forget the private completed-linkage schedule.  Adjacent stages already
give the eventual forward comparison required by `EventualRows`. -/
noncomputable def toEventualRows
    (R : CompletedDisplaySchedule G fixed A₀ kappa
      huncountable hsingular hcard)
    (hNorm : G.IsNormalized) :
    EventualRows G fixed A₀ kappa huncountable hsingular hcard where
  sources i n := (R.state i n).sources
  paths i n := (R.state i n).displayed
  seed := R.seed
  sources_subset i n := (R.state i n).sources_subset
  sources_card := R.sources_card
  sources_mono := R.sources_mono
  isWarp i n := (R.state i n).displayed_isWarp hNorm
  finiteCharacter i n := (R.state i n).displayed_finiteCharacter
  initialSet i n := (R.state i n).displayed_initialSet
  links i n := (R.state i n).displayed_links
  close := R.close
  eventualForward n := by
    refine ⟨n + 1, Nat.lt_succ_self n, ?_⟩
    intro i
    exact CompletedDisplayState.forward_displayed_of_mono
      (R.state i n) (R.state i (n + 1))
      (R.sources_mono i (Nat.le_succ n))
      (R.completed_mono i (Nat.le_succ n))

#print axioms CompletedDisplayState.forward_displayed_of_mono
#print axioms CompletedDisplaySchedule.toEventualRows

end CompletedDisplaySchedule
end SingularCompletedDisplayEventualRows
end CardinalInduction
end Erdos599
