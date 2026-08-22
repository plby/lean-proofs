/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZPathEvents

/-!
# Additive good-history transition assembly

The raw HLOZ transition event contains arbitrary future continuations.  A
decaying finite-product screen therefore cannot cover it merely by screening
the stopped prefix.  The source proof instead removes, at each successive
rank, the histories on which the balance or candidate-count screen fails and
pays for those histories additively.

This module implements that correction at the assembly level.  The three
good events remove cumulative bad-history sets, so they remain nested.  The
union of all branchwise bad histories is added to the already established
HLOZ exceptional event.  A later module can prove the three good-event
transition factors by a stopped-history/strong-Markov argument without ever
claiming that a prefix-only product law controls an unrestricted future.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZFilteredTransitionAssembly

open HLOZPathEvents

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := (GapScale × GapScale) × GapScale
abbrev BranchEvent := DominoTiling → ℕ → GapTriple → Set WalkPath

/-- First transition after removing the rank-one bad-history set. -/
def goodFirstTransitionEvent (bad₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) : Set WalkPath :=
  firstTransitionEvent t m a \ bad₁ t m a

/-- Second transition after removing every bad history exposed through rank
two. -/
def goodSecondTransitionEvent (bad₁ bad₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) : Set WalkPath :=
  secondTransitionEvent t m a \ (bad₁ t m a ∪ bad₂ t m a)

/-- Screened third transition after removing every bad history exposed
through rank three. -/
def goodThirdTransitionEvent (bad₁ bad₂ bad₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) : Set WalkPath :=
  screenedThirdTransitionEvent t m a \
    ((bad₁ t m a ∪ bad₂ t m a) ∪ bad₃ t m a)

/-- All three bad-history mechanisms for one mesh branch. -/
def branchBadHistoryEvent (bad₁ bad₂ bad₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) : Set WalkPath :=
  (bad₁ t m a ∪ bad₂ t m a) ∪ bad₃ t m a

/-- Finite union of the bad-history mechanisms over the HLOZ mesh. -/
def transitionBadHistoryEvent (bad₁ bad₂ bad₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  UpperAssembly.meshBranchUnion properGapMesh
    (branchBadHistoryEvent bad₁ bad₂ bad₃ t m)

/-- The original exceptional event enlarged by the additive transition
screen failures. -/
def filteredExceptionalEvent (bad₁ bad₂ bad₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  hlozExceptionalEvent t m ∪ transitionBadHistoryEvent bad₁ bad₂ bad₃ t m

/-- Generic finite-mesh split, kept polymorphic so its proof never unfolds
the comparatively large concrete `GapScale` decision procedure. -/
theorem meshBranchUnion_subset_bad_union_diff
    {Ω Scale : Type*}
    (mesh : Finset Scale)
    (branch bad : ((Scale × Scale) × Scale) → Set Ω) :
    UpperAssembly.meshBranchUnion mesh branch ⊆
    UpperAssembly.meshBranchUnion mesh bad ∪
        UpperAssembly.meshBranchUnion mesh (fun a ↦ branch a \ bad a) := by
  intro s hs
  rw [UpperAssembly.mem_meshBranchUnion] at hs
  change s ∈ UpperAssembly.meshBranchUnion mesh bad ∨
    s ∈ UpperAssembly.meshBranchUnion mesh (fun a ↦ branch a \ bad a)
  rw [UpperAssembly.mem_meshBranchUnion,
    UpperAssembly.mem_meshBranchUnion]
  obtain ⟨a, ha, hbranch⟩ := hs
  by_cases hbad : s ∈ bad a
  · exact Or.inl ⟨a, ha, hbad⟩
  · exact Or.inr ⟨a, ha, hbranch, hbad⟩

/-- Generic source-correct split in which the histories removed to prove a
transition factor need not all be paid as a new exceptional event.  The
`route` hypothesis may instead send a removed terminal history to an
exceptional family that was already present. -/
theorem meshBranchUnion_subset_exception_paid_union_diff
    {Ω Scale : Type*}
    (mesh : Finset Scale) (base : Set Ω)
    (branch filter paid : ((Scale × Scale) × Scale) → Set Ω)
    (route : ∀ a ∈ UpperAssembly.meshTriples mesh,
      branch a ∩ filter a ⊆ base ∪ paid a) :
    UpperAssembly.meshBranchUnion mesh branch ⊆
      (base ∪ UpperAssembly.meshBranchUnion mesh paid) ∪
        UpperAssembly.meshBranchUnion mesh (fun a ↦ branch a \ filter a) := by
  intro s hs
  rw [UpperAssembly.mem_meshBranchUnion] at hs
  obtain ⟨a, ha, hbranch⟩ := hs
  by_cases hfilter : s ∈ filter a
  · rcases route a ha ⟨hbranch, hfilter⟩ with hbase | hpaid
    · exact Or.inl (Or.inl hbase)
    · apply Or.inl
      apply Or.inr
      rw [UpperAssembly.mem_meshBranchUnion]
      exact ⟨a, ha, hpaid⟩
  · apply Or.inr
    rw [UpperAssembly.mem_meshBranchUnion]
    exact ⟨a, ha, hbranch, hfilter⟩

theorem goodSecondTransitionEvent_subset_goodFirst
    (bad₁ bad₂ : BranchEvent) (t : DominoTiling) (m : ℕ)
    (a : GapTriple) :
    goodSecondTransitionEvent bad₁ bad₂ t m a ⊆
      goodFirstTransitionEvent bad₁ t m a := by
  rintro s ⟨hsecond, hbad⟩
  exact ⟨secondTransitionEvent_subset_first t m a hsecond,
    fun h ↦ hbad (Or.inl h)⟩

theorem goodThirdTransitionEvent_subset_goodSecond
    (bad₁ bad₂ bad₃ : BranchEvent) (t : DominoTiling) (m : ℕ)
    (a : GapTriple) :
    goodThirdTransitionEvent bad₁ bad₂ bad₃ t m a ⊆
      goodSecondTransitionEvent bad₁ bad₂ t m a := by
  rintro s ⟨hthird, hbad⟩
  exact ⟨thirdTransitionEvent_subset_second t m a hthird.1,
    fun h ↦ hbad (Or.inl h)⟩

/-- Source-correct mesh cover: a terminal branch either encountered a bad
history at one of its three ranks or belongs to the cumulatively filtered
third transition. -/
theorem hlozSeparatedLevelEvent_filtered_mesh_cover
    (bad₁ bad₂ bad₃ : BranchEvent) (t : DominoTiling) (m : ℕ) :
    hlozSeparatedLevelEvent t m ⊆
      filteredExceptionalEvent bad₁ bad₂ bad₃ t m ∪
        UpperAssembly.meshBranchUnion properGapMesh
          (goodThirdTransitionEvent bad₁ bad₂ bad₃ t m) := by
  intro s hs
  rcases hlozSeparatedLevelEvent_screened_mesh_cover t m hs with
      hexception | hbranch
  · exact Or.inl (Or.inl hexception)
  · have hsplit := meshBranchUnion_subset_bad_union_diff properGapMesh
      (screenedThirdTransitionEvent t m)
      (branchBadHistoryEvent bad₁ bad₂ bad₃ t m) hbranch
    rcases hsplit with hbad | hgood
    · exact Or.inl (Or.inr hbad)
    · exact Or.inr hgood

/-! ## Separate factor filters and paid auxiliary failures -/

/-- Only the auxiliary history failures that have not already been charged
to `hlozExceptionalEvent` are included in this mesh union. -/
def paidTransitionBadHistoryEvent (paid : BranchEvent)
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  UpperAssembly.meshBranchUnion properGapMesh (paid t m)

/-- Source-correct exceptional family.  Rank-local gap filters are absent
from this definition: on terminal four-favorite paths they route to the
existing low-gap exceptional event. -/
def sourceCorrectFilteredExceptionalEvent (paid : BranchEvent)
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  hlozExceptionalEvent t m ∪ paidTransitionBadHistoryEvent paid t m

/-- Terminal routing condition for cumulative factor filters.  It expresses
the exact distinction used in the source proof: a removed terminal history
is either a previously charged gap failure or a genuinely new lazy/candidate
auxiliary failure. -/
def TerminalFilteredBadHistoryRouting
    (bad₁ bad₂ bad₃ paid : BranchEvent) : Prop :=
  ∀ t m a, a ∈ UpperAssembly.meshTriples properGapMesh →
    screenedThirdTransitionEvent t m a ∩
        branchBadHistoryEvent bad₁ bad₂ bad₃ t m a ⊆
      hlozExceptionalEvent t m ∪ paid t m a

/-- Mesh cover with distinct factor-filter and paid-exception families. -/
theorem hlozSeparatedLevelEvent_sourceCorrect_filtered_mesh_cover
    (bad₁ bad₂ bad₃ paid : BranchEvent)
    (route : TerminalFilteredBadHistoryRouting bad₁ bad₂ bad₃ paid)
    (t : DominoTiling) (m : ℕ) :
    hlozSeparatedLevelEvent t m ⊆
      sourceCorrectFilteredExceptionalEvent paid t m ∪
        UpperAssembly.meshBranchUnion properGapMesh
          (goodThirdTransitionEvent bad₁ bad₂ bad₃ t m) := by
  intro s hs
  rcases hlozSeparatedLevelEvent_screened_mesh_cover t m hs with
      hexception | hbranch
  · exact Or.inl (Or.inl hexception)
  · exact meshBranchUnion_subset_exception_paid_union_diff properGapMesh
      (hlozExceptionalEvent t m) (screenedThirdTransitionEvent t m)
      (branchBadHistoryEvent bad₁ bad₂ bad₃ t m) (paid t m)
      (route t m) hbranch

/-- Additive summability for the source-correct paid auxiliary family. -/
theorem sourceCorrectFilteredExceptional_series_ne_top
    (paid : BranchEvent) (t : DominoTiling)
    (hbase : ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (hpaid : ∑' m,
      simpleRandomWalk (paidTransitionBadHistoryEvent paid t m) ≠ ∞) :
    ∑' m,
      simpleRandomWalk (sourceCorrectFilteredExceptionalEvent paid t m) ≠ ∞ := by
  have hmajor : ∑' m,
      (simpleRandomWalk (hlozExceptionalEvent t m) +
        simpleRandomWalk (paidTransitionBadHistoryEvent paid t m)) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hbase, hpaid⟩
  apply ne_top_of_le_ne_top hmajor
  apply ENNReal.tsum_le_tsum
  intro m
  exact measure_union_le _ _

/-- Summability is stable under the additive enlargement of the exceptional
family. -/
theorem filteredExceptional_series_ne_top
    (bad₁ bad₂ bad₃ : BranchEvent) (t : DominoTiling)
    (hbase : ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (hbad : ∑' m,
      simpleRandomWalk (transitionBadHistoryEvent bad₁ bad₂ bad₃ t m) ≠ ∞) :
    ∑' m,
      simpleRandomWalk (filteredExceptionalEvent bad₁ bad₂ bad₃ t m) ≠ ∞ := by
  have hmajor : ∑' m,
      (simpleRandomWalk (hlozExceptionalEvent t m) +
        simpleRandomWalk
          (transitionBadHistoryEvent bad₁ bad₂ bad₃ t m)) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hbase, hbad⟩
  apply ne_top_of_le_ne_top hmajor
  apply ENNReal.tsum_le_tsum
  intro m
  exact measure_union_le _ _

/-- Assembly from the three genuinely filtered transition factors.  This is
an internal bridge for the concrete stopped-history screens: the final
public theorem must derive its three factor hypotheses and the bad-history
series from literal product/strong-Markov data. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_filtered_estimates
    (K : ℝ≥0) (bad₁ bad₂ bad₃ : BranchEvent)
    (hfirst : ∀ t m a, a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk (goodFirstTransitionEvent bad₁ t m a) ≤
        UpperCanonical.hlozTransitionCost K m)
    (hsecond : ∀ t m a, a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk (goodSecondTransitionEvent bad₁ bad₂ t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk (goodFirstTransitionEvent bad₁ t m a))
    (hthird : ∀ t m a, a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk (goodThirdTransitionEvent bad₁ bad₂ bad₃ t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk (goodSecondTransitionEvent bad₁ bad₂ t m a))
    (hbase : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (hbad : ∀ t, ∑' m,
      simpleRandomWalk (transitionBadHistoryEvent bad₁ bad₂ bad₃ t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  have hscreened : ∀ t,
      ∑' m, simpleRandomWalk (hlozSeparatedLevelEvent t m) ≠ ∞ := by
    intro t
    apply UpperAssembly.screenedLevel_series_ne_top simpleRandomWalk properGapMesh
      (hlozSeparatedLevelEvent t)
      (filteredExceptionalEvent bad₁ bad₂ bad₃ t)
      (goodFirstTransitionEvent bad₁ t)
      (goodSecondTransitionEvent bad₁ bad₂ t)
      (goodThirdTransitionEvent bad₁ bad₂ bad₃ t)
      (UpperCanonical.hlozTransitionCost K) (K ^ 3)
      (3 * ScreeningInstantiation.kappa)
    · exact ScreeningInstantiation.hloz_parameter_inequalities.2.2.2.2.2.2.2.1
    · exact hlozSeparatedLevelEvent_filtered_mesh_cover bad₁ bad₂ bad₃ t
    · exact hfirst t
    · exact hsecond t
    · exact hthird t
    · exact filteredExceptional_series_ne_top bad₁ bad₂ bad₃ t
        (hbase t) (hbad t)
    · intro m
      exact (UpperCanonical.hlozTransitionCost_cube K m).le
  have hsum : ∑' m, simpleRandomWalk (levelFavoriteSet m 4) ≠ ∞ :=
    level_event_summable_of_six_tilings simpleRandomWalk
      levelFavoriteSet_four_subset_six_hloz_tilings hscreened
  exact UpperAssembly.ae_eventually_favoriteCount_le_three_of_M4_summable
    simpleRandomWalk hsum simpleRandomWalk_maxLocalTime_tendsto

/-- Preferred source-correct endgame.  The `bad₁,bad₂,bad₃` families are
the cumulative filters needed for the three strong-Markov factors, whereas
`paid` contains only auxiliary failures whose probabilities must be added.
Rank-local gap failures can be routed to the original HLOZ exceptional event
through `route` and therefore are not incorrectly required to be summable on
arbitrary rank-one or rank-two transitions. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_sourceCorrect_filtered_estimates
    (K : ℝ≥0) (bad₁ bad₂ bad₃ paid : BranchEvent)
    (route : TerminalFilteredBadHistoryRouting bad₁ bad₂ bad₃ paid)
    (hfirst : ∀ t m a, a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk (goodFirstTransitionEvent bad₁ t m a) ≤
        UpperCanonical.hlozTransitionCost K m)
    (hsecond : ∀ t m a, a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk (goodSecondTransitionEvent bad₁ bad₂ t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk (goodFirstTransitionEvent bad₁ t m a))
    (hthird : ∀ t m a, a ∈ UpperAssembly.meshTriples properGapMesh →
      simpleRandomWalk (goodThirdTransitionEvent bad₁ bad₂ bad₃ t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk (goodSecondTransitionEvent bad₁ bad₂ t m a))
    (hbase : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (hpaid : ∀ t, ∑' m,
      simpleRandomWalk (paidTransitionBadHistoryEvent paid t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  have hscreened : ∀ t,
      ∑' m, simpleRandomWalk (hlozSeparatedLevelEvent t m) ≠ ∞ := by
    intro t
    apply UpperAssembly.screenedLevel_series_ne_top simpleRandomWalk properGapMesh
      (hlozSeparatedLevelEvent t)
      (sourceCorrectFilteredExceptionalEvent paid t)
      (goodFirstTransitionEvent bad₁ t)
      (goodSecondTransitionEvent bad₁ bad₂ t)
      (goodThirdTransitionEvent bad₁ bad₂ bad₃ t)
      (UpperCanonical.hlozTransitionCost K) (K ^ 3)
      (3 * ScreeningInstantiation.kappa)
    · exact ScreeningInstantiation.hloz_parameter_inequalities.2.2.2.2.2.2.2.1
    · exact hlozSeparatedLevelEvent_sourceCorrect_filtered_mesh_cover
        bad₁ bad₂ bad₃ paid route t
    · exact hfirst t
    · exact hsecond t
    · exact hthird t
    · exact sourceCorrectFilteredExceptional_series_ne_top paid t
        (hbase t) (hpaid t)
    · intro m
      exact (UpperCanonical.hlozTransitionCost_cube K m).le
  have hsum : ∑' m, simpleRandomWalk (levelFavoriteSet m 4) ≠ ∞ :=
    level_event_summable_of_six_tilings simpleRandomWalk
      levelFavoriteSet_four_subset_six_hloz_tilings hscreened
  exact UpperAssembly.ae_eventually_favoriteCount_le_three_of_M4_summable
    simpleRandomWalk hsum simpleRandomWalk_maxLocalTime_tendsto

end

end Erdos1165.HLOZFilteredTransitionAssembly
