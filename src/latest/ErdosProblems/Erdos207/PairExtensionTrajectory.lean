/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairExtensionDeletionDrift
import ErdosProblems.Erdos207.FiniteRealExpectation
import ErdosProblems.Erdos207.EnvelopeStoppedGreedy

/-!
# A fixed pair-extension trajectory

The local drift lemmas use the current pair star as their test family.  Along
a greedy trajectory availability only decreases, so restricting the initial
pair star to the current availability gives exactly the current pair star.
This file packages that observation and transfers the local drift and second
moment estimates to one fixed observable suitable for martingale arguments.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A pair is alive while it has at least one available extension. -/
def PairAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset V) (S : GreedyStateOn V) : Prop :=
  (availableTrianglesContainingPair S P).Nonempty

instance instDecidablePairAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset V) (S : GreedyStateOn V) : Decidable (PairAlive P S) :=
  Finset.decidableNonempty

/-- A pair alive in a smaller availability family was already alive in any
larger availability family. -/
theorem PairAlive.of_available_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : Finset V} {S S' : GreedyStateOn V}
    (hsub : S.available ⊆ S'.available) (h : PairAlive P S) :
    PairAlive P S' := by
  exact h.mono fun T hT ↦
    mem_availableTrianglesContainingPair_iff.mpr
      ⟨hsub (mem_availableTrianglesContainingPair_iff.mp hT).1,
        (mem_availableTrianglesContainingPair_iff.mp hT).2⟩

/-- Pair-star availability is monotone under a greedy step. -/
theorem availableTrianglesContainingPair_step_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (P : Finset V) (T : TripleOn V) :
    availableTrianglesContainingPair (greedyStep F S T) P ⊆
      availableTrianglesContainingPair S P := by
  intro U hU
  have hdata := mem_availableTrianglesContainingPair_iff.mp hU
  exact mem_availableTrianglesContainingPair_iff.mpr
    ⟨greedyStep_available_subset F S T hdata.1, hdata.2⟩

/-- Greedy invariant together with monotonicity below an initial availability
family. -/
def PairTrajectoryInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S₀ S : GreedyStateOn V) : Prop :=
  GreedyInvariant F S ∧ S.available ⊆ S₀.available

theorem pairTrajectoryInvariant_initial
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ : GreedyStateOn V}
    (hS₀ : GreedyInvariant F S₀) :
    PairTrajectoryInvariant F S₀ S₀ := ⟨hS₀, Subset.rfl⟩

/-- The ordinary greedy kernel preserves the fixed-initial trajectory
invariant. -/
theorem greedyKernel_supported_pairTrajectoryInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    (hS : PairTrajectoryInvariant F S₀ S) :
    FiniteLaw.SupportedOn (PairTrajectoryInvariant F S₀)
      (greedyKernel F S) := by
  intro S' hmass
  have hInv' := greedyKernel_supported hS.1 S' hmass
  have hstep := greedyKernel_supported_step_or_self F S S' hmass
  refine ⟨hInv', ?_⟩
  rcases hstep with rfl | ⟨T, _hT, rfl⟩
  · exact hS.2
  · exact (greedyStep_available_subset F S T).trans hS.2

/-- Restricting the initial pair star to a later availability family is the
current pair star. -/
theorem greedyAvailableIn_initialPairStar_eq_current
    {V : Type*} [Fintype V] [DecidableEq V]
    {S₀ S : GreedyStateOn V} {P : Finset V}
    (hsub : S.available ⊆ S₀.available) :
    greedyAvailableIn (availableTrianglesContainingPair S₀ P) S =
      availableTrianglesContainingPair S P := by
  ext T
  simp only [greedyAvailableIn, mem_inter,
    mem_availableTrianglesContainingPair_iff]
  constructor
  · rintro ⟨hTS, _hTS₀, hPT⟩
    exact ⟨hTS, hPT⟩
  · rintro ⟨hTS, hPT⟩
    exact ⟨hTS, hsub hTS, hPT⟩

/-- Fixed observable counting the surviving members of the initial pair
star. -/
def fixedPairAvailableCountReal
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (P : Finset V) (S : GreedyStateOn V) : ℝ :=
  greedyAvailableCountReal (availableTrianglesContainingPair S₀ P) S

theorem fixedPairAvailableCountReal_eq_current
    {V : Type*} [Fintype V] [DecidableEq V]
    {S₀ S : GreedyStateOn V} {P : Finset V}
    (hsub : S.available ⊆ S₀.available) :
    fixedPairAvailableCountReal S₀ P S =
      (availableTrianglesContainingPair S P).card := by
  simp only [fixedPairAvailableCountReal, greedyAvailableCountReal]
  rw [greedyAvailableIn_initialPairStar_eq_current hsub]

/-- Along a greedy step, the fixed-initial pair observable drops by exactly
the number of current pair-star triangles deleted by that step. -/
theorem fixedPairAvailableCountReal_step_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S₀ S : GreedyStateOn V)
    (P : Finset V) (T : TripleOn V)
    (hsub : S.available ⊆ S₀.available) :
    fixedPairAvailableCountReal S₀ P (greedyStep F S T) -
        fixedPairAvailableCountReal S₀ P S =
      -((greedyDeletedIn F (availableTrianglesContainingPair S P) S T).card : ℝ) := by
  have hstep : (greedyStep F S T).available ⊆ S.available :=
    greedyStep_available_subset F S T
  calc
    fixedPairAvailableCountReal S₀ P (greedyStep F S T) -
        fixedPairAvailableCountReal S₀ P S =
      greedyAvailableCountReal (availableTrianglesContainingPair S P)
          (greedyStep F S T) -
        greedyAvailableCountReal (availableTrianglesContainingPair S P) S := by
          simp only [fixedPairAvailableCountReal, greedyAvailableCountReal]
          rw [greedyAvailableIn_initialPairStar_eq_current
              (S₀ := S₀) (S := greedyStep F S T) (P := P)
              (hstep.trans hsub),
            greedyAvailableIn_initialPairStar_eq_current hsub,
            greedyAvailableIn_initialPairStar_eq_current
              (S₀ := S) (S := greedyStep F S T) (P := P) hstep,
            greedyAvailableIn_initialPairStar_eq_current
              (S₀ := S) (S := S) (P := P) Subset.rfl]
    _ = _ := greedyAvailableCountReal_step_sub F
      (availableTrianglesContainingPair S P) S T

/-- A positive-mass successor of a nonempty greedy state changes the fixed
pair observable by a nonpositive amount whose magnitude is at most the
pair/two-away deletion envelope. -/
theorem greedyKernel_fixedPair_increment_mem_interval
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S S' : GreedyStateOn V}
    {P : Finset V} {Δ K : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S)
    (hmass : 0 < (greedyKernel F S).mass S') :
    -((3 * Δ + K : ℕ) : ℝ) ≤
        fixedPairAvailableCountReal S₀ P S' -
          fixedPairAvailableCountReal S₀ P S ∧
      fixedPairAvailableCountReal S₀ P S' -
          fixedPairAvailableCountReal S₀ P S ≤ 0 := by
  obtain ⟨T, hT, rfl⟩ :=
    greedyKernel_supported_step_of_nonempty F S hA _ hmass
  rw [fixedPairAvailableCountReal_step_sub F S₀ S P T hS.2]
  have hcard := card_greedyDeletedIn_le_pairCutoff
    hS.1 hpair htwo hT (Q := availableTrianglesContainingPair S P)
  have hcardReal :
      ((greedyDeletedIn F (availableTrianglesContainingPair S P) S T).card : ℝ) ≤
        ((3 * Δ + K : ℕ) : ℝ) := by
    exact_mod_cast hcard
  constructor
  · linarith
  · exact neg_nonpos.mpr (Nat.cast_nonneg _)

/-- The fixed-initial and current-pair observables have the same one-step
increment in conditional expectation. -/
theorem greedyKernel_expectationReal_fixedPair_increment_eq_current
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S₀ S : GreedyStateOn V)
    (P : Finset V) (hsub : S.available ⊆ S₀.available) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ fixedPairAvailableCountReal S₀ P S' -
          fixedPairAvailableCountReal S₀ P S) =
      (greedyKernel F S).expectationReal
        (fun S' ↦ greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S' -
          greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S) := by
  have hsupp : FiniteLaw.SupportedOn
      (fun S' : GreedyStateOn V ↦ S'.available ⊆ S.available)
      (greedyKernel F S) := by
    intro S' hmass
    rcases greedyKernel_supported_step_or_self F S S' hmass with
      rfl | ⟨T, _hT, rfl⟩
    · exact Subset.rfl
    · exact greedyStep_available_subset F S T
  apply FiniteLaw.expectationReal_congr_of_supported (greedyKernel F S) hsupp
  intro S' hS'sub
  have hS'₀sub := hS'sub.trans hsub
  rw [fixedPairAvailableCountReal_eq_current hsub,
    fixedPairAvailableCountReal_eq_current hS'₀sub]
  simp only [greedyAvailableCountReal]
  rw [greedyAvailableIn_initialPairStar_eq_current hS'sub,
    greedyAvailableIn_initialPairStar_eq_current (S₀ := S) (S := S)
      Subset.rfl]

/-- The same transfer for conditional squared increments. -/
theorem greedyKernel_expectationReal_fixedPair_sqIncrement_eq_current
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S₀ S : GreedyStateOn V)
    (P : Finset V) (hsub : S.available ⊆ S₀.available) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ (fixedPairAvailableCountReal S₀ P S' -
          fixedPairAvailableCountReal S₀ P S) ^ 2) =
      (greedyKernel F S).expectationReal
        (fun S' ↦ (greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S' -
          greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S) ^ 2) := by
  have hsupp : FiniteLaw.SupportedOn
      (fun S' : GreedyStateOn V ↦ S'.available ⊆ S.available)
      (greedyKernel F S) := by
    intro S' hmass
    rcases greedyKernel_supported_step_or_self F S S' hmass with
      rfl | ⟨T, _hT, rfl⟩
    · exact Subset.rfl
    · exact greedyStep_available_subset F S T
  apply FiniteLaw.expectationReal_congr_of_supported (greedyKernel F S) hsupp
  intro S' hS'sub
  have hS'₀sub := hS'sub.trans hsub
  rw [fixedPairAvailableCountReal_eq_current hsub,
    fixedPairAvailableCountReal_eq_current hS'₀sub]
  simp only [greedyAvailableCountReal]
  rw [greedyAvailableIn_initialPairStar_eq_current hS'sub,
    greedyAvailableIn_initialPairStar_eq_current (S₀ := S) (S := S)
      Subset.rfl]

/-- Three-pair negative drift for the fixed observable. -/
theorem greedyKernel_expectationReal_fixedPair_increment_le_threeFloor
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {P : Finset V} {δ : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (hfloor : HasAvailablePairFloor δ S) (hδ : 1 ≤ δ) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ fixedPairAvailableCountReal S₀ P S' -
          fixedPairAvailableCountReal S₀ P S) ≤
      -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P).card : ℝ) *
          (3 * δ - 2 : ℕ)) := by
  rw [greedyKernel_expectationReal_fixedPair_increment_eq_current
    F S₀ S P hS.2]
  exact greedyKernel_expectationReal_pairStar_increment_le_threeFloor
    hS.1 hA hfloor hδ

/-- Cutoff lower drift for the fixed observable. -/
theorem greedyKernel_expectationReal_fixedPair_increment_ge_cutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {P : Finset V} {Δ K : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S) :
    -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P).card : ℝ) *
          (3 * Δ + K : ℕ)) ≤
      (greedyKernel F S).expectationReal
        (fun S' ↦ fixedPairAvailableCountReal S₀ P S' -
          fixedPairAvailableCountReal S₀ P S) := by
  rw [greedyKernel_expectationReal_fixedPair_increment_eq_current
    F S₀ S P hS.2]
  exact greedyKernel_expectationReal_pairStar_increment_ge_cutoffs
    hS.1 hA hpair htwo

/-- Conditional second moment for the fixed observable. -/
theorem greedyKernel_expectationReal_fixedPair_sqIncrement_le_cutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {P : Finset V} {Δ K : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ (fixedPairAvailableCountReal S₀ P S' -
          fixedPairAvailableCountReal S₀ P S) ^ 2) ≤
      (S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P).card : ℝ) *
          (3 * Δ + K : ℕ) ^ 2) := by
  rw [greedyKernel_expectationReal_fixedPair_sqIncrement_eq_current
    F S₀ S P hS.2]
  exact greedyKernel_expectationReal_pairStar_sqIncrement_le_cutoffs
    hS.1 hA hpair htwo

end

end Erdos207
