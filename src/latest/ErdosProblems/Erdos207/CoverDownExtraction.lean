/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoverDownProbability
import ErdosProblems.Erdos207.RootedThreatExtraction

/-!
# Union-bound extraction of a cover-down state

The last probabilistic step has one bad event for every ordered pair of
distinct vertices.  This file packages the exact finite union bound.  It
also retains positive mass of the extracted state, so the support theorem
for the constrained greedy law can be applied without any extra argument.
-/

namespace Erdos207

open Finset
open scoped NNReal

/-- Ordered distinct pairs have the expected cardinality. -/
theorem card_distinctPair
    (V : Type*) [Fintype V] [DecidableEq V] :
    Fintype.card (DistinctPair V) =
      Fintype.card V * (Fintype.card V - 1) := by
  let e : DistinctPair V ≃ Σ u : V, {v : V // v ≠ u} :=
    { toFun := fun p ↦ ⟨p.1.1, p.1.2, fun h ↦ p.2 h.symm⟩
      invFun := fun p ↦ ⟨(p.1, p.2.1), fun h ↦ p.2.2 h.symm⟩
      left_inv := by intro p; cases p; rfl
      right_inv := by intro p; cases p; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp [Set.card_ne_eq]

namespace FiniteLaw

/-- A strict union bound has a positive-mass outcome avoiding every event. -/
theorem exists_avoiding_with_mass_of_sum_probability_lt_one
    {Ω I : Type*} [Fintype Ω] [Fintype I]
    (L : FiniteLaw Ω) (P : I → Ω → Prop)
    (hsmall : ∑ i : I, L.probability (P i) < 1) :
    ∃ ω, (∀ i, ¬ P i ω) ∧ 0 < L.mass ω := by
  classical
  let bad : Ω → Prop := fun ω ↦ ∃ i, P i ω
  have hbad : L.probability bad < 1 := by
    have h := (L.probability_exists_le (univ : Finset I) P).trans_lt (by
      simpa using hsmall)
    simpa [bad] using h
  have hgood : 0 < L.probability (fun ω ↦ ¬ bad ω) := by
    rw [L.probability_not bad]
    exact tsub_pos_iff_lt.mpr hbad
  obtain ⟨ω, hω, hmass⟩ :=
    L.exists_of_probability_pos_with_mass hgood
  refine ⟨ω, ?_, hmass⟩
  intro i hi
  exact hω ⟨i, hi⟩

end FiniteLaw

/-- Failure of the exact rooted-threat/common-leave surplus at one ordered
pair.  Pairs which are already covered, belong to the absorber, or lie
entirely in the flexible set impose no condition. -/
def KSSSCountFailureAt
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (e : DistinctPair V)
    (S : GreedyStateOn V) : Prop :=
  ∃ huv : (graphDifference (leaveGraph S.chosen) H).Adj e.1.1 e.1.2,
    (e.1.1 ∉ X ∨ e.1.2 ∉ X) ∧
      (packingCompatibleThirdVertices
          (outsideAvailableTriangles H B) S.chosen huv.1.ne).card ≤
        (rootedActiveForbiddenConfigurations
          (absorberErdosForbiddenConfigurationsOn q B)
          S.chosen e.1.1 e.1.2).card * q

/-- Avoiding all pair-indexed failures is precisely the numerical part of
`IsKSSSCountGoodState`. -/
theorem countGoodState_of_exhausted_of_avoids_failures
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {S : GreedyStateOn V}
    (hexhausted : S.available = ∅)
    (havoid : ∀ e : DistinctPair V,
      ¬ KSSSCountFailureAt q H X B e S) :
    IsKSSSCountGoodState q H X B S := by
  refine ⟨hexhausted, ?_⟩
  intro u v huv houtside
  let e : DistinctPair V := ⟨(u, v), huv.1.ne⟩
  have hnot := havoid e
  have hstrict : ¬
      (packingCompatibleThirdVertices
          (outsideAvailableTriangles H B) S.chosen huv.1.ne).card ≤
        (rootedActiveForbiddenConfigurations
          (absorberErdosForbiddenConfigurationsOn q B)
          S.chosen u v).card * q := by
    intro hle
    exact hnot ⟨huv, houtside, hle⟩
  omega

/-- If every positive-mass state is an exhausted greedy-invariant state and
the sum of the pairwise failure probabilities is below one, then an outside
packing exists. -/
theorem exists_ksssOutsidePacking_of_sum_failure_probability_lt_one
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (L : FiniteLaw Ω)
    (state : Ω → GreedyStateOn V)
    (hsupport : L.SupportedOn (fun ω ↦
      AbsorberGreedyInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B) (state ω) ∧
      (state ω).available = ∅))
    (hsmall : ∑ e : DistinctPair V,
      L.probability (fun ω ↦ KSSSCountFailureAt q H X B e (state ω)) < 1) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  obtain ⟨ω, havoid, hmass⟩ :=
    L.exists_avoiding_with_mass_of_sum_probability_lt_one
      (fun e ω ↦ KSSSCountFailureAt q H X B e (state ω)) hsmall
  have hs := hsupport ω hmass
  exact ⟨(state ω).chosen,
    hasKSSSOutsidePacking_of_countGoodState hs.1
      (countGoodState_of_exhausted_of_avoids_failures hs.2 havoid)⟩

/-- Uniform pairwise estimates reduce the final cover-down extraction to the
single numerical inequality `|V|(|V|-1) ε < 1`. -/
theorem exists_ksssOutsidePacking_of_uniform_failure_probability
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (L : FiniteLaw Ω)
    (state : Ω → GreedyStateOn V) (ε : ℝ≥0)
    (hsupport : L.SupportedOn (fun ω ↦
      AbsorberGreedyInvariant
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B) (state ω) ∧
      (state ω).available = ∅))
    (hprob : ∀ e : DistinctPair V,
      L.probability (fun ω ↦ KSSSCountFailureAt q H X B e (state ω)) ≤ ε)
    (hsmall : (Fintype.card (DistinctPair V) : ℝ≥0) * ε < 1) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  apply exists_ksssOutsidePacking_of_sum_failure_probability_lt_one
    q H X B L state hsupport
  calc
    ∑ e : DistinctPair V,
        L.probability (fun ω ↦ KSSSCountFailureAt q H X B e (state ω)) ≤
        ∑ _e : DistinctPair V, ε := by
      apply sum_le_sum
      intro e _he
      exact hprob e
    _ = (Fintype.card (DistinctPair V) : ℝ≥0) * ε := by simp
    _ < 1 := hsmall

end Erdos207
