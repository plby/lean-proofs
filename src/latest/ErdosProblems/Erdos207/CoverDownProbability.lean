/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CompatibleCandidates
import ErdosProblems.Erdos207.RootedThreatExtraction

/-!
# Probabilistic count certificate for cover-down

This file identifies the exact event whose positive probability suffices for
the KSSS outside packing.  The exhausted constrained-greedy invariant supplies
packinghood, forbidden avoidance, ambient containment, and maximality.  The
only additional event is the pointwise strict surplus of common-leave
candidates over rooted forbidden threats.
-/

namespace Erdos207

open Finset

namespace FiniteLaw

/-- A positive-probability event has a positive-mass witness. -/
lemma exists_of_probability_pos_with_mass
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) {P : Ω → Prop}
    (hP : 0 < L.probability P) : ∃ ω, P ω ∧ 0 < L.mass ω := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero : L.probability P = 0 := by
    unfold probability
    apply Finset.sum_eq_zero
    intro ω _hω
    by_cases hωP : P ω
    · have hmass : L.mass ω = 0 := by
        exact nonpos_iff_eq_zero.mp (hnone ω hωP)
      simp [hωP, hmass]
    · simp [hωP]
  exact (hzero ▸ hP).false

end FiniteLaw

/-- The additional numerical event required of an exhausted greedy state. -/
def IsKSSSCountGoodState
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (S : GreedyStateOn V) : Prop :=
  S.available = ∅ ∧
    ∀ ⦃u v : V⦄
      (huv : (graphDifference (leaveGraph S.chosen) H).Adj u v),
      (u ∉ X ∨ v ∉ X) →
      (rootedActiveForbiddenConfigurations
          (absorberErdosForbiddenConfigurationsOn q B)
          S.chosen u v).card * q <
        (packingCompatibleThirdVertices
          (outsideAvailableTriangles H B) S.chosen huv.1.ne).card

/-- An invariant state satisfying the count event is already a complete
outside-packing certificate. -/
theorem hasKSSSOutsidePacking_of_countGoodState
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {S : GreedyStateOn V}
    (hInv : AbsorberGreedyInvariant
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B) S)
    (hgood : IsKSSSCountGoodState q H X B S) :
    HasKSSSOutsidePacking q H X B S.chosen := by
  have hmax : legalAvailable
      (absorberErdosForbiddenConfigurationsOn q B) S.chosen
      (outsideAvailableTriangles H B) = ∅ := by
    rw [← hInv.2.2]
    exact hgood.1
  have hsupport : GraphSupportedOn
      (graphDifference (leaveGraph S.chosen) H) (X : Set V) := by
    apply graphSupportedOn_of_maximal_absorber_rooted_lt_compatible
      hInv.1.1 hInv.1.2.1 hmax
    exact hgood.2
  exact hasKSSSOutsidePacking_of_maximal
    hInv.1.1 hInv.2.1.1 hInv.1.2.1 hsupport

/-- Positive probability of the exact count event under the exhausted
canonical greedy law yields a deterministic KSSS outside packing. -/
theorem exists_ksssOutsidePacking_of_countGood_probability_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V)
    (hpos : 0 < (absorberGreedyLaw q
      (outsideAvailableTriangles H B).card B
      (outsideAvailableTriangles H B)).probability
        (IsKSSSCountGoodState q H X B)) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let L := absorberGreedyLaw q (outsideAvailableTriangles H B).card B
    (outsideAvailableTriangles H B)
  obtain ⟨S, hgood, hmass⟩ :=
    L.exists_of_probability_pos_with_mass hpos
  have hInv := absorberGreedyLaw_supported q
    (outsideAvailableTriangles H B).card B
    (outsideAvailableTriangles H B) S hmass
  exact ⟨S.chosen, hasKSSSOutsidePacking_of_countGoodState hInv hgood⟩

end Erdos207
