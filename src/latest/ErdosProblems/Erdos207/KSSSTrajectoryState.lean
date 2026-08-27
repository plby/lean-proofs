/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSIndexedThreat
import ErdosProblems.Erdos207.KSSSErrorEnvelopeGrowth
import ErdosProblems.Erdos207.GlobalPairTrajectory

/-! # The actual coupled trajectory event at one greedy state -/

namespace Erdos207

open Finset

noncomputable section

/-- The source tracks every residual pair, including pairs with an empty
star, and every configuration class rooted at an available triangle. -/
def KSSSOnTrajectories
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (q : ℕ) (Q : Finset (Finset V))
    (a : ℕ → ℝ) (E₀ A₀ scale : ℝ) (B : ℕ) (t : ℝ) : Prop :=
  (∀ P ∈ Q, |((availableTrianglesContainingPair S P).card : ℝ) -
    ksssPairTrajectory (ksssOrders q) a E₀ A₀ t| ≤ ksssErrorEnvelope E₀ scale B t) ∧
  ∀ T ∈ S.available, ∀ j ∈ Icc 4 q, ∀ c, c + 4 ≤ j →
    |((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T c).card : ℝ) -
      ksssConfigurationTrajectory (ksssOrders q) a E₀ A₀ (j - 3) c t| ≤
        ksssConfigurationErrorEnvelope E₀ A₀ scale B (j - 4 - c) t

theorem KSSSOnTrajectories.availability_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {Q : Finset (Finset V)}
    {a : ℕ → ℝ} {E₀ A₀ scale t : ℝ} {B : ℕ}
    (h : KSSSOnTrajectories F S q Q a E₀ A₀ scale B t)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q) :
    |(S.available.card : ℝ) - Q.card * ksssPairTrajectory (ksssOrders q) a E₀ A₀ t / 3| ≤
      Q.card * ksssErrorEnvelope E₀ scale B t / 3 :=
  abs_available_sub_pair_trajectory_le S Q _ _ hQ hcover h.1

theorem KSSSOnTrajectories.closed_threat_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {Q : Finset (Finset V)}
    {a : ℕ → ℝ} {E₀ A₀ scale t : ℝ} {B : ℕ} {K : CrudeThresholds}
    (h : KSSSOnTrajectories F S q Q a E₀ A₀ scale B t)
    (hcrude : CrudeStateBounds F S q K)
    (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    (hcard : ∀ E ∈ F, 2 ≤ E.card → E.card + 2 ≤ q)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (he : 2 ≤ ksssErrorEnvelope E₀ scale B t)
    (hcommon : (K.common : ℝ) ≤ ksssErrorEnvelope E₀ scale B t)
    {T : TripleOn V} (hT : T ∈ S.available) :
    |((greedyClosedThreats F S T).card : ℝ) - ksssThreatTrajectory (ksssOrders q) a E₀ A₀ t| ≤
      ((q : ℝ) + 5) * ksssErrorEnvelope E₀ scale B t := by
  apply hcrude.ksss_threat_error hS hpack hcard a E₀ A₀ t _ he hcommon hT
  · intro P hP
    have hp := mem_powersetCard.mp hP
    exact h.1 P (hcover P hp.2 ⟨T, mem_availableTrianglesContainingPair_iff.mpr ⟨hT, hp.1⟩⟩)
  · intro j hj
    have hc : j - 4 + 4 ≤ j := by have hlow := (mem_Icc.mp hj).1; omega
    have hjc := h.2 T hT j hj (j - 4) hc
    simpa only [Nat.sub_self, ksssConfigurationErrorEnvelope, pow_zero, mul_one] using hjc

end

end Erdos207
