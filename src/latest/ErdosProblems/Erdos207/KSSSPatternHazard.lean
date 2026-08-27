/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternHazardTrajectory
import ErdosProblems.Erdos207.KSSSTrajectoryState

/-! # Extension hazard control from the actual coupled trajectory and crude events -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def patternHazardErrorCoefficient (q h m : ℕ) : ℕ :=
  h + m * (q + 1) + ((h + m) * m + (h + m).choose 2)

theorem pattern_hazard_error_coefficient_bound
    (q h m K : ℕ) (e : ℝ) (hKe : (K : ℝ) ≤ e) :
    (h : ℝ) * e + m * (q * e + K) +
      ((h + m) * (m * K) + (h + m).choose 2 * K : ℕ) ≤
        patternHazardErrorCoefficient q h m * e := by
  have h₁ := mul_le_mul_of_nonneg_left hKe (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have h₂ := mul_le_mul_of_nonneg_left hKe
    (Nat.cast_nonneg ((h + m) * m + (h + m).choose 2) :
      (0 : ℝ) ≤ ((h + m) * m + (h + m).choose 2 : ℕ))
  dsimp only [patternHazardErrorCoefficient]
  push_cast at h₂ ⊢
  nlinarith only [h₁, h₂]

theorem properPatternExtensions_vertical_pair_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    {u x : V} (hu : u ∈ properPatternExtensions S.available Q U)
    (hx : x ∈ graphSupportFinset Q) :
    (availableTrianglesContainingPair S {u, x}).Nonempty := by
  obtain ⟨y, hxy⟩ := mem_graphSupportFinset_iff.mp hx
  have he : s(x, y) ∈ graphEdges Q := mem_graphEdges_iff.mpr hxy
  have hold := (mem_iterationExtensionVertices_iff.mp (mem_properPatternExtensions_iff.mp hu).1).2
  obtain ⟨T, hT, huT, heT⟩ := hold s(x, y) he
  have hxT := (mk_mem_tripleEdgeFinset_iff.mp heT).1
  exact ⟨T, mem_availableTrianglesContainingPair_iff.mpr
    ⟨hT, insert_subset huT (singleton_subset_iff.mpr hxT)⟩⟩

theorem KSSSOnTrajectories.terminal_sum_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {Q₀ : Finset (Finset V)}
    {a : ℕ → ℝ} {E A scale time : ℝ} {B : ℕ}
    (h : KSSSOnTrajectories F S q Q₀ a E A scale B time)
    (he : 0 ≤ ksssErrorEnvelope E scale B time)
    {T : TripleOn V} (hT : T ∈ S.available) :
    |(∑ j ∈ Icc 4 q, ((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)).card : ℝ)) -
      ∑ j ∈ Icc 4 q, ksssConfigurationTrajectory (ksssOrders q) a E A (j - 3) (j - 4) time| ≤
        q * ksssErrorEnvelope E scale B time := by
  have hpoint : ∀ j ∈ Icc 4 q,
      |((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)).card : ℝ) -
        ksssConfigurationTrajectory (ksssOrders q) a E A (j - 3) (j - 4) time| ≤
          ksssErrorEnvelope E scale B time := by
    intro j hj
    have hj4 := (mem_Icc.mp hj).1
    have hlocal := h.2 T hT j hj (j - 4) (by omega)
    simpa only [Nat.sub_self, ksssConfigurationErrorEnvelope, pow_zero, mul_one] using hlocal
  rw [← sum_sub_distrib]
  have hsize : (Icc 4 q).card ≤ q := by rw [Nat.card_Icc]; omega
  calc
    _ ≤ ∑ _j ∈ Icc 4 q, ksssErrorEnvelope E scale B time :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpoint)
    _ = (Icc 4 q).card * ksssErrorEnvelope E scale B time := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) he

theorem KSSSOnTrajectories.pattern_hazard_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {Q₀ : Finset (Finset V)}
    {a : ℕ → ℝ} {E A scale time : ℝ} {B : ℕ} {Kc : CrudeThresholds}
    (h : KSSSOnTrajectories F S q Q₀ a E A scale B time)
    (hcrude : CrudeStateBounds F S q Kc)
    (hS : GreedyInvariant F S) (hpack : ∀ C ∈ F, IsPackingOn C)
    (hcard : ∀ C ∈ F, 2 ≤ C.card → C.card + 2 ≤ q)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q₀)
    (K : ℕ) (hK : 1 ≤ K) (hpairK : Kc.pair ≤ K) (hcommonK : Kc.common ≤ K)
    (hKe : (K : ℝ) ≤ ksssErrorEnvelope E scale B time)
    (Q : SimpleGraph V) (U : Finset V) (u : V)
    (hu : u ∈ properPatternExtensions S.available Q U) :
    |((patternExtensionKillers F Q U S u).card : ℝ) -
      ((graphSupportFinset Q).card * ksssPairTrajectory (ksssOrders q) a E A time +
        (graphEdges Q).card * ∑ j ∈ Icc 4 q,
          ksssConfigurationTrajectory (ksssOrders q) a E A (j - 3) (j - 4) time)| ≤
      patternHazardErrorCoefficient q (graphSupportFinset Q).card (graphEdges Q).card *
        ksssErrorEnvelope E scale B time := by
  have huout := (mem_properPatternExtensions_iff.mp hu).2
  have he : 0 ≤ ksssErrorEnvelope E scale B time := (Nat.cast_nonneg K).trans hKe
  have herror := patternExtensionKillers_card_trajectory_error hS hpack hcard Q U u huout hu K hK
    (fun T P ↦ (hcrude.pair T P).le.trans hpairK)
    (fun T T' ↦ (hcrude.common T T').le.trans hcommonK)
    (ksssPairTrajectory (ksssOrders q) a E A time)
    (∑ j ∈ Icc 4 q, ksssConfigurationTrajectory (ksssOrders q) a E A (j - 3) (j - 4) time)
    (ksssErrorEnvelope E scale B time) (q * ksssErrorEnvelope E scale B time) ?_ ?_
  · exact herror.trans (pattern_hazard_error_coefficient_bound q _ _ K _ hKe)
  · intro v hv
    have huv : u ≠ v := fun heq ↦ huout (heq ▸ hv)
    apply h.1
    exact hcover {u, v} (by simp [huv]) (properPatternExtensions_vertical_pair_nonempty Q U S hu hv)
  · intro e
    exact h.terminal_sum_error he
      (((mem_properPatternExtensions_iff_triangles S.available Q U u huout).mp hu).2 e)

end

end Erdos207
