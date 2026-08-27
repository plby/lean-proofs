/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSInitialValues
import ErdosProblems.Erdos207.KSSSIndexedTrajectoryFailure

/-! # Initial signed margins from the source's pair and configuration regularity -/

namespace Erdos207

open Finset

noncomputable section

def KSSSInitialRegularity
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V) (q : ℕ) (Q₀ : Finset (Finset V))
    (a : ℕ → ℝ) (E₀ A₀ eta : ℝ) : Prop :=
  (∀ P ∈ Q₀, |((availableTrianglesContainingPair S₀ P).card : ℝ) - 3 * A₀ / E₀| ≤ eta * (3 * A₀ / E₀)) ∧
  ∀ T ∈ S₀.available, ∀ j ∈ Icc 4 q,
    |(((forbiddenFamilyOfOrder F j).filter (fun C ↦ T ∈ C)).card : ℝ) -
      a (j - 3) * A₀ ^ (j - 3)| ≤ eta * (A₀ / E₀) ^ (j - 3)

def ksssInitialMargin
    {V : Type*} [DecidableEq V] {q : ℕ}
    (E₀ A₀ margin : ℝ) : KSSSTrajectoryIndex V q → ℝ
  | .inl _ => margin
  | .inr (i, _) => margin * (A₀ / E₀) ^ (i.order - 4 - i.chosen)

theorem KSSSInitialRegularity.initial_margin
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ : GreedyStateOn V} {q : ℕ} {Q₀ : Finset (Finset V)}
    {a : ℕ → ℝ} {E₀ A₀ eta scale margin : ℝ} (B : ℕ)
    (h : KSSSInitialRegularity F S₀ q Q₀ a E₀ A₀ eta)
    (hchosen : S₀.chosen = ∅) (havailable : ∀ C ∈ F, C ⊆ S₀.available)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (heta : 0 ≤ eta)
    (hbudget : 3 * eta * (A₀ / E₀) + margin ≤ scale)
    (i : KSSSTrajectoryIndex V q) (hi : ksssTrajectoryTracked S₀ Q₀ i) :
    |ksssTrajectoryValue F S₀ i - ksssTrajectoryTarget a E₀ A₀ 0 i| +
      ksssInitialMargin E₀ A₀ margin i ≤ ksssTrajectoryError E₀ A₀ scale B 0 i := by
  have horders : ∀ d ∈ ksssOrders q, 1 ≤ d := fun d hd ↦ (mem_Icc.mp hd).1
  have hw : 0 ≤ A₀ / E₀ := div_nonneg hA hE.le
  rcases i with P | ⟨i, T⟩
  · change |((availableTrianglesContainingPair S₀ P.1).card : ℝ) -
      ksssPairTrajectory (ksssOrders q) a E₀ A₀ 0| + margin ≤ ksssErrorEnvelope E₀ scale B 0
    rw [ksssPairTrajectory_zero (ksssOrders q) a E₀ A₀ hE.ne' horders,
      ksssErrorEnvelope_zero E₀ scale B hE.ne']
    have hp := h.1 P.1 hi
    have heq : eta * (3 * A₀ / E₀) = 3 * eta * (A₀ / E₀) := by ring
    rw [heq] at hp
    linarith only [hp, hbudget]
  · have hlow : 4 ≤ i.order := by have hc := i.budget; omega
    have hj : i.order ∈ Icc 4 q := mem_Icc.mpr ⟨hlow, i.order_le⟩
    change |((greedyConfigurationClass (forbiddenFamilyOfOrder F i.order) S₀ T i.chosen).card : ℝ) -
      ksssConfigurationTrajectory (ksssOrders q) a E₀ A₀ (i.order - 3) i.chosen 0| +
        margin * (A₀ / E₀) ^ (i.order - 4 - i.chosen) ≤
          ksssConfigurationErrorEnvelope E₀ A₀ scale B (i.order - 4 - i.chosen) 0
    rw [ksssConfigurationErrorEnvelope_zero E₀ A₀ scale B _ hE.ne']
    by_cases hc : i.chosen = 0
    · rw [hc, Nat.sub_zero, ksssConfigurationTrajectory_zero_zero (ksssOrders q) a E₀ A₀
        (i.order - 3) hE.ne' horders,
        greedyConfigurationClass_initial_zero (forbiddenFamilyOfOrder F i.order) S₀ T hchosen
          (fun C hC ↦ havailable C (mem_forbiddenFamilyOfOrder.mp hC).1)]
      have he : i.order - 3 - 1 = i.order - 4 := by omega
      simpa only [he] using initial_configuration_margin (i.order - 3) (by omega)
        heta hw (h.2 T hi i.order hj) hbudget
    · have hcpos : 0 < i.chosen := Nat.pos_of_ne_zero hc
      rw [greedyConfigurationClass_empty_of_initial_chosen _ S₀ T _ hchosen hcpos,
        ksssConfigurationTrajectory_zero_of_chosen_pos _ a E₀ A₀ _ _ hcpos]
      simp only [card_empty, Nat.cast_zero, sub_self, abs_zero, zero_add]
      have hm : margin ≤ scale := by nlinarith [mul_nonneg heta hw]
      exact mul_le_mul_of_nonneg_right hm (pow_nonneg hw _)

theorem ksssInitialMargin_nonneg
    {V : Type*} [DecidableEq V] {q : ℕ}
    (E₀ A₀ margin : ℝ) (hE : 0 < E₀) (hA : 0 ≤ A₀) (hm : 0 ≤ margin)
    (i : KSSSTrajectoryIndex V q) : 0 ≤ ksssInitialMargin E₀ A₀ margin i := by
  rcases i with P | ⟨i, T⟩
  · exact hm
  · dsimp only [ksssInitialMargin]
    positivity

theorem KSSSInitialRegularity.onTrajectories
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ : GreedyStateOn V} {q : ℕ} {Q₀ : Finset (Finset V)}
    {a : ℕ → ℝ} {E₀ A₀ eta scale : ℝ} (B : ℕ)
    (h : KSSSInitialRegularity F S₀ q Q₀ a E₀ A₀ eta)
    (hchosen : S₀.chosen = ∅) (havailable : ∀ C ∈ F, C ⊆ S₀.available)
    (hQ : ∀ P ∈ Q₀, P.card = 2)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (heta : 0 ≤ eta)
    (hbudget : 3 * eta * (A₀ / E₀) ≤ scale) :
    KSSSOnTrajectories F S₀ q Q₀ a E₀ A₀ scale B 0 := by
  apply (ksssOnTrajectories_iff_index_bounds F S₀ q Q₀ a E₀ A₀ scale B 0 hQ).mpr
  intro i hi
  have hm := h.initial_margin B hchosen havailable hE hA heta
    (margin := 0) (by simpa using hbudget) i hi
  rcases i with P | ⟨i, T⟩ <;> simpa only [ksssInitialMargin, zero_mul, add_zero] using hm

end

end Erdos207
