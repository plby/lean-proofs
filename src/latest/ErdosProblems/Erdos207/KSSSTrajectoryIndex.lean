/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSTrajectoryState

/-! # The exact polynomial-size index set for coupled trajectory failures -/

namespace Erdos207

open Finset

noncomputable section

abbrev KSSSTrajectoryIndex (V : Type*) [DecidableEq V] (q : ℕ) :=
  PairOn V ⊕ (CrudeOrderIndex q 4 × TripleOn V)

def ksssTrajectoryTracked
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (S : GreedyStateOn V) (Q : Finset (Finset V)) : KSSSTrajectoryIndex V q → Prop
  | .inl P => P.1 ∈ Q
  | .inr (_, T) => T ∈ S.available

def ksssTrajectoryValue
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) : KSSSTrajectoryIndex V q → ℝ
  | .inl P => (availableTrianglesContainingPair S P.1).card
  | .inr (i, T) => (greedyConfigurationClass (forbiddenFamilyOfOrder F i.order) S T i.chosen).card

def ksssTrajectoryTarget
    {V : Type*} [DecidableEq V] {q : ℕ}
    (a : ℕ → ℝ) (E₀ A₀ t : ℝ) : KSSSTrajectoryIndex V q → ℝ
  | .inl _ => ksssPairTrajectory (ksssOrders q) a E₀ A₀ t
  | .inr (i, _) => ksssConfigurationTrajectory (ksssOrders q) a E₀ A₀ (i.order - 3) i.chosen t

def ksssTrajectoryError
    {V : Type*} [DecidableEq V] {q : ℕ}
    (E₀ A₀ scale : ℝ) (B : ℕ) (t : ℝ) : KSSSTrajectoryIndex V q → ℝ
  | .inl _ => ksssErrorEnvelope E₀ scale B t
  | .inr (i, _) => ksssConfigurationErrorEnvelope E₀ A₀ scale B (i.order - 4 - i.chosen) t

theorem ksssOnTrajectories_iff_index_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (q : ℕ) (Q : Finset (Finset V))
    (a : ℕ → ℝ) (E₀ A₀ scale : ℝ) (B : ℕ) (t : ℝ)
    (hQ : ∀ P ∈ Q, P.card = 2) :
    KSSSOnTrajectories F S q Q a E₀ A₀ scale B t ↔
      ∀ i : KSSSTrajectoryIndex V q, ksssTrajectoryTracked S Q i →
        |ksssTrajectoryValue F S i - ksssTrajectoryTarget a E₀ A₀ t i| ≤
          ksssTrajectoryError E₀ A₀ scale B t i := by
  constructor
  · intro h i hi
    rcases i with P | ⟨i, T⟩
    · exact h.1 P.1 hi
    · have hlow : 4 ≤ i.order := by have hb := i.budget; omega
      exact h.2 T hi i.order (mem_Icc.mpr ⟨hlow, i.order_le⟩) i.chosen i.budget
  · intro h
    constructor
    · intro P hP
      exact h (.inl ⟨P, hQ P hP⟩) hP
    · intro T hT j hj c hc
      exact h (.inr (crudeOrderIndexOfBudget j c (mem_Icc.mp hj).2 hc, T)) hT

theorem card_ksssTrajectoryIndex_le
    (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :
    Fintype.card (KSSSTrajectoryIndex V q) ≤
      Fintype.card V ^ 2 + (q + 1) ^ 2 * Fintype.card V ^ 3 := by
  simp only [KSSSTrajectoryIndex, Fintype.card_sum, Fintype.card_prod]
  exact Nat.add_le_add (card_pairOn_le_sq V)
    (Nat.mul_le_mul (card_crudeOrderIndex_le q 4) (card_tripleOn_le_cube V))

theorem not_ksssOnTrajectories_iff_exists_index
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (q : ℕ) (Q : Finset (Finset V))
    (a : ℕ → ℝ) (E₀ A₀ scale : ℝ) (B : ℕ) (t : ℝ)
    (hQ : ∀ P ∈ Q, P.card = 2) :
    ¬ KSSSOnTrajectories F S q Q a E₀ A₀ scale B t ↔
      ∃ i : KSSSTrajectoryIndex V q, ksssTrajectoryTracked S Q i ∧
        ksssTrajectoryError E₀ A₀ scale B t i <
          |ksssTrajectoryValue F S i - ksssTrajectoryTarget a E₀ A₀ t i| := by
  rw [ksssOnTrajectories_iff_index_bounds F S q Q a E₀ A₀ scale B t hQ]
  simp only [not_forall, not_le, exists_prop]

end

end Erdos207
