/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos21

def IsUniform {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A.card = n

def IsIntersecting {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty

def AvoidsAllSmallSets {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ S : Finset α, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

def IsErdosLovaszFamily {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  IsUniform n F ∧ IsIntersecting F ∧ AvoidsAllSmallSets n F

noncomputable def erdosLovaszF (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily n F ∧ F.card = m}

theorem erdos_21 :
    ∃ C N : ℕ, ∀ n : ℕ, N ≤ n → erdosLovaszF n ≤ C * n := by
  sorry

end Erdos21
