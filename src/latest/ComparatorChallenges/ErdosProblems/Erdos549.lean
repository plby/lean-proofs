/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open SimpleGraph

namespace Erdos549

def HasBipartitionSizes {V : Type*} [Fintype V]
    (T : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ A B : Finset V,
    A.card = k ∧ B.card = 2 * k ∧
      (A : Set V) ∪ (B : Set V) = Set.univ ∧
      T.IsBipartiteWith (A : Set V) (B : Set V)

def GraphRamseyAt {V : Type*} [Fintype V] (T : SimpleGraph V) (N : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W], Fintype.card W = N →
    ∀ H : SimpleGraph W, T ⊑ H ∨ T ⊑ Hᶜ

noncomputable def graphRamseyNumber {V : Type*} [Fintype V]
    (T : SimpleGraph V) : ℕ :=
  sInf {N : ℕ | GraphRamseyAt T N}

/-! ## Double stars -/

theorem not_erdos_549 :
    ¬ (∀ (V : Type) [Fintype V] (T : SimpleGraph V) (k : ℕ),
      T.IsTree → HasBipartitionSizes T k →
        graphRamseyNumber T = 4 * k - 1) := by
  sorry

end Erdos549
