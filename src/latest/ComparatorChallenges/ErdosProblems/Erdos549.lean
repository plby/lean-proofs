import Mathlib

open Finset SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos549

def HasBipartitionSizes {V : Type*} [Fintype V]
    (T : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ A B : Finset V,
    A.card = k ∧ B.card = 2 * k ∧
      (A : Set V) ∪ (B : Set V) = Set.univ ∧
      T.IsBipartiteWith (A : Set V) (B : Set V)

end Erdos549

namespace Erdos549

def GraphRamseyAt {V : Type*} [Fintype V] (T : SimpleGraph V) (N : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W], Fintype.card W = N →
    ∀ H : SimpleGraph W, T ⊑ H ∨ T ⊑ Hᶜ

end Erdos549

namespace Erdos549

noncomputable def graphRamseyNumber {V : Type*} [Fintype V]
    (T : SimpleGraph V) : ℕ :=
  sInf {N : ℕ | GraphRamseyAt T N}

end Erdos549

namespace Erdos549

def Erdos549Statement : Prop :=
  ∀ (V : Type) [Fintype V] (T : SimpleGraph V) (k : ℕ),
    T.IsTree → HasBipartitionSizes T k →
      graphRamseyNumber T = 4 * k - 1

/-! ## Double stars -/

end Erdos549

namespace Erdos549

theorem erdos_549 : ¬Erdos549Statement := by
  sorry

end Erdos549

end
