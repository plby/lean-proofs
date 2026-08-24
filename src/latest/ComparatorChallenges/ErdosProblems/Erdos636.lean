/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos88

universe u

def HomogeneousFree {n : ℕ} (ε : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n),
    (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) →
      (S.card : ℝ) < ε * Real.log n

noncomputable def inducedEdges {V : Type u} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).edgeSet

end Erdos88

namespace Erdos636

noncomputable def inducedProfile {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ × ℕ :=
  (S.card, Erdos88.inducedEdges G S)

def IsProfileInjectiveFamily {n : ℕ} (G : SimpleGraph (Fin n))
    (F : Finset (Finset (Fin n))) : Prop :=
  Set.InjOn (inducedProfile G) (F : Set (Finset (Fin n)))

theorem erdos_636 (C : ℝ) (hC : 0 < C) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), Erdos88.HomogeneousFree C G →
        ∃ F : Finset (Finset (Fin n)),
          IsProfileInjectiveFamily G F ∧
            γ * (n : ℝ) ^ 2 * Real.sqrt n ≤ (F.card : ℝ) := by
  sorry

end Erdos636
