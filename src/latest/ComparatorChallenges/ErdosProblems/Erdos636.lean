import Mathlib

open Classical SimpleGraph
open MeasureTheory ProbabilityTheory

noncomputable section


namespace Erdos88

universe u

open scoped Classical in
def HomogeneousFree {n : ℕ} (ε : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n),
    (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) →
      (S.card : ℝ) < ε * Real.log n

open scoped Classical in
noncomputable def inducedEdges {V : Type u} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).edgeSet

end Erdos88

namespace Erdos636

open scoped Classical in
noncomputable def inducedProfile {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ × ℕ :=
  (S.card, Erdos88.inducedEdges G S)

end Erdos636

namespace Erdos636

open scoped Classical in
def IsProfileInjectiveFamily {n : ℕ} (G : SimpleGraph (Fin n))
    (F : Finset (Finset (Fin n))) : Prop :=
  Set.InjOn (inducedProfile G) (F : Set (Finset (Fin n)))

end Erdos636

namespace Erdos636

open scoped Classical in
theorem erdos636 (C : ℝ) (hC : 0 < C) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), Erdos88.HomogeneousFree C G →
        ∃ F : Finset (Finset (Fin n)),
          IsProfileInjectiveFamily G F ∧
            γ * (n : ℝ) ^ 2 * Real.sqrt n ≤ (F.card : ℝ) := by
  sorry

end Erdos636

end
