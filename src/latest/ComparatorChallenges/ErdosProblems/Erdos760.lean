/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos760

namespace SimpleGraph

def CochromPartable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → Fin n, ∀ i : Fin n, G.IsClique (f ⁻¹' {i}) ∨ G.IsIndepSet (f ⁻¹' {i})

noncomputable def cochromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  ⨅ n ∈ {n : ℕ | CochromPartable G n}, (n : ℕ∞)

theorem erdos_760 : ∃ C : ℕ, 0 < C ∧
    ∀ (V : Type*) [Finite V] (G : SimpleGraph V) (m : ℕ),
      G.chromaticNumber = ↑m → 2 ≤ m →
    ∃ (S : Set V) (H : SimpleGraph S),
      (∀ (u v : S), H.Adj u v → G.Adj ↑u ↑v) ∧
      (m : ℕ∞) ≤ C * Nat.log 2 m * cochromaticNumber H := by
  sorry

end SimpleGraph

end Erdos760
