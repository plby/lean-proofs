import Mathlib

namespace Erdos760

set_option linter.style.setOption false
set_option linter.flexible false

open scoped ENat

namespace SimpleGraph

open _root_.SimpleGraph

def CochromPartable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → Fin n, ∀ i : Fin n, G.IsClique (f ⁻¹' {i}) ∨ G.IsIndepSet (f ⁻¹' {i})

noncomputable def cochromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  ⨅ n ∈ {n : ℕ | CochromPartable G n}, (n : ℕ∞)
end SimpleGraph

end Erdos760



open scoped ENat
open _root_.SimpleGraph

namespace Erdos760.SimpleGraph

open scoped Classical in
theorem erdos_760 : ∃ C : ℕ, 0 < C ∧
    ∀ (V : Type*) [Finite V] (G : SimpleGraph V) (m : ℕ),
      G.chromaticNumber = ↑m → 2 ≤ m →
    ∃ (S : Set V) (H : SimpleGraph S),
      (∀ (u v : S), H.Adj u v → G.Adj ↑u ↑v) ∧
      (m : ℕ∞) ≤ C * Nat.log 2 m * cochromaticNumber H := by
  sorry

end Erdos760.SimpleGraph
