import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos581.UpperBlock

abbrev F (t : ℕ) := GaloisField 2 (t + 1)

end Erdos581.UpperBlock

namespace Erdos581.UpperBlock

abbrev V (t : ℕ) := Fin 3 → F t

end Erdos581.UpperBlock

namespace Erdos581

def Guarantees (m k : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.CliqueFree 3 → G.edgeSet.ncard = m →
      ∃ H : SimpleGraph V,
        H ≤ G ∧ H.IsBipartite ∧ k ≤ H.edgeSet.ncard

end Erdos581

namespace Erdos581

noncomputable def f (m : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (Guarantees m) m

end Erdos581

namespace Erdos581

theorem erdos581 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ m : ℕ,
        (m : ℝ) / 2 + c₁ * (m : ℝ) ^ ((4 : ℝ) / 5) ≤ (f m : ℝ) ∧
        (f m : ℝ) ≤ (m : ℝ) / 2 + c₂ * (m : ℝ) ^ ((4 : ℝ) / 5) := by
  sorry

end Erdos581

end
