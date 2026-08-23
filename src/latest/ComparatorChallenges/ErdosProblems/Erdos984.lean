import Mathlib

noncomputable section


namespace Erdos984

open scoped Classical in
def IsMonochromaticAP (color : ℕ → Bool) (a d k : ℕ) : Prop :=
  ∃ b : Bool, ∀ i < k, color (a + i * d) = b

end Erdos984

namespace Erdos984

open scoped Classical in
def Erdos984Statement : Prop :=
  ∃ color : ℕ → Bool, ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, 0 < A ∧ ∀ a d k : ℕ,
      0 < a → 0 < d → IsMonochromaticAP color a d k →
        (k : ℝ) ≤ A * (a : ℝ) ^ ε

end Erdos984

namespace Erdos984

open scoped Classical in
theorem erdos_984 : Erdos984Statement := by
  sorry

end Erdos984

end
