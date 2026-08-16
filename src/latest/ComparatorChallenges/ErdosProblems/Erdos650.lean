import Mathlib

namespace Erdos650

set_option linter.style.setOption false
set_option linter.flexible false

open Finset Real Nat

def HasDivMatching (A : Finset ℕ) (B : Finset ℤ) (r : ℕ) : Prop :=
  ∃ (c : Fin r → ℕ) (b : Fin r → ℤ),
    Function.Injective c ∧ Function.Injective b ∧
    (∀ i, c i ∈ A) ∧ (∀ i, b i ∈ B) ∧
    (∀ i, (c i : ℤ) ∣ b i)

noncomputable def erdos_f (m : ℕ) : ℕ :=
  sSup { r : ℕ | ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) → A.card = m →
    ∀ (x : ℝ), HasDivMatching A (Finset.Ioo ⌊x⌋ ⌈x + 2 * ↑(A.sup id)⌉) r }
end Erdos650

attribute [local instance] Classical.propDecidable

open Finset Real Nat

namespace Erdos650

theorem erdos_f_eq (m : ℕ) (hm : 0 < m) :
    erdos_f m = min m ⌈(2 : ℝ) * Real.sqrt ↑m⌉₊ := by
  sorry

end Erdos650
