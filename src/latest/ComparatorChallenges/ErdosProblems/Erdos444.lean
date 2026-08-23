import Mathlib

open Filter Set

noncomputable section


namespace Erdos444

open scoped Classical in
noncomputable def positiveBelow (x : ℝ) : Finset ℕ :=
  Finset.Ico 1 ⌈x⌉₊

end Erdos444

namespace Erdos444

open scoped Classical in
noncomputable def divisorCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact (n.divisors.filter fun d ↦ d ∈ A).card

end Erdos444

namespace Erdos444

open scoped Classical in
noncomputable def maxDivisorCount (A : Set ℕ) (x : ℝ) : ℕ :=
  (positiveBelow x).sup (divisorCount A)

end Erdos444

namespace Erdos444

open scoped Classical in
noncomputable def reciprocalMass (A : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ a ∈ (positiveBelow x).filter (fun a ↦ a ∈ A), (a : ℝ)⁻¹

end Erdos444

namespace Erdos444

open scoped Classical in
noncomputable def ratio (A : Set ℕ) (k : ℕ) (x : ℝ) : ℝ :=
  (maxDivisorCount A x : ℝ) / (reciprocalMass A x) ^ k

end Erdos444

namespace Erdos444

open scoped Classical in
theorem erdos_444 : True ↔
    ∀ (A : Set ℕ), A.Infinite → ∀ k : ℕ,
      atTop.limsup (fun x : ℝ ↦ (ratio A k x : EReal)) = ⊤ := by
  sorry

end Erdos444

end
