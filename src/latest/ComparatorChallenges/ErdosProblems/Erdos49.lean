import Mathlib

open Filter Set Topology

noncomputable section


namespace Erdos49

open scoped Classical in
def TotientStrictOn (A : Finset ℕ) : Prop :=
  ∀ ⦃m⦄, m ∈ A → ∀ ⦃n⦄, n ∈ A → m < n →
    Nat.totient m < Nat.totient n

end Erdos49

namespace Erdos49

open scoped Classical in
def strictFamilies (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter (TotientStrictOn ·)

end Erdos49

namespace Erdos49

open scoped Classical in
def strictMaximum (N : ℕ) : ℕ :=
  (strictFamilies N).sup Finset.card

end Erdos49

namespace Erdos49

open scoped Classical in
theorem erdos_49_density_zero :
    (fun N : ℕ ↦ (strictMaximum N : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  sorry

end Erdos49

end
