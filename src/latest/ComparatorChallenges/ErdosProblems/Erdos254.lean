import Mathlib

open Filter Set
open scoped BigOperators Topology

namespace Erdos254

def IsSumOfDistinct (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ ∑ x ∈ S, x = n

def IsComplete (A : Set ℕ) : Prop := ∀ᶠ n in atTop, IsSumOfDistinct A n

def IsStronglyComplete (A : Set ℕ) : Prop :=
  ∀ D : Finset ℕ, IsComplete (A \ (D : Set ℕ))

noncomputable def distToNearestInt (x : ℝ) : ℝ := ‖(x : UnitAddCircle)‖

/-- Six elements per dyadic block and phase divergence imply strong completeness. -/
theorem fan_six_per_dyadic (A : Set ℕ)
    (hcount : ∀ᶠ k in atTop, 6 ≤ (A ∩ Ioc (2 ^ k) (2 ^ (k + 1))).ncard)
    (hdiv : ∀ θ : ℝ, θ ∉ Set.range (fun z : ℤ ↦ (z : ℝ)) →
      ¬ Summable (fun a : A ↦ distToNearestInt ((a : ℝ) * θ))) :
    IsStronglyComplete A := by
  sorry

/-- Every sufficiently large integer is a sum of distinct elements. -/
theorem erdos_254 (A : Set ℕ)
    (hcount : Tendsto (fun x : ℕ ↦
      (A ∩ Icc 1 (2 * x)).ncard - (A ∩ Icc 1 x).ncard) atTop atTop)
    (hdiv : ∀ θ : ℝ, 0 < θ → θ < 1 →
      ¬ Summable (fun a : A ↦ distToNearestInt (θ * (a : ℝ)))) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧ ∑ a ∈ F, a = n := by
  sorry

end Erdos254
