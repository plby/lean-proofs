import ErdosProblems.Erdos520.LargestPrimeDecomposition
import ErdosProblems.Erdos520.SmoothContribution
import ErdosProblems.Erdos520.CaichConcentration

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Reassembling the two squarefree Rademacher pieces at test points

The squareful largest-prime remainder is identically absent in this model.
Thus the smooth contribution and the stopped largest-prime martingale are
the only two terms to combine.
-/

/-- Deterministic triangle-inequality form of the exact largest-prime
decomposition. -/
theorem abs_partialSum_le_smooth_add_largestPrimeMain
    (omega : Omega) {x y₀ : ℕ} (hy₀x : y₀ ≤ x) :
    |partialSum omega x| ≤
      |Ψ omega x y₀| + |largestPrimeMain omega x y₀ x| := by
  rw [partialSum_eq_smooth_add_largestPrimeMain omega x y₀ hy₀x]
  exact abs_add_le _ _

/-- If both pieces are bounded by the same test-point threshold, the full
partial sum is bounded by twice that threshold. -/
theorem abs_partialSum_le_two_mul_of_pieces
    (omega : Omega) {x y₀ : ℕ} {u : ℝ} (hy₀x : y₀ ≤ x)
    (hsmooth : |Ψ omega x y₀| ≤ u)
    (hmain : |largestPrimeMain omega x y₀ x| < u) :
    |partialSum omega x| ≤ 2 * u := by
  calc
    |partialSum omega x| ≤
        |Ψ omega x y₀| + |largestPrimeMain omega x y₀ x| :=
      abs_partialSum_le_smooth_add_largestPrimeMain omega hy₀x
    _ ≤ u + u := add_le_add hsmooth hmain.le
    _ = 2 * u := by ring

/-- Almost-sure eventual assembly, simultaneously over every finite test
family at each scale. -/
theorem ae_eventually_partialSum_testPoints_le_two_mul
    (tests : ℕ → Finset ℕ) (x y₀ : ℕ → ℕ → ℕ)
    (u : ℕ → ℕ → ℝ)
    (hy₀x : ∀ ell r, r ∈ tests ell → y₀ ell r ≤ x ell r)
    (hsmooth : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        |Ψ omega (x ell r) (y₀ ell r)| ≤ u ell r)
    (hmain : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        |largestPrimeMain omega
          (x ell r) (y₀ ell r) (x ell r)| < u ell r) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        |partialSum omega (x ell r)| ≤ 2 * u ell r := by
  filter_upwards [hsmooth, hmain] with omega hsmoothOmega hmainOmega
  filter_upwards [hsmoothOmega, hmainOmega] with ell hsmoothEll hmainEll
  intro r hr
  exact abs_partialSum_le_two_mul_of_pieces omega (hy₀x ell r hr)
    (hsmoothEll r hr) (hmainEll r hr)

end Problem520
end Erdos
