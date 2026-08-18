import ErdosProblems.Erdos140.BalancedRestrictionAssembly

/-!
# Balanced restriction with two Bohr geometries

The balanced function is formed relative to a baseline rank-regular Bohr
carrier `K`, because that is the carrier containing `A` and hence the one
whose reciprocal cardinality is the main term in localized unbalancing.
The convolution-comparison norm, however, may be taken on a second
rank-regular Bohr carrier `W`.  The same smoothing sets `D,E` are assumed
small for the geometry of `W`, while their autocorrelation weight is assumed
supported in the narrow dilate of `K` required by localized unbalancing.

This is the form needed downstream when the uniform norm and the density
baseline live on different regular Bohr sets.
-/

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal Pointwise mu

namespace Erdos140
namespace TwoBohrBalanced

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- Two-Bohr version of the concrete balanced-restriction contradiction.

The baseline `K` controls the balanced function, main term, and localized
unbalancing boundary estimate.  The second Bohr datum `W` controls only the
outer probability weight in the convolution comparison.  Thus the conclusion
is a `W`-weighted norm, but its scale is the correct baseline
`1 / |K|`. -/
theorem balanced_of_two_bohr_concrete_stopping
    {K W : BohrData G}
    (hKreg : K.IsRankRegular)
    (hWreg : W.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAK : A ⊆ K.carrier)
    {eta : ℝ≥0} (heta : 0 < eta)
    (hnarrowW : 4 * eta ≤
      1 / (400 * (max W.rank 1 : ℕ) : ℝ≥0))
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    (hDsmallW : D ⊆ (W.dilate eta).carrier)
    (hEsmallW : E ⊆ (W.dilate eta).carrier)
    {kappa : ℝ≥0}
    (hkappaK : kappa ≤ 1 / (100 * (max K.rank 1 : ℕ) : ℝ≥0))
    (hsupportK : ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (K.dilate kappa).carrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hwidthK :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
        (K.carrier.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
        epsilon / 8 * (K.carrier.card : ℝ)⁻¹)
    {p : ℕ} (hp : 0 < p)
    (hnohigh : ¬
      (1 + epsilon / 8) * (K.carrier.card : ℝ)⁻¹ ≤
        BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          (μ_[ℝ] A ○ᵈ μ A)
          (BalancedRestriction.stoppingExponent epsilon p)) :
    BalancedRestriction.weightedLpNorm (normalizedIndicator W.carrier)
        (normalizedConvolution
          (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier)) p ≤
      epsilon * (K.carrier.card : ℝ)⁻¹ := by
  let a : G → ℝ := μ_[ℝ] A - μ K.carrier
  have hq : 0 < BalancedRestriction.comparisonExponent p := by
    exact Nat.mul_pos (by norm_num) hp
  have hcomparison :=
    BalancedRestrictionAssembly.concrete_comparison_lp hWreg heta hnarrowW
      hD hE hDsmallW hEsmallW hq
      (BalancedRestriction.comparisonExponent_even p) a
  rw [BalancedRestrictionAssembly.normalizedDifferenceConvolution_eq_dddconv]
    at hcomparison
  apply BalancedRestrictionAssembly.balanced_of_localized_unbalancing
      hKreg hA hAK hD hE hkappaK hsupportK
      hepsilon hepsilon_one hwidthK hp
      ⟨normalizedIndicator_nonneg W.carrier,
        sum_normalizedIndicator W.carrier_nonempty⟩
  · simpa [a] using hcomparison
  · exact lt_of_not_ge hnohigh

#print axioms balanced_of_two_bohr_concrete_stopping

end
end TwoBohrBalanced
end Erdos140
