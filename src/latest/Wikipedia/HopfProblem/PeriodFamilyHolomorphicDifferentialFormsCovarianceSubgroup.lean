import Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialFormsCovariance

/-!
# The full local subgroup-invariant statement of Lemma 9.15

For every open base and every subgroup preserving it, the same actual
holomorphic coefficient functions give both the full local normal form
and the source's covariance equations. The only invariance premise is
invariance of the genuine local form under actual native-family pullback.
Neither coefficient laws nor a normal-form representation are premises.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms.Covariance

open SpecialPeriods

attribute [local instance] familyChartedSpace coverChartedSpace family_isManifold cover_isManifold

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

variable (U : TopologicalSpace.Opens UpperHalfPlane)

/-- Lemma 9.15(a) and all three equations (9.8), simultaneously for an
arbitrary subgroup and arbitrary genuine invariant local one-form. -/
theorem oneForm_subgroup_normal_form (G : Subgroup TriangleGroup)
    (hU : ∀ g : G, Preserves U (g : TriangleGroup)) (θ : Form U 1)
    (hθ : ∀ g : G, IsInvariant U θ (g : TriangleGroup) (hU g)) :
    ∃ a : U → ℂ, ∃ c : U → ComplexPlane₂,
      ContMDiff I₁ I₁ ω a ∧ ContMDiff I₁ I₂ ω c ∧
      (∀ z ζ u, coverPullback U θ (z, ζ) ![u] =
        a z * u.1 + dotProduct (c z) u.2) ∧
      (∀ z ℓ, dotProduct (c z)
        (PeriodFamilyHolomorphicForms.periodDerivative specialPeriodMap z.val ℓ) = 0) ∧
      ∀ (g : G) (z : U),
        c (baseMap U g (hU g) z) ᵥ* rightBlock U g z = c z ∧
        a (baseMap U g (hU g) z) * baseDerivative U g (hU g) z = a z ∧
        c (baseMap U g (hU g) z) ᵥ* rightBlockDerivative U g z = 0 := by
  refine ⟨baseOne U θ, fibreOne U θ, baseOne_holomorphic U θ,
    fibreOne_holomorphic U θ, oneForm_evaluation U θ, fibreOne_periodDerivative U θ, ?_⟩
  intro g z
  exact oneForm_covariance U θ g (hU g) (hθ g) z

/-- Lemma 9.15(b) and equation (9.9) for every subgroup preserving the
open base, with no extra period or derivative condition on the local form. -/
theorem twoForm_subgroup_normal_form (G : Subgroup TriangleGroup)
    (hU : ∀ g : G, Preserves U (g : TriangleGroup)) (θ : Form U 2)
    (hθ : ∀ g : G, IsInvariant U θ (g : TriangleGroup) (hU g)) :
    ∃ b : U → ComplexPlane₂, ContMDiff I₁ I₂ ω b ∧
      (∀ z ζ u v, coverPullback U θ (z, ζ) ![u, v] =
        u.1 * dotProduct (b z) v.2 - v.1 * dotProduct (b z) u.2) ∧
      ∀ (g : G) (z : U), baseDerivative U g (hU g) z •
        (b (baseMap U g (hU g) z) ᵥ* rightBlock U g z) = b z := by
  refine ⟨mixedTwo U θ, mixedTwo_holomorphic U θ, twoForm_evaluation U θ, ?_⟩
  intro g z
  exact twoForm_covariance U θ g (hU g) (hθ g) z

/-- Lemma 9.15(c) and equation (9.10), using the actual restricted base
Jacobian and the original all-word period right-block determinant. -/
theorem threeForm_subgroup_normal_form (G : Subgroup TriangleGroup)
    (hU : ∀ g : G, Preserves U (g : TriangleGroup)) (θ : Form U 3)
    (hθ : ∀ g : G, IsInvariant U θ (g : TriangleGroup) (hU g)) :
    ∃ c : U → ℂ, ContMDiff I₁ I₁ ω c ∧
      (∀ z ζ u v w, coverPullback U θ (z, ζ) ![u, v, w] =
        c z * PeriodFamilyHolomorphicForms.coordinateVolume u v w) ∧
      ∀ (g : G) (z : U), c (baseMap U g (hU g) z) * baseDerivative U g (hU g) z *
        (rightBlock U g z).det = c z := by
  refine ⟨baseTop U θ, baseTop_holomorphic U θ, threeForm_evaluation U θ, ?_⟩
  intro g z
  exact threeForm_covariance U θ g (hU g) (hθ g) z

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms.Covariance
