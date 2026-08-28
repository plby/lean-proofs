import Wikipedia.NoExoticSixSphere.ManifoldCompactSupportDuality

/-!
# Bijectivity of cap with the constructed compact-manifold fundamental class

On a compact manifold the proved compact-support comparison is the
original absolute cohomology equivalence, and the actual compact-support
cap is the original absolute cap. The checked manifold theorem therefore
proves bijectivity of cap with the constructed global fundamental class.
No geometric-intersection or framed-bordism comparison is asserted here.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.ManifoldCapMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]

/-- The original absolute cap factors through the proved compact-support equivalence. -/
theorem dualityMap_eq_compactSupport (p q : ℕ) (h : p + q = n + 3) :
    dualityMap (E := E) n M p q h =
      (CompactSupportCapMap.dualityMap (E := E) n M p q h).comp
        (CompactSupportCohomology.absoluteEquiv M p).symm.toLinearMap := by
  apply LinearMap.ext
  intro a
  have he := CompactSupportCapMap.dualityMap_eq_absolute (E := E) n M p q h
    ((CompactSupportCohomology.absoluteEquiv M p).symm a)
  rw [LinearEquiv.apply_symm_apply] at he
  exact he.symm

/-- Cap with the original global fundamental class is bijective in complementary degrees. -/
theorem dualityMap_bijective (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (dualityMap (E := E) n M p q h) := by
  rw [dualityMap_eq_compactSupport]
  exact (CompactSupportCapMap.manifold_bijective (E := E) n M p q h).comp
    (CompactSupportCohomology.absoluteEquiv M p).symm.bijective

/-- The actual global cap map equipped with the inverse supplied by its proved bijectivity. -/
def dualityEquiv (p q : ℕ) (h : p + q = n + 3) :
    ModTwoCapProduct.Cohomology M p ≃ₗ[ℤ] ModHomology 2 M q :=
  LinearEquiv.ofBijective (dualityMap (E := E) n M p q h)
    (dualityMap_bijective (E := E) n M p q h)

theorem dualityEquiv_toLinearMap (p q : ℕ) (h : p + q = n + 3) :
    (dualityEquiv (E := E) n M p q h).toLinearMap = dualityMap (E := E) n M p q h := rfl

end NoExoticSixSphere.ManifoldCapMap
