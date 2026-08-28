import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspCentralizer
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspCoordinates

/-!
# Actual cusp Wang classes and their source-generator coordinates

The native mapping-torus monodromy is the actual triangle cusp action.
Its Wang boundary is therefore fixed by that action.  The exact source
word and the proved geometric cusp centralizer control the two inverse
generator coordinates without supplying a homology matrix as an input.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle Homology
open SingularMayerVietoris PeriodTorusHigherHomology ThreefoldOverlapMappingTorus.Cusp

/-- The actual native monodromy induces the actual source cusp action in every degree. -/
theorem monodromyHomology_triangle (n : ℕ) :
    singularHomologyMap (monodromy : C(RealTorus₄, RealTorus₄)) n =
      (triangleHomologyEquiv triangleCuspGenerator n).toLinearMap := by
  have hm : monodromy = triangleTorusHomeomorph triangleCuspGenerator := by
    simpa only [zpow_one] using (triangleTorusHomeomorph_cusp_zpow (1 : ℤ)).symm
  rw [hm]
  rfl

/-- Exactness puts every genuine Wang-boundary class in the actual cusp-invariant subgroup. -/
theorem wangBoundary_generator_fixed (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus monodromy) (n + 1)) :
    triangleHomologyEquiv triangleCuspGenerator n
        (MappingTorusHomology.wangBoundary monodromy n a) =
      MappingTorusHomology.wangBoundary monodromy n a := by
  have hb : MappingTorusHomology.wangBoundary monodromy n a ∈
      LinearMap.ker (MappingTorusHomology.wangDifference monodromy n) := by
    rw [← MappingTorusHomology.wangBoundary_range]
    exact ⟨a, rfl⟩
  have he := LinearMap.mem_ker.mp hb
  change MappingTorusHomology.wangBoundary monodromy n a -
    singularHomologyMap (monodromy : C(RealTorus₄, RealTorus₄)) n
      (MappingTorusHomology.wangBoundary monodromy n a) = 0 at he
  rw [monodromyHomology_triangle] at he
  exact (sub_eq_zero.mp he).symm

/-- The exact cusp word removes the second inverse-generator action
after the first on an actual Wang-boundary class. -/
theorem wangBoundary_inverse_word (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus monodromy) (n + 1)) :
    (generatorHomologyEquiv true n).symm
        (triangleHomologyEquiv triangleGenerator₁⁻¹ n
          (MappingTorusHomology.wangBoundary monodromy n a)) =
      MappingTorusHomology.wangBoundary monodromy n a := by
  have he := wangBoundary_generator_fixed n a
  rw [triangleCuspGenerator, mul_inv_rev, triangleHomologyEquiv_mul_apply,
    triangleHomologyEquiv_inv] at he
  exact he

/-- A geometrically established commuting tail fixes the native Wang class. -/
theorem commutingFrame_inv_wangBoundary (g : TriangleGroup)
    (hg : Commute triangleCuspGenerator g) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus monodromy) (n + 1)) :
    triangleHomologyEquiv g⁻¹ n (MappingTorusHomology.wangBoundary monodromy n a) =
      MappingTorusHomology.wangBoundary monodromy n a :=
  cuspCentralizer_inv_homology_fixed g hg n _ (wangBoundary_generator_fixed n a)

/-- The full common column frame retains its first-generator factor;
only the proved commuting tail disappears on actual Wang classes. -/
theorem commutingColumnFrame_inv_wangBoundary (g : TriangleGroup)
    (hg : Commute triangleCuspGenerator g) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus monodromy) (n + 1)) :
    triangleHomologyEquiv (g * triangleGenerator₁)⁻¹ n
        (MappingTorusHomology.wangBoundary monodromy n a) =
      triangleHomologyEquiv triangleGenerator₁⁻¹ n
        (MappingTorusHomology.wangBoundary monodromy n a) := by
  rw [mul_inv_rev, triangleHomologyEquiv_mul_apply, commutingFrame_inv_wangBoundary g hg]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
