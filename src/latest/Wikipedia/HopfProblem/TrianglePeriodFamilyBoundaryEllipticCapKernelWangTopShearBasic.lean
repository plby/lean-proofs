import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangShearCross

/-!
# Circle shears over arbitrary finite product tori

The map is the literal subtraction in the first circle coordinate. These
definitions retain the native product topology and agree with the previously
constructed four-torus shear.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

open SingularMayerVietoris PeriodTorusHigherHomology CircleTopology

/-- Subtract a continuous circle-valued function on the remaining torus. -/
def shearOn (r : ℕ) (χ : C(ProductTorus r, Circle)) :
    C(Circle × ProductTorus r, Circle × ProductTorus r) :=
  ⟨fun p => (p.1 - χ p.2, p.2),
    (continuous_fst.sub (χ.continuous.comp continuous_snd)).prodMk continuous_snd⟩

@[simp] theorem shearOn_apply (r : ℕ) (χ : C(ProductTorus r, Circle))
    (p : Circle × ProductTorus r) :
    shearOn r χ p = (p.1 - χ p.2, p.2) := rfl

theorem shearOn_four_eq_shear (χ : C(ProductTorus 4, Circle)) : shearOn 4 χ = shear χ := rfl

/-- Fibre maps intertwine the literal shears after restricting the character. -/
theorem shearOn_naturality {r s : ℕ} (f : C(ProductTorus r, ProductTorus s))
    (χ : C(ProductTorus s, Circle)) :
    (circleProductMap f).comp (shearOn r (χ.comp f)) =
      (shearOn s χ).comp (circleProductMap f) := rfl

/-- A circle times an `r`-torus has no actual integral homology above degree `r+1`. -/
theorem circleTorus_homology_subsingleton_of_lt {r n : ℕ} (h : r + 1 < n) :
    Subsingleton (SingularHomology (Circle × ProductTorus r) n) := by
  let := productTorus_homology_subsingleton_of_lt h
  exact (homeomorphHomologyEquiv (productTorusSuccHomeomorph r).symm n).injective.subsingleton

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear
