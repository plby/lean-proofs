import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangGeometry
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangNorm
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangShear

/-!
# The actual elliptic cap-circle Wang transfer in degrees one and two

The native twist-circle shear fixes the genuine positive-circle cross
classes.  Combining that proved singular-homology fact with the literal
covering square computes the cap-circle Wang map on all original covering
torus classes, with no assumed transfer or norm formula.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology

/-- The original twist-circle character is additive on the actual quotient torus. -/
theorem twistCircleCharacter_add (j : Kind) (x y : RealTorus₄) :
    twistCircleCharacter j (x + y) = twistCircleCharacter j x + twistCircleCharacter j y := by
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective y
  rw [← map_add, twistCircleCharacter_apply, twistCircleCharacter_apply,
    twistCircleCharacter_apply, splitFlatTorusHomeomorph_mkQ,
    splitFlatTorusHomeomorph_mkQ, splitFlatTorusHomeomorph_mkQ]
  simp only [map_add, Prod.fst_add, AddCircle.coe_add]

/-- The native shear is literally the shear used in the genuine homology calculation. -/
theorem nativeShear_eq_realShear (j : Kind) :
    nativeShear j =
      BoundaryEllipticCapKernelWangShear.realShear (twistCircleCharacter j) := rfl

/-- The actual native shear fixes the positive-circle summand in the two required degrees. -/
theorem nativeShear_positiveCircleCross (j : Kind) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (nativeShear j) (n + 1) (positiveCircleCross RealTorus₄ n a) =
      positiveCircleCross RealTorus₄ n a := by
  rw [nativeShear_eq_realShear]
  exact BoundaryEllipticCapKernelWangShear.realShear_positiveCircleCross
    (twistCircleCharacter j) (twistCircleCharacter_add j) n hn a

/-- On every original covering-torus class, the actual cap-circle Wang map is
the already calculated original affine norm. -/
theorem crossWang_surfaceCover (j : Kind) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (a : SingularHomology RealTorus₄ n) :
    crossWang j n (singularHomologyMap (surfaceCover j) n a) = originalAffineNorm j n a :=
  crossWang_surfaceCover_of_shear j n a (nativeShear_positiveCircleCross j n hn a)

theorem crossWang_surfaceCover_one (j : Kind) (a : SingularHomology RealTorus₄ 1) :
    crossWang j 1 (singularHomologyMap (surfaceCover j) 1 a) = originalAffineNorm j 1 a :=
  crossWang_surfaceCover j 1 (Or.inl rfl) a

theorem crossWang_surfaceCover_two (j : Kind) (a : SingularHomology RealTorus₄ 2) :
    crossWang j 2 (singularHomologyMap (surfaceCover j) 2 a) = originalAffineNorm j 2 a :=
  crossWang_surfaceCover j 2 (Or.inr rfl) a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
