import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryOrientation
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyGeneratorActions
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTranslations
import Wikipedia.HopfProblem.MappingTorusHomology

/-!
# The actual elliptic tail frames on invariant singular homology

The original affine torus monodromy is identified pointwise with the
original triangle linear action followed by its actual translation.
Homotopy invariance then identifies their singular-homology maps in all
degrees.  The geometrically constructed tail frame, already proved to be
a power of the same generator, fixes the actual Wang-boundary classes.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Homology Elliptic
open SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

/-- Composition of the actual triangle homeomorphisms gives composition
of their actual singular-homology maps. -/
theorem triangleHomologyEquiv_mul_apply (g h : TriangleGroup) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    triangleHomologyEquiv (g * h) n a =
      triangleHomologyEquiv g n (triangleHomologyEquiv h n a) := by
  unfold triangleHomologyEquiv
  rw [triangleTorusHomeomorph_mul, homeomorphHomologyEquiv_trans]
  rfl

/-- Every power fixes an actual class fixed by the original generator. -/
theorem triangleHomologyEquiv_pow_fixed (g : TriangleGroup) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) (ha : triangleHomologyEquiv g n a = a) (k : ℕ) :
    triangleHomologyEquiv (g ^ k) n a = a := by
  induction k with
  | zero => rw [pow_zero, triangleHomologyEquiv_one]; rfl
  | succ k ih => rw [pow_succ, triangleHomologyEquiv_mul_apply, ha, ih]

/-- The original matrices act on every real-period representative as
the actual first or second triangle generator. -/
theorem ellipticTriangle_mkQ (j : Kind) (x : RealCoordinates) :
    triangleTorusHomeomorph (ellipticGenerator j) (standardLattice.mkQ x) =
      standardLattice.mkQ (flatLinear j x) := by
  cases j
  · exact triangleTorusAction_generator₁_mkQ x
  · exact triangleTorusAction_generator₂_mkQ x

/-- The original affine map is exactly the triangle map followed by its
specified constant translation on the real period torus. -/
theorem flatTorusAffine_eq_translation_triangle (j : Kind) (v : Lattice) :
    (flatTorusAffine j v : C(RealTorus₄, RealTorus₄)) =
      (rightTranslation (standardLattice.mkQ ((1 / (j.order : ℝ)) • realCast v))).comp
        (triangleTorusHomeomorph (ellipticGenerator j) : C(RealTorus₄, RealTorus₄)) := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  simp only [ContinuousMap.comp_apply, rightTranslation_apply]
  calc
    _ = standardLattice.mkQ (flatAffine j v u) := flatTorusAffine_mkQ j v u
    _ = _ := by
      rw [flatAffine, map_add]
      exact congrArg
        (fun w : RealTorus₄ => w + standardLattice.mkQ ((1 / (j.order : ℝ)) • realCast v))
        (ellipticTriangle_mkQ j u).symm

/-- The literal affine boundary monodromy and the source triangle
generator induce the same actual integral singular-homology map. -/
theorem flatTorusAffine_homology_triangle (j : Kind) (v : Lattice) (n : ℕ) :
    singularHomologyMap (flatTorusAffine j v : C(RealTorus₄, RealTorus₄)) n =
      (triangleHomologyEquiv (ellipticGenerator j) n).toLinearMap := by
  rw [flatTorusAffine_eq_translation_triangle, singularHomologyMap_comp,
    rightTranslation_singularHomologyMap, LinearMap.id_comp]
  rfl

/-- The actual tail frame is trivial on the original generator's
invariant subgroup of actual singular homology. -/
theorem nativeTailFrame_homology_fixed (j : Kind) (n : ℕ)
    (a : SingularHomology RealTorus₄ n)
    (ha : triangleHomologyEquiv (ellipticGenerator j) n a = a) :
    triangleHomologyEquiv (nativeTailFrame j) n a = a := by
  obtain ⟨k, _, hk⟩ := nativeTailFrame_eq_power j
  rw [hk]
  exact triangleHomologyEquiv_pow_fixed (ellipticGenerator j) n a ha k

/-- The inverse frame used by the actual upper-chart coordinates is
also trivial on the same invariant classes. -/
theorem nativeTailFrame_inv_homology_fixed (j : Kind) (n : ℕ)
    (a : SingularHomology RealTorus₄ n)
    (ha : triangleHomologyEquiv (ellipticGenerator j) n a = a) :
    triangleHomologyEquiv (nativeTailFrame j)⁻¹ n a = a := by
  obtain ⟨k, _, hk⟩ := nativeTailFrame_inv_eq_power j
  rw [hk]
  exact triangleHomologyEquiv_pow_fixed (ellipticGenerator j) n a ha k

/-- The actual Wang connecting map lands in the invariant subgroup for
the original source generator, via the proved affine-to-linear equality. -/
theorem ellipticWangBoundary_generator_fixed (j : Kind) (v : Lattice) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus (flatTorusAffine j v)) (n + 1)) :
    triangleHomologyEquiv (ellipticGenerator j) n
        (MappingTorusHomology.wangBoundary (flatTorusAffine j v) n a) =
      MappingTorusHomology.wangBoundary (flatTorusAffine j v) n a := by
  have hb : MappingTorusHomology.wangBoundary (flatTorusAffine j v) n a ∈
      LinearMap.ker (MappingTorusHomology.wangDifference (flatTorusAffine j v) n) := by
    rw [← MappingTorusHomology.wangBoundary_range]
    exact ⟨a, rfl⟩
  have he := LinearMap.mem_ker.mp hb
  change MappingTorusHomology.wangBoundary (flatTorusAffine j v) n a -
    singularHomologyMap (flatTorusAffine j v : C(RealTorus₄, RealTorus₄)) n
      (MappingTorusHomology.wangBoundary (flatTorusAffine j v) n a) = 0 at he
  rw [flatTorusAffine_homology_triangle] at he
  exact (sub_eq_zero.mp he).symm

/-- Thus the actual tail-frame change in the slit coordinate does not
alter any actual elliptic Wang-boundary class, in every degree. -/
theorem nativeTailFrame_inv_wangBoundary (j : Kind) (v : Lattice) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus (flatTorusAffine j v)) (n + 1)) :
    triangleHomologyEquiv (nativeTailFrame j)⁻¹ n
        (MappingTorusHomology.wangBoundary (flatTorusAffine j v) n a) =
      MappingTorusHomology.wangBoundary (flatTorusAffine j v) n a :=
  nativeTailFrame_inv_homology_fixed j n _ (ellipticWangBoundary_generator_fixed j v n a)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
