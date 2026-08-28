import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductMarked
import Wikipedia.HopfProblem.MappingTorusHomologyCovering

/-!
# The genuine covering square for the elliptic cap-circle summand

The inverse cap-product homeomorphism, pulled back through the original
finite torus-to-surface covering, is the actual finite mapping-torus
covering after a circle shear.  This identity retains the original affine
torus map, the native cap surface, and the positive circle convention.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods.EllipticFilling
open ThreefoldOverlapMappingTorus.Elliptic EllipticCapProduct
open MappingTorusHomology

local notation "B" => ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary
local notation "S" => ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface

/-- The original finite affine quotient, with its original flat period coordinates. -/
def surfaceCover (j : Kind) : C(RealTorus₄, S j) :=
  (specialBoundaryToCentral j).comp
    (MappingTorus.HomologyCover.fibreInclusion (flatTorusAffine j j.twist))

theorem surfaceCover_apply (j : Kind) (x : RealTorus₄) :
    surfaceCover j x =
      surfaceProjection j (specialLocalData j).centralPeriod j.twist
        (mainTwist_admissible j)
        (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val x) :=
  specialBoundaryToCentral_mk j 0 x

/-- The twist-circle character of the actual flat torus. -/
def twistCircleCharacter (j : Kind) : C(RealTorus₄, MappingTorus.Circle) where
  toFun x := (splitFlatTorusHomeomorph j x).1
  continuous_toFun := continuous_fst.comp (splitFlatTorusHomeomorph j).continuous

@[simp] theorem twistCircleCharacter_apply (j : Kind) (x : RealTorus₄) :
    twistCircleCharacter j x = (splitFlatTorusHomeomorph j x).1 := rfl

/-- The covering-space circle shear, before taking either quotient. -/
def nativeShear (j : Kind) :
    C(MappingTorus.Circle × RealTorus₄, MappingTorus.Circle × RealTorus₄) where
  toFun p := (p.1 - twistCircleCharacter j p.2, p.2)
  continuous_toFun :=
    (continuous_fst.sub ((twistCircleCharacter j).continuous.comp continuous_snd)).prodMk
      continuous_snd

@[simp] theorem nativeShear_apply (j : Kind)
    (c : MappingTorus.Circle) (x : RealTorus₄) :
    nativeShear j (c, x) = (c - twistCircleCharacter j x, x) := rfl

/-- The actual finite cyclic covering of the native positive-monodromy boundary. -/
def nativeProductCover (j : Kind) : C(MappingTorus.Circle × RealTorus₄, B j) :=
  Covering.productCover j.order (flatTorusAffine j j.twist).symm
    (affine_symm_pow_order j j.twist j.matrix_fixes_twist)

theorem nativeProductCover_real_apply (j : Kind) (t : ℝ) (x : RealTorus₄) :
    nativeProductCover j ((t : MappingTorus.Circle), x) =
      MappingTorus.mk (flatTorusAffine j j.twist) (t * j.order, x) :=
  Covering.productCover_real_apply j.order (flatTorusAffine j j.twist).symm
    (affine_symm_pow_order j j.twist j.matrix_fixes_twist) t x

/-- The exact cap-product coordinates of the original mapping-torus representative. -/
theorem boundaryCircleFirstHomeomorph_mk (j : Kind) (t : ℝ) (x : RealTorus₄) :
    boundaryCircleFirstHomeomorph j
        (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      (twistCircleCharacter j x + ((t / j.order : ℝ) : MappingTorus.Circle),
        surfaceCover j x) := by
  change Prod.swap (boundaryProductHomeomorph j
    (MappingTorus.mk (flatTorusAffine j j.twist) (t, x))) = _
  rw [boundaryProductHomeomorph_mk]
  apply Prod.ext
  · rfl
  · exact specialBoundaryToCentral_angle j t 0 x

/-- On every actual circle and torus point, the two genuine covering constructions agree. -/
theorem nativeProductCover_shear_apply (j : Kind)
    (c : MappingTorus.Circle) (x : RealTorus₄) :
    nativeProductCover j (nativeShear j (c, x)) =
      (boundaryCircleFirstHomeomorph j).symm (c, surfaceCover j x) := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (c - twistCircleCharacter j x)
  apply (boundaryCircleFirstHomeomorph j).injective
  rw [Homeomorph.apply_symm_apply]
  change boundaryCircleFirstHomeomorph j
    (nativeProductCover j (c - twistCircleCharacter j x, x)) = _
  rw [← ht, nativeProductCover_real_apply, boundaryCircleFirstHomeomorph_mk]
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast j.order_pos.ne'
  rw [mul_div_cancel_right₀ _ hm, ht]
  exact Prod.ext (add_sub_cancel _ _) rfl

/-- The literal continuous-map square, not an assigned homology comparison. -/
theorem nativeProductCover_comp_shear (j : Kind) :
    (nativeProductCover j).comp (nativeShear j) =
      ((boundaryCircleFirstHomeomorph j).symm : C(_, _)).comp
        (circleProductMap (surfaceCover j)) := by
  apply ContinuousMap.ext
  rintro ⟨c, x⟩
  exact nativeProductCover_shear_apply j c x

/-- The actual Wang map restricted to the genuine positive cap-circle summand. -/
def crossWang (j : Kind) (n : ℕ) :
    SingularHomology (S j) n →ₗ[ℤ] SingularHomology RealTorus₄ n :=
  (wangBoundary (flatTorusAffine j j.twist) n).comp (boundaryPositiveCircleCross j n)

@[simp] theorem crossWang_apply (j : Kind) (n : ℕ) (a : SingularHomology (S j) n) :
    crossWang j n a =
      wangBoundary (flatTorusAffine j j.twist) n (boundaryPositiveCircleCross j n a) := rfl

/-- The inverse of the original cap-kernel isomorphism has exactly this Wang map. -/
theorem wangBoundary_capKernel_symm (j : Kind) (n : ℕ)
    (a : SingularHomology (S j) n) :
    wangBoundary (flatTorusAffine j j.twist) n
        ((boundaryCapKernelEquiv j n).symm a).val = crossWang j n a := rfl

/-- A shear-invariant cross class is sent by the original covering square to
the actual finite monodromy norm. -/
theorem crossWang_surfaceCover_of_shear (j : Kind) (n : ℕ)
    (a : SingularHomology RealTorus₄ n)
    (ha : singularHomologyMap (nativeShear j) (n + 1)
      (positiveCircleCross RealTorus₄ n a) = positiveCircleCross RealTorus₄ n a) :
    crossWang j n (singularHomologyMap (surfaceCover j) n a) =
      Covering.homologyNorm j.order (flatTorusAffine j j.twist).symm n a := by
  rw [crossWang_apply, boundaryPositiveCircleCross_apply,
    ← positiveCircleCross_naturality]
  have hmap := congrArg
    (fun f : C(MappingTorus.Circle × RealTorus₄, B j) => singularHomologyMap f (n + 1))
    (nativeProductCover_comp_shear j)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at hmap
  have hc := LinearMap.congr_fun hmap (positiveCircleCross RealTorus₄ n a)
  simp only [LinearMap.comp_apply, ha] at hc
  rw [← hc]
  exact Covering.wangBoundary_productCover_positiveCircleCross j.order
    (flatTorusAffine j j.twist).symm
    (affine_symm_pow_order j j.twist j.matrix_fixes_twist) n a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
