import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmallProduct
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothFullProduct

/-!
# The original small elliptic product in its inherited smooth atlases

The root ball carries the open-subset atlas inherited from the original
open unit disc.  The source uses the original small-filling atlas, and the
surface factor uses its original finite-quotient atlas.  Restriction of
the full product uses precisely these structures, not an atlas
transported along the product homeomorphism.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth

open Elliptic SpecialPeriods SpecialPeriods.EllipticFilling
open ThreefoldOverlapMappingTorus.Elliptic
open EllipticSmallProduct EllipticFullProduct

local notation "IR" => modelWithCornersSelf ℝ FamilyModel
local notation "I₁" => modelWithCornersSelf ℝ ℂ
local notation "I₂" => modelWithCornersSelf ℝ ComplexPlane₂

/-- The literal root-radius predicate is an open subset of the original disc. -/
def rootBallOpen (j : Kind) : TopologicalSpace.Opens Disc :=
  ⟨{s : Disc | ‖(s : ℂ)‖ ^ j.order < Threefold.specialBaseCover.radius (some j)},
    isOpen_lt (continuous_subtype_val.norm.pow j.order) continuous_const⟩

@[simp] theorem mem_rootBallOpen (j : Kind) (s : Disc) :
    s ∈ rootBallOpen j ↔
      ‖(s : ℂ)‖ ^ j.order < Threefold.specialBaseCover.radius (some j) := Iff.rfl

/-- The root ball inherits its atlas from the original open disc. -/
@[instance_reducible] def rootBallChartedSpace (j : Kind) :
    ChartedSpace ℂ (RootBall j) :=
  inferInstanceAs (ChartedSpace ℂ (rootBallOpen j))

attribute [local instance] rootBallChartedSpace

/-- The original surface atlas and the inherited root-ball atlas give the product atlas. -/
@[instance_reducible] def smallSurfaceProductChartedSpace (j : Kind) :
    ChartedSpace FamilyModel (RootBall j × BoundaryCentralSurface j) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂)
    (RootBall j × BoundaryCentralSurface j))

attribute [local instance] smallSurfaceProductChartedSpace surfaceProductChartedSpace
  Threefold.specialEllipticPieceChartedSpace specialFullFillingChartedSpace

/-- Inclusion in the original disc is smooth in the inherited atlas. -/
theorem rootBall_inclusion_contMDiff (j : Kind) :
    ContMDiff I₁ I₁ ∞ (Subtype.val : RootBall j → Disc) :=
  contMDiff_subtype_val (U := rootBallOpen j)

/-- The inherited atlas makes the actual root ball a smooth real manifold. -/
theorem rootBall_isManifold (j : Kind) : IsManifold I₁ ∞ (RootBall j) :=
  inferInstanceAs (IsManifold I₁ ∞ (rootBallOpen j))

/-- The original small-filling inclusion uses its unchanged open-submanifold atlas. -/
theorem smallPiece_inclusion_contMDiff (j : Kind) :
    ContMDiff IR IR ∞ (Subtype.val : Threefold.SpecialEllipticPiece j → SpecialFullFilling j) :=
  contMDiff_subtype_val
    (U := pieceDomain specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ Threefold.specialBaseCover j)

/-- Inclusion of the root-ball product into the original full disc-surface product. -/
def rootBallProductInclusion (j : Kind) (p : RootBall j × BoundaryCentralSurface j) :
    Disc × BoundaryCentralSurface j := (p.1.val, p.2)

@[simp] theorem rootBallProductInclusion_apply (j : Kind)
    (p : RootBall j × BoundaryCentralSurface j) :
    rootBallProductInclusion j p = (p.1.val, p.2) := rfl

/-- This product inclusion is smooth for exactly the two inherited product atlases. -/
theorem rootBallProductInclusion_contMDiff (j : Kind) :
    ContMDiff IR IR ∞ (rootBallProductInclusion j) := by
  have hfst : ContMDiff ((I₁).prod I₂) I₁ ∞
      (fun p : RootBall j × BoundaryCentralSurface j => p.1.val) :=
    (rootBall_inclusion_contMDiff j).comp contMDiff_fst
  have hsnd : ContMDiff ((I₁).prod I₂) I₂ ∞
      (fun p : RootBall j × BoundaryCentralSurface j => p.2) := contMDiff_snd
  rw [modelWithCornersSelf_prod]
  exact hfst.prodMk hsnd

/-- The source retains the real smoothness of its original complex open-submanifold atlas. -/
theorem smallPiece_isRealManifold (j : Kind) :
    IsManifold IR ∞ (Threefold.SpecialEllipticPiece j) := by
  let := Threefold.specialEllipticPiece_isManifold j
  exact complexManifold_isRealManifold _ ∞

/-- The actual root-ball/surface product is a real smooth manifold in its inherited atlas. -/
theorem smallSurfaceProduct_isRealManifold (j : Kind) :
    IsManifold IR ∞ (RootBall j × BoundaryCentralSurface j) := by
  have : IsManifold (modelWithCornersSelf ℂ ℂ) ω (RootBall j) :=
    inferInstanceAs (IsManifold (modelWithCornersSelf ℂ ℂ) ω (rootBallOpen j))
  have : IsManifold (modelWithCornersSelf ℂ FamilyModel) ω
      (RootBall j × BoundaryCentralSurface j) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := modelWithCornersSelf ℂ ℂ)
      (I' := modelWithCornersSelf ℂ ComplexPlane₂) (RootBall j) (BoundaryCentralSurface j)
  exact complexManifold_isRealManifold _ ∞

/-- Smoothness of the exact frozen small-piece homeomorphism in the two original atlases. -/
theorem smallProductHomeomorph_contMDiff (j : Kind) :
    ContMDiff IR IR ∞ (smallProductHomeomorph j) := by
  have h : ContMDiff IR IR ∞
      (fun y : Threefold.SpecialEllipticPiece j => specialFillingProductHomeomorph j y.val) :=
    (specialFillingProductHomeomorph_contMDiff j).comp (smallPiece_inclusion_contMDiff j)
  have hp : ContMDiff IR ((I₁).prod I₂) ∞
      (fun y : Threefold.SpecialEllipticPiece j => specialFillingProductHomeomorph j y.val) := by
    simpa only [modelWithCornersSelf_prod] using h
  have hf : ContMDiff IR I₁ ∞
      (fun y : Threefold.SpecialEllipticPiece j => (smallProductHomeomorph j y).1) := by
    apply (ContMDiff.subtypeVal_comp_iff (rootBallOpen j) _).mp
    exact hp.fst.congr (fun y => (smallProductHomeomorph_fst_val j y).symm)
  have hs : ContMDiff IR I₂ ∞
      (fun y : Threefold.SpecialEllipticPiece j => (smallProductHomeomorph j y).2) := by
    simpa only [smallProductHomeomorph_snd] using hp.snd
  simpa only [modelWithCornersSelf_prod] using hf.prodMk hs

/-- The exact inverse is smooth by restriction of the original full-product inverse. -/
theorem smallProductHomeomorph_symm_contMDiff (j : Kind) :
    ContMDiff IR IR ∞ (smallProductHomeomorph j).symm := by
  apply (ContMDiff.subtypeVal_comp_iff
    (pieceDomain specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
      Threefold.specialBaseCover j) _).mp
  have h := (specialFillingProductHomeomorph_symm_contMDiff j).comp
    (rootBallProductInclusion_contMDiff j)
  simpa only [Function.comp_def, smallProductHomeomorph_symm_val,
    rootBallProductInclusion_apply] using h

/-- The actual small elliptic product is a real smooth diffeomorphism, in its native atlases. -/
def smallProductDiffeomorph (j : Kind) :
    Diffeomorph IR IR (Threefold.SpecialEllipticPiece j)
      (RootBall j × BoundaryCentralSurface j) ∞ where
  toEquiv := (smallProductHomeomorph j).toEquiv
  contMDiff_toFun := smallProductHomeomorph_contMDiff j
  contMDiff_invFun := smallProductHomeomorph_symm_contMDiff j

@[simp] theorem smallProductDiffeomorph_apply (j : Kind)
    (y : Threefold.SpecialEllipticPiece j) :
    smallProductDiffeomorph j y = smallProductHomeomorph j y := rfl

@[simp] theorem smallProductDiffeomorph_symm_apply (j : Kind)
    (p : RootBall j × BoundaryCentralSurface j) :
    (smallProductDiffeomorph j).symm p = (smallProductHomeomorph j).symm p := rfl

/-- The smooth upgrade has exactly the previously checked underlying homeomorphism. -/
theorem smallProductDiffeomorph_toHomeomorph (j : Kind) :
    (smallProductDiffeomorph j).toHomeomorph = smallProductHomeomorph j := by
  apply Homeomorph.ext
  intro y
  rfl

/-- The smooth restriction agrees with the native full smooth product on every actual point. -/
theorem smallProductDiffeomorph_inclusion (j : Kind)
    (y : Threefold.SpecialEllipticPiece j) :
    rootBallProductInclusion j (smallProductDiffeomorph j y) =
      specialFillingProductDiffeomorph j y.val := rfl

/-- The smooth forward map retains the literal original quotient formula. -/
theorem smallProductDiffeomorph_quotient (j : Kind) (s : RootBall j) (x : RealTorus₄) :
    smallProductDiffeomorph j (smallQuotient j s x) =
      (rootBallRotate j (EllipticGamma.normalizedGamma j x) s,
        surfaceProjection j (specialLocalData j).centralPeriod j.twist (mainTwist_admissible j)
          (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val x)) :=
  smallProductHomeomorph_quotient j s x

/-- The smooth inverse retains the original small-filling representative with opposite phase. -/
theorem smallProductDiffeomorph_symm_surfaceProjection (j : Kind)
    (s : RootBall j) (x : RealTorus₄) :
    (smallProductDiffeomorph j).symm
      (s, surfaceProjection j (specialLocalData j).centralPeriod j.twist (mainTwist_admissible j)
        (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val x)) =
      smallQuotient j (rootBallRotate j (-EllipticGamma.normalizedGamma j x) s) x :=
  smallProductHomeomorph_symm_surfaceProjection j s x

/-- The surface coordinate is still the native radial retraction after the smooth upgrade. -/
theorem smallProductDiffeomorph_snd_retraction (j : Kind)
    (y : Threefold.SpecialEllipticPiece j) :
    (smallProductDiffeomorph j y).2 =
      (specialLocalData j).fillingSurfaceRetraction j.twist (mainTwist_admissible j) y.val :=
  smallProductHomeomorph_snd_retraction j y

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth
