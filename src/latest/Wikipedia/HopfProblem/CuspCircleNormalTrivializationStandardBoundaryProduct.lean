import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardBoundaryAction
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardClosedDisk
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationBoundary

/-!
# The literal standard product coordinates on the normal boundary

The standard two-sphere is identified with the original Riemann sphere
by the native real-analytic sphere map. The standard unit three-sphere
is identified with the original radius level by positive scaling and
the explicit real/imaginary normal coordinates. The resulting boundary
map agrees with the already constructed closed-disk map on its literal
sphere inclusion.
-/

noncomputable section

open Set Topology Metric

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

/-- Reassociation of the unchanged base and normal-level subtypes. -/
def boundaryProductReassociationHomeomorph (r : ℝ) :
    (RiemannSphere × {v : Fibre // radiusSq v = r ^ 2}) ≃ₜ Conifold.ProductBoundary r where
  toFun p := ⟨(p.1, p.2.val), p.2.property⟩
  invFun p := (p.val.1, ⟨p.val.2, p.property⟩)
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun :=
    continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)

/-- The explicit standard sphere product coordinates on the actual positive normal level. -/
def standardBoundaryProductHomeomorph :
    StandardNormalBoundary ≃ₜ Conifold.ProductBoundary closedRadius :=
  (RealSphere.sphereDiffeomorph.symm.toHomeomorph.prodCongr
    ((Radial.sphereHomeomorph (E := RealFour.Space) closedRadius closedRadius_pos).trans
      (RealFour.sphereHomeomorph closedRadius closedRadius_pos.le).symm)).trans
    (boundaryProductReassociationHomeomorph closedRadius)

@[simp] theorem standardBoundaryProductHomeomorph_val (p : StandardNormalBoundary) :
    (standardBoundaryProductHomeomorph p).val =
      (RealSphere.sphereDiffeomorph.symm p.1,
        RealFour.coordinateEquiv.symm (closedRadius • (p.2 : RealFour.Space))) := rfl

/-- The unit direction is exactly the original real/imaginary coordinate inverse. -/
theorem standardBoundaryProductHomeomorph_unitDirection (p : StandardNormalBoundary) :
    (closedRadius⁻¹ : ℝ) • (standardBoundaryProductHomeomorph p).val.2 =
      RealFour.coordinateEquiv.symm (p.2 : RealFour.Space) := by
  change (closedRadius⁻¹ : ℝ) •
    RealFour.coordinateEquiv.symm (closedRadius • (p.2 : RealFour.Space)) = _
  rw [map_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt closedRadius_pos), one_smul]

/-- The literal inclusion of the standard sphere into the standard closed unit disk. -/
def standardBoundaryIntoClosedDisk (p : StandardNormalBoundary) : StandardClosedNormalProduct :=
  (p.1, ⟨p.2.val, sphere_subset_closedBall p.2.property⟩)

@[simp] theorem standardBoundaryIntoClosedDisk_fst (p : StandardNormalBoundary) :
    (standardBoundaryIntoClosedDisk p).1 = p.1 := rfl

@[simp] theorem standardBoundaryIntoClosedDisk_snd_coe (p : StandardNormalBoundary) :
    ((standardBoundaryIntoClosedDisk p).2 : RealFour.Space) = p.2 := rfl

theorem standardBoundaryIntoClosedDisk_continuous : Continuous standardBoundaryIntoClosedDisk :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

/-- The original exact-radius level included in the actual closed normal product. -/
def productBoundaryIntoClosedProduct (p : Conifold.ProductBoundary closedRadius) :
    ClosedNormalProduct :=
  (p.val.1, ⟨p.val.2, p.property.le⟩)

/-- Both constructions use the same base and the same positive normal scaling. -/
theorem standardBoundaryProductHomeomorph_intoClosed (p : StandardNormalBoundary) :
    productBoundaryIntoClosedProduct (standardBoundaryProductHomeomorph p) =
      standardClosedProductHomeomorph (standardBoundaryIntoClosedDisk p) := rfl

/-- Restricting the original closed-product map gives precisely the original boundary map. -/
theorem closedProductMap_productBoundaryIntoClosedProduct
    (p : Conifold.ProductBoundary closedRadius) :
    closedProductMap (productBoundaryIntoClosedProduct p) =
      boundaryMap closedRadius closedRadius_pos closedRadius_lt_injectiveRadius p := rfl

/-- The standard rotation becomes literal scalar multiplication in the unchanged normal fibre. -/
theorem standardBoundaryProductHomeomorph_circleAction (t : Circle)
    (p : StandardNormalBoundary) :
    standardBoundaryProductHomeomorph (standardBoundaryCircleAction t p) =
      Conifold.productBoundaryCircle (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t)
        (standardBoundaryProductHomeomorph p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change RealFour.coordinateEquiv.symm
      (closedRadius • RealFour.circleRotation t (p.2 : RealFour.Space)) =
        (DeltaSweep.circleParameter t : ℂ) •
          RealFour.coordinateEquiv.symm (closedRadius • (p.2 : RealFour.Space))
    have h := RealFour.coordinateEquiv_symm_circleRotation t
      (closedRadius • (p.2 : RealFour.Space))
    rw [(RealFour.circleRotation t).map_smul] at h
    exact h

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
