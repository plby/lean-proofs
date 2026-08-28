import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationNegation
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationShear
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearizationNative
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangGeometry
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryFibreTransport

/-!
# The actual elliptic covering maps with their vertical shear removed

Subtracting the original period circle from the genuine finite-cover
boundary map gives an actual continuous map into the original regular
family. Its literal representatives keep the real fibre coordinate
unchanged. It therefore commutes with genuine fibre negation, and the
complete shear formula separates its horizontal class from the original
fibre contribution.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open Elliptic SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyPontryagin EllipticCapKernelWang EllipticGaugeLinearization
open Homology CircleTopology

local notation "Circle" => MappingTorus.Circle

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The genuine original finite cover followed by the actual linearized regular map. -/
def coveredRegularMap (j : Kind) (τ : ℝ) : C(Circle × RealTorus₄, (Dsp).Space) :=
  (linearRegularBoundaryMap j τ).comp (nativeProductCover j)

/-- Remove exactly the original integral period circle, as an actual map of spaces. -/
def untwistedRegularMap (j : Kind) (τ : ℝ) : C(Circle × RealTorus₄, (Dsp).Space) :=
  (coveredRegularMap j τ).comp
    ((verticalShearHomeomorph j.twist).symm : C(Circle × RealTorus₄, Circle × RealTorus₄))

/-- The original real period coordinate is unchanged at every representative. -/
theorem untwistedRegularMap_real_apply (j : Kind) (τ t : ℝ) (x : RealTorus₄) :
    untwistedRegularMap j τ ((t : Circle), x) =
      (Dsp).quotient (nativeShiftedBase j τ (t * j.order), x) := by
  change linearRegularBoundaryMap j τ
    (nativeProductCover j ((t : Circle), x - periodCircle j.twist (t : Circle))) = _
  rw [nativeProductCover_real_apply, linearRegularBoundaryMap_mk,
    periodCircle_real_apply]
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast j.order_pos.ne'
  rw [mul_div_cancel_right₀ _ hm, sub_add_cancel]

/-- Restoring the actual vertical shear recovers the complete native covering map. -/
theorem untwistedRegularMap_comp_shear (j : Kind) (τ : ℝ) :
    (untwistedRegularMap j τ).comp (verticalShear j.twist) = coveredRegularMap j τ := by
  apply ContinuousMap.ext
  intro p
  change coveredRegularMap j τ
    ((verticalShearHomeomorph j.twist).symm (verticalShearHomeomorph j.twist p)) = _
  rw [Homeomorph.symm_apply_apply]

/-- Fibre negation commutes with the genuine untwisted map, before passing to homology. -/
theorem familyNegation_comp_untwistedRegularMap (j : Kind) (τ : ℝ) :
    (familyNegation Dsp).comp (untwistedRegularMap j τ) =
      (untwistedRegularMap j τ).comp (circleProductMap flatNegation) := by
  apply ContinuousMap.ext
  rintro ⟨c, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective c
  change familyNegation Dsp (untwistedRegularMap j τ ((t : Circle), x)) =
    untwistedRegularMap j τ ((t : Circle), -x)
  rw [untwistedRegularMap_real_apply, familyNegation_quotient,
    untwistedRegularMap_real_apply]

/-- The horizontal third-homology class is fixed by the actual regular-family involution. -/
theorem untwistedRegularMap_positiveCircleCross_negation (j : Kind) (τ : ℝ)
    (a : SingularHomology RealTorus₄ 2) :
    singularHomologyMap (familyNegation Dsp) 3
        (singularHomologyMap (untwistedRegularMap j τ) 3
          (positiveCircleCross RealTorus₄ 2 a)) =
      singularHomologyMap (untwistedRegularMap j τ) 3
        (positiveCircleCross RealTorus₄ 2 a) := by
  have h := congrArg (fun f : C(Circle × RealTorus₄, (Dsp).Space) => singularHomologyMap f 3)
    (familyNegation_comp_untwistedRegularMap j τ)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  have ha := LinearMap.congr_fun h (positiveCircleCross RealTorus₄ 2 a)
  simpa only [LinearMap.comp_apply, positiveCircleCross_naturality,
    flatNegation_homology_two] using ha

/-- The zero circle slice is the literal original flat fibre at the corresponding base lift. -/
theorem untwistedRegularMap_comp_circleSection (j : Kind) (τ : ℝ) :
    (untwistedRegularMap j τ).comp (productSection RealTorus₄) =
      pointFamilyFibreInclusion Dsp (nativeShiftedBase j τ 0) := by
  apply ContinuousMap.ext
  intro x
  change untwistedRegularMap j τ (0, x) = (Dsp).quotient (nativeShiftedBase j τ 0, x)
  have h := untwistedRegularMap_real_apply j τ 0 x
  simpa only [AddCircle.coe_zero, zero_mul] using h

/-- Every actual fibre correction uses the same normalized original fibre map. -/
theorem untwistedRegularMap_circleSection_homology (j : Kind) (τ : ℝ) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (untwistedRegularMap j τ) n (circleSectionHomology RealTorus₄ n a) =
      singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) n a := by
  have h := congrArg (fun f : C(RealTorus₄, (Dsp).Space) => singularHomologyMap f n)
    (untwistedRegularMap_comp_circleSection j τ)
  rw [singularHomologyMap_comp, pointFamilyFibreInclusion_homology_eq_normalized] at h
  exact LinearMap.congr_fun h a

/-- The full original covering class is its actual horizontal class
plus its genuine fibre product. -/
theorem coveredRegularMap_positiveCircleCross (j : Kind) (τ : ℝ) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (coveredRegularMap j τ) (n + 1)
        (positiveCircleCross RealTorus₄ n a) =
      singularHomologyMap (untwistedRegularMap j τ) (n + 1)
          (positiveCircleCross RealTorus₄ n a) +
        singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) (n + 1)
          (product RealTorus₄ n (FlatTorus.singularH1Equiv.symm j.twist) a) := by
  have h := congrArg
    (fun f : C(Circle × RealTorus₄, (Dsp).Space) => singularHomologyMap f (n + 1))
    (untwistedRegularMap_comp_shear j τ)
  rw [singularHomologyMap_comp] at h
  have ha := LinearMap.congr_fun h (positiveCircleCross RealTorus₄ n a)
  simpa only [LinearMap.comp_apply, verticalShear_positiveCircleCross, map_add,
    untwistedRegularMap_circleSection_homology] using ha.symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
