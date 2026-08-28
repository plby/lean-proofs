import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusSurface
import Wikipedia.HopfProblem.EllipticHigherHomologyRetraction

/-!
# Actual fibre and period-cover maps into the elliptic surface

The primitive fibre axes are included at zero in the distinguished split
circle.  Their actual surface map becomes the actual time-zero fibre
inclusion under the constructed surface homeomorphism.  The original period
cover likewise becomes the actual finite product cover.  Functoriality gives
these same commutative diagrams on integral singular homology in every degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusQuotient

/-- Inclusion of the actual three-dimensional fibre torus at zero in
the primitive twist-circle coordinate of the original period torus. -/
def fibreIntoPeriodTorus (j : Kind) (p : FixedPeriod j) :
    C(ProductTorus 3, p.val.Torus) where
  toFun x := (splitPeriodTorusHomeomorph j p.val).symm (0, x)
  continuous_toFun := (splitPeriodTorusHomeomorph j p.val).symm.continuous.comp
    (continuous_const.prodMk continuous_id)

@[simp] theorem fibreIntoPeriodTorus_apply (j : Kind) (p : FixedPeriod j)
    (x : ProductTorus 3) :
    fibreIntoPeriodTorus j p x = (splitPeriodTorusHomeomorph j p.val).symm (0, x) := rfl

/-- The literal real-coordinate lift preserves the specified primitive
fibre axes before either orbit projection is taken. -/
theorem fibreIntoPeriodTorus_coordinateProjection (j : Kind) (p : FixedPeriod j)
    (x : FibreCoordinates) :
    fibreIntoPeriodTorus j p (coordinateProjection 3 x) =
      flatProjection p.val ((splitRealCoordinates j).symm (0, x)) := by
  apply (splitPeriodTorusHomeomorph j p.val).injective
  rw [fibreIntoPeriodTorus_apply, Homeomorph.apply_symm_apply,
    splitPeriodTorusHomeomorph_flatProjection, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The actual finite period cover followed by the primitive fibre inclusion. -/
def fibreIntoSurface (j : Kind) (p : FixedPeriod j) :
    C(ProductTorus 3, Surface j p j.twist (mainTwist_admissible j)) :=
  (periodCover j p j.twist (mainTwist_admissible j)).comp (fibreIntoPeriodTorus j p)

@[simp] theorem fibreIntoSurface_apply (j : Kind) (p : FixedPeriod j)
    (x : ProductTorus 3) :
    fibreIntoSurface j p x = surfaceProjection j p j.twist (mainTwist_admissible j)
      ((splitPeriodTorusHomeomorph j p.val).symm (0, x)) := rfl

/-- The actual surface homeomorphism preserves the time-zero fibre map. -/
theorem surfaceMappingTorusHomeomorph_comp_fibreIntoSurface (j : Kind) (p : FixedPeriod j) :
    (surfaceMappingTorusHomeomorph j p :
      C(Surface j p j.twist (mainTwist_admissible j), mappingTorusModel j)).comp
        (fibreIntoSurface j p) =
      MappingTorus.HomologyCover.fibreInclusion (fibreTorusHomeomorph j).symm := by
  ext x
  change surfaceMappingTorusHomeomorph j p
    (surfaceProjection j p j.twist (mainTwist_admissible j)
      ((splitPeriodTorusHomeomorph j p.val).symm (0, x))) =
        MappingTorus.mk (fibreTorusHomeomorph j).symm (0, x)
  simpa only [AddCircle.coe_zero, zero_mul] using
    surfaceMappingTorusHomeomorph_splitPeriodTorus j p (0 : ℝ) x

/-- Equality of the actual fibre maps gives a commutative integral
homology diagram in every degree. -/
theorem surfaceMappingTorusHomology_fibre_map (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    (homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) n).toLinearMap.comp
      (singularHomologyMap (fibreIntoSurface j p) n) =
      MappingTorusHomology.fibreHomologyMap (fibreTorusHomeomorph j).symm n := by
  rw [homeomorphHomologyEquiv_toLinearMap, ← singularHomologyMap_comp,
    surfaceMappingTorusHomeomorph_comp_fibreIntoSurface]

theorem surfaceMappingTorusHomology_fibre (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology (ProductTorus 3) n) :
    homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) n
      (singularHomologyMap (fibreIntoSurface j p) n a) =
      MappingTorusHomology.fibreHomologyMap (fibreTorusHomeomorph j).symm n a :=
  DFunLike.congr_fun (surfaceMappingTorusHomology_fibre_map j p n) a

/-- The actual product-torus finite cover followed by the constructed
mapping-torus homeomorphism, with no homology formula imposed. -/
def mappingTorusProductCover (j : Kind) :
    C(MappingTorus.Circle × ProductTorus 3, mappingTorusModel j) :=
  (mappingTorusHomeomorph j.order (fibreTorusHomeomorph j)
      (fibreTorusHomeomorph_pow_order j) :
    C(surfaceProductQuotient j, mappingTorusModel j)).comp
    ⟨MappingTorusQuotient.project j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j),
      MappingTorusQuotient.project_continuous j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j)⟩

/-- The product cover's value on every real representative of its circle. -/
theorem mappingTorusProductCover_real_apply (j : Kind) (t : ℝ) (x : ProductTorus 3) :
    mappingTorusProductCover j ((t : MappingTorus.Circle), x) =
      MappingTorus.mk (fibreTorusHomeomorph j).symm (t * j.order, x) :=
  mappingTorusHomeomorph_project j.order (fibreTorusHomeomorph j)
    (fibreTorusHomeomorph_pow_order j) t x

/-- The actual original period cover commutes with the proved torus
splitting and the actual surface mapping-torus homeomorphism. -/
theorem surfaceMappingTorusHomeomorph_comp_periodCover (j : Kind) (p : FixedPeriod j) :
    (surfaceMappingTorusHomeomorph j p :
      C(Surface j p j.twist (mainTwist_admissible j), mappingTorusModel j)).comp
        (periodCover j p j.twist (mainTwist_admissible j)) =
      (mappingTorusProductCover j).comp (splitPeriodTorusHomeomorph j p.val :
        C(p.val.Torus, MappingTorus.Circle × ProductTorus 3)) := rfl

/-- Naturality identifies the actual period-cover homology map with
the actual product-cover map, in all degrees and before choosing group bases. -/
theorem surfaceMappingTorusHomology_periodCover_map (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    (homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) n).toLinearMap.comp
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n) =
      (singularHomologyMap (mappingTorusProductCover j) n).comp
        (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n).toLinearMap := by
  rw [homeomorphHomologyEquiv_toLinearMap, ← singularHomologyMap_comp,
    surfaceMappingTorusHomeomorph_comp_periodCover, singularHomologyMap_comp,
    homeomorphHomologyEquiv_toLinearMap]

theorem surfaceMappingTorusHomology_periodCover (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology p.val.Torus n) :
    homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) n
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n a) =
      singularHomologyMap (mappingTorusProductCover j) n
        (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n a) :=
  DFunLike.congr_fun (surfaceMappingTorusHomology_periodCover_map j p n) a

end Wikipedia.HopfProblem.Elliptic.HigherHomology
