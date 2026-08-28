import Wikipedia.HopfProblem.SheafCupProductScalarQuotientGodement

/-!
# The original Godement scalar maps induce the actual quotient scalar maps

On actual global sections the original scalar sheaf endomorphism is
literal multiplication by its global coefficient. Thus the original
partial-resolution endomorphism has the scalar maps already proved on
coface complexes, and canonical homology intertwines their actual quotients.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Wikipedia.HopfProblem.SheafCupProduct.ScalarQuotient

open GodementRing CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}} {F : RingSheaf X}

/-- The original sheaf scalar endomorphism on global sections is literal multiplication. -/
theorem global_scalarEnd (c : Scalars.Coefficients F) (z : ℂ) :
    (globalSectionsFunctor X).map (Scalars.scalarEnd c z).asHom =
      AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (c z)) := by
  ext s
  change F.presheaf.obj (op ⊤) at s
  change (Scalars.scalarEnd c z).hom.app (op ⊤) s = c z * s
  exact (Scalars.scalarEnd_apply c z (op ⊤) s).trans
    (congrArg (fun t => t * s) (Scalars.restricted_top c z))

/-- The original degree-one Godement section map is the actual multiplication complex map. -/
theorem globalOneMap_eq (c : Scalars.Coefficients F) (z : ℂ) :
    (Scalars.scalarPartialResolutionMap c z).globalOneMap =
      (globalCoefficients c).oneComplexMap z := by
  apply ShortComplex.hom_ext
  · exact global_scalarEnd (Scalars.coefficients0 c) z
  · exact global_scalarEnd (Scalars.coefficients1 c) z
  · exact global_scalarEnd (Scalars.coefficients2 c) z

/-- The original degree-two Godement section map is the actual multiplication complex map. -/
theorem globalTwoMap_eq (c : Scalars.Coefficients F) (z : ℂ) :
    (Scalars.scalarPartialResolutionMap c z).globalTwoMap =
      (globalCoefficients c).twoComplexMap z := by
  apply ShortComplex.hom_ext
  · exact global_scalarEnd (Scalars.coefficients1 c) z
  · exact global_scalarEnd (Scalars.coefficients2 c) z
  · exact global_scalarEnd (Scalars.coefficients3 c) z

/-- The original scalar endomorphism's H¹ complex map intertwines the actual first quotient map. -/
theorem oneHomologyIso_scalar (c : Scalars.Coefficients F) (z : ℂ) :
    ShortComplex.homologyMap (Scalars.scalarPartialResolutionMap c z).globalOneMap ≫
        (SheafCupProductResolution.Coface.oneHomologyIso (globalData F)).hom =
      (SheafCupProductResolution.Coface.oneHomologyIso (globalData F)).hom ≫
        AddCommGrpCat.ofHom (scalarOne c z) := by
  exact (congrArg (fun f : SheafCupProductResolution.Coface.oneComplex (globalData F) ⟶
      SheafCupProductResolution.Coface.oneComplex (globalData F) =>
        ShortComplex.homologyMap f ≫
          (SheafCupProductResolution.Coface.oneHomologyIso (globalData F)).hom)
    (globalOneMap_eq c z)).trans ((globalCoefficients c).oneHomologyIso_scalar z)

/-- The original scalar endomorphism's H² complex map intertwines the actual second quotient map. -/
theorem twoHomologyIso_scalar (c : Scalars.Coefficients F) (z : ℂ) :
    ShortComplex.homologyMap (Scalars.scalarPartialResolutionMap c z).globalTwoMap ≫
        (SheafCupProductResolution.Coface.twoHomologyIso (globalData F)).hom =
      (SheafCupProductResolution.Coface.twoHomologyIso (globalData F)).hom ≫
        AddCommGrpCat.ofHom (scalarTwo c z) := by
  exact (congrArg (fun f : SheafCupProductResolution.Coface.twoComplex (globalData F) ⟶
      SheafCupProductResolution.Coface.twoComplex (globalData F) =>
        ShortComplex.homologyMap f ≫
          (SheafCupProductResolution.Coface.twoHomologyIso (globalData F)).hom)
    (globalTwoMap_eq c z)).trans ((globalCoefficients c).twoHomologyIso_scalar z)

end Wikipedia.HopfProblem.SheafCupProduct.ScalarQuotient
