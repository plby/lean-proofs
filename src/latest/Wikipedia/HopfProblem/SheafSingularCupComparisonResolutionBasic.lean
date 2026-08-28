import Wikipedia.HopfProblem.SheafCupProductResolutionCohomology

/-!
# Original partial-resolution comparisons under actual acyclicity

The original kernel truncation and its original global homology maps
only need the indicated genuine Ext vanishings. These definitions use
those exact same maps without requiring injectivity. With injective
terms they equal the previously constructed comparisons.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution

open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}} (R : PartialResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- The original degree-one comparison requires only actual degree-one acyclicity of I₀. -/
def h1IsoAcyclic [h0 : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 1) ≅ R.globalOneComplex.homology := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) := h0
  exact R.toAugmented.h1Iso ≪≫ asIso (ShortComplex.homologyMap R.globalTruncationInclusion)

/-- The original degree-two comparison requires only the three actual low-degree vanishings. -/
def h2IsoAcyclic [h01 : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1)]
    [h02 : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 2)]
    [h11 : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₁ 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 2) ≅ R.globalTwoComplex.homology := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) := h01
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 2) := h02
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₂ 1) := h11
  exact R.toAugmented.h2Iso ≪≫ R.globalTwoCokernelIso

/-- Under injectivity the acyclic comparison is exactly the original comparison. -/
theorem h1IsoAcyclic_eq_h1Iso [Injective R.I₀] :
    R.h1IsoAcyclic (h0 := injective_higher_subsingleton R.I₀ 0) = R.h1Iso := rfl

theorem h2IsoAcyclic_eq_h2Iso [Injective R.I₀] [Injective R.I₁] :
    R.h2IsoAcyclic (h01 := injective_higher_subsingleton R.I₀ 0)
      (h02 := injective_higher_subsingleton R.I₀ 1)
      (h11 := injective_higher_subsingleton R.I₁ 0) = R.h2Iso := rfl

/-- The actual connecting representative is unchanged by the weaker hypothesis. -/
theorem h1IsoAcyclic_connecting [Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1)] :
    R.toAugmented.globalConnectingOne ≫ R.h1IsoAcyclic.hom =
      R.globalOneCycleMap ≫ R.globalOneComplex.homologyπ := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1))
  change R.toAugmented.globalConnectingOne ≫
      (R.toAugmented.h1Iso.hom ≫ ShortComplex.homologyMap R.globalTruncationInclusion) = _
  rw [← Category.assoc, R.toAugmented.h1Iso_connecting, Category.assoc,
    ShortComplex.homologyπ_naturality]
  exact (Category.assoc _ _ _).symm

/-- The genuine double connecting representative is likewise unchanged. -/
theorem h2IsoAcyclic_connecting [Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₁ 1)] :
    R.toAugmented.globalConnectingTwo ≫ R.h2IsoAcyclic.hom =
      R.globalTwoHomologyData.cyclesIso.inv ≫ R.globalTwoComplex.homologyπ := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1))
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 2) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 2))
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₂ 1) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₁ 1))
  change R.toAugmented.globalConnectingTwo ≫
    (R.toAugmented.h2Iso.hom ≫ R.globalTwoCokernelIso.hom) = _
  rw [← Category.assoc, R.toAugmented.h2Iso_connecting]
  exact R.globalTwoCokernelIso_π

end Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution
