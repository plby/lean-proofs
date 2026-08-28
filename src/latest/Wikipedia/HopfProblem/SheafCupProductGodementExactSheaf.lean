import Wikipedia.HopfProblem.SheafCupProductGodementExactContraction
import Wikipedia.HopfProblem.SheafCupProductResolutionBasic

/-!
# Exactness of the actual multiplicative Godement resolution

The stalk contracting identities give explicit preimages of every
stalk cocycle. The genuine sheaf-stalk exactness criterion then proves
exactness of the original additive sheaf complex. Neither injectivity
of the terms nor a cohomology comparison is an exactness premise.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct.GodementExact

open GodementRing

variable {X : TopCat.{0}}

/-- An actual contracting identity supplies every additive cycle lift. -/
theorem exact_of_contraction (S : ShortComplex AddCommGrpCat.{0})
    (r : S.X₂ ⟶ S.X₁) (s : S.X₃ ⟶ S.X₂)
    (h : r ≫ S.f + S.g ≫ s = 𝟙 S.X₂) : S.Exact := by
  apply S.ab_exact_iff.mpr
  intro a ha
  refine ⟨r a, ?_⟩
  have hh : S.f (r a) + s (S.g a) = a := ConcreteCategory.congr_hom h a
  simpa only [ha, map_zero, add_zero] using hh

/-- Exactness at the original degree-zero additive Godement term. -/
theorem exact0 (F : RingSheaf X) : (complex0 F).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (complex0 F)).mpr
  intro x
  exact exact_of_contraction _ (stalkRetraction F x)
    (stalkRetraction (term0 F) x) (contraction0 F x)

/-- Exactness at the original degree-one additive Godement term. -/
theorem exact1 (F : RingSheaf X) : (complex1 F).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (complex1 F)).mpr
  intro x
  exact exact_of_contraction _ (stalkRetraction (term0 F) x)
    (stalkRetraction (term1 F) x) (contraction1 F x)

/-- Exactness at the original degree-two additive Godement term. -/
theorem exact2 (F : RingSheaf X) : (complex2 F).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (complex2 F)).mpr
  intro x
  exact exact_of_contraction _ (stalkRetraction (term1 F) x)
    (stalkRetraction (term2 F) x) (contraction2 F x)

/-- The original augmentation is monic because its actual stalk maps
have the proved evaluation retractions. -/
instance augmentation_mono (F : RingSheaf X) : Mono (augmentation F) := by
  apply (TopCat.Presheaf.mono_iff_stalk_mono (augmentation F)).mpr
  intro x
  change Mono ((additiveStalk x).map (augmentation F))
  apply ConcreteCategory.mono_of_injective
  intro a b hab
  exact (ConcreteCategory.congr_hom (augmentation_stalkRetraction F x) a).symm.trans
    ((congrArg (stalkRetraction F x) hab).trans
      (ConcreteCategory.congr_hom (augmentation_stalkRetraction F x) b))

/-- The original forgotten ring-Godement terms form a genuine partial
resolution, with every required exactness assertion proved above. -/
def partialResolution (F : RingSheaf X) :
    SheafCupProductResolution.PartialResolution (TopCat.Sheaf AddCommGrpCat.{0} X) where
  F := additiveSheaf F
  I₀ := I0 F
  I₁ := I1 F
  I₂ := I2 F
  I₃ := I3 F
  ι := augmentation F
  d₀ := d0 F
  d₁ := d1 F
  d₂ := d2 F
  ι_d₀ := augmentation_d0 F
  d₀_d₁ := d0_d1 F
  d₁_d₂ := d1_d2 F
  exact₀ := exact0 F
  exact₁ := exact1 F
  exact₂ := exact2 F
  mono_ι := augmentation_mono F

end Wikipedia.HopfProblem.SheafCupProduct.GodementExact
