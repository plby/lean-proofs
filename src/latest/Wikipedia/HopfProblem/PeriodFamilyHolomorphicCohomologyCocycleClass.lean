import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleCech
import Wikipedia.HopfProblem.HolomorphicPicardCechClassAdditive
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars

/-!
# Genuine native first cohomology classes of period characters

The actual holomorphic overlap cocycle defines its actual extension
class in the original total-space holomorphic sheaf's native `Ext`.
Additivity and complex-linearity follow from genuine extension-class
naturality. The scalar module is induced by the original scalar sheaf
endomorphisms, with no dimension calculation or transported cohomology.

Our cocycle is `L_i - L_j`. In the existing extension comparison
convention, local comparison sections therefore have sign `-L_i`.
This file makes no assertion identifying a fibre's Dolbeault marking.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle

open HolomorphicFunctionSheaf.SphereH1

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The original additive group structure on the native `Ext` group,
exposed for the unchanged family sheaf definition. -/
instance totalCohomologyAddCommGroup (P : HolomorphicPeriodMap V B) (q : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0}
      (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) q) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Complex scalar multiplication on the original native total-space
cohomology, induced by multiplication of actual holomorphic functions. -/
@[instance_reducible] def totalCohomologyModule (P : HolomorphicPeriodMap V B) (q : ℕ) :
    Module ℂ (CategoryTheory.Sheaf.H.{0}
      (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) q) := by
  letI := P.totalChartedSpace
  exact CuspNormalization.SheafCohomology.holomorphicCohomologyModule
    (modelWithCornersSelf ℂ (V × ComplexPlane₂)) P.TotalSpace q

/-- The native module's scalar action is exactly the map of the
original scalar sheaf endomorphism. -/
theorem totalCohomologyModule_smul (P : HolomorphicPeriodMap V B) (q : ℕ)
    (c : ℂ) (x : CategoryTheory.Sheaf.H.{0}
      (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) q) :
    letI := totalCohomologyModule P q
    c • x = CategoryTheory.Sheaf.H.map
      (PeriodFamilyHigherDirectImage.Zero.totalScalarEnd P c) q x := rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The genuine derived extension class of the original holomorphic
period cocycle on the original total family. -/
def periodClass (P : HolomorphicPeriodMap V B) (a : Coefficients V B) :
    CategoryTheory.Sheaf.H.{0}
      (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) 1 :=
  HolomorphicPicard.CechExtension.classOf (cocycle P a) (coverOpen_covers P)

/-- The class is literally the extension class of the constructed
holomorphic cocycle, with no cohomology equivalence in its definition. -/
theorem periodClass_eq_classOf (P : HolomorphicPeriodMap V B) (a : Coefficients V B) :
    periodClass P a = HolomorphicPicard.CechExtension.classOf
      (cocycle P a) (coverOpen_covers P) := rfl

@[simp] theorem periodClass_zero (P : HolomorphicPeriodMap V B) :
    periodClass P (0 : Coefficients V B) = 0 := by
  exact (congrArg (fun c => HolomorphicPicard.CechExtension.classOf c (coverOpen_covers P))
    (cocycle_zero P)).trans (HolomorphicPicard.CechExtension.classOf_zero (coverOpen_covers P))

/-- Addition of period characters gives addition in the actual native
first cohomology group. -/
theorem periodClass_add (P : HolomorphicPeriodMap V B) (a a' : Coefficients V B) :
    periodClass P (a + a') = periodClass P a + periodClass P a' := by
  exact (congrArg (fun c => HolomorphicPicard.CechExtension.classOf c (coverOpen_covers P))
    (cocycle_add P a a')).trans
      (HolomorphicPicard.CechExtension.classOf_add (cocycle P a) (cocycle P a')
        (coverOpen_covers P))

/-- The coefficient-to-native-`Ext` map as an actual additive homomorphism. -/
def periodClassHom (P : HolomorphicPeriodMap V B) :
    Coefficients V B →+ CategoryTheory.Sheaf.H.{0}
      (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) 1 where
  toFun := periodClass P
  map_zero' := periodClass_zero P
  map_add' := periodClass_add P

@[simp] theorem periodClassHom_apply (P : HolomorphicPeriodMap V B) (a : Coefficients V B) :
    periodClassHom P a = periodClass P a := rfl

/-- Complex multiplication of coefficients is exactly the genuine map
of the original scalar sheaf endomorphism on native first cohomology. -/
theorem periodClass_smul_map (P : HolomorphicPeriodMap V B) (c : ℂ) (a : Coefficients V B) :
    periodClass P (c • a) = CategoryTheory.Sheaf.H.map
      (PeriodFamilyHigherDirectImage.Zero.totalScalarEnd P c) 1 (periodClass P a) := by
  exact (congrArg (fun d => HolomorphicPicard.CechExtension.classOf d (coverOpen_covers P))
    (cocycle_smul_map P c a)).trans
      (HolomorphicPicard.CechExtension.classOf_naturality
        (PeriodFamilyHigherDirectImage.Zero.totalScalarEnd P c) (cocycle P a)
        (coverOpen_covers P)).symm

/-- The actual period class is complex-linear for the sheaf-induced
native scalar action. -/
theorem periodClass_smul (P : HolomorphicPeriodMap V B) (c : ℂ) (a : Coefficients V B) :
    letI := totalCohomologyModule P 1
    periodClass P (c • a) = c • periodClass P a := periodClass_smul_map P c a

/-- A genuine complex-linear map into the original native cohomology,
not a replacement group or a transported vector-space structure. -/
def periodClassLinearMap (P : HolomorphicPeriodMap V B) :
    letI := totalCohomologyModule P 1
    Coefficients V B →ₗ[ℂ] CategoryTheory.Sheaf.H.{0}
      (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) 1 := by
  letI := totalCohomologyModule P 1
  exact { periodClassHom P with map_smul' := periodClass_smul P }

@[simp] theorem periodClassLinearMap_apply (P : HolomorphicPeriodMap V B)
    (a : Coefficients V B) :
    letI := totalCohomologyModule P 1
    periodClassLinearMap P a = periodClass P a := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle
