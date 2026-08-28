import Wikipedia.HopfProblem.SheafSingularCupComparisonBicosimplicialBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryBasic
import Wikipedia.HopfProblem.SheafCupProductGodementExactBasic

/-!
# The actual additive double complex underlying the ring sheaves

The differentials are literal alternating sums after forgetting
multiplication. Their identities are checked on every original section,
using the already proved coface identities of the actual ring sheaves.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.Bicosimplicial

open SheafCupProduct.GodementRing

variable {X : TopCat.{0}}

def alternating0 {A B : RingSheaf X} (f : Fin 2 → (A ⟶ B)) :
    (forgetSheaf X).obj A ⟶ (forgetSheaf X).obj B :=
  (forgetSheaf X).map (f 0) - (forgetSheaf X).map (f 1)

def alternating1 {A B : RingSheaf X} (f : Fin 3 → (A ⟶ B)) :
    (forgetSheaf X).obj A ⟶ (forgetSheaf X).obj B :=
  (forgetSheaf X).map (f 0) - (forgetSheaf X).map (f 1) +
    (forgetSheaf X).map (f 2)

def alternating2 {A B : RingSheaf X} (f : Fin 4 → (A ⟶ B)) :
    (forgetSheaf X).obj A ⟶ (forgetSheaf X).obj B :=
  (forgetSheaf X).map (f 0) - (forgetSheaf X).map (f 1) +
    (forgetSheaf X).map (f 2) - (forgetSheaf X).map (f 3)

namespace Data

variable (D : Data X)

/-- The actual additive-sheaf diagram, retaining all original maps. -/
def categoryData : TotalCategory.Data
    ((forgetSheaf X).obj D.R00) ((forgetSheaf X).obj D.R10)
    ((forgetSheaf X).obj D.R01) ((forgetSheaf X).obj D.R20)
    ((forgetSheaf X).obj D.R11) ((forgetSheaf X).obj D.R02)
    ((forgetSheaf X).obj D.R30) ((forgetSheaf X).obj D.R21)
    ((forgetSheaf X).obj D.R12) ((forgetSheaf X).obj D.R03) where
  v00 := alternating0 D.v00
  h00 := alternating0 D.h00
  v10 := alternating1 D.v10
  h10 := alternating0 D.h10
  v01 := alternating0 D.v01
  h01 := alternating1 D.h01
  v20 := alternating2 D.v20
  h20 := alternating0 D.h20
  v11 := alternating1 D.v11
  h11 := alternating1 D.h11
  v02 := alternating0 D.v02
  h02 := alternating2 D.h02
  vertical00 := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    exact (D.sectionData U).complexData.v10_v00 s
  vertical10 := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    exact (D.sectionData U).complexData.v20_v10 s
  vertical01 := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    exact (D.sectionData U).complexData.v11_v01 s
  horizontal00 := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    exact (D.sectionData U).complexData.h01_h00 s
  horizontal01 := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    exact (D.sectionData U).complexData.h02_h01 s
  horizontal10 := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    exact (D.sectionData U).complexData.h11_h10 s
  mixed00 := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    exact (D.sectionData U).complexData.v01_h00 s
  mixed10 := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    exact (D.sectionData U).complexData.v11_h10 s
  mixed01 := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    exact (D.sectionData U).complexData.v02_h01 s

end Data

end Wikipedia.HopfProblem.SheafSingularCupComparison.Bicosimplicial
