import Wikipedia.HopfProblem.SheafCupProductGodementCofaceNaturality
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalAlgebra

/-!
# Actual triangular bicosimplicial ring sheaves

The ten objects below are ring sheaves, and every face is a morphism of
those actual sheaves. Evaluating on an open gives the original literal
ring diagrams and Alexander--Whitney products.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.Bicosimplicial

open SheafCupProduct.GodementRing

universe v u

/-- Ordinary coface identities in the original category. -/
def FaceIdentities {C : Type u} [Category.{v} C] {n : ℕ} {A B E : C}
    (f : Fin (n + 2) → (A ⟶ B)) (g : Fin (n + 3) → (B ⟶ E)) : Prop :=
  ∀ i j, i ≤ j → f i ≫ g j.succ = f j ≫ g i.castSucc

/-- Actual ring sheaves, faces, and their original commuting identities. -/
structure Data (X : TopCat.{0}) where
  R00 : RingSheaf X
  R10 : RingSheaf X
  R01 : RingSheaf X
  R20 : RingSheaf X
  R11 : RingSheaf X
  R02 : RingSheaf X
  R30 : RingSheaf X
  R21 : RingSheaf X
  R12 : RingSheaf X
  R03 : RingSheaf X
  v00 : Fin 2 → (R00 ⟶ R10)
  h00 : Fin 2 → (R00 ⟶ R01)
  v10 : Fin 3 → (R10 ⟶ R20)
  h10 : Fin 2 → (R10 ⟶ R11)
  v01 : Fin 2 → (R01 ⟶ R11)
  h01 : Fin 3 → (R01 ⟶ R02)
  v20 : Fin 4 → (R20 ⟶ R30)
  h20 : Fin 2 → (R20 ⟶ R21)
  v11 : Fin 3 → (R11 ⟶ R21)
  h11 : Fin 3 → (R11 ⟶ R12)
  v02 : Fin 2 → (R02 ⟶ R12)
  h02 : Fin 4 → (R02 ⟶ R03)
  cofaceV00 : FaceIdentities v00 v10
  cofaceV10 : FaceIdentities v10 v20
  cofaceV01 : FaceIdentities v01 v11
  cofaceH00 : FaceIdentities h00 h01
  cofaceH01 : FaceIdentities h01 h02
  cofaceH10 : FaceIdentities h10 h11
  mixed00 : ∀ i j, h00 j ≫ v01 i = v00 i ≫ h10 j
  mixed10 : ∀ i j, h10 j ≫ v11 i = v10 i ≫ h20 j
  mixed01 : ∀ i j, h01 j ≫ v02 i = v01 i ≫ h11 j

namespace Data

variable {X : TopCat.{0}} (D : Data X)

/-- Evaluate the actual ring-sheaf diagram on an actual open. -/
def sectionData (U : (Opens X)ᵒᵖ) :
    TotalAlgebra.Data (D.R00.obj.obj U) (D.R10.obj.obj U) (D.R01.obj.obj U)
      (D.R20.obj.obj U) (D.R11.obj.obj U) (D.R02.obj.obj U)
      (D.R30.obj.obj U) (D.R21.obj.obj U) (D.R12.obj.obj U) (D.R03.obj.obj U) where
  v00 i := ((D.v00 i).hom.app U).hom
  h00 i := ((D.h00 i).hom.app U).hom
  v10 i := ((D.v10 i).hom.app U).hom
  h10 i := ((D.h10 i).hom.app U).hom
  v01 i := ((D.v01 i).hom.app U).hom
  h01 i := ((D.h01 i).hom.app U).hom
  v20 i := ((D.v20 i).hom.app U).hom
  h20 i := ((D.h20 i).hom.app U).hom
  v11 i := ((D.v11 i).hom.app U).hom
  h11 i := ((D.h11 i).hom.app U).hom
  v02 i := ((D.v02 i).hom.app U).hom
  h02 i := ((D.h02 i).hom.app U).hom
  cofaceV00 i j h := congrArg (fun f => (f.hom.app U).hom) (D.cofaceV00 i j h)
  cofaceV10 i j h := congrArg (fun f => (f.hom.app U).hom) (D.cofaceV10 i j h)
  cofaceV01 i j h := congrArg (fun f => (f.hom.app U).hom) (D.cofaceV01 i j h)
  cofaceH00 i j h := congrArg (fun f => (f.hom.app U).hom) (D.cofaceH00 i j h)
  cofaceH01 i j h := congrArg (fun f => (f.hom.app U).hom) (D.cofaceH01 i j h)
  cofaceH10 i j h := congrArg (fun f => (f.hom.app U).hom) (D.cofaceH10 i j h)
  mixed00 i j := congrArg (fun f => (f.hom.app U).hom) (D.mixed00 i j)
  mixed10 i j := congrArg (fun f => (f.hom.app U).hom) (D.mixed10 i j)
  mixed01 i j := congrArg (fun f => (f.hom.app U).hom) (D.mixed01 i j)

abbrev globalData := D.sectionData (op ⊤)

end Data

end Wikipedia.HopfProblem.SheafSingularCupComparison.Bicosimplicial
