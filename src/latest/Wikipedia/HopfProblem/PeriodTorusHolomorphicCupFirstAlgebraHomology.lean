import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstAlgebraQuotient
import Wikipedia.HopfProblem.SheafCupProductResolutionCoface

/-!
# The actual first-column maps on canonical short-complex homology

The literal cochain maps induce the quotient maps already defined by
boundary descent. Their agreement is proved with the original cycle,
boundary, and projection maps of additive short-complex homology.
-/

noncomputable section

open CategoryTheory

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstAlgebra.Data

open SheafCupProductResolution

variable {A0 A1 A2 A3 R0 R1 R2 R3 : Type u}
  [CommRing A0] [CommRing A1] [CommRing A2] [CommRing A3]
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  {E : SheafCupProduct.Coface.Data A0 A1 A2 A3}
  {D : Algebra.Data R0 R1 R2 R3} (F : Data E D)

/-- The original first-column maps on the first native short complexes. -/
def oneComplexMap : Coface.oneComplex E ⟶ D.complexData.oneComplex where
  τ₁ := AddCommGrpCat.ofHom F.mapZero
  τ₂ := AddCommGrpCat.ofHom F.mapOne
  τ₃ := AddCommGrpCat.ofHom F.mapTwo
  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun x => (F.d0_comm x).symm)
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun x => (F.d1_comm x).symm)

/-- The original first-column maps on the second native short complexes. -/
def twoComplexMap : Coface.twoComplex E ⟶ D.complexData.twoComplex where
  τ₁ := AddCommGrpCat.ofHom F.mapOne
  τ₂ := AddCommGrpCat.ofHom F.mapTwo
  τ₃ := AddCommGrpCat.ofHom F.mapThree
  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun x => (F.d1_comm x).symm)
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun x => (F.d2_comm x).symm)

/-- The first kernel and quotient maps are genuine native homology-map data. -/
def oneHomologyMapData : ShortComplex.LeftHomologyMapData F.oneComplexMap
    (Coface.oneComplex E).abLeftHomologyData D.complexData.oneComplex.abLeftHomologyData where
  φK := AddCommGrpCat.ofHom F.cocycleOneMap
  φH := AddCommGrpCat.ofHom F.cohomologyOneMap
  commi := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun _ => rfl)
  commf' := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext F.cocycleOneMap_boundary
  commπ := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext F.cohomologyOneMap_classOne

/-- The second kernel and quotient maps are genuine native homology-map data. -/
def twoHomologyMapData : ShortComplex.LeftHomologyMapData F.twoComplexMap
    (Coface.twoComplex E).abLeftHomologyData D.complexData.twoComplex.abLeftHomologyData where
  φK := AddCommGrpCat.ofHom F.cocycleTwoMap
  φH := AddCommGrpCat.ofHom F.cohomologyTwoMap
  commi := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun _ => rfl)
  commf' := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext F.cocycleTwoMap_boundary
  commπ := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext F.cohomologyTwoMap_classTwo

/-- The first native homology map is exactly the original first quotient map. -/
theorem oneHomologyIso_naturality :
    ShortComplex.homologyMap F.oneComplexMap ≫ D.oneHomologyIso.hom =
      (Coface.oneHomologyIso E).hom ≫ AddCommGrpCat.ofHom F.cohomologyOneMap := by
  have hm : ShortComplex.leftHomologyMap' F.oneComplexMap
      (Coface.oneComplex E).abLeftHomologyData D.complexData.oneComplex.abLeftHomologyData =
        AddCommGrpCat.ofHom F.cohomologyOneMap := F.oneHomologyMapData.leftHomologyMap'_eq
  exact (ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality F.oneComplexMap
    (Coface.oneComplex E).abLeftHomologyData D.complexData.oneComplex.abLeftHomologyData).symm.trans
      (congrArg (fun f => (Coface.oneHomologyIso E).hom ≫ f) hm)

/-- The second native homology map is exactly the original second quotient map. -/
theorem twoHomologyIso_naturality :
    ShortComplex.homologyMap F.twoComplexMap ≫ D.twoHomologyIso.hom =
      (Coface.twoHomologyIso E).hom ≫ AddCommGrpCat.ofHom F.cohomologyTwoMap := by
  have hm : ShortComplex.leftHomologyMap' F.twoComplexMap
      (Coface.twoComplex E).abLeftHomologyData D.complexData.twoComplex.abLeftHomologyData =
        AddCommGrpCat.ofHom F.cohomologyTwoMap := F.twoHomologyMapData.leftHomologyMap'_eq
  exact (ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality F.twoComplexMap
    (Coface.twoComplex E).abLeftHomologyData D.complexData.twoComplex.abLeftHomologyData).symm.trans
      (congrArg (fun f => (Coface.twoHomologyIso E).hom ≫ f) hm)

/-- Pointwise first native homology compatibility with the original quotient map. -/
theorem oneHomologyMap_apply (x : (Coface.oneComplex E).homology) :
    D.oneHomologyEquiv (ShortComplex.homologyMap F.oneComplexMap x) =
      F.cohomologyOneMap ((Coface.oneHomologyIso E).hom x) :=
  ConcreteCategory.congr_hom F.oneHomologyIso_naturality x

/-- Pointwise second native homology compatibility with the original quotient map. -/
theorem twoHomologyMap_apply (x : (Coface.twoComplex E).homology) :
    D.twoHomologyEquiv (ShortComplex.homologyMap F.twoComplexMap x) =
      F.cohomologyTwoMap ((Coface.twoHomologyIso E).hom x) :=
  ConcreteCategory.congr_hom F.twoHomologyIso_naturality x

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstAlgebra.Data
