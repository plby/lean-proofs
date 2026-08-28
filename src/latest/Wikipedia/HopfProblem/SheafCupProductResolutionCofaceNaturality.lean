import Wikipedia.HopfProblem.SheafCupProductResolutionCoface

/-!
# Coefficient naturality of the literal coface homology comparisons

The maps on canonical short-complex homology agree with the original
degreewise ring maps on the already constructed cocycle quotients.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProductResolution.Coface

universe u

variable {R0 R1 R2 R3 S0 S1 S2 S3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  [CommRing S0] [CommRing S1] [CommRing S2] [CommRing S3]
  {D : SheafCupProduct.Coface.Data R0 R1 R2 R3}
  {E : SheafCupProduct.Coface.Data S0 S1 S2 S3} (M : D.Morphism E)

/-- The original degreewise coefficient maps on the first coface complex. -/
def oneMap : oneComplex D ⟶ oneComplex E where
  τ₁ := AddCommGrpCat.ofHom M.f0.toAddMonoidHom
  τ₂ := AddCommGrpCat.ofHom M.f1.toAddMonoidHom
  τ₃ := AddCommGrpCat.ofHom M.f2.toAddMonoidHom
  comm₁₂ := by ext r; exact (M.d0_comm r).symm
  comm₂₃ := by ext a; exact (M.d1_comm a).symm

/-- The original degreewise coefficient maps on the second coface complex. -/
def twoMap : twoComplex D ⟶ twoComplex E where
  τ₁ := AddCommGrpCat.ofHom M.f1.toAddMonoidHom
  τ₂ := AddCommGrpCat.ofHom M.f2.toAddMonoidHom
  τ₃ := AddCommGrpCat.ofHom M.f3.toAddMonoidHom
  comm₁₂ := by ext a; exact (M.d1_comm a).symm
  comm₂₃ := by ext a; exact (M.d2_comm a).symm

/-- The explicit first cocycle and quotient maps are genuine left homology map data. -/
def oneHomologyMapData : ShortComplex.LeftHomologyMapData (oneMap M)
    (oneComplex D).abLeftHomologyData (oneComplex E).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom M.cocycleOneMap
  φH := AddCommGrpCat.ofHom M.cohomologyOneMap
  commi := by ext a; rfl
  commf' := by ext r; exact M.cocycleOneMap_boundary r
  commπ := by ext a; exact M.cohomologyOneMap_classOne a

/-- The explicit second cocycle and quotient maps are genuine left homology map data. -/
def twoHomologyMapData : ShortComplex.LeftHomologyMapData (twoMap M)
    (twoComplex D).abLeftHomologyData (twoComplex E).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom M.cocycleTwoMap
  φH := AddCommGrpCat.ofHom M.cohomologyTwoMap
  commi := by ext a; rfl
  commf' := by ext a; exact M.cocycleTwoMap_boundary a
  commπ := by ext a; exact M.cohomologyTwoMap_classTwo a

/-- Canonical first homology maps are the actual coefficient maps on first quotients. -/
theorem oneHomologyIso_naturality :
    ShortComplex.homologyMap (oneMap M) ≫ (oneHomologyIso E).hom =
      (oneHomologyIso D).hom ≫ AddCommGrpCat.ofHom M.cohomologyOneMap := by
  have hm : ShortComplex.leftHomologyMap' (oneMap M)
      (oneComplex D).abLeftHomologyData (oneComplex E).abLeftHomologyData =
        AddCommGrpCat.ofHom M.cohomologyOneMap :=
    (oneHomologyMapData M).leftHomologyMap'_eq
  exact (ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality (oneMap M)
    (oneComplex D).abLeftHomologyData (oneComplex E).abLeftHomologyData).symm.trans
      (congrArg (fun f => (oneHomologyIso D).hom ≫ f) hm)

/-- Canonical second homology maps are the actual coefficient maps on second quotients. -/
theorem twoHomologyIso_naturality :
    ShortComplex.homologyMap (twoMap M) ≫ (twoHomologyIso E).hom =
      (twoHomologyIso D).hom ≫ AddCommGrpCat.ofHom M.cohomologyTwoMap := by
  have hm : ShortComplex.leftHomologyMap' (twoMap M)
      (twoComplex D).abLeftHomologyData (twoComplex E).abLeftHomologyData =
        AddCommGrpCat.ofHom M.cohomologyTwoMap :=
    (twoHomologyMapData M).leftHomologyMap'_eq
  exact (ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality (twoMap M)
    (twoComplex D).abLeftHomologyData (twoComplex E).abLeftHomologyData).symm.trans
      (congrArg (fun f => (twoHomologyIso D).hom ≫ f) hm)

end Wikipedia.HopfProblem.SheafCupProductResolution.Coface
