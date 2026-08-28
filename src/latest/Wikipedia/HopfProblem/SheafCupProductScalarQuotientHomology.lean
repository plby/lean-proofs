import Wikipedia.HopfProblem.SheafCupProductScalarQuotientGroups
import Wikipedia.HopfProblem.SheafCupProductResolutionCoface

/-!
# Scalar compatibility of the actual coface homology comparisons

Multiplication is an additive complex endomorphism, not a unital ring
morphism. Its actual maps on kernels and quotient groups supply the
left-homology map data proving compatibility with canonical homology.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProduct.ScalarQuotient.CompatibleCoefficients

universe u v

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  {K : Type v} [CommRing K] {D : Coface.Data R0 R1 R2 R3}
  (c : CompatibleCoefficients K D)

/-- Literal multiplication on the original first alternating complex. -/
def oneComplexMap (z : K) : SheafCupProductResolution.Coface.oneComplex D ⟶
    SheafCupProductResolution.Coface.oneComplex D where
  τ₁ := AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (c.c0 z))
  τ₂ := AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (c.c1 z))
  τ₃ := AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (c.c2 z))
  comm₁₂ := by ext r; exact c.d0_mul z r
  comm₂₃ := by ext a; exact c.d1_mul z a

/-- Literal multiplication on the original second alternating complex. -/
def twoComplexMap (z : K) : SheafCupProductResolution.Coface.twoComplex D ⟶
    SheafCupProductResolution.Coface.twoComplex D where
  τ₁ := AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (c.c1 z))
  τ₂ := AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (c.c2 z))
  τ₃ := AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (c.c3 z))
  comm₁₂ := by ext a; exact c.d1_mul z a
  comm₂₃ := by ext a; exact c.d2_mul z a

/-- The actual first scalar quotient map is the induced homology map. -/
def oneHomologyMapData (z : K) : ShortComplex.LeftHomologyMapData (c.oneComplexMap z)
    (SheafCupProductResolution.Coface.oneComplex D).abLeftHomologyData
    (SheafCupProductResolution.Coface.oneComplex D).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom (c.cocycleScalarOne z)
  φH := AddCommGrpCat.ofHom (c.scalarOne z)
  commi := by ext a; rfl
  commf' := by ext r; exact c.cocycleScalarOne_boundary z r
  commπ := by ext a; exact c.scalarOne_class z a

/-- The actual second scalar quotient map is the induced homology map. -/
def twoHomologyMapData (z : K) : ShortComplex.LeftHomologyMapData (c.twoComplexMap z)
    (SheafCupProductResolution.Coface.twoComplex D).abLeftHomologyData
    (SheafCupProductResolution.Coface.twoComplex D).abLeftHomologyData where
  φK := AddCommGrpCat.ofHom (c.cocycleScalarTwo z)
  φH := AddCommGrpCat.ofHom (c.scalarTwo z)
  commi := by ext a; rfl
  commf' := by ext a; exact c.cocycleScalarTwo_boundary z a
  commπ := by ext a; exact c.scalarTwo_class z a

/-- Canonical first homology intertwines literal multiplication with its actual quotient map. -/
theorem oneHomologyIso_scalar (z : K) :
    ShortComplex.homologyMap (c.oneComplexMap z) ≫
        (SheafCupProductResolution.Coface.oneHomologyIso D).hom =
      (SheafCupProductResolution.Coface.oneHomologyIso D).hom ≫
        AddCommGrpCat.ofHom (c.scalarOne z) := by
  have hm : ShortComplex.leftHomologyMap' (c.oneComplexMap z)
      (SheafCupProductResolution.Coface.oneComplex D).abLeftHomologyData
      (SheafCupProductResolution.Coface.oneComplex D).abLeftHomologyData =
        AddCommGrpCat.ofHom (c.scalarOne z) :=
    (c.oneHomologyMapData z).leftHomologyMap'_eq
  exact (ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality (c.oneComplexMap z)
    (SheafCupProductResolution.Coface.oneComplex D).abLeftHomologyData
    (SheafCupProductResolution.Coface.oneComplex D).abLeftHomologyData).symm.trans
      (congrArg (fun f => (SheafCupProductResolution.Coface.oneHomologyIso D).hom ≫ f) hm)

/-- Canonical second homology intertwines literal multiplication with its actual quotient map. -/
theorem twoHomologyIso_scalar (z : K) :
    ShortComplex.homologyMap (c.twoComplexMap z) ≫
        (SheafCupProductResolution.Coface.twoHomologyIso D).hom =
      (SheafCupProductResolution.Coface.twoHomologyIso D).hom ≫
        AddCommGrpCat.ofHom (c.scalarTwo z) := by
  have hm : ShortComplex.leftHomologyMap' (c.twoComplexMap z)
      (SheafCupProductResolution.Coface.twoComplex D).abLeftHomologyData
      (SheafCupProductResolution.Coface.twoComplex D).abLeftHomologyData =
        AddCommGrpCat.ofHom (c.scalarTwo z) :=
    (c.twoHomologyMapData z).leftHomologyMap'_eq
  exact (ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality (c.twoComplexMap z)
    (SheafCupProductResolution.Coface.twoComplex D).abLeftHomologyData
    (SheafCupProductResolution.Coface.twoComplex D).abLeftHomologyData).symm.trans
      (congrArg (fun f => (SheafCupProductResolution.Coface.twoHomologyIso D).hom ≫ f) hm)

end Wikipedia.HopfProblem.SheafCupProduct.ScalarQuotient.CompatibleCoefficients
