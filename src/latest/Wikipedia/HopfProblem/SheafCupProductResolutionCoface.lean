import Wikipedia.HopfProblem.SheafCupProductCoface
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The actual coface quotients as canonical short-complex homology

The short complexes below use the literal alternating coface maps.
Their canonical abelian-group homology is exactly the already constructed
kernel/range quotient, including its formula on actual cocycles.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProductResolution.Coface

universe u

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  (D : SheafCupProduct.Coface.Data R0 R1 R2 R3)

/-- The literal first alternating complex of the given ring cofaces. -/
def oneComplex : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (AddCommGrpCat.ofHom D.d0) (AddCommGrpCat.ofHom D.d1) (by
    ext r
    exact D.d1_d0 r)

/-- The literal second alternating complex of the given ring cofaces. -/
def twoComplex : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (AddCommGrpCat.ofHom D.d1) (AddCommGrpCat.ofHom D.d2) (by
    ext a
    exact D.d2_d1 a)

@[simp] theorem oneComplex_abToCycles : (oneComplex D).abToCycles = D.boundaryOne := rfl

@[simp] theorem twoComplex_abToCycles : (twoComplex D).abToCycles = D.boundaryTwo := rfl

/-- The canonical actual homology comparison with the actual degree-one coface quotient. -/
def oneHomologyIso : (oneComplex D).homology ≅ AddCommGrpCat.of D.CohomologyOne :=
  (oneComplex D).abHomologyIso

/-- The canonical actual homology comparison with the actual degree-two coface quotient. -/
def twoHomologyIso : (twoComplex D).homology ≅ AddCommGrpCat.of D.CohomologyTwo :=
  (twoComplex D).abHomologyIso

private theorem abHomologyIso_class (S : ShortComplex AddCommGrpCat.{u}) :
    S.abCyclesIso.inv ≫ S.homologyπ ≫ S.abHomologyIso.hom =
      AddCommGrpCat.ofHom (QuotientAddGroup.mk' S.abToCycles.range) := by
  change S.abLeftHomologyData.cyclesIso.inv ≫ S.homologyπ ≫
    S.abLeftHomologyData.homologyIso.hom = S.abLeftHomologyData.π
  rw [S.abLeftHomologyData.homologyπ_comp_homologyIso_hom,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The comparison sends each literal first cocycle to its literal quotient class. -/
theorem oneHomologyIso_class :
    (oneComplex D).abCyclesIso.inv ≫ (oneComplex D).homologyπ ≫ (oneHomologyIso D).hom =
      AddCommGrpCat.ofHom D.classOne := abHomologyIso_class (oneComplex D)

/-- The comparison sends each literal second cocycle to its literal quotient class. -/
theorem twoHomologyIso_class :
    (twoComplex D).abCyclesIso.inv ≫ (twoComplex D).homologyπ ≫ (twoHomologyIso D).hom =
      AddCommGrpCat.ofHom D.classTwo := abHomologyIso_class (twoComplex D)

end Wikipedia.HopfProblem.SheafCupProductResolution.Coface
