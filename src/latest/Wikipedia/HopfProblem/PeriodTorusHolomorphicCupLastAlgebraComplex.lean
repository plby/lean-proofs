import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupLastAlgebraBasic

/-!
# The original row short complexes and their literal total maps
-/

noncomputable section

open CategoryTheory

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastAlgebra.Data

variable {A R0 R1 R2 R3 : Type u}
  [CommRing A] [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  {D : Algebra.Data R0 R1 R2 R3} (F : Data A D)

/-- The original row complex `A → A × A → A`, with gradient and curl. -/
def rowOneComplex : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (AddCommGrpCat.ofHom F.rowD0) (AddCommGrpCat.ofHom F.rowD1) (by
    apply AddCommGrpCat.hom_ext
    exact F.rowD1_comp_rowD0)

/-- The original row complex `A × A → A → PUnit`, with curl and zero. -/
def rowTwoComplex : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (AddCommGrpCat.ofHom F.rowD1) (AddCommGrpCat.ofHom F.rowD2) (by
    apply AddCommGrpCat.hom_ext
    exact F.rowD2_comp_rowD1)

/-- The literal degree-zero, one, and two row maps form an actual short-complex map. -/
def oneComplexMap : F.rowOneComplex ⟶ D.complexData.oneComplex where
  τ₁ := AddCommGrpCat.ofHom F.mapZero
  τ₂ := AddCommGrpCat.ofHom F.mapOne
  τ₃ := AddCommGrpCat.ofHom F.mapTwo
  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun x => (F.d0_comm x).symm)
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun x => (F.d1_comm x).symm)

/-- The literal degree-one, two, and three row maps form an actual short-complex map. -/
def twoComplexMap : F.rowTwoComplex ⟶ D.complexData.twoComplex where
  τ₁ := AddCommGrpCat.ofHom F.mapOne
  τ₂ := AddCommGrpCat.ofHom F.mapTwo
  τ₃ := AddCommGrpCat.ofHom F.mapThree
  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun x => (F.d1_comm x).symm)
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (fun x => (F.d2_comm x).symm)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastAlgebra.Data
