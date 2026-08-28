import Wikipedia.HopfProblem.SheafSingularCupComparisonSingularBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainSingular
import Wikipedia.HopfProblem.SheafCupProductResolutionCoface

/-!
# The original singular differential and its literal coface complex

Evaluation on the original singular-simplex generators gives actual
isomorphisms of short complexes. Thus their homology comparisons use the
native singular cochain differential, not a separately postulated model.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.Singular

open FirstHurewicz

open ConstantSheafSingularComparison

variable (X : Type) [TopologicalSpace X] (R : Type) [CommRing R]

/-- Evaluation of an original additive cochain on its original simplex generators. -/
abbrev evaluation (n : ℕ) :
    Cochains X (AddCommGrpCat.of R) n ≃+ Values X R n :=
  cochainEvalEquiv X (AddCommGrpCat.of R) n

/-- The categorical form of the original cochain evaluation equivalence. -/
def evaluationIso (n : ℕ) :
    (singularCochainComplex X (AddCommGrpCat.of R)).X n ≅
      AddCommGrpCat.of (Values X R n) :=
  (evaluation X R n).toAddCommGrpIso

theorem evaluation_d0 (a : Cochains X (AddCommGrpCat.of R) 0) :
    evaluation X R 1 ((singularCochainComplex X (AddCommGrpCat.of R)).d 0 1 a) =
      (cofaceData X R).d0 (evaluation X R 0 a) := by
  ext σ
  change (singularCochainComplex X (AddCommGrpCat.of R)).d 0 1 a
    (simplexChain X 1 σ) = _
  rw [singularCochainComplex_d_simplex]
  simp [Fin.sum_univ_succ, cofaceData, SheafCupProduct.Coface.Data.d0_apply,
    face_apply, evaluation, sub_eq_add_neg]

theorem evaluation_d1 (a : Cochains X (AddCommGrpCat.of R) 1) :
    evaluation X R 2 ((singularCochainComplex X (AddCommGrpCat.of R)).d 1 2 a) =
      (cofaceData X R).d1 (evaluation X R 1 a) := by
  ext σ
  change (singularCochainComplex X (AddCommGrpCat.of R)).d 1 2 a
    (simplexChain X 2 σ) = _
  rw [singularCochainComplex_d_simplex]
  simp [Fin.sum_univ_succ, cofaceData, SheafCupProduct.Coface.Data.d1_apply,
    face_apply, evaluation, sub_eq_add_neg, add_assoc]

theorem evaluation_d2 (a : Cochains X (AddCommGrpCat.of R) 2) :
    evaluation X R 3 ((singularCochainComplex X (AddCommGrpCat.of R)).d 2 3 a) =
      (cofaceData X R).d2 (evaluation X R 2 a) := by
  ext σ
  change (singularCochainComplex X (AddCommGrpCat.of R)).d 2 3 a
    (simplexChain X 3 σ) = _
  rw [singularCochainComplex_d_simplex]
  simp only [Fin.sum_univ_succ, cofaceData, SheafCupProduct.Coface.Data.d2_apply,
    evaluation, sub_eq_add_neg, add_assoc]
  simp

/-- The actual degree-one singular short complex is the literal coface complex. -/
def oneComplexIso :
    (singularCochainComplex X (AddCommGrpCat.of R)).sc 1 ≅
      SheafCupProductResolution.Coface.oneComplex (cofaceData X R) :=
  (singularCochainComplex X (AddCommGrpCat.of R)).isoSc' 0 1 2
    (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1) ≪≫
      ShortComplex.isoMk (evaluationIso X R 0) (evaluationIso X R 1)
        (evaluationIso X R 2)
        (by ext a; exact (evaluation_d0 X R a).symm)
        (by ext a; exact (evaluation_d1 X R a).symm)

/-- The actual degree-two singular short complex is the literal coface complex. -/
def twoComplexIso :
    (singularCochainComplex X (AddCommGrpCat.of R)).sc 2 ≅
      SheafCupProductResolution.Coface.twoComplex (cofaceData X R) :=
  (singularCochainComplex X (AddCommGrpCat.of R)).isoSc' 1 2 3
    (CochainComplex.prev_nat_succ 1) (CochainComplex.next ℕ 2) ≪≫
      ShortComplex.isoMk (evaluationIso X R 1) (evaluationIso X R 2)
        (evaluationIso X R 3)
        (by ext a; exact (evaluation_d1 X R a).symm)
        (by ext a; exact (evaluation_d2 X R a).symm)

/-- Native singular first cohomology is its actual cocycle/coboundary quotient. -/
def oneHomologyIso :
    (singularCochainComplex X (AddCommGrpCat.of R)).homology 1 ≅
      AddCommGrpCat.of (cofaceData X R).CohomologyOne :=
  ShortComplex.homologyMapIso (oneComplexIso X R) ≪≫
    SheafCupProductResolution.Coface.oneHomologyIso (cofaceData X R)

/-- Native singular second cohomology is its actual cocycle/coboundary quotient. -/
def twoHomologyIso :
    (singularCochainComplex X (AddCommGrpCat.of R)).homology 2 ≅
      AddCommGrpCat.of (cofaceData X R).CohomologyTwo :=
  ShortComplex.homologyMapIso (twoComplexIso X R) ≪≫
    SheafCupProductResolution.Coface.twoHomologyIso (cofaceData X R)

def oneHomologyEquiv :
    (singularCochainComplex X (AddCommGrpCat.of R)).homology 1 ≃+
      (cofaceData X R).CohomologyOne :=
  (oneHomologyIso X R).addCommGroupIsoToAddEquiv

def twoHomologyEquiv :
    (singularCochainComplex X (AddCommGrpCat.of R)).homology 2 ≃+
      (cofaceData X R).CohomologyTwo :=
  (twoHomologyIso X R).addCommGroupIsoToAddEquiv

end Wikipedia.HopfProblem.SheafSingularCupComparison.Singular
