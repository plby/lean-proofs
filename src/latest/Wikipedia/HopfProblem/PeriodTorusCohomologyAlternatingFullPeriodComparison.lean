import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingFullPeriodNaturality
import Wikipedia.HopfProblem.PeriodTorusFirstHomologyComparison
import Wikipedia.HopfProblem.SingularCohomologyFreeHomotopy

/-!
# The actual cohomology comparison between the two period markings

The identity on the covering complex vector space induces the genuine
biholomorphism between the ordinary `[Z | I]` and full `[I | Z]` tori.
Its native cohomology pullback exchanges the two integer coordinate
blocks.  The comparison on second homology is proved from actual marked
period loops and naturality of their actual products.

Consequently the six alternating coefficients are permuted with their
required signs.  The two markings are never identified by an identity
map on their four integer coordinates.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin
open PeriodTorusTypeOneOne

/-- The actual integer-coordinate map from `[Z | I]` to `[I | Z]`. -/
def fullPeriodComparisonLatticeMap : Lattice →ₗ[ℤ] Lattice :=
  (PeriodDomain.fullPeriodCoordinatesEquiv.trans
    FullPeriodMatrix.integerCoordinatesEquiv).toLinearMap

@[simp] theorem fullPeriodComparisonLatticeMap_apply (c : Lattice) :
    fullPeriodComparisonLatticeMap c = ![c 2, c 3, c 0, c 1] := rfl

theorem fullPeriodComparisonLatticeMap_involutive :
    Function.Involutive fullPeriodComparisonLatticeMap := by
  intro c
  ext i
  fin_cases i <;> rfl

/-- The full-period integer pairs retain the original comparison's actual period marking. -/
@[simp] theorem fullPeriodComparisonLatticeMap_coordinates (c : Lattice) :
    FullPeriodMatrix.integerCoordinatesEquiv.symm (fullPeriodComparisonLatticeMap c) =
      PeriodDomain.fullPeriodCoordinatesEquiv c := by
  change FullPeriodMatrix.integerCoordinatesEquiv.symm
    (FullPeriodMatrix.integerCoordinatesEquiv (PeriodDomain.fullPeriodCoordinatesEquiv c)) = _
  exact FullPeriodMatrix.integerCoordinatesEquiv.symm_apply_apply _

/-- Exchanging the period blocks gives precisely these six coefficients and signs. -/
theorem fullPeriodComparison_coefficientPullback (E : Fin 6 → ℤ) :
    coefficientPullback fullPeriodComparisonLatticeMap E =
      ![E 5, -E 1, -E 3, -E 2, -E 4, E 0] := by
  ext k
  rw [coefficientPullback_apply]
  fin_cases k <;>
    simp [fullPeriodComparisonLatticeMap_apply, coefficientPair,
      coordinateForm_apply, coordinateValue]

theorem fullPeriodComparison_coefficientPullback_involutive :
    Function.Involutive (coefficientPullback fullPeriodComparisonLatticeMap) := by
  intro E
  funext k
  fin_cases k <;> simp [fullPeriodComparison_coefficientPullback]

/-- Additivity of the actual identity-induced comparison follows on quotient representatives. -/
theorem fullPeriodComparison_add (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) (x y : p.Torus) :
    p.fullPeriodContinuousMap q h (x + y) =
      p.fullPeriodContinuousMap q h x + p.fullPeriodContinuousMap q h y := by
  obtain ⟨x, rfl⟩ := p.lattice.mkQ_surjective x
  obtain ⟨y, rfl⟩ := p.lattice.mkQ_surjective y
  rw [← map_add, p.fullPeriodContinuousMap_mkQ,
    p.fullPeriodContinuousMap_mkQ, p.fullPeriodContinuousMap_mkQ, map_add]

/-- The literal comparison on positive first-homology markings has the proved block swap. -/
theorem fullPeriodComparison_h1 (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) (v : Lattice) :
    singularHomologyMap (p.fullPeriodContinuousMap q h) 1 (p.singularH1Equiv.symm v) =
      fullPeriodCoordinateH1 q (fullPeriodComparisonLatticeMap v) := by
  rw [singularHomologyMap_one, p.singularH1Equiv_symm_apply,
    p.fullPeriod_inducedHomology_periodLoop q h, fullPeriodCoordinateH1_periodLoop,
    fullPeriodComparisonLatticeMap_coordinates]

/-- The actual products of positive periods commute with the genuine comparison map. -/
theorem fullPeriodComparison_wedgeTwo (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) :
    (singularHomologyMap (p.fullPeriodContinuousMap q h) 2).comp (periodTorusWedgeTwo p) =
      (fullPeriodTorusWedgeTwo q).comp (exteriorPower.map 2 fullPeriodComparisonLatticeMap) := by
  let := periodTorus_homology_torsionFree p 2
  let := fullPeriodTorus_homology_torsionFree q 2
  exact latticeWedgeTwo_natural (p.fullPeriodContinuousMap q h) (fullPeriodComparison_add p q h)
    p.singularH1Equiv.symm.toLinearMap (fullPeriodCoordinateH1 q)
    fullPeriodComparisonLatticeMap (fullPeriodComparison_h1 p q h)

/-- The actual exterior-square marking changes by the exterior square of the block swap. -/
theorem fullPeriodComparison_h2 (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) (z : SingularHomology p.Torus 2) :
    fullPeriodTorusH2ExteriorEquiv q (singularHomologyMap (p.fullPeriodContinuousMap q h) 2 z) =
      exteriorPower.map 2 fullPeriodComparisonLatticeMap (periodTorusH2ExteriorEquiv p z) := by
  obtain ⟨v, rfl⟩ := periodTorusWedgeTwo_surjective p z
  have hv := LinearMap.congr_fun (fullPeriodComparison_wedgeTwo p q h) v
  change singularHomologyMap (p.fullPeriodContinuousMap q h) 2 (periodTorusWedgeTwo p v) =
    fullPeriodTorusWedgeTwo q (exteriorPower.map 2 fullPeriodComparisonLatticeMap v) at hv
  rw [hv, fullPeriodTorusH2ExteriorEquiv_wedge, periodTorusH2ExteriorEquiv_wedge]

/-- The actual biholomorphism induces the native contravariant cohomology equivalence. -/
def fullPeriodComparisonCohomologyEquiv (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) (n : ℕ) :
    SingularCohomology q.Torus n ≃ₗ[ℤ] SingularCohomology p.Torus n :=
  homeomorphCohomologyEquiv (p.fullPeriodBiholomorph q h).toHomeomorph n

@[simp] theorem fullPeriodComparisonCohomologyEquiv_apply (p : PeriodDomain)
    (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock) (n : ℕ)
    (a : SingularCohomology q.Torus n) :
    fullPeriodComparisonCohomologyEquiv p q h n a =
      singularCohomologyPullback (p.fullPeriodContinuousMap q h) n a := rfl

@[simp] theorem fullPeriodComparisonCohomologyEquiv_symm_apply (p : PeriodDomain)
    (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock) (n : ℕ)
    (a : SingularCohomology p.Torus n) :
    (fullPeriodComparisonCohomologyEquiv p q h n).symm a =
      singularCohomologyPullback
        ((p.fullPeriodBiholomorph q h).toHomeomorph.symm : C(q.Torus, p.Torus)) n a := rfl

/-- Pullback by the actual comparison acts on alternating classes by the proved block swap. -/
theorem fullAlternatingClass_pullback_comparison (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    singularCohomologyPullback (p.fullPeriodContinuousMap q h) 2 (fullAlternatingClass q B) =
      alternatingClass p (B.compLinearMap fullPeriodComparisonLatticeMap) := by
  apply (evaluationEquiv p 2).injective
  apply LinearMap.ext
  intro z
  simp only [evaluationEquiv_apply, singularEvaluation_naturality,
    fullAlternatingClass_evaluate, alternatingClass_evaluate, fullPeriodComparison_h2]
  rw [exteriorLift_compLinearMap]
  rfl

/-- Every actual native class has the same marked comparison, not only chosen generators. -/
theorem cohomologyAlternatingEquiv_pullback_comparison (p : PeriodDomain)
    (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock)
    (a : SingularCohomology q.Torus 2) :
    cohomologyAlternatingEquiv p
        (singularCohomologyPullback (p.fullPeriodContinuousMap q h) 2 a) =
      (fullCohomologyAlternatingEquiv q a).compLinearMap fullPeriodComparisonLatticeMap := by
  have ha := congrArg (cohomologyAlternatingEquiv p)
    (fullAlternatingClass_pullback_comparison p q h (fullCohomologyAlternatingEquiv q a))
  simpa only [fullAlternatingClass_fullCohomologyAlternatingEquiv,
    cohomologyAlternatingEquiv_alternatingClass] using ha

/-- The actual comparison pulls a full-period coefficient class back with the true lattice map. -/
theorem fullCoefficientClass_pullback_comparison (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) (E : Fin 6 → ℤ) :
    singularCohomologyPullback (p.fullPeriodContinuousMap q h) 2 (fullCoefficientClass q E) =
      coefficientClass p (coefficientPullback fullPeriodComparisonLatticeMap E) := by
  rw [fullCoefficientClass_asAlternating, coefficientClass_asAlternating,
    coefficientAlternatingEquiv_coefficientPullback]
  exact fullAlternatingClass_pullback_comparison p q h _

/-- The native pullback has the literal signed permutation of the original six coefficients. -/
theorem fullCoefficientClass_pullback_comparison_explicit (p : PeriodDomain)
    (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock) (E : Fin 6 → ℤ) :
    singularCohomologyPullback (p.fullPeriodContinuousMap q h) 2 (fullCoefficientClass q E) =
      coefficientClass p ![E 5, -E 1, -E 3, -E 2, -E 4, E 0] := by
  rw [fullCoefficientClass_pullback_comparison, fullPeriodComparison_coefficientPullback]

/-- The actual cohomology equivalence, evaluated on any full-period coefficient class. -/
theorem fullPeriodComparisonCohomologyEquiv_fullCoefficientClass (p : PeriodDomain)
    (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock) (E : Fin 6 → ℤ) :
    fullPeriodComparisonCohomologyEquiv p q h 2 (fullCoefficientClass q E) =
      coefficientClass p ![E 5, -E 1, -E 3, -E 2, -E 4, E 0] := by
  rw [fullPeriodComparisonCohomologyEquiv_apply,
    fullCoefficientClass_pullback_comparison_explicit]

/-- The genuine inverse equivalence transports the same geometric form back to full slots. -/
theorem fullPeriodComparisonCohomologyEquiv_symm_coefficientClass (p : PeriodDomain)
    (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock) (E : Fin 6 → ℤ) :
    (fullPeriodComparisonCohomologyEquiv p q h 2).symm (coefficientClass p E) =
      fullCoefficientClass q (coefficientPullback fullPeriodComparisonLatticeMap E) := by
  apply (fullPeriodComparisonCohomologyEquiv p q h 2).injective
  rw [LinearEquiv.apply_symm_apply, fullPeriodComparisonCohomologyEquiv_apply,
    fullCoefficientClass_pullback_comparison, fullPeriodComparison_coefficientPullback_involutive]

/-- The inverse has the same signed permutation because the block swap is involutive. -/
theorem fullPeriodComparisonCohomologyEquiv_symm_coefficientClass_explicit
    (p : PeriodDomain) (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock)
    (E : Fin 6 → ℤ) :
    (fullPeriodComparisonCohomologyEquiv p q h 2).symm (coefficientClass p E) =
      fullCoefficientClass q ![E 5, -E 1, -E 3, -E 2, -E 4, E 0] := by
  rw [fullPeriodComparisonCohomologyEquiv_symm_coefficientClass,
    fullPeriodComparison_coefficientPullback]

/-- Literal pullback by the inverse biholomorphism agrees with the marked inverse comparison. -/
theorem coefficientClass_pullback_comparison_symm (p : PeriodDomain)
    (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock) (E : Fin 6 → ℤ) :
    singularCohomologyPullback
        ((p.fullPeriodBiholomorph q h).toHomeomorph.symm : C(q.Torus, p.Torus)) 2
        (coefficientClass p E) =
      fullCoefficientClass q ![E 5, -E 1, -E 3, -E 2, -E 4, E 0] := by
  rw [← fullPeriodComparisonCohomologyEquiv_symm_apply,
    fullPeriodComparisonCohomologyEquiv_symm_coefficientClass_explicit]

end Wikipedia.HopfProblem.PeriodTorusCohomology
