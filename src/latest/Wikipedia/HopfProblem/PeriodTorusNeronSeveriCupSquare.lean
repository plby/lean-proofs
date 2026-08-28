import Wikipedia.HopfProblem.PeriodTorusNeronSeveriSpecial
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCupScalingEta

/-!
# Square-zero classes in the actual special-torus Néron--Severi image

Away from the actual exceptional locus, the native Chern image is `ℤη`.
The integer is recovered by evaluation on the original positive `u,w`
period cycle. Its genuine singular cup square evaluates to `12n²` on
the positive four-period product. Hence a class in this actual image has
zero cup square exactly when the class itself is zero.

The final statements apply to arbitrary original native holomorphic line
bundles. They use neither a complex-orientation comparison nor Poincaré
duality, algebraic dimension, or any meromorphic-function assumption.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open SingularCohomologyCup PeriodTorusCohomology PeriodTorusCohomologyCup
open PeriodTorusHigherHomology PeriodTorusTypeOneOne SpecialPeriods UpperHalfPlane

/-- The actual period evaluation recovers the unique coefficient of every native NS class. -/
theorem neronSeveri_special_eq_etaEvaluation_smul (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet)
    (a : SingularCohomology (specialPeriodMap.point z).Torus 2)
    (ha : a ∈ neronSeveri (specialPeriodMap.point z)) :
    a = etaEvaluation (specialPeriodMap.point z) a • etaClass (specialPeriodMap.point z) := by
  rw [neronSeveri_special_eq_zmultiples_eta z hz, AddSubgroup.mem_zmultiples_iff] at ha
  obtain ⟨n, hn⟩ := ha
  rw [← hn]
  simp only [map_zsmul, etaEvaluation_etaClass, zsmul_eq_mul, Int.cast_id, mul_one]

/-- The actual cup square of every native NS class, using its genuine period marking. -/
theorem neronSeveri_special_cup_square (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet)
    (a : SingularCohomology (specialPeriodMap.point z).Torus 2)
    (ha : a ∈ neronSeveri (specialPeriodMap.point z)) :
    cupProduct (specialPeriodMap.point z).Torus 2 2 a a =
      (12 * (etaEvaluation (specialPeriodMap.point z) a) ^ 2) •
        positivePeriodTopCohomologyClass (specialPeriodMap.point z) := by
  have hclass : Chern.firstChernClass (Chern.etaChernFactor (specialPeriodMap.point z)
      (etaEvaluation (specialPeriodMap.point z) a)) = a :=
    (Chern.firstChernClass_etaChernFactor _ _).trans
      (neronSeveri_special_eq_etaEvaluation_smul z hz a ha).symm
  simpa only [hclass] using Chern.firstChernClass_etaChernFactor_cup_square
    (specialPeriodMap.point z) (etaEvaluation (specialPeriodMap.point z) a)

/-- Literal square evaluation on the original positive four-period homology class. -/
theorem neronSeveri_special_cup_square_evaluate_positivePeriodTop (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet)
    (a : SingularCohomology (specialPeriodMap.point z).Torus 2)
    (ha : a ∈ neronSeveri (specialPeriodMap.point z)) :
    singularEvaluation (specialPeriodMap.point z).Torus 4
      (cupProduct (specialPeriodMap.point z).Torus 2 2 a a)
      (positivePeriodTopClass (specialPeriodMap.point z)) =
        12 * (etaEvaluation (specialPeriodMap.point z) a) ^ 2 := by
  have hclass : Chern.firstChernClass (Chern.etaChernFactor (specialPeriodMap.point z)
      (etaEvaluation (specialPeriodMap.point z) a)) = a :=
    (Chern.firstChernClass_etaChernFactor _ _).trans
      (neronSeveri_special_eq_etaEvaluation_smul z hz a ha).symm
  simpa only [hclass] using Chern.firstChernClass_etaChernFactor_cup_square_positivePeriodTop
    (specialPeriodMap.point z) (etaEvaluation (specialPeriodMap.point z) a)

/-- No nonzero class in the actual nonexceptional native NS image has zero cup square. -/
theorem neronSeveri_special_cup_square_eq_zero_iff (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet)
    (a : SingularCohomology (specialPeriodMap.point z).Torus 2)
    (ha : a ∈ neronSeveri (specialPeriodMap.point z)) :
    cupProduct (specialPeriodMap.point z).Torus 2 2 a a = 0 ↔ a = 0 := by
  constructor
  · intro hsquare
    have he := neronSeveri_special_cup_square_evaluate_positivePeriodTop z hz a ha
    rw [hsquare, map_zero, LinearMap.zero_apply] at he
    have hn2 : (etaEvaluation (specialPeriodMap.point z) a) ^ 2 = 0 :=
      (mul_eq_zero.mp he.symm).resolve_left (by norm_num)
    have hn : etaEvaluation (specialPeriodMap.point z) a = 0 := sq_eq_zero_iff.mp hn2
    rw [neronSeveri_special_eq_etaEvaluation_smul z hz a ha, hn, zero_zsmul]
  · rintro rfl
    exact map_zero (cupProduct (specialPeriodMap.point z).Torus 2 2 0)

/-- Every arbitrary original native holomorphic line bundle has the same actual square formula. -/
theorem firstChernClass_special_cup_square_evaluate_positivePeriodTop (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (V : (specialPeriodMap.point z).Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
    [ContMDiffVectorBundle ω ℂ V (modelWithCornersSelf ℂ ComplexPlane₂)] :
    singularEvaluation (specialPeriodMap.point z).Torus 4
      (cupProduct (specialPeriodMap.point z).Torus 2 2
        (firstChernClass (specialPeriodMap.point z) V)
        (firstChernClass (specialPeriodMap.point z) V))
      (positivePeriodTopClass (specialPeriodMap.point z)) =
        12 * (etaEvaluation (specialPeriodMap.point z)
          (firstChernClass (specialPeriodMap.point z) V)) ^ 2 :=
  neronSeveri_special_cup_square_evaluate_positivePeriodTop z hz _
    (firstChernClass_mem_neronSeveri _ V)

/-- An arbitrary original native line bundle has square-zero Chern class exactly when it is zero. -/
theorem firstChernClass_special_cup_square_eq_zero_iff (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (V : (specialPeriodMap.point z).Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
    [ContMDiffVectorBundle ω ℂ V (modelWithCornersSelf ℂ ComplexPlane₂)] :
    cupProduct (specialPeriodMap.point z).Torus 2 2
      (firstChernClass (specialPeriodMap.point z) V)
      (firstChernClass (specialPeriodMap.point z) V) = 0 ↔
        firstChernClass (specialPeriodMap.point z) V = 0 :=
  neronSeveri_special_cup_square_eq_zero_iff z hz _ (firstChernClass_mem_neronSeveri _ V)

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative
