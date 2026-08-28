import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClassEvaluation
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertEtaBundles
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingEta

/-!
# Actual native bundles realizing the distinguished integral Chern classes

With the original positive-translation, first-linear Hermitian convention,
the already constructed factor for `nη` has first Chern class `-nη`.
Consequently the actual factor for `-nη` realizes the positively marked
native singular-cohomology class `nη`.  This file keeps both signs visible
and identifies the original native holomorphic bundle and section spaces.
No classification of arbitrary bundles or Néron--Severi group is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert PeriodTorusCohomology SpecialPeriods
open FirstHurewicz SingularCohomologyFree PeriodTorusHigherHomologyPontryagin
open scoped ContDiff

/-- The original canonical factor retains its proved negative Chern convention. -/
theorem firstChernClass_etaFactor (p : PeriodDomain) (n : ℤ) :
    firstChernClass (etaFactor p n) = (-n) • etaClass p := by
  calc
    firstChernClass (etaFactor p n) = -coefficientClass p (n • periodRelationEta) :=
      firstChernClass_integralFactor p (n • periodRelationEta)
        (PeriodTorusTypeOneOne.etaMultipleTangent_isTypeOneOne p n)
    _ = (-n) • etaClass p := by
      change -(coefficientClassEquiv p (n • periodRelationEta)) =
        (-n) • coefficientClassEquiv p periodRelationEta
      rw [map_zsmul]
      exact (neg_zsmul (coefficientClassEquiv p periodRelationEta) n).symm

/-- The actual negative-form factor, chosen to realize the positive class `nη`. -/
def etaChernFactor (p : PeriodDomain) (n : ℤ) : FactorOfAutomorphy p := etaFactor p (-n)

/-- This is the original native holomorphic bundle for the actual factor `-nη`. -/
abbrev etaChernLineBundle (p : PeriodDomain) (n : ℤ) := etaLineBundle p (-n)

theorem etaChernLineBundle_fibre_finrank (p : PeriodDomain) (n : ℤ) (b : p.Torus) :
    Module.finrank ℂ ((etaChernLineBundle p n).Fiber b) = 1 :=
  etaLineBundle_fibre_finrank p (-n) b

theorem etaChernLineBundle_isHolomorphic (p : PeriodDomain) (n : ℤ) :
    ContMDiffVectorBundle ω ℂ (etaChernLineBundle p n).Fiber
      (modelWithCornersSelf ℂ ComplexPlane₂) := etaLineBundle_isHolomorphic p (-n)

/-- The actual winding-defined Chern class is the positively normalized native multiple. -/
theorem firstChernClass_etaChernFactor (p : PeriodDomain) (n : ℤ) :
    firstChernClass (etaChernFactor p n) = n • etaClass p := by
  rw [etaChernFactor, firstChernClass_etaFactor, neg_neg]

@[simp] theorem firstChernClass_etaChernFactor_one (p : PeriodDomain) :
    firstChernClass (etaChernFactor p 1) = etaClass p := by
  rw [firstChernClass_etaChernFactor, one_smul]

/-- Exact Chern numbers on the original positive ordered period-loop products. -/
theorem firstChernClass_etaChernFactor_evaluate_periodLoops (p : PeriodDomain)
    (n : ℤ) (x y : Lattice) :
    singularEvaluation p.Torus 2 (firstChernClass (etaChernFactor p n))
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) =
      n * (x 1 * y 2 - x 2 * y 1 + 6 * (x 0 * y 3 - x 3 * y 0)) := by
  rw [firstChernClass_etaChernFactor, map_zsmul, LinearMap.smul_apply,
    zsmul_eq_mul, etaClass_evaluate_periodLoops]
  simp only [Int.cast_id]

/-- The genuine positive `u,w` two-cycle measures the integer parameter exactly. -/
@[simp] theorem etaEvaluation_firstChernClass_etaChernFactor (p : PeriodDomain) (n : ℤ) :
    etaEvaluation p (firstChernClass (etaChernFactor p n)) = n := by
  rw [firstChernClass_etaChernFactor, map_zsmul, etaEvaluation_etaClass, zsmul_eq_mul,
    mul_one]
  simp only [Int.cast_id]

theorem firstChernClass_etaChernFactor_eq_zero_iff (p : PeriodDomain) (n : ℤ) :
    firstChernClass (etaChernFactor p n) = 0 ↔ n = 0 := by
  constructor
  · intro h
    have he := congrArg (etaEvaluation p) h
    simpa only [etaEvaluation_firstChernClass_etaChernFactor, map_zero] using he
  · rintro rfl
    rw [firstChernClass_etaChernFactor, zero_smul]

theorem firstChernClass_etaChernFactor_injective (p : PeriodDomain) :
    Function.Injective (fun n : ℤ => firstChernClass (etaChernFactor p n)) := by
  intro n m h
  have he := congrArg (etaEvaluation p) h
  simpa only [etaEvaluation_firstChernClass_etaChernFactor] using he

/-- The class of this actual native line bundle is primitive in integral singular cohomology. -/
theorem firstChernClass_etaChernFactor_one_primitive (p : PeriodDomain) (n : ℤ)
    (a : SingularCohomology p.Torus 2)
    (ha : n • a = firstChernClass (etaChernFactor p 1)) : IsUnit n := by
  rw [firstChernClass_etaChernFactor_one] at ha
  exact etaClass_primitive p n a ha

/-- Every genuine holomorphic section of a nonzero realized multiple vanishes. -/
theorem etaChernBundleSection_eq_zero (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0)
    (s : Core.HolomorphicSection (etaChernFactor p n)) : s = 0 :=
  etaBundleSection_eq_zero p (-n) (neg_ne_zero.mpr hn) s

/-- Naturality on the first actual period-change map. -/
theorem firstChernClass_etaChernFactor_step₁ (p : PeriodDomain) (n : ℤ) :
    singularCohomologyPullback p.step₁ContinuousMap 2
      (firstChernClass (etaChernFactor p.step₁ n)) =
        firstChernClass (etaChernFactor p n) := by
  rw [firstChernClass_etaChernFactor, map_zsmul, etaClass_pullback_step₁,
    firstChernClass_etaChernFactor]

/-- Naturality on the second actual period-change map. -/
theorem firstChernClass_etaChernFactor_step₂ (p : PeriodDomain) (n : ℤ) :
    singularCohomologyPullback p.step₂ContinuousMap 2
      (firstChernClass (etaChernFactor p.step₂ n)) =
        firstChernClass (etaChernFactor p n) := by
  rw [firstChernClass_etaChernFactor, map_zsmul, etaClass_pullback_step₂,
    firstChernClass_etaChernFactor]

/-- Naturality on the actual cusp period-change map. -/
theorem firstChernClass_etaChernFactor_step₀ (p : PeriodDomain) (n : ℤ) :
    singularCohomologyPullback p.step₀ContinuousMap 2
      (firstChernClass (etaChernFactor p.step₀ n)) =
        firstChernClass (etaChernFactor p n) := by
  rw [firstChernClass_etaChernFactor, map_zsmul, etaClass_pullback_step₀,
    firstChernClass_etaChernFactor]

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
