import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupPath

/-!
# The logarithmic meridian is the inverse-gauge zero-section loop

The two loops below are defined by their actual pointwise formulas in the
punctured filling and the untwisted punctured quotient.  The logarithmic
gauge carries one to the other exactly, with only equality casts at their
identical basepoints.
-/

noncomputable section

open Set Topology
open scoped Matrix unitInterval ContDiff

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods CuspUniformization

variable {j : Kind} (D : Equivariant.Data j)

def logMeridianRootStar (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) : BaseStar :=
  ⟨logMeridianRoot j s₀ hs₀ t, logMeridianRoot_ne_zero j s₀ hs₀ t⟩

theorem logMeridianRootStar_continuous (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (logMeridianRootStar (j := j) s₀ hs₀) :=
  (logMeridianRoot_continuous j s₀ hs₀).subtype_mk _

def logMeridianComplexPoint (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    CoverStar :=
  ⟨(logMeridianRoot j s₀ hs₀ t, logMeridianComplex D v s₀ hs₀ t),
    logMeridianRoot_ne_zero j s₀ hs₀ t⟩

def logMeridianFamilyStar (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    FamilyStar D.periods :=
  ⟨logMeridianFamily D v s₀ hs₀ t, logMeridianRoot_ne_zero j s₀ hs₀ t⟩

theorem logMeridianFamilyStar_eq_project (v : Lattice)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    logMeridianFamilyStar D v s₀ hs₀ t =
      project D.periods (logMeridianComplexPoint D v s₀ hs₀ t) := rfl

theorem logMeridianFamilyStar_continuous (v : Lattice)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (logMeridianFamilyStar D v s₀ hs₀) :=
  (logMeridianFamily_continuous D v s₀ hs₀).subtype_mk _

/-- Cancellation is exact for the displayed normalized logarithm. -/
theorem gaugeMap_logMeridianFamilyStar (v : Lattice)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    gaugeMap D.periods v (logMeridianFamilyStar D v s₀ hs₀ t) =
      zeroSection D.periods (logMeridianRootStar (j := j) s₀ hs₀ t) := by
  apply Subtype.ext
  rw [logMeridianFamilyStar_eq_project,
    gaugeMap_project_of_exponential D.periods v (logMeridianComplexPoint D v s₀ hs₀ t)
      (logMeridianParameter j s₀ t) rfl]
  change D.periods.quotientMap
      (logMeridianRoot j s₀ hs₀ t, logMeridianComplex D v s₀ hs₀ t +
        logMeridianParameter j s₀ t • periodVector D.periods v (logMeridianRoot j s₀ hs₀ t)) =
    (logMeridianRoot j s₀ hs₀ t, 0)
  simp only [logMeridianComplex, neg_smul, neg_add_cancel]
  change (logMeridianRoot j s₀ hs₀ t,
    standardLattice.mkQ ((D.periods.periodEquiv _).symm 0)) = (logMeridianRoot j s₀ hs₀ t, 0)
  simp only [map_zero]

def logMeridianFillingPoint (v : Lattice) (hv : AdmissibleTwist j v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) : FillingStar D v hv :=
  fillingStarProject D v hv (logMeridianFamilyStar D v s₀ hs₀ t)

@[simp] theorem logMeridianFillingPoint_coe (v : Lattice) (hv : AdmissibleTwist j v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    (logMeridianFillingPoint D v hv s₀ hs₀ t : D.Space v hv) =
      logMeridianLoop D v hv s₀ hs₀ t := rfl

theorem logMeridianFillingPoint_continuous (v : Lattice) (hv : AdmissibleTwist j v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (logMeridianFillingPoint D v hv s₀ hs₀) :=
  ((D.quotient_continuous v hv).comp (logMeridianFamily_continuous D v s₀ hs₀)).subtype_mk _

/-- The logarithmic loop lies in the actual punctured filling. -/
def logMeridianFillingLoop (v : Lattice) (hv : AdmissibleTwist j v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path (logMeridianFillingPoint D v hv s₀ hs₀ 0)
      (logMeridianFillingPoint D v hv s₀ hs₀ 0) where
  toFun := logMeridianFillingPoint D v hv s₀ hs₀
  continuous_toFun := logMeridianFillingPoint_continuous D v hv s₀ hs₀
  source' := rfl
  target' := Subtype.ext (logMeridianLoop D v hv s₀ hs₀).target

/-- The untwisted zero section along the same explicit root path. -/
def tautologicalZeroPoint (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) : TautologicalStar D :=
  starProject D 0 (Matrix.mulVec_zero j.matrix)
    (zeroSection D.periods (logMeridianRootStar (j := j) s₀ hs₀ t))

theorem tautologicalZeroPoint_continuous (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (tautologicalZeroPoint D s₀ hs₀) := by
  apply (starProject_continuous D 0 (Matrix.mulVec_zero j.matrix)).comp
  exact ((logMeridianRoot_continuous j s₀ hs₀).prodMk continuous_const).subtype_mk _

theorem starProject_starPermutation (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : FamilyStar D.periods) :
    starProject D v hv (starPermutation D v x) = starProject D v hv x := by
  let := starAction D v hv
  have h : CyclicAction.generator j.order • x = starPermutation D v x :=
    CyclicAction.generator_smul (starPermutation D v) (starPermutation_pow_order D v hv) x
  rw [← h]
  exact FiniteQuotient.project_smul (CyclicGroup j) (FamilyStar D.periods)
    (CyclicAction.generator j.order) x

theorem tautologicalZeroPoint_one (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    tautologicalZeroPoint D s₀ hs₀ 1 = tautologicalZeroPoint D s₀ hs₀ 0 := by
  have hzero : flatTorusAffine j 0 0 = 0 := by
    have hz : realCast (0 : Lattice) = 0 := by ext i; simp [realCast]
    have h := flatTorusAffine_mkQ j 0 (0 : RealCoordinates)
    simpa only [map_zero, flatAffine, hz, smul_zero, add_zero] using h
  have hfamily : zeroSection D.periods (logMeridianRootStar (j := j) s₀ hs₀ 1) =
      starPermutation D 0 (zeroSection D.periods (logMeridianRootStar (j := j) s₀ hs₀ 0)) := by
    apply Subtype.ext
    change (logMeridianRoot j s₀ hs₀ 1, (0 : RealTorus₄)) =
      (familyRotation j (logMeridianRoot j s₀ hs₀ 0), flatTorusAffine j 0 0)
    exact Prod.ext (logMeridianRoot_one j s₀ hs₀) hzero.symm
  unfold tautologicalZeroPoint
  rw [hfamily, starProject_starPermutation]

/-- The independent pointwise zero-section loop in the untwisted quotient. -/
def tautologicalZeroLoop (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path (tautologicalZeroPoint D s₀ hs₀ 0) (tautologicalZeroPoint D s₀ hs₀ 0) where
  toFun := tautologicalZeroPoint D s₀ hs₀
  continuous_toFun := tautologicalZeroPoint_continuous D s₀ hs₀
  source' := rfl
  target' := tautologicalZeroPoint_one D s₀ hs₀

/-- The actual filling gauge sends the displayed logarithmic path to zero. -/
theorem fillingToTautological_logMeridian (v : Lattice) (hv : AdmissibleTwist j v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    fillingToTautologicalBiholomorph D v hv (logMeridianFillingPoint D v hv s₀ hs₀ t) =
      tautologicalZeroPoint D s₀ hs₀ t := by
  rw [logMeridianFillingPoint, fillingToTautologicalBiholomorph_project,
    gaugeMap_logMeridianFamilyStar]
  rfl

/-- The existing biholomorphism, retaining only its actual topological maps. -/
def fillingGaugeHomeomorph (v : Lattice) (hv : AdmissibleTwist j v) :
    FillingStar D v hv ≃ₜ TautologicalStar D := by
  let := D.chartedSpace v hv
  let := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
  exact (fillingToTautologicalBiholomorph D v hv).toHomeomorph

/-- The logarithmic path is exactly the inverse-gauge image of the zero section. -/
theorem fillingToTautological_symm_zeroPoint (v : Lattice) (hv : AdmissibleTwist j v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    (fillingGaugeHomeomorph D v hv).symm (tautologicalZeroPoint D s₀ hs₀ t) =
      logMeridianFillingPoint D v hv s₀ hs₀ t := by
  rw [← fillingToTautological_logMeridian D v hv s₀ hs₀ t]
  exact (fillingGaugeHomeomorph D v hv).symm_apply_apply _

/-- Equality of actual loops under the gauge, not merely equality of loop classes. -/
theorem fillingToTautological_logMeridianLoop (v : Lattice) (hv : AdmissibleTwist j v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    (logMeridianFillingLoop D v hv s₀ hs₀).map
        (fillingGaugeHomeomorph D v hv).continuous =
      (tautologicalZeroLoop D s₀ hs₀).cast
        (fillingToTautological_logMeridian D v hv s₀ hs₀ 0)
        (fillingToTautological_logMeridian D v hv s₀ hs₀ 0) := by
  ext t
  exact fillingToTautological_logMeridian D v hv s₀ hs₀ t

end Wikipedia.HopfProblem.Elliptic.LogGauge
