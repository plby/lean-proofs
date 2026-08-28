import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupBase
import Wikipedia.HopfProblem.EllipticLogGaugeSource
import Wikipedia.HopfProblem.EllipticLogGaugeQuotients

/-!
# The actual logarithmic meridian path

Following the clockwise root path and the complex vector `-s Π(z)v`
produces an honest path in real period coordinates.  Exact period
covariance identifies its endpoint with the affine generator, without
an unrecorded lattice translation.
-/

noncomputable section

open Set Topology
open scoped Matrix unitInterval ContDiff

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods CuspUniformization

variable {j : Kind} (D : Equivariant.Data j)

/-- Real coordinates of the source's negative logarithmic period vector. -/
def negativeLogFlat (v : Lattice) (z : Disc) (s : ℂ) : RealCoordinates :=
  (D.periods.periodEquiv z).symm (-s • periodVector D.periods v z)

theorem negativeLogFlat_continuous (v : Lattice) :
    Continuous (fun p : Disc × ℂ => negativeLogFlat D v p.1 p.2) := by
  change Continuous ((fun q : Disc × ComplexPlane₂ => (D.periods.periodEquiv q.1).symm q.2) ∘
    (fun p : Disc × ℂ => (p.1, -p.2 • periodVector D.periods v p.1)))
  apply D.periods.continuous_periodEquiv_symm.comp
  exact continuous_fst.prodMk (continuous_snd.neg.smul
    ((periodVector_holomorphic D.periods v).continuous.comp continuous_fst))

/-- A decrement of exactly `1/m` is exactly the positive affine generator
in real period coordinates.  There is no residual integral translation. -/
theorem negativeLogFlat_rotation (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (z : Disc) (s : ℂ) :
    negativeLogFlat D v (familyRotation j z) (s - 1 / (j.order : ℂ)) =
      flatAffine j v (negativeLogFlat D v z s) := by
  apply (D.periods.periodEquiv (familyRotation j z)).injective
  simp only [negativeLogFlat, LinearEquiv.apply_symm_apply, flatAffine, map_add,
    D.periodEquiv_flatLinear, complexLift_translation, Matrix.mulVec_smul,
    periodVector_covariance D v hv]
  rw [← add_smul]
  congr 1
  ring

/-- The actual varying complex vector along the clockwise root path. -/
def logMeridianComplex (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    ComplexPlane₂ :=
  -logMeridianParameter j s₀ t • periodVector D.periods v (logMeridianRoot j s₀ hs₀ t)

theorem logMeridianComplex_continuous (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (logMeridianComplex D v s₀ hs₀) :=
  (logMeridianParameter_continuous j s₀).neg.smul
    ((periodVector_holomorphic D.periods v).continuous.comp
      (logMeridianRoot_continuous j s₀ hs₀))

/-- The real lift is obtained by inverting the actual varying period matrix. -/
def logMeridianFlat (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    RealCoordinates :=
  negativeLogFlat D v (logMeridianRoot j s₀ hs₀ t) (logMeridianParameter j s₀ t)

theorem logMeridianFlat_eq (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    logMeridianFlat D v s₀ hs₀ t =
      (D.periods.periodEquiv (logMeridianRoot j s₀ hs₀ t)).symm
        (logMeridianComplex D v s₀ hs₀ t) := rfl

theorem logMeridianFlat_continuous (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (logMeridianFlat D v s₀ hs₀) := by
  change Continuous ((fun q : Disc × ComplexPlane₂ => (D.periods.periodEquiv q.1).symm q.2) ∘
    (fun t : I => (logMeridianRoot j s₀ hs₀ t, logMeridianComplex D v s₀ hs₀ t)))
  apply D.periods.continuous_periodEquiv_symm.comp
  exact (logMeridianRoot_continuous j s₀ hs₀).prodMk
    (logMeridianComplex_continuous D v s₀ hs₀)

/-- The lift has the exact affine endpoint for either elliptic order. -/
theorem logMeridianFlat_one (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    logMeridianFlat D v s₀ hs₀ 1 =
      flatAffine j v (logMeridianFlat D v s₀ hs₀ 0) := by
  simp only [logMeridianFlat, logMeridianRoot_one,
    logMeridianParameter_one, logMeridianParameter_zero]
  exact negativeLogFlat_rotation D v hv _ _

/-- The real-coordinate path whose projected loop is the logarithmic meridian. -/
def logMeridianFlatPath (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path (logMeridianFlat D v s₀ hs₀ 0)
      (flatAffine j v (logMeridianFlat D v s₀ hs₀ 0)) where
  toFun := logMeridianFlat D v s₀ hs₀
  continuous_toFun := logMeridianFlat_continuous D v s₀ hs₀
  source' := rfl
  target' := logMeridianFlat_one D v hv s₀ hs₀

@[simp] theorem logMeridianFlatPath_apply (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    logMeridianFlatPath D v hv s₀ hs₀ t = logMeridianFlat D v s₀ hs₀ t := rfl

/-- The simultaneous root and real-coordinate path on the actual cover. -/
def logMeridianCoverPath (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path (logMeridianRoot j s₀ hs₀ 0, logMeridianFlat D v s₀ hs₀ 0)
      (familyRotation j (logMeridianRoot j s₀ hs₀ 0),
        flatAffine j v (logMeridianFlat D v s₀ hs₀ 0)) where
  toFun t := (logMeridianRoot j s₀ hs₀ t, logMeridianFlat D v s₀ hs₀ t)
  continuous_toFun := (logMeridianRoot_continuous j s₀ hs₀).prodMk
    (logMeridianFlat_continuous D v s₀ hs₀)
  source' := rfl
  target' := Prod.ext (logMeridianRoot_one j s₀ hs₀) (logMeridianFlat_one D v hv s₀ hs₀)

/-- The same path in the actual flat-torus family. -/
def logMeridianFamily (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) : D.TotalSpace :=
  (logMeridianRoot j s₀ hs₀ t, standardLattice.mkQ (logMeridianFlat D v s₀ hs₀ t))

theorem logMeridianFamily_continuous (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (logMeridianFamily D v s₀ hs₀) :=
  (logMeridianRoot_continuous j s₀ hs₀).prodMk
    (standardLattice.continuous_mkQ.comp (logMeridianFlat_continuous D v s₀ hs₀))

theorem logMeridianFamily_one (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    logMeridianFamily D v s₀ hs₀ 1 = D.permutation v (logMeridianFamily D v s₀ hs₀ 0) := by
  simp only [logMeridianFamily, D.permutation_apply, logMeridianRoot_one,
    logMeridianFlat_one D v hv, flatTorusAffine_mkQ]

/-- The affine generator does not change the actual filling-quotient point. -/
theorem quotient_permutation (v : Lattice) (hv : AdmissibleTwist j v) (x : D.TotalSpace) :
    D.quotient v hv (D.permutation v x) = D.quotient v hv x := by
  let := D.action v hv.1
  have hg : CyclicAction.generator j.order • x = D.permutation v x :=
    familyAction_generator_smul j v hv.1 x
  rw [← hg]
  exact D.quotient_smul v hv (CyclicAction.generator j.order) x

/-- The honest loop in the actual filling, with its displayed basepoint. -/
def logMeridianLoop (v : Lattice) (hv : AdmissibleTwist j v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path (D.quotient v hv (logMeridianFamily D v s₀ hs₀ 0))
      (D.quotient v hv (logMeridianFamily D v s₀ hs₀ 0)) where
  toFun t := D.quotient v hv (logMeridianFamily D v s₀ hs₀ t)
  continuous_toFun := (D.quotient_continuous v hv).comp
    (logMeridianFamily_continuous D v s₀ hs₀)
  source' := rfl
  target' := (congrArg (D.quotient v hv) (logMeridianFamily_one D v hv.1 s₀ hs₀)).trans
    (quotient_permutation D v hv _)

@[simp] theorem logMeridianLoop_apply (v : Lattice) (hv : AdmissibleTwist j v)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    logMeridianLoop D v hv s₀ hs₀ t =
      D.quotient v hv (logMeridianFamily D v s₀ hs₀ t) := rfl

end Wikipedia.HopfProblem.Elliptic.LogGauge
