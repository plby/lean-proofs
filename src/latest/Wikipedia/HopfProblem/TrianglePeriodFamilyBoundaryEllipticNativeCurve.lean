import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticPeriodicLift
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticPaths

/-!
# Literal native elliptic roots in the whole lifted boundary homotopy

The actual normalized real covering lift is identified with the inverse
Cayley image of the original logarithmic root at every real time.  Reversing
the clockwise loop parameter gives the positive native boundary, with its
original inverse-generator deck convention and a genuine lifted homotopy.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Elliptic Elliptic.LogGauge
open SpecialPeriods.EllipticFilling SpecialPeriods.Threefold.EllipticGeometry
open CuspUniformization BoundaryLoopSquares

/-- The original native logarithmic parameter at an unrestricted real time. -/
def nativeClockwiseParameter (j : Kind) (t : ℝ) : ℂ :=
  chosenAttachingParameter j - (t : ℂ) / (j.order : ℂ)

@[simp] theorem nativeClockwiseParameter_im (j : Kind) (t : ℝ) :
    (nativeClockwiseParameter j t).im = (chosenAttachingParameter j).im := by
  simp [nativeClockwiseParameter, Complex.div_im]

/-- The logarithmic root remains in the actual punctured unit disc for all real times. -/
def nativeClockwiseRoot (j : Kind) : C(ℝ, Disc) where
  toFun t := ⟨exponential (nativeClockwiseParameter j t), by
    change dist (exponential (nativeClockwiseParameter j t)) 0 < 1
    rw [dist_zero_right]
    apply TauCusp.exponential_norm_lt_one_of_upperHalfPlane
    simpa only [nativeClockwiseParameter_im] using chosenAttachingParameter_im_pos j⟩
  continuous_toFun := (exponential_holomorphic.continuous.comp
    (continuous_const.sub (Complex.continuous_ofReal.div_const (j.order : ℂ)))).subtype_mk _

@[simp] theorem nativeClockwiseRoot_coe (j : Kind) (t : ℝ) :
    (nativeClockwiseRoot j t : ℂ) = exponential (nativeClockwiseParameter j t) := rfl

theorem nativeClockwiseRoot_ne_zero (j : Kind) (t : ℝ) :
    (nativeClockwiseRoot j t : ℂ) ≠ 0 := exponential_ne_zero _

theorem nativeClockwiseRoot_norm (j : Kind) (t : ℝ) :
    ‖(nativeClockwiseRoot j t : ℂ)‖ = ‖exponential (chosenAttachingParameter j)‖ := by
  simp [nativeClockwiseRoot_coe, nativeClockwiseParameter, exponential,
    Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Restriction gives precisely the original native logarithmic root path. -/
theorem nativeClockwiseRoot_unit (j : Kind) (t : unitInterval) :
    nativeClockwiseRoot j (t : ℝ) =
      logMeridianRoot j (chosenAttachingParameter j) (chosenAttachingParameter_im_pos j) t := by
  apply Subtype.ext
  rfl

theorem nativeClockwiseRoot_add_one (j : Kind) (t : ℝ) :
    nativeClockwiseRoot j (t + 1) = familyRotation j (nativeClockwiseRoot j t) := by
  apply Subtype.ext
  rw [familyRotation_val_exponential, nativeClockwiseRoot_coe, nativeClockwiseRoot_coe]
  have he : nativeClockwiseParameter j (t + 1) =
      nativeClockwiseParameter j t + -(1 / (j.order : ℂ)) := by
    simp only [nativeClockwiseParameter]
    push_cast
    ring
  rw [he, exponential_add]
  exact mul_comm _ _

/-- The literal inverse-Cayley root curve in the original regular covering space. -/
def nativeClockwiseBase (j : Kind) : C(ℝ, TriangleRegularPoint) :=
  ⟨fun t => localBase j ⟨nativeClockwiseRoot j t, nativeClockwiseRoot_ne_zero j t⟩,
    (localBase_continuous j).comp ((nativeClockwiseRoot j).continuous.subtype_mk _)⟩

theorem nativeClockwiseBase_unit (j : Kind) (t : unitInterval) :
    nativeClockwiseBase j (t : ℝ) = chosenNativeLift j t := by
  change localBase j ⟨nativeClockwiseRoot j (t : ℝ), _⟩ =
    localBase j (logMeridianRootStar (j := j) (chosenAttachingParameter j)
      (chosenAttachingParameter_im_pos j) t)
  apply congrArg (localBase j)
  apply Subtype.ext
  exact nativeClockwiseRoot_unit j t

/-- The whole real root curve obeys the actual local rotation identity. -/
theorem nativeClockwiseBase_endpoint (j : Kind) (t : ℝ) :
    nativeClockwiseBase j (t + 1) = ellipticGenerator j • nativeClockwiseBase j t := by
  let z₀ : BaseStar := ⟨nativeClockwiseRoot j t, nativeClockwiseRoot_ne_zero j t⟩
  let z₁ : BaseStar := ⟨nativeClockwiseRoot j (t + 1), nativeClockwiseRoot_ne_zero j (t + 1)⟩
  have hz : puncturedRotation j z₀ = z₁ := Subtype.ext (nativeClockwiseRoot_add_one j t).symm
  have h := localBase_rotation j z₀
  rw [hz] at h
  exact h

theorem nativeClockwiseBase_projection_periodic (j : Kind) :
    Function.Periodic (fun t : ℝ => triangleRegularProject (nativeClockwiseBase j t)) 1 := by
  intro t
  change triangleRegularProject (nativeClockwiseBase j (t + 1)) =
    triangleRegularProject (nativeClockwiseBase j t)
  rw [nativeClockwiseBase_endpoint, triangleRegularProject_covering.map_smul]

/-- The actual root projection is the exact periodic extension of the original loop. -/
theorem nativeClockwiseBase_projection_eq (j : Kind) (t : ℝ) :
    triangleRegularProject (nativeClockwiseBase j t) =
      loopPeriodic (chosenAttachingBaseLoop j) t := by
  apply congrFun (loopPeriodic_unique
    (fun t : ℝ => triangleRegularProject (nativeClockwiseBase j t))
    (nativeClockwiseBase_projection_periodic j) _) t
  intro u
  rw [nativeClockwiseBase_unit, chosenNativeLift_projection]

/-- Uniqueness identifies the entire previously normalized lift with
the literal native inverse-Cayley root, not merely its endpoints. -/
theorem nativeClockwiseBase_eq_periodicLift (j : Kind) :
    nativeClockwiseBase j = chosenAttachingPeriodicLift j :=
  realCurveLift_unique (loopPeriodic (chosenAttachingBaseLoop j)) (chosenNativeLift j 0)
    (chosenAttachingPeriodicBasepoint j) (nativeClockwiseBase j)
    (nativeClockwiseBase_projection_eq j) (nativeClockwiseBase_unit j 0)

/-- The actual positive native base curve uses the same original root and fibre marking. -/
def nativePositiveBase (j : Kind) : C(ℝ, TriangleRegularPoint) :=
  (nativeClockwiseBase j).comp ⟨Neg.neg, continuous_neg⟩

@[simp] theorem nativePositiveBase_apply (j : Kind) (t : ℝ) :
    nativePositiveBase j t = nativeClockwiseBase j (-t) := rfl

theorem nativePositiveBase_eq_periodicLift (j : Kind) (t : ℝ) :
    nativePositiveBase j t = chosenAttachingPeriodicLift j (-t) := by
  rw [nativePositiveBase_apply, nativeClockwiseBase_eq_periodicLift]

/-- Reverse only the loop parameter in the actual lifted native square. -/
def nativePositiveSquareLift (j : Kind) : C(unitInterval × ℝ, TriangleRegularPoint) :=
  (chosenAttachingPeriodicSquareLift j).comp
    ⟨fun p => (p.1, -p.2), continuous_fst.prodMk (continuous_neg.comp continuous_snd)⟩

@[simp] theorem nativePositiveSquareLift_apply (j : Kind) (s : unitInterval) (t : ℝ) :
    nativePositiveSquareLift j (s, t) = chosenAttachingPeriodicSquareLift j (s, -t) := rfl

@[simp] theorem nativePositiveSquareLift_zero (j : Kind) (t : ℝ) :
    nativePositiveSquareLift j (0, t) = nativePositiveBase j t := by
  rw [nativePositiveSquareLift_apply, chosenAttachingPeriodicSquareLift_zero,
    nativePositiveBase_eq_periodicLift]

/-- The full positive square retains the inverse-generator deck convention. -/
theorem nativePositiveSquareLift_translate (j : Kind) (s : unitInterval) (k : ℤ) (t : ℝ) :
    nativePositiveSquareLift j (s, t + k) =
      (ellipticGenerator j ^ (-k)) • nativePositiveSquareLift j (s, t) := by
  rw [nativePositiveSquareLift_apply, nativePositiveSquareLift_apply]
  have ht : -(t + (k : ℝ)) = -t + ((-k : ℤ) : ℝ) := by push_cast; ring
  rw [ht]
  exact chosenAttachingPeriodicSquareLift_add_int j s (-t) (-k)

theorem nativePositiveBase_translate (j : Kind) (k : ℤ) (t : ℝ) :
    nativePositiveBase j (t + k) =
      (ellipticGenerator j ^ (-k)) • nativePositiveBase j t := by
  simpa only [nativePositiveSquareLift_zero] using
    nativePositiveSquareLift_translate j 0 k t

/-- The actual final edge retains its proved native tail frame. -/
theorem nativePositiveSquareLift_final (j : Kind) (t : ℝ) :
    nativePositiveSquareLift j (1, t) =
      nativeTailFrame j • clockwisePeriodicLift (attachingMeridianIndex j) (-t) :=
  chosenAttachingPeriodicSquareLift_final j (-t)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
