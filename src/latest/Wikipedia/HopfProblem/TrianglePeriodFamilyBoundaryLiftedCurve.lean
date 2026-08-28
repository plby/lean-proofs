import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLiftedHomotopy
import Mathlib.Analysis.Convex.Contractible

/-!
# Actual infinite-cylinder lifts of periodic regular-base curves

The real line is simply connected, so a continuous periodic base curve has
a unique normalized lift through the actual triangle covering.  Its single
loop endpoint determines every integer translate by uniqueness of lifts;
the deck relation is not an independently assigned monodromy label.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle

/-- The unique actual real-parameter lift with the prescribed initial point. -/
def realCurveLift (c : C(ℝ, TriangleRegularQuotient))
    (z : TriangleRegularPoint) (hz : triangleRegularProject z = c 0) :
    C(ℝ, TriangleRegularPoint) :=
  (triangleRegularProject_covering.isCoveringMap.existsUnique_continuousMap_lifts
    c 0 z hz).choose

@[simp] theorem realCurveLift_zero (c : C(ℝ, TriangleRegularQuotient))
    (z : TriangleRegularPoint) (hz : triangleRegularProject z = c 0) :
    realCurveLift c z hz 0 = z :=
  (triangleRegularProject_covering.isCoveringMap.existsUnique_continuousMap_lifts
    c 0 z hz).choose_spec.1.1

@[simp] theorem realCurveLift_projection (c : C(ℝ, TriangleRegularQuotient))
    (z : TriangleRegularPoint) (hz : triangleRegularProject z = c 0) (t : ℝ) :
    triangleRegularProject (realCurveLift c z hz t) = c t :=
  congr_fun (triangleRegularProject_covering.isCoveringMap.existsUnique_continuousMap_lifts
    c 0 z hz).choose_spec.1.2 t

/-- Agreement at one point identifies any other continuous actual lift. -/
theorem realCurveLift_unique (c : C(ℝ, TriangleRegularQuotient))
    (z : TriangleRegularPoint) (hz : triangleRegularProject z = c 0)
    (L : C(ℝ, TriangleRegularPoint)) (hL : ∀ t, triangleRegularProject (L t) = c t)
    (hzero : L 0 = z) : L = realCurveLift c z hz := by
  apply ContinuousMap.ext
  exact congr_fun (triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
    L.continuous (realCurveLift c z hz).continuous
    (by funext t; simp only [Function.comp_apply, hL, realCurveLift_projection])
    0 (hzero.trans (realCurveLift_zero c z hz).symm))

/-- The one-loop endpoint propagates to every real starting time. -/
theorem realCurveLift_translate_one (c : C(ℝ, TriangleRegularQuotient))
    (z : TriangleRegularPoint) (hz : triangleRegularProject z = c 0)
    (hperiod : ∀ t : ℝ, c (t + 1) = c t) (g : TriangleGroup)
    (hend : realCurveLift c z hz 1 = g⁻¹ • z) (t : ℝ) :
    realCurveLift c z hz (t + 1) = g⁻¹ • realCurveLift c z hz t := by
  have hleft : Continuous (fun t : ℝ => realCurveLift c z hz (t + 1)) :=
    (realCurveLift c z hz).continuous.comp (continuous_id.add continuous_const)
  have hright : Continuous (fun t : ℝ => g⁻¹ • realCurveLift c z hz t) :=
    (continuous_const_smul g⁻¹).comp (realCurveLift c z hz).continuous
  have he : triangleRegularProject ∘ (fun t : ℝ => realCurveLift c z hz (t + 1)) =
      triangleRegularProject ∘ (fun t : ℝ => g⁻¹ • realCurveLift c z hz t) := by
    funext t
    simp only [Function.comp_apply, realCurveLift_projection,
      triangleRegularProject_covering.map_smul, hperiod]
  exact congr_fun (triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
    hleft hright he 0 (by simpa only [zero_add, realCurveLift_zero] using hend)) t

/-- The one-step relation implies the full integer deck relation. -/
theorem realCurve_integer_translate (L : ℝ → TriangleRegularPoint) (g : TriangleGroup)
    (hstep : ∀ t : ℝ, L (t + 1) = g⁻¹ • L t) (k : ℤ) (t : ℝ) :
    L (t + k) = (g ^ (-k)) • L t := by
  have hprev (s : ℝ) : L (s - 1) = g • L s := by
    have h := congrArg (fun y : TriangleRegularPoint => g • y) (hstep (s - 1))
    simpa only [sub_add_cancel, smul_inv_smul] using h.symm
  have hall : ∀ k : ℤ, ∀ t : ℝ, L (t + k) = (g ^ (-k)) • L t := by
    intro k
    induction k using Int.induction_on with
    | zero => intro t; simp
    | succ k ih =>
        intro t
        rw [Int.cast_add, Int.cast_one, ← add_assoc, hstep, ih]
        rw [show -((k : ℤ) + 1) = -1 + -(k : ℤ) by omega,
          zpow_add, zpow_neg_one, mul_smul]
    | pred k ih =>
        intro t
        rw [Int.cast_sub, Int.cast_one, ← add_sub_assoc, hprev, ih]
        rw [show -(-(k : ℤ) - 1) = 1 + -(-(k : ℤ)) by omega,
          zpow_add, zpow_one, mul_smul]
  exact hall k t

/-- The actual one-loop endpoint fixes all integer shifts of the actual
normalized covering lift. -/
theorem realCurveLift_translate (c : C(ℝ, TriangleRegularQuotient))
    (z : TriangleRegularPoint) (hz : triangleRegularProject z = c 0)
    (hperiod : ∀ t : ℝ, c (t + 1) = c t) (g : TriangleGroup)
    (hend : realCurveLift c z hz 1 = g⁻¹ • z) (k : ℤ) (t : ℝ) :
    realCurveLift c z hz (t + k) = (g ^ (-k)) • realCurveLift c z hz t :=
  realCurve_integer_translate (realCurveLift c z hz) g
    (realCurveLift_translate_one c z hz hperiod g hend) k t

/-- Restriction of the periodic curve to the actual unit-interval loop. -/
def realCurveLoop (c : C(ℝ, TriangleRegularQuotient))
    (hperiod : ∀ t : ℝ, c (t + 1) = c t) : Path (c 0) (c 0) where
  toFun t := c t
  continuous_toFun := c.continuous.comp continuous_subtype_val
  source' := rfl
  target' := by
    change c (1 : ℝ) = c 0
    simpa only [zero_add] using hperiod 0

/-- The infinite-cylinder lift restricts to the uniquely lifted actual loop. -/
theorem realCurveLift_eq_liftPath (c : C(ℝ, TriangleRegularQuotient))
    (z : TriangleRegularPoint) (hz : triangleRegularProject z = c 0)
    (hperiod : ∀ t : ℝ, c (t + 1) = c t) (t : unitInterval) :
    realCurveLift c z hz t =
      triangleRegularProject_covering.isCoveringMap.liftPath
        (realCurveLoop c hperiod) z hz.symm t := by
  apply congr_fun ((triangleRegularProject_covering.isCoveringMap.eq_liftPath_iff _).mpr
    ⟨(realCurveLift c z hz).continuous.comp continuous_subtype_val,
      by funext u; exact realCurveLift_projection c z hz u,
      realCurveLift_zero c z hz⟩) t

/-- Any proved endpoint formula for the literal unit-interval loop
determines the full real-cylinder deck action. -/
theorem realCurveLift_translate_of_liftPath
    (c : C(ℝ, TriangleRegularQuotient)) (z : TriangleRegularPoint)
    (hz : triangleRegularProject z = c 0)
    (hperiod : ∀ t : ℝ, c (t + 1) = c t) (g : TriangleGroup)
    (hend : triangleRegularProject_covering.isCoveringMap.liftPath
      (realCurveLoop c hperiod) z hz.symm 1 = g⁻¹ • z) (k : ℤ) (t : ℝ) :
    realCurveLift c z hz (t + k) = (g ^ (-k)) • realCurveLift c z hz t := by
  apply realCurveLift_translate c z hz hperiod g _ k t
  exact (realCurveLift_eq_liftPath c z hz hperiod 1).trans hend

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
