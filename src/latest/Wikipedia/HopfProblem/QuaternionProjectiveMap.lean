import Wikipedia.HopfProblem.QuaternionCoordinatePowers
import Wikipedia.HopfProblem.RiemannSphere

/-!
# The projective map on the punctured quaternion space

For `q = z + w j`, the chosen target coordinate is `[z : z-w]`.
The ratio is continuous at infinity by the reciprocal sphere chart.
-/

noncomputable section

open Filter Topology
open scoped Quaternion OnePoint

namespace Wikipedia.HopfProblem.QuaternionCoordinatePowers

def projectiveRatio (a b : ℂ) : RiemannSphere :=
  if b = 0 then (∞ : RiemannSphere) else ((a / b : ℂ) : RiemannSphere)

theorem projectiveRatio_reciprocal {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    projectiveRatio a b = RiemannSphere.infinityParametrization (b / a) := by
  by_cases hb : b = 0
  · simp [projectiveRatio, hb]
  · rw [projectiveRatio, if_neg hb,
      RiemannSphere.infinityParametrization_of_ne (div_ne_zero hb ha), inv_div]

theorem projectiveRatio_continuous {X : Type*} [TopologicalSpace X]
    (a b : X → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hne : ∀ x, a x ≠ 0 ∨ b x ≠ 0) :
    Continuous (fun x => projectiveRatio (a x) (b x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : b x = 0
  · have hax : a x ≠ 0 := (hne x).resolve_right (not_not.mpr hx)
    have h := RiemannSphere.infinityParametrization_continuous.continuousAt.comp
      (hb.continuousAt.div ha.continuousAt hax)
    apply h.congr_of_eventuallyEq
    filter_upwards [ha.continuousAt.eventually_ne hax] with y hy
    exact projectiveRatio_reciprocal hy (b y)
  · have h := OnePoint.continuous_coe.continuousAt.comp
      (ha.continuousAt.div hb.continuousAt hx)
    apply h.congr_of_eventuallyEq
    filter_upwards [hb.continuousAt.eventually_ne hx] with y hy
    exact if_neg hy

def projectiveMap : C(Punctured, RiemannSphere) where
  toFun q := projectiveRatio (first q.val) (first q.val - second q.val)
  continuous_toFun := projectiveRatio_continuous _ _
    (first_continuous.comp continuous_subtype_val)
    ((first_continuous.sub second_continuous).comp continuous_subtype_val) (by
      intro q
      rcases coordinates_ne_zero q with h | h
      · exact Or.inl h
      · by_cases hf : first q.val = 0
        · exact Or.inr (by simpa only [hf, zero_sub, neg_ne_zero] using h)
        · exact Or.inl hf)

end Wikipedia.HopfProblem.QuaternionCoordinatePowers
