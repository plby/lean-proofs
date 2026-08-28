import Wikipedia.NoExoticSixSphere.BallExteriorHomotopy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# An enclosing sphere still generates after shifting its interior point

For `‖x‖ < r`, the sphere maps `u ↦ r • u - t • x` never hit zero.
Their actual homotopy identifies the shifted sphere map with the radial
homotopy equivalence of the punctured vector space. This retains the
literal inclusion of the exterior into the space punctured at `x`.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped unitInterval

namespace NoExoticSixSphere.BallExterior

open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem time_smul_norm_le (t : I) (x : E) : ‖(t : ℝ) • x‖ ≤ ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  exact mul_le_of_le_one_left (norm_nonneg x) t.2.2

theorem shiftedSphere_ne_zero (r : ℝ) (hr : 0 < r) (x : E) (hx : ‖x‖ < r)
    (t : I) (u : sphere (0 : E) 1) : r • (u : E) - (t : ℝ) • x ≠ 0 := by
  intro hz
  have he := congrArg norm (sub_eq_zero.mp hz)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    mem_sphere_zero_iff_norm.mp u.2, mul_one] at he
  exact (not_le_of_gt hx) (he.le.trans (time_smul_norm_le t x))

theorem shiftedSphere_endpoint_ne_zero (r : ℝ) (hr : 0 < r) (x : E) (hx : ‖x‖ < r)
    (u : sphere (0 : E) 1) : r • (u : E) - x ≠ 0 := by
  have h := shiftedSphere_ne_zero r hr x hx 1 u
  change r • (u : E) - (1 : ℝ) • x ≠ 0 at h
  simpa only [one_smul] using h

def shiftedSphereMap (r : ℝ) (hr : 0 < r) (x : E) (hx : ‖x‖ < r) :
    C(sphere (0 : E) 1, PuncturedRadial.Space E) :=
  ⟨fun u => ⟨r • (u : E) - x, shiftedSphere_endpoint_ne_zero r hr x hx u⟩,
    ((continuous_const.smul continuous_subtype_val).sub continuous_const).subtype_mk _⟩

/-- The whole homotopy stays in the original punctured target. -/
def shiftedSphereHomotopy (r : ℝ) (hr : 0 < r) (x : E) (hx : ‖x‖ < r) :
    (PuncturedRadial.fromSphere r hr).Homotopy (shiftedSphereMap r hr x hx) where
  toFun q := ⟨r • (q.2 : E) - (q.1 : ℝ) • x, shiftedSphere_ne_zero r hr x hx q.1 q.2⟩
  continuous_toFun :=
    ((continuous_const.smul (continuous_subtype_val.comp continuous_snd)).sub
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const)).subtype_mk _
  map_zero_left u := by
    apply Subtype.ext
    simp [PuncturedRadial.fromSphere]
  map_one_left u := by
    apply Subtype.ext
    simp [shiftedSphereMap]

/-- The actual punctured-space translation, retaining the literal subtraction formula. -/
def puncturedTranslate (x : E) : ({x}ᶜ : Set E) ≃ₜ PuncturedRadial.Space E :=
  (Homeomorph.subRight x).subtype (fun y => by
    change y ≠ x ↔ y - x ≠ 0
    exact sub_ne_zero.symm)

omit [NormedSpace ℝ E] in
theorem exterior_ne_point (R : ℝ) (x : E) (hx : ‖x‖ ≤ R) (y : Space E R) : (y : E) ≠ x := by
  intro h
  have hy := norm_gt R y
  rw [h] at hy
  exact (not_lt_of_ge hx) hy

/-- Include the original exterior into the space punctured at any point of the closed ball. -/
def toPointPuncture (R : ℝ) (x : E) (hx : ‖x‖ ≤ R) :
    C(Space E R, ({x}ᶜ : Set E)) :=
  ⟨fun y => ⟨y.1, exterior_ne_point R x hx y⟩, continuous_subtype_val.subtype_mk _⟩

theorem enclosingSphere_puncture_translate (R : ℝ) (hR : 0 ≤ R) (r : ℝ) (hr : R < r)
    (x : E) (hx : ‖x‖ ≤ R) :
    (puncturedTranslate x : C(({x}ᶜ : Set E), PuncturedRadial.Space E)).comp
        ((toPointPuncture R x hx).comp (fromSphere R hR r hr)) =
      shiftedSphereMap r (radius_pos R hR r hr) x (hx.trans_lt hr) := rfl

end NoExoticSixSphere.BallExterior

namespace NoExoticSixSphere.BallExterior

open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem shiftedSphereMap_homology_bijective (r : ℝ) (hr : 0 < r) (x : E) (hx : ‖x‖ < r)
    (n : ℕ) : Function.Bijective (singularHomologyMap (shiftedSphereMap r hr x hx) n) := by
  rw [← homotopy_homologyMap (shiftedSphereHomotopy r hr x hx) n]
  exact (homotopyEquivHomologyEquiv (PuncturedRadial.sphereHomotopyEquiv r hr) n).bijective

end NoExoticSixSphere.BallExterior
