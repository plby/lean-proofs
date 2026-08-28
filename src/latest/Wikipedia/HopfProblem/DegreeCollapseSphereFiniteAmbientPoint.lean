import Wikipedia.HopfProblem.DegreeCollapseSphereCenteredAmbientChart
import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteRepresentative

/-!
# The original inverse sphere chart as a smooth ambient map

Keep the exact finite compactification chart, including its zero and pole
conventions. Sphere-map germs pass to these finite coordinates. The zero
slice and original pairing take their south points to the corresponding
south points, so the specified product-fiber target is a chart center.
-/

noncomputable section

open Filter
open scoped Topology Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteAmbientPoint

open NoExoticSixSphere SphereCenteredAmbientChart
open FiniteSphereProductCharts hiding V

theorem neg_pole_ne_pole (n : ℕ) : -spherePole n ≠ spherePole n := by
  intro h
  have hi := congrArg (fun y : Sphere n ↦ inner ℝ (spherePole n).val y.val) h
  change inner ℝ (spherePole n).val (-(spherePole n).val) =
    inner ℝ (spherePole n).val (spherePole n).val at hi
  rw [inner_neg_right, real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, one_pow] at hi
  norm_num at hi

theorem projection_neg_pole (n : ℕ) : sphereProjection n (-spherePole n) = 0 := by
  rw [sphereProjection_ambientChart, ambientChart_self]

theorem point_zero (n : ℕ) : SphereFiniteRepresentative.point n 0 = -spherePole n := by
  rw [← projection_neg_pole n,
    SphereFiniteRepresentative.point_projection n (neg_pole_ne_pole n)]

def ambientPoint (n : ℕ) (u : V n) : V (n + 1) :=
  (SphereFiniteRepresentative.point n u).val

theorem ambientPoint_norm (n : ℕ) (u : V n) : ‖ambientPoint n u‖ = 1 :=
  ClosedHemisphere.unit_norm (SphereFiniteRepresentative.point n u)

theorem contDiff_ambientPoint (n : ℕ) : ContDiff ℝ ∞ (ambientPoint n) := by
  let : Fact (Module.finrank ℝ (V (n + 1)) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  have h : ContMDiff (𝓡 n) 𝓘(ℝ, V (n + 1)) ∞ (ambientPoint n) :=
    (contMDiff_coe_sphere (n := n) (m := ∞)).comp
      (SphereFiniteRepresentative.point_contMDiff n)
  exact h.contDiff

theorem contDiff_fderiv_ambientPoint (n : ℕ) : ContDiff ℝ ∞ (fderiv ℝ (ambientPoint n)) :=
  (contDiff_ambientPoint n).fderiv_right (by simp)

theorem slice_neg_pole (n : ℕ) :
    ProductSphereFiber.slice n (-spherePole n) = -spherePole (n + 1) := by
  rw [slice_finite n (neg_pole_ne_pole n), projection_neg_pole]
  change SphereFiniteRepresentative.point (n + 1)
    (lineCoordinates n (0 : V n × ℝ)) = _
  rw [map_zero, point_zero]

theorem pairing_neg_poles (n : ℕ) :
    JamesSphere.pairing n (-spherePole n, -spherePole n) = -spherePole (n + n) := by
  rw [pairing_finite n (neg_pole_ne_pole n) (neg_pole_ne_pole n), projection_neg_pole]
  change SphereFiniteRepresentative.point (n + n)
    (sumCoordinates n (0 : V n × V n)) = _
  rw [map_zero, point_zero]

theorem value_eventuallyEq {m n : ℕ} (f g : C(Sphere m, Sphere n)) (u : V m)
    (h : (f : Sphere m → Sphere n) =ᶠ[𝓝 (SphereFiniteRepresentative.point m u)] g) :
    SphereFiniteRepresentative.value f =ᶠ[𝓝 u] SphereFiniteRepresentative.value g := by
  have ht : Tendsto (SphereFiniteRepresentative.point m) (𝓝 u)
      (𝓝 (SphereFiniteRepresentative.point m u)) :=
    (SphereFiniteRepresentative.point_contMDiff m).continuous.continuousAt
  filter_upwards [h.comp_tendsto ht] with v hv
  exact congrArg (sphereProjection n) hv

theorem value_fderiv_eq {m n : ℕ} (f g : C(Sphere m, Sphere n)) (u : V m)
    (h : (f : Sphere m → Sphere n) =ᶠ[𝓝 (SphereFiniteRepresentative.point m u)] g) :
    fderiv ℝ (SphereFiniteRepresentative.value f) u =
      fderiv ℝ (SphereFiniteRepresentative.value g) u :=
  (value_eventuallyEq f g u h).fderiv_eq

end Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteAmbientPoint
