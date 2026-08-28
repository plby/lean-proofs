import Wikipedia.HopfProblem.DegreeCollapseSphereEquatorialChartDifferential
import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteRepresentative

/-!
# The finite derivative of a sphere map in the original chart coordinates

Radial retraction supplies an equality of actual Euclidean germs. Its
derivative fixes tangent vectors, so differentiating this equality compares
the finite representative with the original ambient map without changing
either stereographic basis.
-/

noncomputable section

open Filter
open scoped Topology Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteTangentDerivative

open NoExoticSixSphere SphereCenteredAmbientChart SphereRadialDifferential

variable {m n : ℕ} (f : C(Sphere m, Sphere n)) (P : V (m + 1) → V (n + 1))
  (hval : ∀ x, (f x).val = P x.val) (a x : Sphere m)

include hval in
theorem finite_retract_eventuallyEq (hx : x ≠ spherePole m) :
    (fun y ↦ SphereFiniteRepresentative.value f
      (ambientChart (-spherePole m) (ambientRetract a y))) =ᶠ[𝓝 x.val]
    (fun y ↦ ambientChart (-spherePole n) (P (ambientRetract a y))) := by
  let : Fact (Module.finrank ℝ (V (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have ht : Tendsto (SphereRadialRetraction.retract a) (𝓝 x.val) (𝓝 x) := by
    have hc : Tendsto (SphereRadialRetraction.retract a) (𝓝 x.val)
        (𝓝 (SphereRadialRetraction.retract a x.val)) :=
      (SphereRadialRetraction.contMDiffAt_retract (n := m) a
        (ne_zero_of_mem_unit_sphere x)).continuousAt
    rwa [SphereRadialRetraction.retract_coe] at hc
  have hn : ∀ᶠ u in 𝓝 x, u ≠ spherePole m := isOpen_ne.mem_nhds hx
  filter_upwards [ht.eventually hn] with y hy
  change SphereFiniteRepresentative.value f
    (ambientChart (-spherePole m) (SphereRadialRetraction.retract a y).val) = _
  rw [← sphereProjection_ambientChart, SphereFiniteRepresentative.value,
    SphereFiniteRepresentative.point_projection m hy, sphereProjection_ambientChart, hval]
  rfl

include hval in
theorem fderiv_value_tangent (hx : x ≠ spherePole m)
    (hF : DifferentiableAt ℝ (SphereFiniteRepresentative.value f) (sphereProjection m x))
    (hS : DifferentiableAt ℝ (ambientChart (-spherePole m)) x.val)
    (hT : DifferentiableAt ℝ (ambientChart (-spherePole n)) (P x.val))
    (hP : DifferentiableAt ℝ P x.val) (v : V (m + 1)) (hv : inner ℝ x.val v = 0) :
    fderiv ℝ (SphereFiniteRepresentative.value f) (sphereProjection m x)
      (fderiv ℝ (ambientChart (-spherePole m)) x.val v) =
    fderiv ℝ (ambientChart (-spherePole n)) (P x.val) (fderiv ℝ P x.val v) := by
  have hR := hasFDerivAt_ambientRetract x x
  have hS' : HasFDerivAt (ambientChart (-spherePole m))
      (fderiv ℝ (ambientChart (-spherePole m)) x.val) (ambientRetract x x.val) := by
    rw [ambientRetract_coe]
    exact hS.hasFDerivAt
  have hP' : HasFDerivAt P (fderiv ℝ P x.val) (ambientRetract x x.val) := by
    rw [ambientRetract_coe]
    exact hP.hasFDerivAt
  have hF' : HasFDerivAt (SphereFiniteRepresentative.value f)
      (fderiv ℝ (SphereFiniteRepresentative.value f) (sphereProjection m x))
      (ambientChart (-spherePole m) (ambientRetract x x.val)) := by
    rw [ambientRetract_coe, ← sphereProjection_ambientChart]
    exact hF.hasFDerivAt
  have hT' : HasFDerivAt (ambientChart (-spherePole n))
      (fderiv ℝ (ambientChart (-spherePole n)) (P x.val)) (P (ambientRetract x x.val)) := by
    rw [ambientRetract_coe]
    exact hT.hasFDerivAt
  have hleft := hF'.comp x.val (hS'.comp x.val hR)
  have hright := hT'.comp x.val (hP'.comp x.val hR)
  have he := hleft.unique
    (hright.congr_of_eventuallyEq (finite_retract_eventuallyEq f P hval x x hx))
  have heval := congrArg (fun L : V (m + 1) →L[ℝ] V n ↦ L v) he
  change fderiv ℝ (SphereFiniteRepresentative.value f) (sphereProjection m x)
    (fderiv ℝ (ambientChart (-spherePole m)) x.val (tangentProjection x v)) =
    fderiv ℝ (ambientChart (-spherePole n)) (P x.val)
      (fderiv ℝ P x.val (tangentProjection x v)) at heval
  rwa [tangentProjection_tangent x v hv] at heval

theorem value_differentiableAt (hx : x ≠ spherePole m)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f x) (hb : f x ≠ spherePole n) :
    DifferentiableAt ℝ (SphereFiniteRepresentative.value f) (sphereProjection m x) := by
  have hf' : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f
      (SphereFiniteRepresentative.point m (sphereProjection m x)) := by
    rwa [SphereFiniteRepresentative.point_projection m hx]
  have hb' : f (SphereFiniteRepresentative.point m (sphereProjection m x)) ≠ spherePole n := by
    rwa [SphereFiniteRepresentative.point_projection m hx]
  have h := SphereFiniteRepresentative.value_contDiffAt f (sphereProjection m x) hf' hb'
  exact h.differentiableAt (by simp)

end Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteTangentDerivative
