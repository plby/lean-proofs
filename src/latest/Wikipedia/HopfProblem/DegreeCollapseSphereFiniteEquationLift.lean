import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteAmbientPoint
import Wikipedia.HopfProblem.DegreeCollapseSphereCenteredEquationDerivative
import Wikipedia.NoExoticSixSphere.SmoothSphereAmbientExtension

/-!
# Lifting a finite right inverse to the original full sphere equations

The equations composed with the actual inverse chart have zero radial
component and the original finite sphere-map component. Their derivative
on the radial vector is separately (2,0). These identities give the full
right inverse with an explicit radial half-column and inverse-chart lift.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteEquationLift

open NoExoticSixSphere SphereCenteredAmbientChart SphereFiniteAmbientPoint

local instance (n : ℕ) : Fact (Module.finrank ℝ (V (n + 1)) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {m n : ℕ}

theorem equations_ambientPoint (f : C(Sphere m, Sphere n)) (a : Sphere m) (u : V m) :
    SphereFiberNormalFrame.equations f (-spherePole n) a (ambientPoint m u) =
      WithLp.toLp 2 (0, SphereFiniteRepresentative.value f u) := by
  change SphereLevelEquations.equations a
    (CenteredChartCoordinates.coordinates f
      (modelChartPartialDiffeomorph (I := 𝓡 n) (-spherePole n)) (-spherePole n))
        (SphereFiniteRepresentative.point m u).val = _
  rw [SphereLevelEquations.equations_coe]
  change WithLp.toLp 2 (0,
    modelChartPartialDiffeomorph (I := 𝓡 n) (-spherePole n)
      (f (SphereFiniteRepresentative.point m u)) -
    modelChartPartialDiffeomorph (I := 𝓡 n) (-spherePole n) (-spherePole n)) = _
  rw [modelChart_apply, modelChart_apply, ambientChart_self, sub_zero,
    ← sphereProjection_ambientChart]
  rfl

theorem equations_fderiv_ambientPoint (f : C(Sphere m, Sphere n))
    (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (a : Sphere m) (u v : V m)
    (hx : f (SphereFiniteRepresentative.point m u) = -spherePole n) :
    fderiv ℝ (SphereFiberNormalFrame.equations f (-spherePole n) a) (ambientPoint m u)
      (fderiv ℝ (ambientPoint m) u v) =
      WithLp.toLp 2 (0, fderiv ℝ (SphereFiniteRepresentative.value f) u v) := by
  have hE := (SphereFiberNormalFrame.contDiffAt_equations f hf (-spherePole n) a
    (SphereFiniteRepresentative.point m u) hx).differentiableAt (by simp)
  have hA := (contDiff_ambientPoint m).differentiable (by simp) u
  have hV := (SphereFiniteRepresentative.value_contDiffAt f u (hf _) (by
    rw [hx]
    exact neg_pole_ne_pole n)).differentiableAt (by simp)
  have hleft := hE.hasFDerivAt.comp u hA.hasFDerivAt
  have he : SphereFiberNormalFrame.equations f (-spherePole n) a ∘ ambientPoint m =
      fun w ↦ WithLp.toLp 2 (0, SphereFiniteRepresentative.value f w) :=
    funext (equations_ambientPoint f a)
  rw [he] at hleft
  have hright := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V n)).symm.hasFDerivAt.comp u
    ((hasFDerivAt_const (0 : ℝ) u).prodMk hV.hasFDerivAt)
  exact congrArg (fun L : V m →L[ℝ] WithLp 2 (ℝ × V n) ↦ L v) (hleft.unique hright)

theorem equations_fderiv_radial (f : C(Sphere m, Sphere n))
    (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n) (a x : Sphere m) (hx : f x = b) :
    fderiv ℝ (SphereFiberNormalFrame.equations f b a) x.val x.val =
      WithLp.toLp 2 (2, (0 : V n)) := by
  let P : V (m + 1) → V (n + 1) :=
    SmoothSphereAmbient.extension a (fun y : Sphere m ↦ (f y).val)
  have hval : ∀ y : Sphere m, (f y).val = P y.val :=
    fun y ↦ (SmoothSphereAmbient.extension_coe a (fun z : Sphere m ↦ (f z).val) y).symm
  have hP : ContDiff ℝ ∞ P := SmoothSphereAmbient.contDiff_extension a _
    ((contMDiff_coe_sphere (n := n) (m := ∞)).comp hf)
  rw [SphereCenteredEquationDerivative.fderiv_equations f P hval b a x hx
    (hP.differentiable (by simp) x.val)]
  change WithLp.toLp 2 ((2 : ℕ) • inner ℝ x.val x.val,
    linearPart b (fderiv ℝ P x.val (SphereRadialDifferential.tangentProjection x x.val))) = _
  rw [SphereRadialDifferential.tangentProjection_radial, map_zero, map_zero,
    real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, one_pow]
  norm_num

def lift (u : V m) (R : V n →L[ℝ] V m) : WithLp 2 (ℝ × V n) →L[ℝ] V (m + 1) :=
  ContinuousLinearMap.smulRight ((1 / 2 : ℝ) • WithLp.fstL 2 ℝ ℝ (V n)) (ambientPoint m u) +
    (fderiv ℝ (ambientPoint m) u).comp (R.comp (WithLp.sndL 2 ℝ ℝ (V n)))

theorem lift_apply (u : V m) (R : V n →L[ℝ] V m) (p : WithLp 2 (ℝ × V n)) :
    lift u R p = ((1 / 2 : ℝ) * p.fst) • ambientPoint m u +
      fderiv ℝ (ambientPoint m) u (R p.snd) := rfl

theorem equations_lift (f : C(Sphere m, Sphere n))
    (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (a : Sphere m) (u : V m)
    (hx : f (SphereFiniteRepresentative.point m u) = -spherePole n)
    (R : V n →L[ℝ] V m)
    (hR : ∀ w, fderiv ℝ (SphereFiniteRepresentative.value f) u (R w) = w)
    (p : WithLp 2 (ℝ × V n)) :
    fderiv ℝ (SphereFiberNormalFrame.equations f (-spherePole n) a) (ambientPoint m u)
      (lift u R p) = p := by
  rw [lift_apply, map_add, map_smul,
    equations_fderiv_ambientPoint f hf a u (R p.snd) hx, hR]
  have hr := equations_fderiv_radial f hf (-spherePole n) a
    (SphereFiniteRepresentative.point m u) hx
  change fderiv ℝ (SphereFiberNormalFrame.equations f (-spherePole n) a)
    (ambientPoint m u) (ambientPoint m u) = _ at hr
  rw [hr]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change ((1 / 2 : ℝ) * p.fst) * 2 + 0 = p.fst
    ring
  · change ((1 / 2 : ℝ) * p.fst) • (0 : V n) + p.snd = p.snd
    simp

section Family

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiff_lift {u : M → V m} {R : M → V n →L[ℝ] V m}
    (hu : ContMDiff I 𝓘(ℝ, V m) ∞ u)
    (hR : ContMDiff I 𝓘(ℝ, V n →L[ℝ] V m) ∞ R) :
    ContMDiff I 𝓘(ℝ, WithLp 2 (ℝ × V n) →L[ℝ] V (m + 1)) ∞
      (fun x ↦ lift (u x) (R x)) := by
  have hA := (contDiff_ambientPoint m).contMDiff.comp hu
  have hD := (contDiff_fderiv_ambientPoint m).contMDiff.comp hu
  have hr : ContMDiff I 𝓘(ℝ, WithLp 2 (ℝ × V n) →L[ℝ] V (m + 1)) ∞
      (fun x ↦ ContinuousLinearMap.smulRight
        ((1 / 2 : ℝ) • WithLp.fstL 2 ℝ ℝ (V n)) (ambientPoint m (u x))) :=
    ((ContinuousLinearMap.smulRightL ℝ (WithLp 2 (ℝ × V n)) (V (m + 1)))
      ((1 / 2 : ℝ) • WithLp.fstL 2 ℝ ℝ (V n))).contDiff.contMDiff.comp hA
  exact hr.add (hD.clm_comp (hR.clm_comp contMDiff_const))

end Family

end Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteEquationLift
