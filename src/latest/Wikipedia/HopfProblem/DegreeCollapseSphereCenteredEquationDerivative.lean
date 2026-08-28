import Wikipedia.HopfProblem.DegreeCollapseSphereCenteredAmbientChart
import Wikipedia.NoExoticSixSphere.SphereFiberNormalFrame

/-!
# The full sphere-level equation derivative from an actual ambient map

The radial equation and the original centered target chart are both kept.
For an ambient sphere map with the stated radial identities, the full
derivative is the original ambient differential followed by a fixed
radial/tangent target equivalence. Its orthogonal right inverse transforms
by the exact inverse target equivalence.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereCenteredEquationDerivative

open NoExoticSixSphere SphereCenteredAmbientChart SphereRadialDifferential

variable {m n : ℕ}

theorem equations_formula (f : C(Sphere m, Sphere n)) (P : V (m + 1) → V (n + 1))
    (hval : ∀ x : Sphere m, (f x).val = P x.val) (b : Sphere n) (a : Sphere m)
    (y : V (m + 1)) :
    SphereFiberNormalFrame.equations f b a y =
      WithLp.toLp 2 (‖y‖ ^ 2 - 1,
        ambientChart b (P (ambientRetract a y)) - ambientChart b b.val) := by
  change WithLp.toLp 2 (‖y‖ ^ 2 - 1,
    modelChartPartialDiffeomorph (I := 𝓡 n) b (f (SphereRadialRetraction.retract a y)) -
      modelChartPartialDiffeomorph (I := 𝓡 n) b b) = _
  rw [modelChart_apply, modelChart_apply, hval]
  rfl

def operator (P : V (m + 1) → V (n + 1)) (b : Sphere n) (x : Sphere m) :
    V (m + 1) →L[ℝ] WithLp 2 (ℝ × V n) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V n)).symm.toContinuousLinearMap.comp
    (((2 : ℕ) • innerSL ℝ x.val).prod
      ((linearPart b).comp ((fderiv ℝ P x.val).comp (tangentProjection x))))

theorem hasFDerivAt_equations (f : C(Sphere m, Sphere n)) (P : V (m + 1) → V (n + 1))
    (hval : ∀ x : Sphere m, (f x).val = P x.val) (b : Sphere n) (a x : Sphere m)
    (hx : f x = b) (hP : DifferentiableAt ℝ P x.val) :
    HasFDerivAt (SphereFiberNormalFrame.equations f b a) (operator P b x) x.val := by
  have hp : HasFDerivAt P (fderiv ℝ P x.val) (ambientRetract a x.val) := by
    rw [ambientRetract_coe]
    exact hP.hasFDerivAt
  have hpx := hp.comp x.val (hasFDerivAt_ambientRetract a x)
  have hpoint : P (ambientRetract a x.val) = b.val := by
    rw [ambientRetract_coe, ← hval, hx]
  have hc : HasFDerivAt (ambientChart b) (linearPart b) (P (ambientRetract a x.val)) :=
    hpoint.symm ▸ hasFDerivAt_ambientChart b
  have hcoord := (hc.comp x.val hpx).sub_const (ambientChart b b.val)
  have hnorm := (hasStrictFDerivAt_norm_sq x.val).hasFDerivAt.sub_const 1
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V n)).symm.hasFDerivAt.comp x.val
    (hnorm.prodMk hcoord)
  have he : SphereFiberNormalFrame.equations f b a =
      fun y ↦ WithLp.toLp 2 (‖y‖ ^ 2 - 1,
        ambientChart b (P (ambientRetract a y)) - ambientChart b b.val) :=
    funext (equations_formula f P hval b a)
  rw [he]
  exact h

theorem fderiv_equations (f : C(Sphere m, Sphere n)) (P : V (m + 1) → V (n + 1))
    (hval : ∀ x : Sphere m, (f x).val = P x.val) (b : Sphere n) (a x : Sphere m)
    (hx : f x = b) (hP : DifferentiableAt ℝ P x.val) :
    fderiv ℝ (SphereFiberNormalFrame.equations f b a) x.val = operator P b x :=
  (hasFDerivAt_equations f P hval b a x hx hP).fderiv

theorem operator_eq_split_comp (P : V (m + 1) → V (n + 1)) (b : Sphere n) (x : Sphere m)
    (hN : ∀ v, 2 * inner ℝ x.val v = inner ℝ b.val (fderiv ℝ P x.val v))
    (hR : linearPart b (fderiv ℝ P x.val x.val) = 0) :
    operator P b x = (coordinateEquiv b).toContinuousLinearMap.comp (fderiv ℝ P x.val) := by
  ext v
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (2 : ℕ) • inner ℝ x.val v = inner ℝ b.val (fderiv ℝ P x.val v)
    simpa only [two_smul, two_mul] using hN v
  · change linearPart b (fderiv ℝ P x.val (tangentProjection x v)) =
      linearPart b (fderiv ℝ P x.val v)
    rw [tangentProjection_apply, map_sub, map_smul, map_sub, map_smul, hR,
      smul_zero, sub_zero]

theorem fderiv_equations_eq_split_comp
    (f : C(Sphere m, Sphere n)) (P : V (m + 1) → V (n + 1))
    (hval : ∀ x : Sphere m, (f x).val = P x.val) (b : Sphere n) (a x : Sphere m)
    (hx : f x = b) (hP : DifferentiableAt ℝ P x.val)
    (hN : ∀ v, 2 * inner ℝ x.val v = inner ℝ b.val (fderiv ℝ P x.val v))
    (hR : linearPart b (fderiv ℝ P x.val x.val) = 0) :
    fderiv ℝ (SphereFiberNormalFrame.equations f b a) x.val =
      (coordinateEquiv b).toContinuousLinearMap.comp (fderiv ℝ P x.val) :=
  (fderiv_equations f P hval b a x hx hP).trans (operator_eq_split_comp P b x hN hR)

theorem canonical_postcompose (b : Sphere n) (D : V (m + 1) →L[ℝ] V (n + 1))
    (hD : Function.Surjective D) :
    orthogonalRightInverse ((coordinateEquiv b).toContinuousLinearMap.comp D) =
      (orthogonalRightInverse D).comp (coordinateEquiv b).symm.toContinuousLinearMap := by
  have hk : ((coordinateEquiv b).toContinuousLinearMap.comp D).ker = D.ker := by
    ext v
    change coordinateEquiv b (D v) = 0 ↔ D v = 0
    constructor
    · intro h
      exact (coordinateEquiv b).injective (h.trans (map_zero (coordinateEquiv b)).symm)
    · intro h
      rw [h, map_zero]
  apply orthogonalRightInverse_eq_of_rightInverse
    ((coordinateEquiv b).toContinuousLinearMap.comp D)
    ((coordinateEquiv b).surjective.comp hD)
    ((orthogonalRightInverse D).comp (coordinateEquiv b).symm.toContinuousLinearMap)
  · intro w
    change coordinateEquiv b (D (orthogonalRightInverse D ((coordinateEquiv b).symm w))) = w
    rw [apply_orthogonalRightInverse D hD, ContinuousLinearEquiv.apply_symm_apply]
  · rw [hk]
    rintro _ ⟨w, rfl⟩
    rw [← range_orthogonalRightInverse D hD]
    exact ⟨(coordinateEquiv b).symm w, rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.SphereCenteredEquationDerivative
