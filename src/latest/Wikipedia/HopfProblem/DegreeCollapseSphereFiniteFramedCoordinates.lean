import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteRadialCoordinates
import Wikipedia.NoExoticSixSphere.SphereThreeFramedDerivative
import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates

/-!
# Exact finite-coordinate factorization of the original framed derivative

The global quaternionic tangent columns obey the actual chain rule, proved
through the native inclusion derivative. Combining this identity with the
radial half-column factors the whole lifted normal-plus-tangent operator
through the invertible inverse-chart coordinate family.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteFramedCoordinates

open NoExoticSixSphere SphereCenteredAmbientChart SphereFiniteAmbientPoint
open SphereFiniteRadialCoordinates SphereThreeTangentFrame

theorem framedDerivative_comp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (hg : ContDiff ℝ ∞ g) (u : Sphere 3 → E)
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ u) (s : Sphere 3) :
    framedDerivative (g ∘ u) s = (fderiv ℝ g (u s)).comp (framedDerivative u s) := by
  have hgu := hg.contMDiff.comp hu
  have hc := mfderiv_comp s ((hg.differentiable (by simp) (u s)).mdifferentiableAt)
    (hu.mdifferentiable (by simp) s)
  rw [mfderiv_eq_fderiv] at hc
  apply ContinuousLinearMap.ext
  intro v
  have ht : operator s.val v ∈ (inclusionDerivative s).range := by
    rw [range_inclusionDerivative, ← range_operator]
    exact ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := ht
  change inclusionDerivative s w = operator s.val v at hw
  have hL := congrArg (fun L : V 3 →L[ℝ] F ↦ L w)
    (extensionDerivative_comp_inclusion (g ∘ u) hgu s)
  have hR := congrArg (fun L : V 3 →L[ℝ] E ↦ L w)
    (extensionDerivative_comp_inclusion u hu s)
  change fderiv ℝ (SmoothSphereAmbient.extension (Stiefel.pole 3) (g ∘ u)) s.val
      (operator s.val v) =
    fderiv ℝ g (u s)
      (fderiv ℝ (SmoothSphereAmbient.extension (Stiefel.pole 3) u) s.val (operator s.val v))
  rw [← hw]
  change fderiv ℝ (SmoothSphereAmbient.extension (Stiefel.pole 3) (g ∘ u)) s.val
    (inclusionDerivative s w) = _ at hL
  change fderiv ℝ (SmoothSphereAmbient.extension (Stiefel.pole 3) u) s.val
    (inclusionDerivative s w) = _ at hR
  rw [hL, hR]
  exact congrArg (fun L : V 3 →L[ℝ] F ↦ L w) hc

variable {m n : ℕ}

theorem framedDerivative_ambientPoint (u : Sphere 3 → V m)
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, V m) ∞ u) (s : Sphere 3) :
    framedDerivative (ambientPoint m ∘ u) s =
      (fderiv ℝ (ambientPoint m) (u s)).comp (framedDerivative u s) :=
  framedDerivative_comp (ambientPoint m) (contDiff_ambientPoint m) u hu s

theorem contMDiff_framedDerivative (u : Sphere 3 → V m)
    (hu : ContMDiff (𝓡 3) 𝓘(ℝ, V m) ∞ u) :
    ContMDiff (𝓡 3) 𝓘(ℝ, V 3 →L[ℝ] V m) ∞ (framedDerivative u) := by
  have h : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, V m) ∞
      (Function.uncurry (fun _ : ℝ ↦ u)) := hu.comp contMDiff_snd
  exact (contMDiff_framedDerivative_family (fun _ : ℝ ↦ u) h).comp
    ((contMDiff_const (c := (0 : ℝ))).prodMk contMDiff_id)

def normalPart (R : V n →L[ℝ] V m) : V (n + 1) →L[ℝ] V (m + 1) :=
  (EuclideanTailCoordinates.split m).symm.toContinuousLinearMap.comp
    (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V m)).symm.toContinuousLinearMap.comp
      ((WithLp.fstL 2 ℝ ℝ (V n)).prod (R.comp (WithLp.sndL 2 ℝ ℝ (V n))))).comp
        (EuclideanTailCoordinates.split n).toContinuousLinearMap)

def tangentPart (B : V 3 →L[ℝ] V m) : V 3 →L[ℝ] V (m + 1) :=
  (EuclideanTailCoordinates.split m).symm.toContinuousLinearMap.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V m)).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inr ℝ ℝ (V m)).comp B))

theorem normalPart_apply (R : V n →L[ℝ] V m) (w : V (n + 1)) :
    normalPart R w = (EuclideanTailCoordinates.split m).symm
      (WithLp.toLp 2 ((EuclideanTailCoordinates.split n w).fst,
        R (EuclideanTailCoordinates.split n w).snd)) := rfl

theorem tangentPart_apply (B : V 3 →L[ℝ] V m) (v : V 3) :
    tangentPart B v = (EuclideanTailCoordinates.split m).symm
      (WithLp.toLp 2 (0, B v)) := rfl

def finiteOperator (R : V n →L[ℝ] V m) (B : V 3 →L[ℝ] V m) :
    V ((n + 1) + 3) →L[ℝ] V (m + 1) := OperatorSum.operator (normalPart R) (tangentPart B)

theorem coordinate_normal (u : V m) (R : V n →L[ℝ] V m) (w : V (n + 1)) :
    frameOperator u (normalPart R w) =
      SphereFiniteEquationLift.lift u R (EuclideanTailCoordinates.split n w) := by
  change coordinateOperator u (EuclideanTailCoordinates.split m (normalPart R w)) = _
  rw [normalPart_apply, LinearIsometryEquiv.apply_symm_apply]
  exact (lift_eq_coordinates u R (EuclideanTailCoordinates.split n w)).symm

theorem coordinate_tangent (u : V m) (B : V 3 →L[ℝ] V m) (v : V 3) :
    frameOperator u (tangentPart B v) = fderiv ℝ (ambientPoint m) u (B v) := by
  change coordinateOperator u (EuclideanTailCoordinates.split m (tangentPart B v)) = _
  rw [tangentPart_apply, LinearIsometryEquiv.apply_symm_apply, coordinateOperator_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, mul_zero, zero_smul, zero_add]

theorem coordinate_finiteOperator (u : V m) (R : V n →L[ℝ] V m) (B : V 3 →L[ℝ] V m) :
    (frameOperator u).comp (finiteOperator R B) =
      OperatorSum.operator
        ((SphereFiniteEquationLift.lift u R).comp
          (EuclideanTailCoordinates.split n).toContinuousLinearMap)
        ((fderiv ℝ (ambientPoint m) u).comp B) := by
  apply ContinuousLinearMap.ext
  intro v
  change frameOperator u (OperatorSum.operator (normalPart R) (tangentPart B) v) = _
  rw [OperatorSum.operator_apply, map_add, coordinate_normal, coordinate_tangent,
    OperatorSum.operator_apply]
  rfl

theorem continuous_normalPart {X : Type*} [TopologicalSpace X]
    (R : X → V n →L[ℝ] V m) (hR : Continuous R) :
    Continuous (fun x ↦ normalPart (R x)) := by
  apply continuous_clm_apply.mpr
  intro w
  simp_rw [normalPart_apply]
  exact (EuclideanTailCoordinates.split m).symm.continuous.comp
    ((WithLp.prod_continuous_toLp 2 ℝ (V m)).comp
      (continuous_const.prodMk (hR.clm_apply continuous_const)))

theorem continuous_tangentPart {X : Type*} [TopologicalSpace X]
    (B : X → V 3 →L[ℝ] V m) (hB : Continuous B) :
    Continuous (fun x ↦ tangentPart (B x)) := by
  apply continuous_clm_apply.mpr
  intro v
  simp_rw [tangentPart_apply]
  exact (EuclideanTailCoordinates.split m).symm.continuous.comp
    ((WithLp.prod_continuous_toLp 2 ℝ (V m)).comp
      (continuous_const.prodMk (hB.clm_apply continuous_const)))

theorem continuous_finiteOperator {X : Type*} [TopologicalSpace X]
    (R : X → V n →L[ℝ] V m) (B : X → V 3 →L[ℝ] V m)
    (hR : Continuous R) (hB : Continuous B) :
    Continuous (fun x ↦ finiteOperator (R x) (B x)) :=
  OperatorSum.continuous_operator (fun x ↦ normalPart (R x)) (fun x ↦ tangentPart (B x))
    (continuous_normalPart R hR) (continuous_tangentPart B hB)

end Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteFramedCoordinates
