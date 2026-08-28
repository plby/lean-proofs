import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteAmbientDerivative
import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteEquationLift
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# Invertible radial and inverse-chart coordinates on the whole finite chart

The radial half-column and the derivative of the actual inverse sphere chart
together form a continuous linear equivalence at every finite point. The
family is smooth on the entire Euclidean chart, including zero. These are
the actual operators appearing in the lifted Hopf normal frame.
-/

noncomputable section

open Function
open scoped Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteRadialCoordinates

open NoExoticSixSphere SphereCenteredAmbientChart SphereFiniteAmbientPoint
open SphereFiniteAmbientDerivative

variable {n : ℕ}

def coordinateOperator (u : V n) : WithLp 2 (ℝ × V n) →L[ℝ] V (n + 1) :=
  SphereFiniteEquationLift.lift u (ContinuousLinearMap.id ℝ (V n))

theorem coordinateOperator_apply (u : V n) (p : WithLp 2 (ℝ × V n)) :
    coordinateOperator u p = ((1 / 2 : ℝ) * p.fst) • ambientPoint n u +
      fderiv ℝ (ambientPoint n) u p.snd := rfl

theorem radial_coefficient (u : V n) (p : WithLp 2 (ℝ × V n)) :
    inner ℝ (ambientPoint n u) (coordinateOperator u p) = (1 / 2 : ℝ) * p.fst := by
  rw [coordinateOperator_apply, inner_add_right, inner_smul_right, derivative_tangent,
    real_inner_self_eq_norm_sq, ambientPoint_norm, one_pow, mul_one, add_zero]

theorem coordinateOperator_injective (u : V n) : Injective (coordinateOperator u) := by
  intro p q h
  have hs : p.fst = q.fst := by
    have hr := congrArg (fun v ↦ inner ℝ (ambientPoint n u) v) h
    rw [radial_coefficient, radial_coefficient] at hr
    linarith
  have ht := h
  rw [coordinateOperator_apply, coordinateOperator_apply, hs] at ht
  apply WithLp.ofLp_injective 2
  exact Prod.ext hs (derivative_injective n u (add_left_cancel ht))

theorem coordinateOperator_surjective (u : V n) : Surjective (coordinateOperator u) := by
  intro w
  let r := inner ℝ (ambientPoint n u) w
  have hm : w - r • ambientPoint n u ∈ (fderiv ℝ (ambientPoint n) u).range := by
    rw [derivative_range]
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      ambientPoint_norm, one_pow, mul_one]
    exact sub_self r
  obtain ⟨v, hv⟩ := hm
  change fderiv ℝ (ambientPoint n) u v = w - r • ambientPoint n u at hv
  refine ⟨WithLp.toLp 2 (2 * r, v), ?_⟩
  rw [coordinateOperator_apply]
  change ((1 / 2 : ℝ) * (2 * r)) • ambientPoint n u +
    fderiv ℝ (ambientPoint n) u v = w
  rw [hv]
  have hr : (1 / 2 : ℝ) * (2 * r) = r := by ring
  rw [hr]
  abel

def coordinateEquiv (u : V n) : WithLp 2 (ℝ × V n) ≃L[ℝ] V (n + 1) :=
  (LinearEquiv.ofBijective (coordinateOperator u).toLinearMap
    ⟨coordinateOperator_injective u, coordinateOperator_surjective u⟩).toContinuousLinearEquiv

theorem coordinateEquiv_apply (u : V n) (p : WithLp 2 (ℝ × V n)) :
    coordinateEquiv u p = coordinateOperator u p := rfl

theorem contDiff_coordinateOperator : ContDiff ℝ ∞ (coordinateOperator (n := n)) :=
  (SphereFiniteEquationLift.contMDiff_lift (m := n) (n := n) (I := 𝓘(ℝ, V n))
    (u := id) (R := fun _ ↦ ContinuousLinearMap.id ℝ (V n))
    contMDiff_id contMDiff_const).contDiff

def frameOperator (u : V n) : V (n + 1) →L[ℝ] V (n + 1) :=
  (coordinateOperator u).comp (EuclideanTailCoordinates.split n).toContinuousLinearMap

def frameEquiv (u : V n) : V (n + 1) ≃L[ℝ] V (n + 1) :=
  (EuclideanTailCoordinates.split n).toContinuousLinearEquiv.trans (coordinateEquiv u)

theorem frameEquiv_apply (u : V n) (v : V (n + 1)) :
    frameEquiv u v = frameOperator u v := rfl

theorem frameOperator_injective (u : V n) : Injective (frameOperator u) :=
  (coordinateOperator_injective u).comp (EuclideanTailCoordinates.split n).injective

theorem contDiff_frameOperator : ContDiff ℝ ∞ (frameOperator (n := n)) :=
  contDiff_coordinateOperator.clm_comp contDiff_const

theorem lift_eq_coordinates {m : ℕ} (u : V n) (R : V m →L[ℝ] V n)
    (p : WithLp 2 (ℝ × V m)) :
    SphereFiniteEquationLift.lift u R p =
      coordinateOperator u (WithLp.toLp 2 (p.fst, R p.snd)) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteRadialCoordinates
