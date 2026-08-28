import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneSheaf
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneCocycle
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Solvable

/-!
# Actual coboundaries in the ideal sheaf of infinity

Map an ideal-valued cocycle into the holomorphic function sheaf and
apply the proved normalized Cousin construction. Its constructed
primitive at infinity has value equal to the original overlap section
at infinity, hence zero. Thus every primitive lies in the actual ideal
sheaf, and the original ideal-valued cocycle is an actual coboundary.

In the reciprocal local frame this is the analytic division by the
coordinate underlying the constructed negative-one Cousin solver. No
vanishing or line-bundle identification is a hypothesis.
-/

noncomputable section

open Set TopologicalSpace Metric
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

open HolomorphicCousin

variable {ι : Type} {U : ι → Opens RiemannSphere}

/-- For an ideal-valued cocycle, the actual normalized primitive has
zero value at infinity whenever its domain contains infinity. -/
theorem cocyclePrimitive_mem_vanishingIdeal
    (c : CechOneCocycle negativeOneSheaf U)
    (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) {R : ℝ} (hR : 0 < R)
    (s : NormalizedCocycleSolution (fun i => (finiteOpen (U i) : Set ℂ))
      (cocycleCoefficient (c.map negativeOneInclusion)) i₀ R) (i : ι) :
    cocyclePrimitive (c.map negativeOneInclusion) i₀ hi₀ hR s i ∈ vanishingIdeal (U i) := by
  intro hi
  rw [cocyclePrimitive_infty,
    cocycleInfinityValue_apply (c.map negativeOneInclusion) i₀ hi₀ i hi]
  exact (c.value i i₀ : NegativeOneSection (U i ⊓ U i₀)).property ⟨hi, hi₀⟩

/-- The Cousin primitive as a genuine section of the actual ideal sheaf. -/
def negativeOnePrimitive (c : CechOneCocycle negativeOneSheaf U)
    (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) {R : ℝ} (hR : 0 < R)
    (s : NormalizedCocycleSolution (fun i => (finiteOpen (U i) : Set ℂ))
      (cocycleCoefficient (c.map negativeOneInclusion)) i₀ R) (i : ι) :
    NegativeOneSection (U i) :=
  ⟨cocyclePrimitive (c.map negativeOneInclusion) i₀ hi₀ hR s i,
    cocyclePrimitive_mem_vanishingIdeal c i₀ hi₀ hR s i⟩

/-- The literal restrictions of the constructed ideal sections give
the original ideal-valued cocycle on every actual overlap. -/
theorem negativeOnePrimitive_equation (c : CechOneCocycle negativeOneSheaf U)
    (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) {R : ℝ} (hR : 0 < R)
    (s : NormalizedCocycleSolution (fun i => (finiteOpen (U i) : Set ℂ))
      (cocycleCoefficient (c.map negativeOneInclusion)) i₀ R) (i j : ι) :
    res negativeOneSheaf inf_le_left (negativeOnePrimitive c i₀ hi₀ hR s i) -
      res negativeOneSheaf inf_le_right (negativeOnePrimitive c i₀ hi₀ hR s j) = c.value i j := by
  apply Subtype.ext
  exact cocyclePrimitive_equation (c.map negativeOneInclusion) i₀ hi₀ hR s i j

/-- In the distinguished reciprocal chart, the actual ideal primitive
has precisely the infinity coefficient of the constructed negative-one
Cousin solution, multiplied by the local frame `u`. -/
theorem negativeOnePrimitive_infinity_frame (c : CechOneCocycle negativeOneSheaf U)
    (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) {R : ℝ} (hR : 0 < R)
    (s : NormalizedCocycleSolution (fun i => (finiteOpen (U i) : Set ℂ))
      (cocycleCoefficient (c.map negativeOneInclusion)) i₀ R)
    (u : ℂ) (hu : u ∈ ball (0 : ℂ) R⁻¹)
    (hUu : RiemannSphere.infinityParametrization u ∈ U i₀) :
    infinityCoefficient (U i₀) (negativeOnePrimitive c i₀ hi₀ hR s i₀).val u =
      u * (s.negativeOne hR).infinityPart u := by
  by_cases hu₀ : u = 0
  · subst u
    rw [infinityCoefficient_zero (U i₀) _ hi₀, zero_mul]
    exact (negativeOnePrimitive c i₀ hi₀ hR s i₀).property hi₀
  · have hfinite : ((u⁻¹ : ℂ) : RiemannSphere) ∈ U i₀ := by
      simpa only [RiemannSphere.infinityParametrization_of_ne hu₀] using hUu
    rw [infinityCoefficient_eq_finiteCoefficient _ _ u hu₀,
      finiteCoefficient_apply (U i₀) _ u⁻¹ hfinite]
    change s.localPart i₀ u⁻¹ = _
    have huR : ‖u‖ < R⁻¹ := by
      simpa only [mem_ball, dist_zero_right] using hu
    have hlarge : R < ‖u⁻¹‖ := by
      rw [norm_inv]
      exact (lt_inv_comm₀ hR (norm_pos_iff.mpr hu₀)).mpr huR
    simpa only [NormalizedCocycleSolution.negativeOne, inv_inv] using
      (s.negativeOne hR).atInfinity u⁻¹ hlarge

/-- Every actual one-cocycle of the ideal sheaf is solvable on its
original arbitrary open cover of the sphere. -/
theorem negativeOne_cechOneVanishing : CechOneVanishing negativeOneSheaf := by
  intro ι U hU c
  obtain ⟨i₀, hi₀⟩ := hU (∞ : RiemannSphere)
  obtain ⟨R, hR, ⟨s⟩⟩ := exists_finite_cocycle_solution hU
    (c.map negativeOneInclusion) i₀ hi₀
  exact ⟨negativeOnePrimitive c i₀ hi₀ hR s, negativeOnePrimitive_equation c i₀ hi₀ hR s⟩

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
