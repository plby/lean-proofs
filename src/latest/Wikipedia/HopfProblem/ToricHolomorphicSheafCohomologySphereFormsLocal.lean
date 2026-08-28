import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereFormsBasic

/-!
# Local determination and actual covectors for sphere forms

The inversion factors compose to one.  Consequently a form section on
an open subset of one chart is determined by that chart's coefficient.
The coefficient also defines an actual real continuous-linear
antiholomorphic covector, whose pullback under the derivative of the
actual inversion chart is precisely the prescribed transition law.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms

/-- The two actual reciprocal covector factors compose to the identity. -/
theorem transition_mul_inv {z : ℂ} (hz : z ≠ 0) : transition z * transition z⁻¹ = 1 := by
  have h : (-(z ^ 2)⁻¹) * (-((z⁻¹) ^ 2)⁻¹) = 1 := by field_simp [hz]
  exact ((starRingEnd ℂ).map_mul _ _).symm.trans
    ((congrArg (starRingEnd ℂ) h).trans (map_one (starRingEnd ℂ)))

/-- The actual form transition in either of the two chart directions. -/
theorem condition_inversion {U : Opens RiemannSphere} (s : Section U) (b : Bool)
    (z : ℂ) (hz : z ≠ 0) (h₀ : z ∈ coordinateOpen U b)
    (h₁ : z⁻¹ ∈ coordinateOpen U (!b)) :
    coefficient s b ⟨z, h₀⟩ = transition z * coefficient s (!b) ⟨z⁻¹, h₁⟩ := by
  cases b
  · exact condition s z hz h₀ h₁
  · have hself : z⁻¹⁻¹ ∈ coordinateOpen U true := by simpa only [inv_inv] using h₀
    have h : coefficient s false ⟨z⁻¹, h₁⟩ =
        transition z⁻¹ * coefficient s true ⟨z, h₀⟩ := by
      simpa only [inv_inv] using condition s z⁻¹ (inv_ne_zero hz) h₁ hself
    change coefficient s true ⟨z, h₀⟩ = transition z * coefficient s false ⟨z⁻¹, h₁⟩
    rw [h, ← mul_assoc, transition_mul_inv hz, one_mul]

/-- On an actual open subset of a chart image, its coefficient determines
the entire form section, including the other coordinate expression. -/
theorem section_ext_of_coefficient (b : Bool) (U : Opens RiemannSphere)
    (hU : (U : Set RiemannSphere) ⊆ range (RiemannSphere.standardCharts.affineMap b))
    {s t : Section U} (h : coefficient s b = coefficient t b) : s = t := by
  apply section_ext
  intro c z
  by_cases hcb : c = b
  · subst c
    exact congrArg (fun f => f z) h
  · have hbc : b = !c := by
      cases b <;> cases c <;> first | rfl | exact False.elim (hcb rfl)
    subst b
    obtain ⟨w, hw⟩ := hU z.property
    have hz : (z : ℂ) ≠ 0 :=
      ((RiemannSphere.standardCharts.affineMap_cross_eq_iff c z w).mp hw.symm).1
    have hi : (z : ℂ)⁻¹ ∈ coordinateOpen U (!c) :=
      (mem_coordinateOpen_inv c hz).mpr z.property
    have he := congrArg (fun f => f ⟨(z : ℂ)⁻¹, hi⟩) h
    exact (condition_inversion s c z hz z.property hi).trans
      ((congrArg (transition (z : ℂ) * ·) he).trans
        (condition_inversion t c z hz z.property hi).symm)

/-- The coefficient is an actual real continuous-linear covector,
antilinear for the original complex coordinate. -/
def coordinateCovector (a : ℂ) : ℂ →L[ℝ] ℂ :=
  a • Complex.conjCLE.toContinuousLinearMap

@[simp] theorem coordinateCovector_apply (a v : ℂ) :
    coordinateCovector a v = a * starRingEnd ℂ v := rfl

/-- These actual real-linear covectors are complex-antilinear. -/
theorem coordinateCovector_complex_smul (a c v : ℂ) :
    coordinateCovector a (c * v) = starRingEnd ℂ c * coordinateCovector a v := by
  change a * starRingEnd ℂ (c * v) = starRingEnd ℂ c * (a * starRingEnd ℂ v)
  rw [map_mul]
  exact mul_left_comm _ _ _

/-- The required section law is precisely the covector pullback law for
the literal complex derivative of the actual inversion transition. -/
theorem coordinateCovector_transition (z a v : ℂ) :
    coordinateCovector (transition z * a) v =
      coordinateCovector a (deriv (fun w : ℂ => w⁻¹) z * v) := by
  change (transition z * a) * starRingEnd ℂ v =
    a * starRingEnd ℂ (deriv (fun w : ℂ => w⁻¹) z * v)
  rw [map_mul, ← transition_eq_conj_deriv]
  exact (mul_assoc _ _ _).trans (mul_left_comm _ _ _)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms
