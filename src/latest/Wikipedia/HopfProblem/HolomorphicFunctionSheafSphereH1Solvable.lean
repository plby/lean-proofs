import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cousin
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Charts

/-!
# Every actual holomorphic sphere one-cocycle is a coboundary

The analytic Cousin coefficients are assembled into genuine holomorphic
sections on the original members of an arbitrary sphere open cover.
The cocycle equation holds at finite points by the Cousin theorem, and
at infinity by the original sheaf cocycle identity. No Čech-to-derived
comparison is used in this analytic construction.
-/

noncomputable section

open Set TopologicalSpace Metric
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

open HolomorphicCousin

variable {ι : Type} {U : ι → Opens RiemannSphere}

/-- The actual holomorphic primitive section constructed by the Cousin
solver, including its value and holomorphic extension at infinity. -/
def cocyclePrimitive (c : CechOneCocycle sphereSheaf U)
    (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) {R : ℝ} (hR : 0 < R)
    (s : NormalizedCocycleSolution (fun i => (finiteOpen (U i) : Set ℂ))
      (cocycleCoefficient c) i₀ R) (i : ι) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere (U i) :=
  fromFiniteSection (U i) (s.localPart i) (cocycleInfinityValue c i₀ hi₀ i)
    (s.local_analytic i) (by
      intro hi
      obtain ⟨r, hr, F, hF, hzero, heq⟩ :=
        finite_cocycle_solution_infinity c i₀ hi₀ hR s i hi
      exact ⟨r, hr, F, hF, hzero, fun u hu hu₀ _ => heq u hu hu₀⟩)

@[simp] theorem cocyclePrimitive_coe (c : CechOneCocycle sphereSheaf U)
    (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) {R : ℝ} (hR : 0 < R)
    (s : NormalizedCocycleSolution (fun i => (finiteOpen (U i) : Set ℂ))
      (cocycleCoefficient c) i₀ R) (i : ι) (z : ℂ) (hz : (z : RiemannSphere) ∈ U i) :
    cocyclePrimitive c i₀ hi₀ hR s i ⟨(z : RiemannSphere), hz⟩ = s.localPart i z := rfl

@[simp] theorem cocyclePrimitive_infty (c : CechOneCocycle sphereSheaf U)
    (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) {R : ℝ} (hR : 0 < R)
    (s : NormalizedCocycleSolution (fun i => (finiteOpen (U i) : Set ℂ))
      (cocycleCoefficient c) i₀ R) (i : ι) (hi : (∞ : RiemannSphere) ∈ U i) :
    cocyclePrimitive c i₀ hi₀ hR s i ⟨(∞ : RiemannSphere), hi⟩ =
      cocycleInfinityValue c i₀ hi₀ i := rfl

/-- The actual primitive sections satisfy the original cocycle identity
on their entire sphere overlaps, including infinity. -/
theorem cocyclePrimitive_equation (c : CechOneCocycle sphereSheaf U)
    (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) {R : ℝ} (hR : 0 < R)
    (s : NormalizedCocycleSolution (fun i => (finiteOpen (U i) : Set ℂ))
      (cocycleCoefficient c) i₀ R) (i j : ι) :
    res sphereSheaf inf_le_left (cocyclePrimitive c i₀ hi₀ hR s i) -
      res sphereSheaf inf_le_right (cocyclePrimitive c i₀ hi₀ hR s j) = c.value i j := by
  apply ContMDiffMap.ext
  rintro ⟨p, hi, hj⟩
  change cocyclePrimitive c i₀ hi₀ hR s i ⟨p, hi⟩ -
    cocyclePrimitive c i₀ hi₀ hR s j ⟨p, hj⟩ = cocycleSection c i j ⟨p, hi, hj⟩
  induction p using OnePoint.rec with
  | infty =>
    rw [cocyclePrimitive_infty, cocyclePrimitive_infty,
      cocycleInfinityValue_apply c i₀ hi₀ i hi, cocycleInfinityValue_apply c i₀ hi₀ j hj]
    exact sub_eq_iff_eq_add.mpr (cocycleSection_condition c i j i₀ ∞ hi hj hi₀).symm
  | coe z =>
    rw [cocyclePrimitive_coe, cocyclePrimitive_coe]
    exact (s.equation i j z hi hj).trans
      (finiteCoefficient_apply (U i ⊓ U j) (cocycleSection c i j) z ⟨hi, hj⟩)

/-- Every actual additive one-cocycle of holomorphic functions on every
open cover of the analytic Riemann sphere is an actual coboundary. -/
theorem sphere_cechOneVanishing : CechOneVanishing sphereSheaf := by
  intro ι U hU c
  obtain ⟨i₀, hi₀⟩ := hU (∞ : RiemannSphere)
  obtain ⟨R, hR, ⟨s⟩⟩ := exists_finite_cocycle_solution hU c i₀ hi₀
  exact ⟨cocyclePrimitive c i₀ hi₀ hR s, cocyclePrimitive_equation c i₀ hi₀ hR s⟩

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
