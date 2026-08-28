import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1ChartsPullback
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Infinity

/-!
# The Cousin solver applied to actual holomorphic sheaf cocycles

The coefficient functions below are obtained from the literal sections
of the holomorphic-function sheaf. Their additive identity is deduced
by evaluating the actual restriction identity of a sheaf cocycle.
The existing arbitrary-cover Cousin theorem then constructs finite
coefficients with a genuine analytic expression at infinity.
-/

noncomputable section

open Set TopologicalSpace Metric
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

open HolomorphicCousin

/-- The actual additive holomorphic-function sheaf on the constructed
analytic sphere. -/
abbrev sphereSheaf := additiveSheaf 𝓘(ℂ) RiemannSphere

variable {ι : Type} {U : ι → Opens RiemannSphere}

/-- The actual cocycle sections, viewed as their bundled holomorphic maps. -/
def cocycleSection (c : CechOneCocycle sphereSheaf U) (i j : ι) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere (U i ⊓ U j) :=
  c.value i j

/-- The actual restriction identity gives the pointwise additive identity. -/
theorem cocycleSection_condition (c : CechOneCocycle sphereSheaf U)
    (i j k : ι) (p : RiemannSphere) (hi : p ∈ U i) (hj : p ∈ U j) (hk : p ∈ U k) :
    cocycleSection c i j ⟨p, hi, hj⟩ + cocycleSection c j k ⟨p, hj, hk⟩ =
      cocycleSection c i k ⟨p, hi, hk⟩ := by
  exact congrArg
    (fun s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere ((U i ⊓ U j) ⊓ U k) =>
      s ⟨p, ⟨hi, hj⟩, hk⟩) (c.condition i j k)

/-- Literal finite affine-coordinate coefficients of the sheaf cocycle. -/
def cocycleCoefficient (c : CechOneCocycle sphereSheaf U) (i j : ι) : ℂ → ℂ :=
  finiteCoefficient (U i ⊓ U j) (cocycleSection c i j)

theorem cocycleCoefficient_analytic (c : CechOneCocycle sphereSheaf U) (i j : ι) :
    AnalyticOnNhd ℂ (cocycleCoefficient c i j)
      ((finiteOpen (U i) : Set ℂ) ∩ finiteOpen (U j)) :=
  finiteCoefficient_analytic (U i ⊓ U j) (cocycleSection c i j)

theorem cocycleCoefficient_condition (c : CechOneCocycle sphereSheaf U)
    (i j k : ι) (z : ℂ) (hi : z ∈ finiteOpen (U i))
    (hj : z ∈ finiteOpen (U j)) (hk : z ∈ finiteOpen (U k)) :
    cocycleCoefficient c i j z + cocycleCoefficient c j k z =
      cocycleCoefficient c i k z := by
  simp only [cocycleCoefficient,
    finiteCoefficient_apply (U i ⊓ U j) (cocycleSection c i j) z ⟨hi, hj⟩,
    finiteCoefficient_apply (U j ⊓ U k) (cocycleSection c j k) z ⟨hj, hk⟩,
    finiteCoefficient_apply (U i ⊓ U k) (cocycleSection c i k) z ⟨hi, hk⟩]
  exact cocycleSection_condition c i j k (z : RiemannSphere) hi hj hk

/-- The actual sheaf cocycle admits a constructed finite-coordinate
Cousin solution, for any chosen sphere patch containing infinity. -/
theorem exists_finite_cocycle_solution (hU : ∀ p : RiemannSphere, ∃ i, p ∈ U i)
    (c : CechOneCocycle sphereSheaf U) (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) :
    ∃ R : ℝ, 0 < R ∧ Nonempty (NormalizedCocycleSolution
      (fun i => (finiteOpen (U i) : Set ℂ)) (cocycleCoefficient c) i₀ R) := by
  obtain ⟨R, hR, htail⟩ := exists_positive_tail_radius (U i₀) hi₀
  exact ⟨R, hR, exists_normalized_holomorphic_cocycle_solution
    (fun i => (finiteOpen (U i)).isOpen) (finiteOpen_cover U hU)
    (cocycleCoefficient_analytic c) (cocycleCoefficient_condition c) i₀ hR htail⟩

/-- The value of the corrected section at infinity on each cover member.
It is determined by the original cocycle and the normalized distinguished
section, whose infinity value is zero. -/
def cocycleInfinityValue (c : CechOneCocycle sphereSheaf U)
    (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) (i : ι) : ℂ := by
  classical
  exact if hi : (∞ : RiemannSphere) ∈ U i then
    cocycleSection c i i₀ ⟨∞, hi, hi₀⟩ else 0

@[simp] theorem cocycleInfinityValue_apply (c : CechOneCocycle sphereSheaf U)
    (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) (i : ι)
    (hi : (∞ : RiemannSphere) ∈ U i) :
    cocycleInfinityValue c i₀ hi₀ i = cocycleSection c i i₀ ⟨∞, hi, hi₀⟩ := by
  classical
  simp only [cocycleInfinityValue, dif_pos hi]

/-- Every constructed finite coefficient extends analytically over
infinity wherever the original cover member contains infinity. -/
theorem finite_cocycle_solution_infinity (c : CechOneCocycle sphereSheaf U)
    (i₀ : ι) (hi₀ : (∞ : RiemannSphere) ∈ U i₀) {R : ℝ} (hR : 0 < R)
    (s : NormalizedCocycleSolution (fun i => (finiteOpen (U i) : Set ℂ))
      (cocycleCoefficient c) i₀ R)
    (i : ι) (hi : (∞ : RiemannSphere) ∈ U i) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (ball 0 r) ∧ F 0 = cocycleInfinityValue c i₀ hi₀ i ∧
      ∀ u ∈ ball (0 : ℂ) r, u ≠ 0 → s.localPart i u⁻¹ = F u := by
  obtain ⟨r, hr, hdisc⟩ := exists_positive_infinity_radius (U i ⊓ U i₀) ⟨hi, hi₀⟩
  let k := infinityCoefficient (U i ⊓ U i₀) (cocycleSection c i i₀)
  have hk : AnalyticOnNhd ℂ k (ball 0 r) :=
    (infinityCoefficient_analytic _ _).mono hdisc
  have hmem : ∀ u ∈ ball (0 : ℂ) r, u ≠ 0 →
      (u⁻¹ : ℂ) ∈ (finiteOpen (U i) : Set ℂ) ∩ finiteOpen (U i₀) := by
    intro u hu hu₀
    have h := hdisc hu
    change RiemannSphere.infinityParametrization u ∈ U i ⊓ U i₀ at h
    rw [RiemannSphere.infinityParametrization_of_ne hu₀] at h
    exact ⟨h.1, h.2⟩
  obtain ⟨t, ht, F, hF, hzero, heq⟩ := infinity_extension_of_overlap hR s i hr k hk
    (fun u hu hu₀ => (hmem u hu hu₀).1)
    (fun u hu hu₀ => (hmem u hu hu₀).2)
    (fun u _ hu₀ => (infinityCoefficient_eq_finiteCoefficient _ _ u hu₀).symm)
  refine ⟨t, ht, F, hF, hzero.trans ?_, heq⟩
  change infinityCoefficient (U i ⊓ U i₀) (cocycleSection c i i₀) 0 = _
  rw [infinityCoefficient_zero (U i ⊓ U i₀) (cocycleSection c i i₀) ⟨hi, hi₀⟩,
    cocycleInfinityValue_apply c i₀ hi₀ i hi]

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
