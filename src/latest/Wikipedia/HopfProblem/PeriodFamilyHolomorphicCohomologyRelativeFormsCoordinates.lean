import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothCoordinates

/-!
# Original inverse period coordinates in the full complex covering chart

These functions are the actual inverse real period coordinates, embedded in
`ℂ`, on the unchanged covering model `ℂ × ComplexPlane₂`. Their smoothness and
the two coordinate equations hold on the full preimage of the original open
base. The extensions outside that open set are used only for ambient calculus.
-/

noncomputable section

open TopologicalSpace Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- A marked inverse real coordinate, viewed as an actual complex-valued
function on the original full covering model. -/
def coordinate (j : Fin 4) (q : ℂ × ComplexPlane₂) : ℂ :=
  (Smooth.inversePeriodCoordinates P q j : ℂ)

@[simp] theorem coordinate_apply (j : Fin 4) (b : U) (z : ComplexPlane₂) :
    coordinate P j ((b : ℂ), z) = ((P.periodEquiv b).symm z j : ℂ) := by
  simp only [coordinate, Smooth.inversePeriodCoordinates_apply]

/-- Joint real smoothness includes the base direction, not only the fibre. -/
theorem coordinate_contDiffOn (j : Fin 4) :
    ContDiffOn ℝ ∞ (coordinate P j) (Smooth.baseProductDomain U ComplexPlane₂) :=
  (Complex.ofRealCLM.comp
    (ContinuousLinearMap.proj j : RealPlane₄ →L[ℝ] ℝ)).contDiff.comp_contDiffOn
    (Smooth.inversePeriodCoordinates_contDiffOn P)

theorem coordinate_differentiableAt (j : Fin 4) (q : ℂ × ComplexPlane₂)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    DifferentiableAt ℝ (coordinate P j) q :=
  ((coordinate_contDiffOn P j).contDiffAt
    ((Smooth.baseProductDomain_isOpen U ComplexPlane₂).mem_nhds hq)).differentiableAt
      (by simp)

/-- Holomorphy of the original mixed period entry in the full covering chart. -/
theorem mu_differentiableAt (q : ℂ × ComplexPlane₂)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    DifferentiableAt ℂ (fun w : ℂ × ComplexPlane₂ => Smooth.muValue P w.1) q := by
  exact (((Smooth.muValue_contDiffOn_complex P).contDiffAt
    (U.isOpen.mem_nhds hq)).differentiableAt (by simp)).comp q differentiableAt_fst

/-- Holomorphy of the original first period entry in the full covering chart. -/
theorem tau_differentiableAt (q : ℂ × ComplexPlane₂)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    DifferentiableAt ℂ (fun w : ℂ × ComplexPlane₂ => Smooth.tauValue P w.1) q := by
  exact (((Smooth.tauValue_contDiffOn_complex P).contDiffAt
    (U.isOpen.mem_nhds hq)).differentiableAt (by simp)).comp q differentiableAt_fst

/-- Holomorphy of the original remaining period entry in the full covering chart. -/
theorem beta_differentiableAt (q : ℂ × ComplexPlane₂)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    DifferentiableAt ℂ (fun w : ℂ × ComplexPlane₂ => Smooth.betaValue P w.1) q := by
  exact (((Smooth.betaValue_contDiffOn_complex P).contDiffAt
    (U.isOpen.mem_nhds hq)).differentiableAt (by simp)).comp q differentiableAt_fst

/-- The first literal complex period equation in the original covering chart. -/
theorem reconstruct_zero (b : U) (z : ComplexPlane₂) :
    z 0 = 6 * (P.point b).val.μ * coordinate P 0 ((b : ℂ), z) +
      (P.point b).val.τ * coordinate P 1 ((b : ℂ), z) +
      coordinate P 2 ((b : ℂ), z) := by
  have h := congrFun (P.periodEquiv_coordinates b ((P.periodEquiv b).symm z)) 0
  simpa only [LinearEquiv.apply_symm_apply, Matrix.cons_val_zero, coordinate_apply] using h

/-- The second literal complex period equation in the original covering chart. -/
theorem reconstruct_one (b : U) (z : ComplexPlane₂) :
    z 1 = (P.point b).val.β * coordinate P 0 ((b : ℂ), z) +
      (P.point b).val.μ * coordinate P 1 ((b : ℂ), z) +
      coordinate P 3 ((b : ℂ), z) := by
  have h := congrFun (P.periodEquiv_coordinates b ((P.periodEquiv b).symm z)) 1
  simpa only [LinearEquiv.apply_symm_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
    coordinate_apply] using h

/-- Solving the original first complex equation for the third real coordinate. -/
theorem coordinate_two_eq (q : ℂ × ComplexPlane₂)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    coordinate P 2 q = q.2 0 -
      (6 * Smooth.muValue P q.1 * coordinate P 0 q +
        Smooth.tauValue P q.1 * coordinate P 1 q) := by
  have h := reconstruct_zero P ⟨q.1, hq⟩ q.2
  have hm := Smooth.muValue_apply P ⟨q.1, hq⟩
  have ht := Smooth.tauValue_apply P ⟨q.1, hq⟩
  change Smooth.muValue P q.1 = _ at hm
  change Smooth.tauValue P q.1 = _ at ht
  rw [hm, ht]
  linear_combination -h

/-- Solving the original second complex equation for the fourth real coordinate. -/
theorem coordinate_three_eq (q : ℂ × ComplexPlane₂)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    coordinate P 3 q = q.2 1 -
      (Smooth.betaValue P q.1 * coordinate P 0 q +
        Smooth.muValue P q.1 * coordinate P 1 q) := by
  have h := reconstruct_one P ⟨q.1, hq⟩ q.2
  have hb := Smooth.betaValue_apply P ⟨q.1, hq⟩
  have hm := Smooth.muValue_apply P ⟨q.1, hq⟩
  change Smooth.betaValue P q.1 = _ at hb
  change Smooth.muValue P q.1 = _ at hm
  rw [hb, hm]
  linear_combination -h

/-- The first coordinate identity holds on an actual neighborhood, so all
ambient derivatives may be computed from it. -/
theorem coordinate_two_eventuallyEq (q : ℂ × ComplexPlane₂)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    coordinate P 2 =ᶠ[𝓝 q] fun w => w.2 0 -
      (6 * Smooth.muValue P w.1 * coordinate P 0 w +
        Smooth.tauValue P w.1 * coordinate P 1 w) := by
  filter_upwards [(Smooth.baseProductDomain_isOpen U ComplexPlane₂).mem_nhds hq] with w hw
  exact coordinate_two_eq P w hw

/-- The second coordinate identity likewise holds on a genuine neighborhood. -/
theorem coordinate_three_eventuallyEq (q : ℂ × ComplexPlane₂)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    coordinate P 3 =ᶠ[𝓝 q] fun w => w.2 1 -
      (Smooth.betaValue P w.1 * coordinate P 0 w +
        Smooth.muValue P w.1 * coordinate P 1 w) := by
  filter_upwards [(Smooth.baseProductDomain_isOpen U ComplexPlane₂).mem_nhds hq] with w hw
  exact coordinate_three_eq P w hw

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms
