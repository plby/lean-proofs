import Wikipedia.HopfProblem.DegreeCollapseNativeFlowTimeDiffeomorph
import Wikipedia.HopfProblem.DegreeCollapseCubicDescent

/-!
# Shifting native field charts by actual flow time

Postcomposing a field chart with a fixed time of the original complete
flow retains its coordinate field, with exactly the same source. This
allows the constant part of an endpoint's time origin to be changed
without changing the native vector field or the model parameter.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Native pullback by any fixed flow time retains the original field. -/
theorem mpullback_flow_time (F : Flow ℝ M)
    (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) (x : M) :
    VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) V x = V x := by
  let D := nativeFlowTimeDiffeomorph F hs t
  let e := D.toPartialDiffeomorph
  have hdiff : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨e.mdifferentiableOn (by simp), e.symm.mdifferentiableOn (by simp)⟩
  have hi : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F t) x).IsInvertible :=
    ⟨hdiff.mfderiv (mem_univ x), rfl⟩
  rw [VectorField.mpullback_apply, ← mfderiv_flow_time_field F hs hF t x]
  exact hi.inverse_apply_self (V x)

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The actual postcomposed chart represents the same model field on its entire target. -/
theorem partialChartField_flow_shift
    (Φ : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, E) B M ∞)
    (F : Flow ℝ M) (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (W : B → B)
    (hmodel : ∀ x ∈ Φ.target, V x = FlowConstruction.partialChartField Φ.symm W x)
    (t : ℝ) {x : M}
    (hx : x ∈ (Φ.trans (nativeFlowTimeDiffeomorph F hs t).toPartialDiffeomorph).target) :
    V x = FlowConstruction.partialChartField
      (Φ.trans (nativeFlowTimeDiffeomorph F hs t).toPartialDiffeomorph).symm W x := by
  have hxΦ : F (-t) x ∈ Φ.target := hx.2
  have hdiff : Φ.symm.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, B) :=
    ⟨Φ.symm.mdifferentiableOn (by simp), Φ.mdifferentiableOn (by simp)⟩
  have hinv : (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, B) Φ.symm univ (F (-t) x)).IsInvertible := by
    rw [mfderivWithin_univ]
    exact ⟨hdiff.mfderiv hxΦ, rfl⟩
  have hh := VectorField.mpullbackWithin_comp_of_left
    (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, B))
    (f := F (-t)) (g := (Φ.symm : M → B))
    (V := fun y => (NormedSpace.fromTangentSpace y).symm (W y))
    (s := univ) (t := univ)
    ((hs (-t)).mdifferentiableAt (by simp)).mdifferentiableWithinAt
    (mapsTo_univ _ _) (uniqueMDiffWithinAt_univ 𝓘(ℝ, E)) hinv
  simp only [VectorField.mpullbackWithin_univ] at hh
  change V x = VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, B) (Φ.symm ∘ F (-t))
    (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) x
  rw [hh, VectorField.mpullback_apply]
  change V x = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F (-t)) x).inverse
    (FlowConstruction.partialChartField Φ.symm W (F (-t) x))
  rw [← hmodel _ hxΦ]
  exact (mpullback_flow_time F hs hF (-t) x).symm

/-- The flow-shifted chart has the same actual model domain. -/
theorem flow_shifted_chart_source
    (Φ : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, E) B M ∞)
    (F : Flow ℝ M) (hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t)) (t : ℝ) :
    (Φ.trans (nativeFlowTimeDiffeomorph F hs t).toPartialDiffeomorph).source = Φ.source := by
  ext p
  change p ∈ Φ.source ∧ Φ p ∈ univ ↔ p ∈ Φ.source
  simp

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
