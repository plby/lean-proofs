import Wikipedia.HopfProblem.DegreeCollapseCubicFlowCylinder
import Mathlib.Dynamics.Flow
import Wikipedia.HopfProblem.DegreeCollapseNativeVerticalCylinderFlow

/-!
# A native cubic field chart on the complete regular connecting cylinder

Compose the actual native flow cylinder with the inverse explicit cubic
flow cylinder. Native differentiation proves the exact original cubic
field normal form on the whole chart target. The open axis is included;
extension across the two critical endpoints is deliberately not asserted.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}

/-- An actual native flow cylinder constructs the exact cubic field chart
on the open regular strip, without claiming either critical endpoint. -/
theorem exists_native_regular_cubic_field_chart (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hsource : Φ.source = U ×ˢ univ) (h0 : (0 : Fin m → ℝ) ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (ι : (Fin m → ℝ) → M) (hformula : ∀ p ∈ Φ.source, Φ p = F p.2 (ι p.1)) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.target = Φ.target ∧ Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Ψ.source ∧
      (∀ s, Ψ (s, 0) = F (cubicAxisClock a s) (ι 0)) ∧
      (∀ x ∈ Ψ.target, V x = nativeCubicDescent σ Ψ (-(a ^ 2)) x) ∧
      Ψ.source ⊆ Ioo (-a) a ×ˢ univ ∧
      ∀ p, Ψ (cubicFlowCylinder σ a p) = Φ p := by
  let C := cubicFlowCylinderChart σ ha
  let Ψ := C.symm.trans Φ
  have htarget : Ψ.target = Φ.target := by
    ext x
    change x ∈ Φ.target ∧ Φ.symm x ∈ univ ↔ x ∈ Φ.target
    simp only [mem_univ, and_true]
  have hcompose (p : (Fin m → ℝ) × ℝ) : Ψ (C p) = Φ p := by
    change Φ (C.symm (C p)) = Φ p
    have hh : C.symm (C p) = p := C.left_inv' (mem_univ p)
    exact congrArg Φ hh
  have hopenaxis : Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Ψ.source := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change (s, (0 : Fin m → ℝ)) ∈ C.target ∧ C.symm (s, 0) ∈ Φ.source
    refine ⟨⟨hs, mem_univ _⟩, ?_⟩
    rw [hsource]
    change (fun i => Real.exp (σ i * cubicAxisClock a s) * (0 : Fin m → ℝ) i) ∈ U ∧ _
    simp only [Pi.zero_apply, mul_zero]
    exact ⟨h0, mem_univ _⟩
  refine ⟨Ψ, htarget, hopenaxis, ?_, ?_, fun _ hp => hp.1, hcompose⟩
  · intro s
    change Φ (cubicFlowCylinderInverse σ a (s, 0)) = _
    have hsΦ : cubicFlowCylinderInverse σ a (s, 0) ∈ Φ.source := by
      rw [hsource]
      simp only [cubicFlowCylinderInverse, Pi.zero_apply, mul_zero]
      exact ⟨h0, mem_univ _⟩
    rw [hformula _ hsΦ]
    simp only [cubicFlowCylinderInverse, Pi.zero_apply, mul_zero]
    rfl
  · intro x hx
    have hxΦ : x ∈ Φ.target := htarget ▸ hx
    let p := Φ.symm x
    have hp : p ∈ Φ.source := Φ.map_target' hxΦ
    have hpU : p.1 ∈ U := by rw [hsource] at hp; exact hp.1
    have hpC : C p ∈ Ψ.source := by
      change C p ∈ C.target ∧ C.symm (C p) ∈ Φ.source
      have hh : C.symm (C p) = p := C.left_inv' (mem_univ p)
      exact ⟨C.map_source' (mem_univ p), hh.symm ▸ hp⟩
    let α : ℝ → Model m := fun s => C (p.1, s)
    have hα : HasDerivAt α (cubicDescent σ (-(a ^ 2)) (α p.2)) p.2 :=
      hasDerivAt_cubicFlowCylinder σ a p.1 p.2
    have hd := FlowConstruction.hasMFDerivAt_lift_partialChartCurve Ψ.symm
      (cubicDescent σ (-(a ^ 2))) hα hpC
    have hcurveeq : Ψ.symm.symm ∘ α = fun t => F t (ι p.1) := by
      funext t
      have hpt : (p.1, t) ∈ Φ.source := by rw [hsource]; exact ⟨hpU, mem_univ _⟩
      exact (hcompose (p.1, t)).trans (hformula (p.1, t) hpt)
    rw [hcurveeq] at hd
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => F t (ι p.1)) p.2
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (FlowConstruction.partialChartField Ψ.symm (cubicDescent σ (-(a ^ 2))) (Ψ (C p)))) at hd
    rw [hcompose p, hformula p hp] at hd
    have hh := (hF (ι p.1) p.2).mfderiv.symm.trans hd.mfderiv
    have hv := congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (F p.2 (ι p.1)) => L 1) hh
    simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at hv
    have hpx : F p.2 (ι p.1) = x := (hformula p hp).symm.trans (Φ.right_inv' hxΦ)
    rw [hpx] at hv
    exact hv

variable [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]

/-- The actual native vertical field supplies its own full-source flow
formula, then constructs the genuine regular cubic chart and strip domain. -/
theorem exists_regular_cubic_chart_of_native_vertical_field (σ : Fin m → ℝ)
    {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hsource : Φ.source = U ×ˢ univ) (h0 : (0 : Fin m → ℝ) ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm
      (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.target = Φ.target ∧ Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Ψ.source ∧
      (∀ s, Ψ (s, 0) = F (cubicAxisClock a s) (Φ (0, 0))) ∧
      (∀ x ∈ Ψ.target, V x = nativeCubicDescent σ Ψ (-(a ^ 2)) x) ∧
      Ψ.source ⊆ Ioo (-a) a ×ˢ univ ∧
      ∀ p, Ψ (cubicFlowCylinder σ a p) = Φ p := by
  apply exists_native_regular_cubic_field_chart σ ha Φ hsource h0 V F hF (fun z => Φ (z, 0))
  intro p hp
  have hz : p.1 ∈ U := by rw [hsource] at hp; exact hp.1
  simpa only [zero_add] using
    (FlowSuspension.native_vertical_cylinder_flow Φ hsource hV hmodel F hF p.1 hz 0 p.2).symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
