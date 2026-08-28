import Wikipedia.HopfProblem.DegreeCollapseCubicModelOrbit
import Wikipedia.HopfProblem.DegreeCollapseCubicAxisFlow
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-!
# The complete native cubic-axis orbit

Native ODE uniqueness identifies the explicit model trajectory with the
given original flow. Its full range is the open chart axis and its limits
are the two actual native critical endpoints.
-/

noncomputable section

open Set Function Manifold Filter
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ} {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- A genuine cubic field chart determines the whole original orbit, with no connection input. -/
theorem native_cubic_axis_flow (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) :
    F t (Φ (0, 0)) = Φ (cubicModelOrbit a t) := by
  have hmem (s : ℝ) : cubicModelOrbit a s ∈ Φ.source := by
    have hs := cubicAxisParameter_mem ha s
    exact haxis ⟨⟨hs.1.le, hs.2.le⟩, rfl⟩
  have hΓ : IsMIntegralCurve (Φ ∘ cubicModelOrbit a) V := by
    intro s
    have hd := FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm
      (cubicDescent σ (-(a ^ 2))) (hasDerivAt_cubicModelOrbit σ a s) (hmem s)
    have he := hmodel (Φ (cubicModelOrbit a s)) (Φ.map_source' (hmem s))
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ ∘ cubicModelOrbit a) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (nativeCubicDescent σ Φ (-(a ^ 2)) (Φ (cubicModelOrbit a s)))) at hd
    rw [← he] at hd
    exact hd
  have hinit : F 0 (Φ (0, 0)) = (Φ ∘ cubicModelOrbit a) 0 := by
    simp only [F.map_zero_apply, comp_apply, cubicModelOrbit_zero]
    rfl
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV
    (hcurve (Φ (0, 0))) hΓ hinit
  exact congrFun heq t

/-- The native cubic orbit has the full open axis as its range and the actual chart endpoints. -/
theorem native_cubic_axis_orbit (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    range (fun t : ℝ => F t (Φ (0, 0))) = Φ '' (Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)}) ∧
      Tendsto (fun t : ℝ => F t (Φ (0, 0))) atTop (𝓝 (Φ (a, 0))) ∧
      Tendsto (fun t : ℝ => F t (Φ (0, 0))) atBot (𝓝 (Φ (-a, 0))) := by
  have heq : (fun t : ℝ => F t (Φ (0, 0))) = Φ ∘ cubicModelOrbit a :=
    funext (native_cubic_axis_flow σ ha Φ haxis hV hmodel F hcurve)
  have hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source :=
    haxis ⟨⟨by linarith, le_rfl⟩, rfl⟩
  have hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source :=
    haxis ⟨⟨le_rfl, by linarith⟩, rfl⟩
  rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · rw [range_comp, range_cubicModelOrbit ha]
  · exact (Φ.mdifferentiableAt (by simp) hp).continuousAt.tendsto.comp
      (tendsto_cubicModelOrbit_atTop ha)
  · exact (Φ.mdifferentiableAt (by simp) hq).continuousAt.tendsto.comp
      (tendsto_cubicModelOrbit_atBot ha)

/-- Closing the actual cubic orbit adds precisely the two actual axis endpoints. -/
theorem native_cubic_closed_axis (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    Φ '' (Icc (-a) a ×ˢ {(0 : Fin m → ℝ)}) =
      insert (Φ (a, 0)) (insert (Φ (-a, 0)) (range (fun t : ℝ => F t (Φ (0, 0))))) := by
  rw [(native_cubic_axis_orbit σ ha Φ haxis hV hmodel F hcurve).1]
  ext x
  constructor
  · rintro ⟨⟨s, z⟩, ⟨hs, hz⟩, rfl⟩
    have hz0 : z = 0 := hz
    subst z
    by_cases hsright : s = a
    · exact Or.inl (congrArg (fun r => Φ (r, 0)) hsright)
    by_cases hsleft : s = -a
    · exact Or.inr (Or.inl (congrArg (fun r => Φ (r, 0)) hsleft))
    · exact Or.inr (Or.inr ⟨(s, 0),
        ⟨⟨lt_of_le_of_ne hs.1 (Ne.symm hsleft), lt_of_le_of_ne hs.2 hsright⟩, rfl⟩, rfl⟩)
  · rintro (hx | hx | hx)
    · exact ⟨(a, 0), ⟨⟨by linarith, le_rfl⟩, rfl⟩, hx.symm⟩
    · exact ⟨(-a, 0), ⟨⟨le_rfl, by linarith⟩, rfl⟩, hx.symm⟩
    · obtain ⟨⟨s, z⟩, ⟨hs, hz⟩, he⟩ := hx
      exact ⟨(s, z), ⟨⟨hs.1.le, hs.2.le⟩, hz⟩, he⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
