import Wikipedia.HopfProblem.DegreeCollapsePrescribedFieldSurgery

/-!
# Fresh separated surgery windows for the exact prescribed flow

After a supported holonomy change, all original critical model germs remain.
Those germs now construct a complete adapted surgery system with smaller
windows, retaining the exact field, the exact complete flow, and each signed
critical chart. Basin geometry is therefore not lost when rebuilding windows.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

open Classical in
theorem exists_adapted_windows_with_prescribed_flow
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f))
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (c : ∀ p : criticalPoints E f, SignedMorseChart (E := E) f p.val)
    (hmodel : ∀ p : criticalPoints E f, ∀ᶠ x in 𝓝 p.val, V x = (c p).descentField x) :
    ∃ S : AdaptedSurgeryWindows E f, S.field = V ∧ S.flow = F ∧ ∀ p, (S.data p).chart = c p := by
  have hfinite := finite_criticalPoints hf hm
  obtain ⟨r, hr, hgap⟩ := exists_separated_value_radii hfinite hinj
  have hex (p : criticalPoints E f) := exists_morseSurgeryData_of_field_germ_lt hf hfinite
    hV F hF hzero hdesc (c p) (fun x hx hfx => hinj hx p.property hfx) (hmodel p) (hr p)
  choose d hd hchart hisolated hgerm using hex
  have hseparated (p q : criticalPoints E f) (hpq : f p < f q) :
      f p + (d p).radius ^ 2 < f q - (d q).radius ^ 2 := by
    have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hd p)) (add_pos (hr p) (d p).radius_pos)]
    have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hd q)) (add_pos (hr q) (d q).radius_pos)]
    linarith [hgap p q hpq]
  exact ⟨{
    finite := hfinite
    distinct := hinj
    data := d
    isolated := hisolated
    separated := hseparated
    field := V
    flow := F
    smooth := hV
    integral := hF
    zero := hzero
    descent := hdesc
    model_germ := hgerm }, rfl, rfl, hchart⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
