import Wikipedia.SmoothSixDPoincare.MorseSurgeryWindows
import Wikipedia.SmoothSixDPoincare.SmoothMorseSurgeryExistence

/-!
# The finite native surgery system with compatible smooth exterior data

Each critical point receives a radius-controlled surgery whose recorded
whole-sublevel realization has both exteriors smooth. The original finite
value-window construction retains these same records, so separation,
critical isolation, regular-band bridges, and exterior smoothness hold
simultaneously throughout one actual finite surgery system.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}

def SurgeryWindows.HasSmoothExteriors (S : SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) : Prop :=
  ∀ p : criticalPoints E f, (S.data p).HasSmoothExterior hf

end Wikipedia.SmoothSixDPoincare.ManifoldMorse

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_surgeryWindows_with_smoothExteriors
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) :
    ∃ S : SurgeryWindows E f, S.HasSmoothExteriors hf := by
  classical
  obtain ⟨r, hr, hgap⟩ := exists_separated_value_radii (finite_criticalPoints hf hm) hinj
  have hex : ∀ p : criticalPoints E f, ∃ d : MorseSurgeryData E f p.val, d.radius < r p ∧
      (∀ x ∈ criticalPoints E f,
        f x ∈ Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p.val) ∧
      d.HasSmoothExterior hf := by
    intro p
    exact exists_morseSurgeryData_smoothExterior_lt hf hm p.property
      (fun x hx hfx => hinj hx p.property hfx) (hr p)
  choose d hd hisolated hsmooth using hex
  refine ⟨{
    finite := finite_criticalPoints hf hm
    distinct := hinj
    data := d
    isolated := hisolated
    separated := ?_ }, hsmooth⟩
  intro p q hpq
  have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
    have h := mul_pos (sub_pos.mpr (hd p)) (add_pos (hr p) (d p).radius_pos)
    nlinarith
  have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
    have h := mul_pos (sub_pos.mpr (hd q)) (add_pos (hr q) (d q).radius_pos)
    nlinarith
  linarith [hgap p q hpq]

variable (E M) in
theorem exists_morse_function_with_smoothSurgeryWindows :
    ∃ (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f),
      IsMorse E f ∧ ∃ S : SurgeryWindows E f, S.HasSmoothExteriors hf := by
  obtain ⟨f, hf, hm, _, hinj⟩ := exists_morse_function_with_distinct_critical_values E M
  exact ⟨f, hf, hm, exists_surgeryWindows_with_smoothExteriors hf hm hinj⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
