import Wikipedia.SmoothSixDPoincare.FlowCollarCoordinates
import Wikipedia.SmoothSixDPoincare.SublevelAttachmentDeformation

/-!
# Retaining the constructed absorbing sublevel flow collar

The same finite-residence and strict-entry construction used for the
sublevel homeomorphism is retained as actual collar data. This permits
the smooth boundary-map results to apply to the chosen whole-sublevel
realization, with its original flow and entry-time formulas.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] {f : M → ℝ}
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

omit [T2Space M] in
theorem nonempty_absorbingSublevelFlowCollar
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    {a b : ℝ} {A : Set M} (hA : IsClosed A)
    (hlower : {x | f x ≤ a} ⊆ A) (hupper : A ⊆ {x | f x ≤ b})
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Icc a b → x ∈ interior A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (htop : ∀ x, f x = b → ∀ t : ℝ, 0 < t → f (F t x) < b) :
    Nonempty (FlowCollarData F A {x | f x ≤ b}) := by
  obtain ⟨T, hT, hhit⟩ := exists_uniform_absorbing_entry hf hV hdesc F hcurve hmono hlower hcover
  have hregion : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ b := by
    intro x hx t ht
    have hh : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht
    exact hh.trans hx
  have hstrict : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 < t →
      F t x ∈ interior {x | f x ≤ b} := by
    intro x hx t ht
    change f x ≤ b at hx
    apply interior_maximal (show {x | f x < b} ⊆ {x | f x ≤ b} from
      fun x (hy : f x < b) => (show f x ≤ b from hy.le))
      (isOpen_lt hf.continuous continuous_const)
    rcases lt_or_eq_of_le hx with hlt | heq
    · have hh : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.le
      exact hh.trans_lt hlt
    · exact htop x heq t ht
  refine ⟨{
    time := T + 1
    time_pos := by linarith
    closed_outer := isClosed_le hf.continuous continuous_const
    closed_inner := hA
    inner_subset := hupper
    forward_outer := hregion
    forward_inner := hforward
    strict_outer := hstrict
    strict_inner := hentry
    core_inside := ?_ }⟩
  intro x hx
  obtain ⟨t, ht, hmem⟩ := hhit x hx
  have hh := hentry _ hmem (T + 1 - t) (by linarith [ht.2])
  rwa [← F.map_add, sub_add_cancel] at hh

end Wikipedia.SmoothSixDPoincare.FlowConstruction
