import Wikipedia.SmoothSixDPoincare.FlowCollarBoundary
import Wikipedia.SmoothSixDPoincare.SublevelAttachmentDeformation

/-!
# Homeomorphism onto an absorbing critical attachment

Uniform finite residence and strict entry construct all the flow-collar
data. The regular upper level gives the strictly absorbing outer boundary.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] {f : M → ℝ}
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The actual absorbing-region homeomorphism retains its inverse boundary-orbit
formula, as well as the frontier and fixed-point information. -/
theorem exists_absorbingSublevelHomeomorph_with_boundary_orbits
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
    ∃ e : {x : M // f x ≤ b} ≃ₜ A,
      (∀ x, (e x).val ∈ frontier A ↔ x.val ∈ frontier {y : M | f y ≤ b}) ∧
      (∀ x, x.val ∈ A → x.val ∈ frontier {y : M | f y ≤ b} → (e x).val = x.val) ∧
      (∀ y, y.val ∈ frontier A → ∀ t : ℝ, t ≤ 0 →
        F t y.val ∈ frontier {x : M | f x ≤ b} → (e.symm y).val = F t y.val) := by
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
  let d : FlowCollarData F A {x | f x ≤ b} := {
    time := T + 1
    time_pos := by linarith
    closed_outer := isClosed_le hf.continuous continuous_const
    closed_inner := hA
    inner_subset := hupper
    forward_outer := hregion
    forward_inner := hforward
    strict_outer := hstrict
    strict_inner := hentry
    core_inside := by
      intro x hx
      obtain ⟨t, ht, hmem⟩ := hhit x hx
      have hh := hentry _ hmem (T + 1 - t) (by linarith [ht.2])
      rwa [← F.map_add, sub_add_cancel] at hh }
  have : CompactSpace ↥({x : M | f x ≤ b}) :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  exact ⟨d.homeomorph, d.homeomorph_mem_frontier_iff,
    d.homeomorph_fixed_on_common_frontier,
    fun y hy _ ht hfront => d.homeomorph_symm_eq_flow_of_mem_frontier y hy ht hfront⟩

/-- An actual critical attachment is homeomorphic to the whole upper sublevel. -/
theorem exists_absorbingSublevelHomeomorph_with_frontier_and_fixed
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
    ∃ e : {x : M // f x ≤ b} ≃ₜ A,
      (∀ x, (e x).val ∈ frontier A ↔ x.val ∈ frontier {y : M | f y ≤ b}) ∧
      (∀ x, x.val ∈ A → x.val ∈ frontier {y : M | f y ≤ b} → (e x).val = x.val) := by
  obtain ⟨e, hfront, hfixed, -⟩ := exists_absorbingSublevelHomeomorph_with_boundary_orbits
    hf hV hdesc F hcurve hmono hA hlower hupper hcover hforward hentry htop
  exact ⟨e, hfront, hfixed⟩

/-- The boundary correspondence, without retaining the additional fixed-point information. -/
theorem exists_absorbingSublevelHomeomorph_with_frontier
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
    ∃ e : {x : M // f x ≤ b} ≃ₜ A,
      ∀ x, (e x).val ∈ frontier A ↔ x.val ∈ frontier {y : M | f y ≤ b} := by
  obtain ⟨e, he, -⟩ := exists_absorbingSublevelHomeomorph_with_frontier_and_fixed
    hf hV hdesc F hcurve hmono hA hlower hupper hcover hforward hentry htop
  exact ⟨e, he⟩

/-- An actual critical attachment is homeomorphic to the whole upper sublevel. -/
theorem nonempty_absorbingSublevelHomeomorph
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
    Nonempty ({x : M // f x ≤ b} ≃ₜ A) := by
  obtain ⟨e, -⟩ := exists_absorbingSublevelHomeomorph_with_frontier hf hV hdesc F hcurve
    hmono hA hlower hupper hcover hforward hentry htop
  exact ⟨e⟩

end Wikipedia.SmoothSixDPoincare.FlowConstruction
