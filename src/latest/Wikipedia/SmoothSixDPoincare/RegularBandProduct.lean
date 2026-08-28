import Wikipedia.SmoothSixDPoincare.RegularBandHeight

/-!
# Product structure of a critical-point-free band

The homeomorphism is constructed using the genuine flow of the preceding
modules. No product, collar, or trivialization is assumed. Its second
coordinate is the original function value.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

section Topological

variable {M : Type*} [TopologicalSpace M]

/-- A height-translating flow trivializes the closed band, including its endpoints. -/
def regularBandHomeomorphOfFlow {f : M → ℝ} (hf : Continuous f) {a b : ℝ}
    (hab : a ≤ b) (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Icc a b → f x + t ∈ Icc a b →
      f (F t x) = f x + t) :
    {x : M // f x ∈ Icc a b} ≃ₜ ({x : M // f x = a} × Icc a b) := by
  have hdown (x : {x : M // f x ∈ Icc a b}) :
      f (F (a - f x.1) x.1) = a := by
    have ht : f x.1 + (a - f x.1) ∈ Icc a b := by
      simpa only [add_sub_cancel] using (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
    simpa only [add_sub_cancel] using hF x.1 (a - f x.1) x.2 ht
  have hup (y : {x : M // f x = a} × Icc a b) :
      f (F (y.2.1 - a) y.1.1) = y.2.1 := by
    have hstart : f y.1.1 ∈ Icc a b := by rw [y.1.2]; exact ⟨le_rfl, hab⟩
    have hend : f y.1.1 + (y.2.1 - a) ∈ Icc a b := by
      simpa only [y.1.2, add_sub_cancel] using y.2.2
    simpa only [y.1.2, add_sub_cancel] using hF y.1.1 (y.2.1 - a) hstart hend
  refine
    { toFun := fun x => (⟨F (a - f x.1) x.1, hdown x⟩, ⟨f x.1, x.2⟩)
      invFun := fun y => ⟨F (y.2.1 - a) y.1.1, by rw [hup y]; exact y.2.2⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro x
    apply Subtype.ext
    change F (f x.1 - a) (F (a - f x.1) x.1) = x.1
    rw [← F.map_add, show f x.1 - a + (a - f x.1) = 0 by ring, F.map_zero_apply]
  · intro y
    apply Prod.ext
    · apply Subtype.ext
      change F (a - f (F (y.2.1 - a) y.1.1)) (F (y.2.1 - a) y.1.1) = y.1.1
      rw [hup y, ← F.map_add, show a - y.2.1 + (y.2.1 - a) = 0 by ring,
        F.map_zero_apply]
    · apply Subtype.ext
      exact hup y
  · exact ((F.continuous (continuous_const.sub (hf.comp continuous_subtype_val))
      continuous_subtype_val).subtype_mk _).prodMk
        ((hf.comp continuous_subtype_val).subtype_mk _)
  · exact (F.continuous
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const)
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _

end Topological

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- A closed band without native critical points is a product with its bottom level. -/
theorem nonempty_regularBandHomeomorph {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    Nonempty ({x : M // f x ∈ Icc a b} ≃ₜ ({x : M // f x = a} × Icc a b)) := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  exact ⟨regularBandHomeomorphOfFlow hf.continuous hab F hF⟩

end Wikipedia.SmoothSixDPoincare.FlowConstruction
