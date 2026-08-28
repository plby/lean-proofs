import Wikipedia.SmoothSixDPoincare.RegularBandProduct
import Wikipedia.SmoothSixDPoincare.Hemisphere
import Mathlib.Topology.Homotopy.Basic

/-! # Transporting level topology through a genuine critical-point-free flow band -/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

section Topological

variable {M : Type*} [TopologicalSpace M]

/-- Fixed-time maps of the actual translating flow identify the two endpoint levels. -/
def regularLevelHomeomorphOfFlow {f : M → ℝ} {a b : ℝ} (hab : a ≤ b) (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Icc a b → f x + t ∈ Icc a b → f (F t x) = f x + t) :
    {x : M // f x = a} ≃ₜ {x : M // f x = b} := by
  have hup (x : {x : M // f x = a}) : f (F (b - a) x) = b := by
    have hs : f x ∈ Icc a b := by rw [x.property]; exact ⟨le_rfl, hab⟩
    have ht : f x + (b - a) ∈ Icc a b := by
      rw [x.property, add_sub_cancel]
      exact ⟨hab, le_rfl⟩
    simpa only [x.property, add_sub_cancel] using hF x (b - a) hs ht
  have hdown (y : {x : M // f x = b}) : f (F (a - b) y) = a := by
    have hs : f y ∈ Icc a b := by rw [y.property]; exact ⟨hab, le_rfl⟩
    have ht : f y + (a - b) ∈ Icc a b := by
      rw [y.property, add_sub_cancel]
      exact ⟨le_rfl, hab⟩
    simpa only [y.property, add_sub_cancel] using hF y (a - b) hs ht
  refine
    { toFun := fun x => ⟨F (b - a) x, hup x⟩
      invFun := fun y => ⟨F (a - b) y, hdown y⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := (F.continuous continuous_const continuous_subtype_val).subtype_mk _
      continuous_invFun := (F.continuous continuous_const continuous_subtype_val).subtype_mk _ }
  · intro x
    apply Subtype.ext
    change F (a - b) (F (b - a) x) = x
    rw [← F.map_add, show a - b + (b - a) = 0 by ring, F.map_zero_apply]
  · intro y
    apply Subtype.ext
    change F (b - a) (F (a - b) y) = y
    rw [← F.map_add, show b - a + (a - b) = 0 by ring, F.map_zero_apply]

end Topological

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem nonempty_regularLevelHomeomorph {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    Nonempty ({x : M // f x = a} ≃ₜ {x : M // f x = b}) := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  exact ⟨regularLevelHomeomorphOfFlow hab F hF⟩

/-- Circle contractions propagate between actual levels when no critical value is crossed. -/
theorem circle_nullhomotopies_regular_level {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f)
    (hnull : ∀ g : C(Hemisphere.Sphere 1, {x : M // f x = a}),
      ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, {x : M // f x = b}),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  obtain ⟨e⟩ := nonempty_regularLevelHomeomorph hf hab hband
  let forward : C({x : M // f x = a}, {x : M // f x = b}) := ⟨e, e.continuous⟩
  let backward : C({x : M // f x = b}, {x : M // f x = a}) := ⟨e.symm, e.symm.continuous⟩
  intro g
  obtain ⟨q, hq⟩ := hnull (backward.comp g)
  have heq : forward.comp (backward.comp g) = g := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (g x)
  have hh : (forward.comp (backward.comp g)).Homotopic (ContinuousMap.const _ (e q)) :=
    (Homotopic.refl forward).comp hq
  exact ⟨e q, heq ▸ hh⟩

end Wikipedia.SmoothSixDPoincare.FlowConstruction
