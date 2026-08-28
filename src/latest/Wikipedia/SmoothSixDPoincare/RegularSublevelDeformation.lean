import Wikipedia.SmoothSixDPoincare.RegularBandProduct
import Mathlib.Topology.Homotopy.Equiv

/-!
# Deformation of sublevels across a regular band

The flow gives a genuine strong deformation retraction of the upper sublevel
onto the lower one. The homotopy is stationary below the lower level, and
the resulting native homotopy equivalence has the inclusion as its forward map.
-/

noncomputable section

open Set Manifold ContinuousMap
open scoped ContDiff Topology unitInterval

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

section Topological

variable {M : Type*} [TopologicalSpace M] {f : M → ℝ} {a b : ℝ}

/-- The canonical inclusion of one closed sublevel into a larger one. -/
def sublevelInclusion (hab : a ≤ b) : C({x : M // f x ≤ a}, {x : M // f x ≤ b}) where
  toFun x := ⟨x.1, x.2.trans hab⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

variable (F : Flow ℝ M)
  (hF : ∀ x t, f x ∈ Icc a b → f x + t ∈ Icc a b →
    f (F t x) = f x + t)

include hF

/-- The clipped downward flow has the expected height throughout the deformation. -/
theorem sublevel_deformation_height {x : M} (hx : f x ≤ b) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    f (F (u * min 0 (a - f x)) x) = f x + u * min 0 (a - f x) := by
  by_cases hxa : f x ≤ a
  · rw [min_eq_left (sub_nonneg.mpr hxa), mul_zero, F.map_zero_apply, add_zero]
  · have hax : a ≤ f x := (lt_of_not_ge hxa).le
    rw [min_eq_right (sub_nonpos.mpr hax)]
    apply hF x _ ⟨hax, hx⟩
    have htime : u * (a - f x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hu.1 (sub_nonpos.mpr hax)
    have hprod : 0 ≤ (1 - u) * (f x - a) :=
      mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hax)
    exact ⟨by nlinarith, by linarith⟩

/-- Every intermediate map remains in the original upper sublevel. -/
theorem sublevel_deformation_mem {x : M} (hx : f x ≤ b) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : f (F (u * min 0 (a - f x)) x) ≤ b := by
  rw [sublevel_deformation_height F hF hx hu]
  exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hu.1 (min_le_left _ _))).trans hx

/-- The endpoint of the downward deformation is in the lower sublevel. -/
theorem sublevel_retraction_mem {x : M} (hx : f x ≤ b) :
    f (F (min 0 (a - f x)) x) ≤ a := by
  have h := sublevel_deformation_height F hF hx (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  simp only [one_mul] at h
  rw [h]
  have hm := min_le_right (0 : ℝ) (a - f x)
  linarith

/-- The actual retraction of the upper sublevel onto the lower one. -/
def sublevelRetraction (hf : Continuous f) : C({x : M // f x ≤ b}, {x : M // f x ≤ a}) where
  toFun x := ⟨F (min 0 (a - f x.1)) x.1, sublevel_retraction_mem F hF x.2⟩
  continuous_toFun := (F.continuous
    (continuous_const.min (continuous_const.sub (hf.comp continuous_subtype_val)))
    continuous_subtype_val).subtype_mk _

/-- The retraction fixes every point of the lower sublevel. -/
theorem sublevelRetraction_inclusion (hf : Continuous f) (hab : a ≤ b)
    (x : {x : M // f x ≤ a}) :
    sublevelRetraction F hF hf (sublevelInclusion hab x) = x := by
  apply Subtype.ext
  change F (min 0 (a - f x.1)) x.1 = x.1
  rw [min_eq_left (sub_nonneg.mpr x.2), F.map_zero_apply]

/-- The flow deformation is fixed on the whole lower sublevel, at every time. -/
def sublevelDeformation (hf : Continuous f) (hab : a ≤ b) :
    (ContinuousMap.id {x : M // f x ≤ b}).HomotopyRel
      ((sublevelInclusion hab).comp (sublevelRetraction F hF hf))
      {x | f x.1 ≤ a} where
  toFun p := ⟨F (p.1.1 * min 0 (a - f p.2.1)) p.2.1,
    sublevel_deformation_mem F hF p.2.2 p.1.2⟩
  continuous_toFun := (F.continuous
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.min (continuous_const.sub
        (hf.comp (continuous_subtype_val.comp continuous_snd)))))
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    change F ((0 : ℝ) * min 0 (a - f x.1)) x.1 = x.1
    rw [zero_mul, F.map_zero_apply]
  map_one_left x := by
    apply Subtype.ext
    change F ((1 : ℝ) * min 0 (a - f x.1)) x.1 = F (min 0 (a - f x.1)) x.1
    rw [one_mul]
  prop' u x hx := by
    apply Subtype.ext
    change F (u.1 * min 0 (a - f x.1)) x.1 = x.1
    rw [min_eq_left (sub_nonneg.mpr hx), mul_zero, F.map_zero_apply]

/-- The inclusion of regular sublevels is a native homotopy equivalence. -/
def regularSublevelHomotopyEquivOfFlow (hf : Continuous f) (hab : a ≤ b) :
    {x : M // f x ≤ a} ≃ₕ {x : M // f x ≤ b} where
  toFun := sublevelInclusion hab
  invFun := sublevelRetraction F hF hf
  left_inv := by
    have heq : (sublevelRetraction F hF hf).comp (sublevelInclusion hab) =
        ContinuousMap.id {x : M // f x ≤ a} := by
      apply ContinuousMap.ext
      intro x
      exact sublevelRetraction_inclusion F hF hf hab x
    rw [heq]
  right_inv := ⟨(sublevelDeformation F hF hf hab).toHomotopy.symm⟩

end Topological

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- Without critical values in the intervening closed band, the sublevel inclusion is a homotopy
equivalence; the inverse and homotopies are constructed from the original smooth function. -/
theorem exists_regularSublevelHomotopyEquiv {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ e : {x : M // f x ≤ a} ≃ₕ {x : M // f x ≤ b},
      ∀ x, (e x).1 = x.1 := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  exact ⟨regularSublevelHomotopyEquivOfFlow F hF hf.continuous hab, fun _ => rfl⟩

end Wikipedia.SmoothSixDPoincare.FlowConstruction
