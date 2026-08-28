import Wikipedia.HopfProblem.DegreeCollapseTwoPunctureHomology

/-!
# Explicit affine sphere homotopies in a one-point complement

Positive radius changes preserve the centered sphere class. Moving the
center to a puncture inside the sphere also preserves its class. A sphere
whose entire ball misses the puncture contracts there. These are actual
continuous homotopies of the original affine sphere parametrizations.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.PassageHomology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affine_sphere_ne_of_norm_ne {p c : E} {r : ℝ} (hr : 0 ≤ r)
    (h : ‖c - p‖ ≠ r) (u : sphere (0 : E) 1) : c + r • u.val ≠ p := by
  intro he
  apply h
  have hvalue : r • u.val = p - c := by rw [← he, add_sub_cancel_left]
  calc
    ‖c - p‖ = ‖p - c‖ := norm_sub_rev c p
    _ = ‖r • u.val‖ := congrArg norm hvalue.symm
    _ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
        mem_sphere_zero_iff_norm.mp u.property, mul_one]

def puncturedSphereMap (p c : E) (r : ℝ)
    (h : ∀ u : sphere (0 : E) 1, c + r • u.val ≠ p) :
    C(sphere (0 : E) 1, ({p}ᶜ : Set E)) where
  toFun u := ⟨c + r • u.val, h u⟩
  continuous_toFun := (continuous_const.add
    (continuous_const.smul continuous_subtype_val)).subtype_mk _

theorem puncturedSphereMap_homotopic_of_family
    (p : E) (c : C(unitInterval, E)) (r : C(unitInterval, ℝ))
    {c₀ c₁ : E} {r₀ r₁ : ℝ}
    (hc₀ : c 0 = c₀) (hc₁ : c 1 = c₁) (hr₀ : r 0 = r₀) (hr₁ : r 1 = r₁)
    (h : ∀ t, ∀ u : sphere (0 : E) 1, c t + r t • u.val ≠ p)
    (h₀ : ∀ u : sphere (0 : E) 1, c₀ + r₀ • u.val ≠ p)
    (h₁ : ∀ u : sphere (0 : E) 1, c₁ + r₁ • u.val ≠ p) :
    (puncturedSphereMap p c₀ r₀ h₀).Homotopic (puncturedSphereMap p c₁ r₁ h₁) := by
  refine ⟨{
    toFun := fun z => ⟨c z.1 + r z.1 • z.2.val, h z.1 z.2⟩
    continuous_toFun := ((c.continuous.comp continuous_fst).add
      ((r.continuous.comp continuous_fst).smul
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro u
    apply Subtype.ext
    change c 0 + r 0 • u.val = c₀ + r₀ • u.val
    rw [hc₀, hr₀]
  · intro u
    apply Subtype.ext
    change c 1 + r 1 • u.val = c₁ + r₁ • u.val
    rw [hc₁, hr₁]

theorem puncturedSphereMap_radius_homotopic (p : E) {r₀ r₁ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (h₀ : ∀ u : sphere (0 : E) 1, p + r₀ • u.val ≠ p)
    (h₁ : ∀ u : sphere (0 : E) 1, p + r₁ • u.val ≠ p) :
    (puncturedSphereMap p p r₀ h₀).Homotopic (puncturedSphereMap p p r₁ h₁) := by
  let r : C(unitInterval, ℝ) := ⟨fun t => (1 - (t : ℝ)) * r₀ + (t : ℝ) * r₁,
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)⟩
  apply puncturedSphereMap_homotopic_of_family p (ContinuousMap.const _ p) r
    rfl rfl (by simp [r]) (by simp [r]) _ h₀ h₁
  intro t u
  have hrt : 0 < r t := by
    change 0 < (1 - (t : ℝ)) * r₀ + (t : ℝ) * r₁
    exact (convex_Ioi (0 : ℝ)) hr₀ hr₁ (sub_nonneg.mpr t.property.2)
      t.property.1 (sub_add_cancel 1 (t : ℝ))
  exact affine_sphere_ne_of_norm_ne hrt.le (by simpa using hrt.ne) u

theorem puncturedSphereMap_center_homotopic (p c : E) {r : ℝ}
    (hinside : ‖c - p‖ < r)
    (h₀ : ∀ u : sphere (0 : E) 1, c + r • u.val ≠ p)
    (h₁ : ∀ u : sphere (0 : E) 1, p + r • u.val ≠ p) :
    (puncturedSphereMap p c r h₀).Homotopic (puncturedSphereMap p p r h₁) := by
  let cpath : C(unitInterval, E) := ⟨fun t => p + (1 - (t : ℝ)) • (c - p),
    continuous_const.add ((continuous_const.sub continuous_subtype_val).smul continuous_const)⟩
  have hc0 : cpath 0 = c := by simp [cpath]
  have hc1 : cpath 1 = p := by simp [cpath]
  apply puncturedSphereMap_homotopic_of_family p cpath (ContinuousMap.const _ r)
    hc0 hc1 rfl rfl _ h₀ h₁
  intro t u
  have hn : ‖cpath t - p‖ ≤ ‖c - p‖ := by
    change ‖(p + (1 - (t : ℝ)) • (c - p)) - p‖ ≤ _
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr t.property.2)]
    exact mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ t.property.1)
  exact affine_sphere_ne_of_norm_ne ((norm_nonneg _).trans_lt hinside).le
    (hn.trans_lt hinside).ne u

theorem puncturedSphereMap_outside_nullhomotopic (p c : E) {r : ℝ}
    (hr : 0 ≤ r) (houtside : r < ‖c - p‖)
    (h : ∀ u : sphere (0 : E) 1, c + r • u.val ≠ p) :
    ∃ q : ({p}ᶜ : Set E), (puncturedSphereMap p c r h).Homotopic (ContinuousMap.const _ q) := by
  have hcp : c ≠ p := by
    intro he
    rw [he, sub_self, norm_zero] at houtside
    exact (not_lt_of_ge hr) houtside
  have hzero : ∀ u : sphere (0 : E) 1, c + (0 : ℝ) • u.val ≠ p := by
    intro u
    simpa only [zero_smul, add_zero] using hcp
  let rpath : C(unitInterval, ℝ) := ⟨fun t => (1 - (t : ℝ)) * r,
    (continuous_const.sub continuous_subtype_val).mul continuous_const⟩
  have H := puncturedSphereMap_homotopic_of_family p (ContinuousMap.const _ c) rpath
    rfl rfl (by simp [rpath]) (by simp [rpath]) (h₀ := h) (h₁ := hzero) (by
      intro t u
      have hrt : 0 ≤ rpath t := mul_nonneg (sub_nonneg.mpr t.property.2) hr
      have hle : rpath t ≤ r := mul_le_of_le_one_left hr (sub_le_self _ t.property.1)
      exact affine_sphere_ne_of_norm_ne hrt (hle.trans_lt houtside).ne' u)
  have he : puncturedSphereMap p c 0 hzero = ContinuousMap.const _ (⟨c, hcp⟩ : ({p}ᶜ : Set E)) := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    change c + (0 : ℝ) • u.val = c
    rw [zero_smul, add_zero]
  exact ⟨⟨c, hcp⟩, he ▸ H⟩

end Wikipedia.HopfProblem.DegreeCollapse.PassageHomology
