import Wikipedia.HopfProblem.DegreeCollapseLocalHeightTranslation
import Mathlib.Topology.Order.IntermediateValue

/-!
# Whole level and sublevel transport by the normalized complete flow

Exact height translation inside a closed band also determines which
side of its moving level an arbitrary point occupies. An intermediate
crossing would flow back to the original level. This proves the whole
sublevel identity without assuming trajectories stay in the band.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {X : Type*} [TopologicalSpace X]

theorem normalized_flow_level_image (F : Flow ℝ X) {f : X → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hshift : ∀ x t, f x ∈ Icc a b → f x - t ∈ Icc a b → f (F t x) = f x - t) :
    F (a - b) '' {x : X | f x = a} = {x : X | f x = b} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change f x = a at hx
    have hh := hshift x (a - b) (by rw [hx]; exact ⟨le_rfl, hab⟩)
      (by rw [hx]; constructor <;> linarith)
    change f (F (a - b) x) = b
    linarith
  · intro hy
    change f y = b at hy
    have hh := hshift y (b - a) (by rw [hy]; exact ⟨hab, le_rfl⟩)
      (by rw [hy]; constructor <;> linarith)
    refine ⟨F (b - a) y, ?_, ?_⟩
    · change f (F (b - a) y) = a
      linarith
    · rw [← F.map_add, show a - b + (b - a) = 0 by ring, F.map_zero_apply]

theorem normalized_flow_sublevel_iff (F : Flow ℝ X) {f : X → ℝ}
    (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (hshift : ∀ x t, f x ∈ Icc a b → f x - t ∈ Icc a b → f (F t x) = f x - t)
    (x : X) : f (F (a - b) x) ≤ b ↔ f x ≤ a := by
  let γ : ℝ → ℝ := fun s => f (F (-s) x) - (a + s)
  have hγ : Continuous γ :=
    (hf.comp (F.continuous continuous_neg continuous_const)).sub
      (continuous_const.add continuous_id)
  have hstart : γ 0 = f x - a := by simp only [γ, neg_zero, F.map_zero_apply, add_zero]
  have hend : γ (b - a) = f (F (a - b) x) - b := by
    dsimp [γ]
    rw [neg_sub, show a + (b - a) = b by ring]
  have hzero (s : ℝ) (hs : s ∈ Icc 0 (b - a)) (hgs : γ s = 0) : f x = a := by
    have hz : f (F (-s) x) = a + s := by dsimp [γ] at hgs; linarith
    have hh := hshift (F (-s) x) s
      (by rw [hz]; constructor <;> linarith [hs.1, hs.2])
      (by rw [hz]; constructor <;> linarith)
    rw [← F.map_add, add_neg_cancel, F.map_zero_apply] at hh
    linarith
  have hzeroEnd (hx : f x = a) : γ (b - a) = 0 := by
    have hh := hshift x (a - b) (by rw [hx]; exact ⟨le_rfl, hab⟩)
      (by rw [hx]; constructor <;> linarith)
    rw [hend]
    linarith
  constructor
  · intro hy
    by_contra hx
    have hx' : a < f x := lt_of_not_ge hx
    obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc' (sub_nonneg.mpr hab) hγ.continuousOn
      (show (0 : ℝ) ∈ Icc (γ (b - a)) (γ 0) by rw [hstart, hend]; constructor <;> linarith)
    linarith [hzero s hs hgs]
  · intro hx
    by_contra hy
    have hy' : b < f (F (a - b) x) := lt_of_not_ge hy
    obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc (sub_nonneg.mpr hab) hγ.continuousOn
      (show (0 : ℝ) ∈ Icc (γ 0) (γ (b - a)) by rw [hstart, hend]; constructor <;> linarith)
    have hh := hzeroEnd (hzero s hs hgs)
    rw [hend] at hh
    linarith

theorem normalized_flow_sublevel_image (F : Flow ℝ X) {f : X → ℝ}
    (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (hshift : ∀ x t, f x ∈ Icc a b → f x - t ∈ Icc a b → f (F t x) = f x - t) :
    F (a - b) '' {x : X | f x ≤ a} = {x : X | f x ≤ b} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (normalized_flow_sublevel_iff F hf hab hshift x).mpr hx
  · intro hy
    have hi : F (a - b) (F (b - a) y) = y := by
      rw [← F.map_add, show a - b + (b - a) = 0 by ring, F.map_zero_apply]
    refine ⟨F (b - a) y, ?_, hi⟩
    apply (normalized_flow_sublevel_iff F hf hab hshift _).mp
    rw [hi]
    exact hy

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
