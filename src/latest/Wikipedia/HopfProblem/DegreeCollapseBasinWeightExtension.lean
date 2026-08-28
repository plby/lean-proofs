import Wikipedia.HopfProblem.DegreeCollapseCriticalOrbitLabelGerms
import Wikipedia.HopfProblem.DegreeCollapseNativeLevelWeights

/-!
# Orbit-invariant extension of the basin weight

Off the chosen level basin, continuity prevents an orbit from changing
sides of the level. Extending a basin weight by one below and zero above
therefore preserves exact flow invariance. Constant germs at the selected
critical points extend to full germs, and propagate to every orbit with
the corresponding endpoint limit. Global smoothness still needs the
classification of the points outside the level basin in the chosen band.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {X : Type*} [TopologicalSpace X]

theorem height_side_of_not_levelBasin (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {a : ℝ} {x : X} (hx : x ∉ levelBasin F f a) (t : ℝ) :
    f (F t x) < a ↔ f x < a := by
  have hc : Continuous (fun s : ℝ => f (F s x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  have hside (s u : ℝ) (hs : f (F s x) < a) : f (F u x) < a := by
    by_contra hu
    obtain ⟨v, hv⟩ := intermediate_value_univ s u hc
      (show a ∈ Icc (f (F s x)) (f (F u x)) from ⟨hs.le, le_of_not_gt hu⟩)
    exact hx ⟨v, hv⟩
  constructor
  · intro ht
    simpa only [F.map_zero_apply] using hside t 0 ht
  · intro hx
    exact hside 0 t (by simpa only [F.map_zero_apply] using hx)

open Classical in
def extendedBasinWeight (F : Flow ℝ X) (f : X → ℝ) (a : ℝ) (w : X → ℝ) (x : X) : ℝ :=
  if x ∈ levelBasin F f a then w x else if f x < a then 1 else 0

theorem extendedBasinWeight_eq (F : Flow ℝ X) (f : X → ℝ) (a : ℝ) (w : X → ℝ)
    {x : X} (hx : x ∈ levelBasin F f a) : extendedBasinWeight F f a w x = w x := by
  classical
  simp only [extendedBasinWeight, if_pos hx]

theorem extendedBasinWeight_flow (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    (a : ℝ) (w : X → ℝ)
    (hinv : ∀ x ∈ levelBasin F f a, ∀ t : ℝ, w (F t x) = w x) (x : X) (t : ℝ) :
    extendedBasinWeight F f a w (F t x) = extendedBasinWeight F f a w x := by
  classical
  by_cases hx : x ∈ levelBasin F f a
  · rw [extendedBasinWeight_eq _ _ _ _ ((levelBasin_flow_iff F f a t x).mpr hx),
      extendedBasinWeight_eq _ _ _ _ hx]
    exact hinv x hx t
  · have htx : F t x ∉ levelBasin F f a := fun h => hx ((levelBasin_flow_iff F f a t x).mp h)
    simp only [extendedBasinWeight, if_neg hx, if_neg htx, height_side_of_not_levelBasin F hf hx t]

theorem extendedBasinWeight_mem_Icc (F : Flow ℝ X) (f : X → ℝ) (a : ℝ) (w : X → ℝ)
    (hw : ∀ x ∈ levelBasin F f a, w x ∈ Icc (0 : ℝ) 1) (x : X) :
    extendedBasinWeight F f a w x ∈ Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : x ∈ levelBasin F f a
  · rw [extendedBasinWeight_eq _ _ _ _ hx]
    exact hw x hx
  · simp only [extendedBasinWeight, if_neg hx]
    split_ifs <;> norm_num

theorem extendedBasinWeight_lower_germ (F : Flow ℝ X) {f : X → ℝ} {a : ℝ} {w : X → ℝ}
    {p : X} (hf : ContinuousAt f p) (hp : f p < a)
    (hw : ∀ᶠ x in 𝓝 p, x ∈ levelBasin F f a → w x = 1) :
    extendedBasinWeight F f a w =ᶠ[𝓝 p] fun _ => 1 := by
  classical
  have hheight : ∀ᶠ x in 𝓝 p, f x < a := hf (eventually_lt_nhds hp)
  filter_upwards [hw, hheight] with x hx hfx
  by_cases hbasin : x ∈ levelBasin F f a
  · exact (extendedBasinWeight_eq _ _ _ _ hbasin).trans (hx hbasin)
  · simp only [extendedBasinWeight, if_neg hbasin, if_pos hfx]

theorem extendedBasinWeight_upper_germ (F : Flow ℝ X) {f : X → ℝ} {a : ℝ} {w : X → ℝ}
    {p : X} (hf : ContinuousAt f p) (hp : a < f p)
    (hw : ∀ᶠ x in 𝓝 p, x ∈ levelBasin F f a → w x = 0) :
    extendedBasinWeight F f a w =ᶠ[𝓝 p] fun _ => 0 := by
  classical
  have hheight : ∀ᶠ x in 𝓝 p, a < f x := hf (eventually_gt_nhds hp)
  filter_upwards [hw, hheight] with x hx hfx
  by_cases hbasin : x ∈ levelBasin F f a
  · exact (extendedBasinWeight_eq _ _ _ _ hbasin).trans (hx hbasin)
  · simp only [extendedBasinWeight, if_neg hbasin, if_neg (not_lt_of_gt hfx)]

theorem constant_germ_of_endpoint_limit (F : Flow ℝ X) {w : X → ℝ}
    (hinv : ∀ x t, w (F t x) = w x) {p x : X} {k : ℝ}
    {l : Filter ℝ} [NeBot l] (hlim : Tendsto (fun t => F t x) l (𝓝 p))
    (hgerm : w =ᶠ[𝓝 p] fun _ => k) : w =ᶠ[𝓝 x] fun _ => k := by
  obtain ⟨t, ht⟩ := (hlim.eventually (eventually_eventually_nhds.mpr hgerm)).exists
  have hc : Continuous (fun y => F t y) := F.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (hinv y t).symm.trans hy

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
