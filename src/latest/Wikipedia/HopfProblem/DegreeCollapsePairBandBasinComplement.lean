import Wikipedia.HopfProblem.DegreeCollapseBasinWeightExtension
import Wikipedia.HopfProblem.DegreeCollapseFlowEndpoints

/-!
# The complement of the middle level basin in an isolated pair band

Every point in the closed band whose orbit misses the middle level has
the lower critical point as its backward endpoint, or the upper critical
point as its forward endpoint. Compact strict-descent endpoint convergence
and the height-side barrier construct this classification, including the
critical points themselves.
-/

noncomputable section

open Set Function Filter
open scoped Topology
open Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem pair_band_basin_complement (F : Flow ℝ X) {f : X → ℝ}
    (hf : Continuous f) {S : Set X} (hinj : InjOn f S)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x)))
    {p q : X} {l a u : ℝ} (hla : l < a) (hau : a < u)
    (hp : f p < a) (hq : a < f q)
    (hpair : ∀ z ∈ S, f z ∈ Icc l u → z = p ∨ z = q)
    {x : X} (hx : f x ∈ Icc l u) (hnot : x ∉ levelBasin F f a) :
    (f x < a ∧ Tendsto (fun t => F t x) atBot (𝓝 p)) ∨
      (a < f x ∧ Tendsto (fun t => F t x) atTop (𝓝 q)) := by
  obtain ⟨r, hr, s, hs, hrlim, hslim, -⟩ :=
    exists_strict_descent_flow_endpoints F hf hinj hmono hstrict x
  have hrheight : Tendsto (fun t => f (F t x)) atBot (𝓝 (f r)) :=
    hf.continuousAt.tendsto.comp hrlim
  have hsheight : Tendsto (fun t => f (F t x)) atTop (𝓝 (f s)) :=
    hf.continuousAt.tendsto.comp hslim
  by_cases hxa : f x < a
  · have hrle : f r ≤ a := isClosed_Iic.mem_of_tendsto hrheight (Eventually.of_forall
      (fun t => ((height_side_of_not_levelBasin F hf hnot t).mpr hxa).le))
    have hxr : f x ≤ f r := by
      simpa only [F.map_zero_apply] using (hmono x).ge_of_tendsto hrheight 0
    have hrp : r = p := (hpair r hr ⟨hx.1.trans hxr, hrle.trans hau.le⟩).resolve_right (by
      intro heq
      rw [heq] at hrle
      exact (not_le_of_gt hq) hrle)
    exact Or.inl ⟨hxa, by simpa only [hrp] using hrlim⟩
  · have hneq : f x ≠ a := fun heq => hnot ⟨0, by simpa only [F.map_zero_apply] using heq⟩
    have hax : a < f x := lt_of_le_of_ne (le_of_not_gt hxa) (Ne.symm hneq)
    have hsge : a ≤ f s := isClosed_Ici.mem_of_tendsto hsheight (Eventually.of_forall
      (fun t => le_of_not_gt (fun ht => hxa ((height_side_of_not_levelBasin F hf hnot t).mp ht))))
    have hsx : f s ≤ f x := by
      simpa only [F.map_zero_apply] using (hmono x).le_of_tendsto hsheight 0
    have hsq : s = q := (hpair s hs ⟨hla.le.trans hsge, hsx.trans hx.2⟩).resolve_left (by
      intro heq
      rw [heq] at hsge
      exact (not_le_of_gt hp) hsge)
    exact Or.inr ⟨hax, by simpa only [hsq] using hslim⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
