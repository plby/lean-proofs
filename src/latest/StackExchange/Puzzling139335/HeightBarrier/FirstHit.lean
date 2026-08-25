import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact

/-!
# First crossing of a scalar level

A continuous function that starts below a level and ends above it has a first
level hit strictly inside the parameter interval. Before that hit, it stays
strictly below the level.
-/

open Set

namespace Puzzling139335.HeightBarrier

/-- The first time a continuous function on `[0,1]` reaches an intermediate level. -/
theorem exists_first_level {f : ℝ → ℝ} {h : ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (h₀ : f 0 < h) (h₁ : h < f 1) :
    ∃ t ∈ Ioo (0 : ℝ) 1, f t = h ∧ ∀ s ∈ Ico (0 : ℝ) t, f s < h := by
  let K : Set ℝ := Icc (0 : ℝ) 1 ∩ f ⁻¹' {h}
  have hKcompact : IsCompact K :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  have hKnonempty : K.Nonempty := by
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc zero_le_one hf ⟨h₀.le, h₁.le⟩
    exact ⟨t, ht, mem_singleton_iff.mpr hft⟩
  obtain ⟨t, ht⟩ := hKcompact.exists_isLeast hKnonempty
  have htI : t ∈ Icc (0 : ℝ) 1 := ht.1.1
  have hft : f t = h := mem_singleton_iff.mp ht.1.2
  have ht₀ : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := le_antisymm (not_lt.mp hnot) htI.1
    exact h₀.ne (htzero ▸ hft)
  have ht₁ : t < 1 := by
    by_contra hnot
    have htone : t = 1 := le_antisymm htI.2 (not_lt.mp hnot)
    exact h₁.ne (htone ▸ hft).symm
  refine ⟨t, ⟨ht₀, ht₁⟩, hft, ?_⟩
  intro s hs
  by_contra hnot
  have hs₁ : s ≤ 1 := hs.2.le.trans htI.2
  have hf' : ContinuousOn f (Icc (0 : ℝ) s) :=
    hf.mono (fun _ hx => ⟨hx.1, hx.2.trans hs₁⟩)
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc hs.1 hf' ⟨h₀.le, not_lt.mp hnot⟩
  have hrK : r ∈ K := ⟨⟨hr.1, hr.2.trans hs₁⟩, mem_singleton_iff.mpr hfr⟩
  exact (not_le_of_gt hs.2) ((ht.2 hrK).trans hr.2)

end Puzzling139335.HeightBarrier
