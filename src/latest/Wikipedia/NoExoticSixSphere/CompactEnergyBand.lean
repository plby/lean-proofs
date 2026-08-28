import Wikipedia.NoExoticSixSphere.CompactLoweringCover

/-!
# An open neighborhood of a compact energy level contains a band

The image of the compact complement is closed and does not contain the chosen
energy. A small real ball disjoint from that image supplies the band, including
when the level or its complement is empty.
-/

open Set

namespace NoExoticSixSphere.FiniteControlledLowering

variable {Y : Type*} [TopologicalSpace Y]

theorem exists_energy_band_in_open (energy : Y → ℝ) (S : Set Y)
    (hS : IsCompact S) (henergy : ContinuousOn energy S) (level : ℝ)
    (U : Set Y) (hU : IsOpen U) (hlevel : ∀ x ∈ S, energy x = level → x ∈ U) :
    ∃ a > 0, ∀ x ∈ S, |energy x - level| ≤ a → x ∈ U := by
  have hclosed : IsClosed (energy '' (S \ U)) :=
    ((hS.diff hU).image_of_continuousOn (henergy.mono sdiff_subset)).isClosed
  have hnot : level ∈ (energy '' (S \ U))ᶜ := by
    rintro ⟨x, ⟨hxS, hxU⟩, hx⟩
    exact hxU (hlevel x hxS hx)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl level hnot
  refine ⟨r / 2, by positivity, ?_⟩
  intro x hxS hx
  by_contra hxU
  have hdist : dist (energy x) level < r := by
    rw [Real.dist_eq]
    linarith
  exact hball hdist ⟨x, ⟨hxS, hxU⟩, rfl⟩

end NoExoticSixSphere.FiniteControlledLowering
