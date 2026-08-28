import Wikipedia.NoExoticSixSphere.SphereSumSourceCover

/-!
# Continuous families glued across the actual sphere source cover

The middle and two cap regions are the fixed open sets already constructed
on the original sphere. Pointwise overlap equality and continuity at each
point of the corresponding region suffice for joint continuity of a family.
-/

noncomputable section

open Set Function Filter Topology

namespace NoExoticSixSphere.SphereSumNeck

variable {X Y : Type*} (B N S : X × Sphere 3 → Y)

def sourceFamilyGlue (p : X × Sphere 3) : Y := by
  classical
  exact if p.2 ∈ neckRegion then B p else if p.2 ∈ northRegion then N p else S p

theorem sourceFamilyGlue_middle {p : X × Sphere 3} (hp : p.2 ∈ neckRegion) :
    sourceFamilyGlue B N S p = B p := by
  simp only [sourceFamilyGlue, if_pos hp]

theorem sourceFamilyGlue_north
    (he : ∀ p, p.2 ∈ neckRegion → p.2 ∈ northRegion → B p = N p)
    {p : X × Sphere 3} (hp : p.2 ∈ northRegion) : sourceFamilyGlue B N S p = N p := by
  by_cases hb : p.2 ∈ neckRegion
  · exact (sourceFamilyGlue_middle B N S hb).trans (he p hb hp)
  · simp only [sourceFamilyGlue, if_neg hb, if_pos hp]

theorem sourceFamilyGlue_south
    (he : ∀ p, p.2 ∈ neckRegion → p.2 ∈ southRegion → B p = S p)
    {p : X × Sphere 3} (hp : p.2 ∈ southRegion) : sourceFamilyGlue B N S p = S p := by
  by_cases hb : p.2 ∈ neckRegion
  · exact (sourceFamilyGlue_middle B N S hb).trans (he p hb hp)
  · have hn : p.2 ∉ northRegion := fun hn ↦
      (not_lt_of_gt (northRegion_head_pos hn)) (southRegion_head_neg hp)
    simp only [sourceFamilyGlue, if_neg hb, if_neg hn]

theorem continuous_sourceFamilyGlue [TopologicalSpace X] [TopologicalSpace Y]
    (hB : ∀ p, p.2 ∈ neckRegion → ContinuousAt B p)
    (hN : ∀ p, p.2 ∈ northRegion → ContinuousAt N p)
    (hS : ∀ p, p.2 ∈ southRegion → ContinuousAt S p)
    (hBN : ∀ p, p.2 ∈ neckRegion → p.2 ∈ northRegion → B p = N p)
    (hBS : ∀ p, p.2 ∈ neckRegion → p.2 ∈ southRegion → B p = S p) :
    Continuous (sourceFamilyGlue B N S) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rcases sourceRegion_cover p.2 with hb | hn | hs
  · have he : sourceFamilyGlue B N S =ᶠ[𝓝 p] B := by
      filter_upwards [(isOpen_neckRegion.preimage continuous_snd).mem_nhds hb] with q hq
      exact sourceFamilyGlue_middle B N S hq
    exact (hB p hb).congr_of_eventuallyEq he
  · have he : sourceFamilyGlue B N S =ᶠ[𝓝 p] N := by
      filter_upwards [(isOpen_northRegion.preimage continuous_snd).mem_nhds hn] with q hq
      exact sourceFamilyGlue_north B N S hBN hq
    exact (hN p hn).congr_of_eventuallyEq he
  · have he : sourceFamilyGlue B N S =ᶠ[𝓝 p] S := by
      filter_upwards [(isOpen_southRegion.preimage continuous_snd).mem_nhds hs] with q hq
      exact sourceFamilyGlue_south B N S hBS hq
    exact (hS p hs).congr_of_eventuallyEq he

end NoExoticSixSphere.SphereSumNeck
