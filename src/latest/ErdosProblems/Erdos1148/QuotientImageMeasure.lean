import Mathlib

/-!
# An image-measure bound for a fundamental-domain parametrization

If a map identifies points only within group orbits, the measure of an
image under the fundamental-domain measure is at most the original
parameter measure. This will compare flow-parameter areas with closed
orbit measures.
-/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped Pointwise

@[to_additive addFundamentalDomain_map_image_le]
theorem fundamentalDomain_map_image_le {G X Y : Type*} [Group G] [Countable G]
    [MeasurableSpace X] [MeasurableSpace Y] [MulAction G X] [MeasurableConstSMul G X]
    (μ : Measure X) [SMulInvariantMeasure G X μ] {s : Set X}
    (hs : IsFundamentalDomain G s μ) {f : X → Y}
    (hf : Measurable f) (hsep : ∀ x y, f x = f y → ∃ g : G, g • x = y)
    (E : Set X) (hE : MeasurableSet (f '' E)) :
    (Measure.map f (μ.restrict s)) (f '' E) ≤ μ E := by
  rw [Measure.map_apply hf hE, Measure.restrict_apply (hf hE)]
  have hsub : f ⁻¹' (f '' E) ∩ s ⊆ ⋃ g : G, g • E ∩ s := by
    rintro y ⟨⟨x, hx, hxy⟩, hys⟩
    obtain ⟨g, hg⟩ := hsep x y hxy
    apply Set.mem_iUnion.mpr
    refine ⟨g, ?_, hys⟩
    rw [← hg]
    exact Set.smul_mem_smul_set hx
  calc
    μ (f ⁻¹' (f '' E) ∩ s) ≤ μ (⋃ g : G, g • E ∩ s) := measure_mono hsub
    _ ≤ ∑' g : G, μ (g • E ∩ s) := measure_iUnion_le _
    _ = μ E := (hs.measure_eq_tsum E).symm

end Erdos1148.DukeArithmetic
