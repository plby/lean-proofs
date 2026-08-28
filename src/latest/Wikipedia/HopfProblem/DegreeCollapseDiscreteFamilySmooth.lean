import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A discrete family of smooth maps is a smooth map on the disjoint product

Give the discrete index the standard zero-dimensional chart structure.
On each open slice the family is the given smooth map composed with the
second projection. Its image is exactly the union of the individual ranges.
The zero-dimensional discrete factor does not increase the model dimension.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {ι V E H M : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiff_discrete_family (f : ι → V → M)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, V) I ∞ (f i)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) ι := ChartedSpace.ofDiscreteTopology
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞
      (fun p : ι × V => f p.1 p.2) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) ι := ChartedSpace.ofDiscreteTopology
  change ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞
    (fun p : ι × V => f p.1 p.2)
  intro p
  have hg : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞
      (fun q : ι × V => f p.1 q.2) p := (hf p.1).contMDiffAt.comp p contMDiffAt_snd
  apply hg.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : ι × V in 𝓝 p, q.1 ∈ ({p.1} : Set ι) :=
    ((isOpen_discrete ({p.1} : Set ι)).preimage continuous_fst).mem_nhds (mem_singleton _)
  filter_upwards [hnear] with q hq
  change f q.1 q.2 = f p.1 q.2
  rw [mem_singleton_iff.mp hq]

theorem range_discrete_family (f : ι → V → M) :
    range (fun p : ι × V => f p.1 p.2) = ⋃ i, range (f i) := by
  ext x
  constructor
  · rintro ⟨⟨i, v⟩, rfl⟩
    exact mem_iUnion.mpr ⟨i, v, rfl⟩
  · intro hx
    obtain ⟨i, v, hv⟩ := mem_iUnion.mp hx
    exact ⟨(i, v), hv⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
