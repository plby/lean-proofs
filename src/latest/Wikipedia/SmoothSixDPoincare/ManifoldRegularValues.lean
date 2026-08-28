import Wikipedia.SmoothSixDPoincare.RegularValuesOn
import Wikipedia.SmoothSixDPoincare.LocalInverseIntoManifold
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Equal-dimensional Sard for native boundaryless manifolds

The proof uses actual smooth charts, the proved Euclidean Sard lemma, and a
countable chart cover. The conclusion refers to the original map and its
native manifold differential, not to a supplied transversality principle.
-/

noncomputable section

open Set Function MeasureTheory MeasureTheory.Measure
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.RegularValues

variable {E F H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [IsAddHaarMeasure μ]

omit [I.Boundaryless] [IsManifold I ∞ X] in
/-- A single actual chart has only a null exceptional set of values. -/
theorem exists_null_exceptional_values_in_chart
    (c : PartialDiffeomorph I 𝓘(ℝ, E) X E ∞) {f : X → F} {s : Set X}
    (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ T : Set F, μ T = 0 ∧ ∀ x ∈ c.source ∩ s, f x ∉ T →
      Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  let L : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hdim
  let W : Set F := L '' (c.target ∩ c.symm ⁻¹' s)
  let G : F → F := fun z => f (c.symm (L.symm z))
  have hcoord (z : F) (hz : z ∈ W) :
      L.symm z ∈ c.target ∧ c.symm (L.symm z) ∈ s := by
    obtain ⟨w, hw, rfl⟩ := hz
    rw [L.symm_apply_apply]
    exact hw
  have hsmooth (z : F) (hz : z ∈ W) : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ G z := by
    have hh := hcoord z hz
    exact (hf.contMDiffAt (hs.mem_nhds hh.2)).comp z
      ((c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds hh.1)).comp z
        L.symm.contDiff.contMDiff.contMDiffAt)
  obtain ⟨T, hT, hgood⟩ := exists_null_exceptional_values_on μ
    (fun z hz => (hsmooth z hz).mdifferentiableAt (by simp) |>.differentiableAt)
  refine ⟨T, hT, ?_⟩
  intro x hx hfx
  let z := L (c x)
  have hz : z ∈ W := by
    refine ⟨c x, ⟨c.map_source' hx.1, ?_⟩, rfl⟩
    change c.symm (c x) ∈ s
    have heq : c.symm (c x) = x := c.left_inv' hx.1
    rw [heq]
    exact hx.2
  have hpoint : c.symm (L.symm z) = x := by
    change c.symm (L.symm (L (c x))) = x
    rw [L.symm_apply_apply]
    exact c.left_inv' hx.1
  have hvalue : G z = f x := congrArg f hpoint
  have hbij := hgood z hz (by rwa [hvalue])
  have hfx' : MDifferentiableAt I 𝓘(ℝ, F) f (c.symm (L.symm z)) :=
    (hf.contMDiffAt (hs.mem_nhds (hcoord z hz).2)).mdifferentiableAt (by simp)
  have hinner : MDifferentiableAt 𝓘(ℝ, F) I (c.symm ∘ L.symm) z :=
    (c.symm.mdifferentiableAt (by simp) (hcoord z hz).1).comp z
      L.symm.toContinuousLinearMap.differentiableAt.mdifferentiableAt
  rw [← mfderiv_eq_fderiv] at hbij
  change Bijective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (f ∘ (c.symm ∘ L.symm)) z) at hbij
  rw [mfderiv_comp z hfx' hinner] at hbij
  have hsurj : Surjective (mfderiv I 𝓘(ℝ, F) f (c.symm (L.symm z))) := by
    intro w
    obtain ⟨v, hv⟩ := hbij.surjective w
    exact ⟨mfderiv 𝓘(ℝ, F) I (c.symm ∘ L.symm) z v, hv⟩
  exact hpoint ▸ hsurj

/-- Native critical values on a smooth open domain lie in a Haar-null set. -/
theorem exists_null_exceptional_values_manifold [LindelofSpace X]
    {f : X → F} {s : Set X} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ T : Set F, μ T = 0 ∧ ∀ x ∈ s, f x ∉ T →
      Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  classical
  let c (x : X) := NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) x
  let U : X → Set X := fun x => (c x).source
  have hU : ∀ x, IsOpen (U x) := fun x => (c x).open_source
  have hcover : (univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨t, htcount, ht⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let _ := htcount.to_subtype
  choose T hT hgood using fun i : t =>
    exists_null_exceptional_values_in_chart μ (c i) hs hf hdim
  refine ⟨⋃ i : t, T i, measure_iUnion_null hT, ?_⟩
  intro x hx hfx
  obtain ⟨i, hit, hxi⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  apply hgood ⟨i, hit⟩ x ⟨hxi, hx⟩
  intro hi
  exact hfx (mem_iUnion.mpr ⟨⟨i, hit⟩, hi⟩)

end Wikipedia.SmoothSixDPoincare.RegularValues
