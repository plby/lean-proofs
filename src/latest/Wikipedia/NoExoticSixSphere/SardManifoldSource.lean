import Wikipedia.NoExoticSixSphere.SardTheorem
import Wikipedia.NoExoticSixSphere.ManifoldLevelNormalForm

/-!
# Sard's theorem with a manifold source

Source charts and second countability transfer the proved Euclidean theorem
to a smooth vector-valued map on an open subset of a boundaryless manifold.
All chart domains and critical loci refer to the original smooth structure.
-/

open scoped Manifold ContDiff Topology
open Set Filter MeasureTheory MeasureTheory.Measure

namespace NoExoticSixSphere.Sard

variable {B F : Type} {H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SecondCountableTopology M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem measure_manifoldCriticalValues_eq_zero
    (μ : Measure F) [IsAddHaarMeasure μ] {f : M → F} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U) :
    μ (f '' {x | x ∈ U ∧ ¬ Function.Surjective (mfderiv I 𝓘(ℝ, F) f x)}) = 0 := by
  let s := {x | x ∈ U ∧ ¬ Function.Surjective (mfderiv I 𝓘(ℝ, F) f x)}
  apply measure_image_eq_zero_of_local μ f s
  intro x hx
  let c := modelChartPartialDiffeomorph (I := I) x
  let W := c.target ∩ c.symm ⁻¹' U
  let fc : B → F := f ∘ c.symm
  have hW : IsOpen W := c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hU
  have hcx : x ∈ c.source := mem_extChartAt_source x
  have hfc : ContDiffOn ℝ ∞ fc W :=
    (hf.comp (c.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right).contDiffOn
  have hnull := measure_criticalValues_eq_zero μ hW hfc
  refine ⟨s ∩ c.source, inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (c.open_source.mem_nhds hcx)), ?_⟩
  apply measure_mono_null _ hnull
  rintro _ ⟨y, hy, rfl⟩
  have hcy : c y ∈ c.target := c.map_source' hy.2
  have hleft : c.symm (c y) = y := c.left_inv' hy.2
  have hyW : c y ∈ W := ⟨hcy, by
    change c.symm (c y) ∈ U
    rw [hleft]
    exact hy.1.1⟩
  refine ⟨c y, ⟨hyW, ?_⟩, ?_⟩
  · intro hs
    have hdf := (hf.contMDiffAt (hU.mem_nhds hy.1.1)).mdifferentiableAt (by simp)
    have hi : IsLocalDiffeomorphAt 𝓘(ℝ, B) I ∞ c.symm (c y) :=
      ⟨c.symm, hcy, fun _ _ ↦ rfl⟩
    have hcomp := mfderiv_comp_of_eq (I := 𝓘(ℝ, B)) (I' := I) (I'' := 𝓘(ℝ, F))
      hdf (hi.mdifferentiableAt (by simp)) hleft
    rw [mfderiv_eq_fderiv] at hcomp
    apply hy.1.2
    intro v
    obtain ⟨u, hu⟩ := hs v
    refine ⟨mfderiv 𝓘(ℝ, B) I c.symm (c y) u, ?_⟩
    change fderiv ℝ fc (c y) = _ at hcomp
    rw [hcomp, hleft] at hu
    exact hu
  · change f (c.symm (c y)) = f y
    rw [hleft]

end NoExoticSixSphere.Sard
